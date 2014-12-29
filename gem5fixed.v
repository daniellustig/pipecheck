(******************************************************************************)
(* PipeCheck: Specifying and Verifying Microarchitectural                     *)
(* Enforcement of Memory Consistency Models                                   *)
(*                                                                            *)
(* Copyright (c) 2014 Daniel Lustig, Princeton University                     *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(*                                                                            *)
(* You should have received a copy of the GNU Lesser General Public           *)
(* License along with this library; if not, write to the Free Software        *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  *)
(* USA                                                                        *)
(******************************************************************************)

Require Import Ensembles.
Require Import Arith.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import wmm.
Require Import util2.
Require Import dot.
Require Import topsort.
Require Import stages.

(** * Fixed gem5 O3 Pipeline *)

(** ** Local Reorderings at different stages *)

(** [FIFO]: any ordering guaranteed at the input is also guaranteed at the
  output.  This is the common case. *)
Definition FIFO : LocalReordering := fun _ => fun ordering => ordering.

(** [NoOrderGuarantees]: Operations can leave the stage in any order; nothing
  is guaranteed. *)
Definition NoOrderGuarantees : LocalReordering := fun _ => fun _ => [].

(** [Restore]: The output order is guaranteed to match some previous
  ordering *)
Definition Restore (n : nat) : LocalReordering :=
  fun e => fun _ => nth n e [].

(** ** Special Edge Maps *)

(** In some cases, we need to add certain extra edges to the graph to
  capture non-local effects. *)

(** In most cases, though, we don't need to add any special edges *)
Definition NoSpecialEdges : SpecialEdgeMap :=
  fun _ _ _ => [].

(** The store buffer only allows one outstanding unacknowledged store at a
  time. *)

(** ** Same Address *)
(** *** Load  x -> Load  x (Locally) : Speculative Load Reordering *)

Fixpoint LoadCacheLineSpecialEdges
  (n c : nat)
  (e_before : list Event)
  (e : Event)
  (e_after : list Event)
  : GlobalGraph :=
  [((9 * c + 4, eiid e), (9 * c + 5, eiid e), "LoadCacheLine")].

Fixpoint SpeculativeLoadReorderingSpecialEdges
  (n c : nat)
  (e_before : list Event)
  (e : Event)
  (e_after : list Event)
  : GlobalGraph :=
  match e_after with
  | h::t =>
    match dirn h with
    | R =>
      ((4 + 9 * c, eiid e), (5 + 9 * c, eiid h), "SLR")
      :: SpeculativeLoadReorderingSpecialEdges n c e_before e t
    | _ => SpeculativeLoadReorderingSpecialEdges n c e_before e t
    end
  | _ => []
  end.

Fixpoint LoadSpecialEdges
  (n c : nat)
  (e_before : list Event)
  (e : Event)
  (e_after : list Event)
  : GlobalGraph :=
  LoadCacheLineSpecialEdges n c e_before e e_after ++
  SpeculativeLoadReorderingSpecialEdges n c e_before e e_after.

(** *** Load  x -> Store x (Locally) : Load checks for entries <= ID in store buffer
  Interpret FR edges as ``don't look at later stores'' *)
(** *** Store x -> Load  x (Locally) : Stores check for ordering violations
  When the store executes, squash the load if it already performed.
  Store set predictors are here too. *)

Fixpoint StoreLoadSpecialEdges
  (n c : nat)
  (e_before : list Event)
  (e : Event)
  (e_after : list Event)
  : GlobalGraph :=
  match e_after with
  | h::t =>
    match (dirn h, nat_compare (loc e) (loc h)) with
    | (R, Eq) => [((4 + 9 * c, eiid e), (3 + 9 * c, eiid h), "StoreLoad")]
    | _ => StoreLoadSpecialEdges n c e_before e t
    end
  | _ => []
  end.

(** *** Store x -> Store x (Locally) : Store buffer ordered by pre-issue order
  Performing location is rename, not execute!  SB slot reserved at rename! *)

(** ** Different Address *)
(** *** Load  x -> Load  y (Remotely) : Fails! *)
(** *** Load  x -> Store y (Remotely) : Load -> In-order commit -> Store *)
(** *** Store x -> Store y (Remotely) : Store buffer is one at a time *)

Fixpoint StoreBufferSpecialEdges
  (n c : nat)
  (e_before : list Event)
  (e : Event)
  (e_after : list Event)
  : GlobalGraph :=
  match e_after with
  | h::t =>
    match dirn h with
    | R => StoreBufferSpecialEdges n c e_before e t
    | W => [((9 * n + 1, eiid e), (9 * c + 7, eiid h), "StoreBuffer")]
    end
  | _ => []
  end.

(** * Pipeline Definition *)

(** ** Pipeline Stages *)

(** Each pipeline stage is defined by a name, a [LocalReordering],
  and a function adding any special edges (in this case, only at the store
  buffer). *)

Definition gem5fixed_O3_PipelineStages n c := [
  mkStage "Fetch"               FIFO                    NoSpecialEdges;
  mkStage "Decode"              FIFO                    NoSpecialEdges;
  mkStage "Rename"              FIFO                    NoSpecialEdges;
  mkStage "Issue"               NoOrderGuarantees       NoSpecialEdges;
  mkStage "Execute"             NoOrderGuarantees       NoSpecialEdges;
  mkStage "CacheLineInvalidate" NoOrderGuarantees       NoSpecialEdges;
  mkStage "Writeback"           NoOrderGuarantees       NoSpecialEdges;
  mkStage "Commit"              (Restore (2 + 9 * c))   NoSpecialEdges;
  mkStage "StoreBuffer"         FIFO                    (StoreBufferSpecialEdges n c)
].
    
Definition gem5fixed_O3_MemoryHierarchyStages := [
  mkStage "L2CacheForWrites"  NoOrderGuarantees NoSpecialEdges;
  mkStage "Retire"            NoOrderGuarantees NoSpecialEdges
].

Definition gem5fixed_O3_AllStages n :=
  fold_left (app (A:=_)) (map (gem5fixed_O3_PipelineStages n) [0 ... n-1]) []
  ++ gem5fixed_O3_MemoryHierarchyStages.

Definition StagesOfCore
  (c : nat)
  (l : list nat)
  : list nat :=
  map (fun x => x + 9 * c) l.

(** ** Pipeline Paths *)

Definition gem5fixed_O3_PathOptions
  (n : nat)
  (e : Event)
  : PathOptions :=
  let c := proc (iiid e) in
  match dirn e with
  | R => [
    mkPathOption (String.append "Read" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 4] ++ StagesOfCore c [6 ... 8])
      [mkPerformStages (4 + 9 * c) [0 ... n-1] [0 ... n-1] (Some (5 + 9 * c)) true]
      (LoadSpecialEdges n c)
    ]
  | W => [
    mkPathOption (String.append "Write" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 4] ++ StagesOfCore c [6 ... 8] ++ StagesOfCore n [0; 1])
      [mkPerformStages (2 + 9 * c) [c] [c] None false;
       mkPerformStages (9 * n) [0 ... n-1] [0 ... n-1] None true]
      (StoreLoadSpecialEdges n c)
    ]
  end.

(** ** Pipeline Definition *)

Definition gem5fixed_O3_Pipeline (n : nat) :=
  mkPipeline
    "gem5fixed_O3"
    (gem5fixed_O3_AllStages n)
    (gem5fixed_O3_PathOptions n).

