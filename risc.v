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

(** * Traditional Five-Stage RISC Pipeline *)

(** ** Local Reorderings at different stages *)

(** [FIFO]: any ordering guaranteed at the input is also guaranteed at the
  output.  This is the common case. *)
Definition FIFO : LocalReordering :=
  fun _ ordering => ordering.

(** [NoOrderGuarantees]: Operations can leave the stage in any order; nothing
  is guaranteed. *)
Definition NoOrderGuarantees : LocalReordering :=
  fun _ _ => [].

(** ** Special Edge Maps *)

(** In most cases, we don't need to add any special edges *)
Definition NoSpecialEdges : SpecialEdgeMap :=
  fun _ _ _ => [].

(** The store buffer only allows one outstanding unacknowledged store at a
  time. *)

Fixpoint StoreBufferSpecialEdges
  (c n : nat)
  (e_before : list Event)
  (e : Event)
  (e_after : list Event)
  : GlobalGraph :=
  match e_after with
  | h::t =>
    match dirn h with
    | R => StoreBufferSpecialEdges c n e_before e t
    | W => [((6 * n, eiid e), (5 + 6 * c, eiid h), "StoreBuffer")]
    end
  | _ => []
  end.

(** * Pipeline Definition *)

(** ** Pipeline Stages *)

(** Each pipeline stage is defined by a name, a number, a [LocalReordering],
  and a function adding any special edges (in this case, only at the store
  buffer). *)

Definition RISC_PipelineStages n c := [
  mkStage "Fetch"       FIFO              NoSpecialEdges;
  mkStage "Decode"      FIFO              NoSpecialEdges;
  mkStage "Execute"     FIFO              NoSpecialEdges;
  mkStage "Memory"      FIFO              NoSpecialEdges;
  mkStage "Writeback"   FIFO              NoSpecialEdges;
  mkStage "StoreBuffer" FIFO              (StoreBufferSpecialEdges c n)
].

Definition RISC_SharedStages := [
  mkStage "MainMemory"  NoOrderGuarantees NoSpecialEdges;
  mkStage "Retire"      FIFO              NoSpecialEdges
].

Fixpoint RISC_AllStages (n : nat) :=
  fold_left (app (A:=_)) (map (RISC_PipelineStages n) [0 ... n-1]) []
  ++ RISC_SharedStages.

Definition StagesOfCore
  (c : nat)
  (l : list nat)
  : list nat :=
  map (fun x => x + 6 * c) l.

(** ** Pipeline Paths *)

Definition RISC_PathOptions
  (n : nat)
  (e : Event)
  : PathOptions :=
  let c := proc (iiid e) in
  match dirn e with
  | R => [
    mkPathOption (String.append "Read" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 4])
      [mkPerformStages (3 + 6 * c) [0 ... n-1] [0 ... n-1] None true]
      NoSpecialEdges;
    mkPathOption (String.append "STBFwd" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 4])
      [mkPerformStages (3 + 6 * c) [0 ... n-1] [c] None false]
      NoSpecialEdges
    ]
  | W => [
    mkPathOption (String.append "Write" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 5] ++ StagesOfCore n [0; 1])
      [mkPerformStages (3 + 6 * c) [c] [c] None false;
       mkPerformStages (6 * n) [0 ... n-1] [0 ... n-1] None true]
      NoSpecialEdges
    ]
  end.

(** ** Pipeline Definition *)

Definition RISC_Pipeline (n : nat) :=
  mkPipeline
    "RISC"
    (RISC_AllStages n)
    (RISC_PathOptions n).

