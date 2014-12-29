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
Require Import stages.

(** * OpenSPARC T2 *)

(**
In this chapter, we prove the OpenSPARC T2 pipeline correct with respect
to its consistency model.

For a top-down approach, skip the definition of the helper functions down to
the definition of [OpenSPARC_T2_Pipeline] itself, and then work back upwards.
*)

(** * Helper Definitions *)

(** ** Local Reorderings at different stages *)

(** [FIFO]: any ordering guaranteed at the input is also guaranteed at the
  output.  This is the common case. *)
Definition FIFO : LocalReordering := fun _ => fun ordering => ordering.

(** [NoOrderGuarantees]: Operations can leave the stage in any order; nothing
  is guaranteed. *)
Definition NoOrderGuarantees : LocalReordering := fun _ => fun _ => [].

(** [SameAddressOrdered]: Only operations to the same address are guaranteed
  to maintain their ordering. *)
Fixpoint SameAddressOrdered
  (l : list (list (Event * Event)))
  (ordering : LocalOrdering)
  : LocalOrdering :=
  match ordering with
  | (h1, h2)::t =>
      (if beq_nat (loc h1) (loc h2)
        then [(h1, h2)]
        else [])
    ++ SameAddressOrdered l t
  | [] => []
  end.

(** ** Special Edge Maps *)

(** In some cases, we need to add certain extra edges to the graph to
  capture non-local effects. *)

(** In most cases, though, we don't need to add any special edges *)
Definition NoSpecialEdges : SpecialEdgeMap := fun _ _ _ => [].

(** The store buffer only allows one outstanding unacknowledged store at a
  time.  In our model, this translates to adding a "happens before" edges
  from a store receiving its ack from L2 cache and updating the cache in the M2
  stage to any subsequent store leaving the store buffer. *)

(** #<img src="../images/storebuffertiming.png"># *)
Definition StoreBufferSpecialEdges n c : SpecialEdgeMap :=
  fun _ e e_after =>
  match e_after with
  | h::_ =>
    if beq_nat (loc h) (loc e)
      then []
      else [((10 * n + 1 + 4 * c + 1, eiid e), (10 * c + 8, eiid h), "StoreBuffer")]
  | _ => []
  end.

(** For loads that miss in the L1 cache and for store buffer RAWs, the
  pipeline is flushed, and no subsequent operations are fetched from the
  missing thread until the missing load is satisfied and writes back its
  result.  In our model, this translates to adding a "happens before" edge
  from any load miss writing back its result in the M2 stage to any subsequent
  operation leaving the pick stage. *)

(** #<img src="../images/loadmisstiming.png"># *)

(** #<img src="../images/rawtiming.png"># *)
Definition SquashSpecialEdges n c : SpecialEdgeMap :=
  fun _ e e_after =>
  match e_after with
  | h::_ => [((10 * n + 1 + 4 * c + 1, eiid e), (10 * c + 2, eiid h), "Squash")]
  | _ => []
  end.

(** *)
Fixpoint NoSTBRAWSpecialEdges
  (n c : nat)
  (e_before : list Event)
  (e : Event)
  (e_after : list Event)
  : GlobalGraph :=
  match e_before with
  | h::t =>
    match (beq_nat (loc e) (loc h), dirn h) with
    | (true, W) =>
      ((10 * n + 1 + 4 * c + 1, eiid h), (10 * c + 5, eiid e), "NoSTBRAW")
        :: NoSTBRAWSpecialEdges n c t e e_after
    | _ => NoSTBRAWSpecialEdges n c t e e_after
    end
  | [] => []
  end.

Definition SquashAndNoSTBRAWSpecialEdges n c : SpecialEdgeMap :=
  fun e_before e e_after =>
  SquashSpecialEdges n c e_before e e_after
  ++ NoSTBRAWSpecialEdges n c e_before e e_after.

(** * Pipeline Definition *)

(** ** Pipeline Stages *)

(** Each pipeline stage is defined by a name, a number, a [LocalReordering],
  and a function adding any special edges (in this case, only at the store
  buffer). *)

Definition OpenSPARC_T2_FrontStages n c := [
  mkStage "Fetch"             FIFO               NoSpecialEdges;
  mkStage "ICache"            FIFO               NoSpecialEdges;
  mkStage "Pick"              FIFO               NoSpecialEdges;
  mkStage "Decode"            FIFO               NoSpecialEdges;
  mkStage "Execute"           FIFO               NoSpecialEdges;
  mkStage "Memory"            FIFO               NoSpecialEdges;
  mkStage "Bypass"            FIFO               NoSpecialEdges;
  mkStage "Writeback"         FIFO               NoSpecialEdges;
  mkStage "StoreBuffer"       SameAddressOrdered (StoreBufferSpecialEdges n c);
  mkStage "LoadMissQueue"     FIFO               NoSpecialEdges
].

Definition OpenSPARC_T2_SharedStages := [
  mkStage "L2Cache"           SameAddressOrdered NoSpecialEdges
].

Definition OpenSPARC_T2_BackStages (c : nat) := [
  mkStage "Execute2"          FIFO               NoSpecialEdges;
  mkStage "Memory2"           FIFO               NoSpecialEdges;
  mkStage "Bypass2"           FIFO               NoSpecialEdges;
  mkStage "Completed"         FIFO               NoSpecialEdges
].

Definition OpenSPARC_T2_AllStages n :=
  fold_left (app (A:=_)) (map (OpenSPARC_T2_FrontStages n) [0 ... n-1]) []
  ++ OpenSPARC_T2_SharedStages ++
  fold_left (app (A:=_)) (map (OpenSPARC_T2_BackStages) [0 ... n-1]) [].

Definition StagesOfCore
  (c : nat)
  (l : list nat)
  : list nat :=
  map (fun x => x + 10 * c) l.

Definition BackStagesOfCore
  (n c : nat)
  (l : list nat)
  : list nat :=
  map (fun x => x + 10 * n + 1 + 4 * c) l.

(** ** Pipeline Paths *)

(** An operation can take one of four paths through the pipeline.
  Reads take one of three paths: load hit, load miss, or store buffer RAW.
  Load hits travel through the eight stage pipeline, perform at the M stage,
  and add no special edges.
  Load misses travel through the eight stage pipeline, enter the LMQ, remote
  read the L2 cache, then re-enter the pipeline at the E stage to write back.
  Load misses also squash the pipeline until the miss is satisfied.
  Store buffer RAWs are like load misses, except they perform (read the store
  buffer data) from within the LMQ.
  Finally, stores take only one path including going through the store
  buffer.

  The paths are also depicted in the timing charts shown earlier. *)

Definition OpenSPARC_T2_PathOptions n (e : Event) : PathOptions :=
  let c := proc (iiid e) in
  match dirn e with
  | R => [
    mkPathOption (String.append "ReadHit" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 7])
      [mkPerformStages (10 * c + 5) [0 ... n-1] [0 ... n-1] None true]
      (NoSTBRAWSpecialEdges n c);
    mkPathOption (String.append "ReadMiss" (stringOfNat (loc e))) e
      (StagesOfCore c ([0 ... 7] ++ [9]) ++
       StagesOfCore n [0] ++
       BackStagesOfCore n c [0 ... 3])
      [mkPerformStages (10 * n + 1 + 4 * c + 1) [0 ... n-1] [0 ... n-1] None true]
      (SquashAndNoSTBRAWSpecialEdges n c);
    mkPathOption (String.append "STBRAW" (stringOfNat (loc e))) e
      (StagesOfCore c ([0 ... 7] ++ [9]) ++
       BackStagesOfCore n c [0 ... 3])
      [mkPerformStages (10 * c + 7) [0 ... n-1] [c] None false]
      (SquashSpecialEdges n c)]
  | W => [
    mkPathOption (String.append "Write" (stringOfNat (loc e))) e
      (StagesOfCore c ([0 ... 8]) ++
       StagesOfCore n [0] ++
       BackStagesOfCore n c [0 ... 3])
      [mkPerformStages (10 * c + 7) [c] [c] None false;
       mkPerformStages (10 * n) [0 ... n-1] [0 ... n-1] None true]
      NoSpecialEdges
    ]
  end.

(** ** Pipeline Definition *)

Definition OpenSPARC_T2_Pipeline n :=
  mkPipeline
    "OpenSPARC_T2"
    (OpenSPARC_T2_AllStages n)
    (OpenSPARC_T2_PathOptions n).

