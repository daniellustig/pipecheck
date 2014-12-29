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

(** * Traditional Five-Stage SCProc Pipeline *)

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

(** * Pipeline Definition *)

(** ** Pipeline Stages *)

(** Each pipeline stage is defined by a name, a number, a [LocalReordering],
  and a function adding any special edges (in this case, only at the store
  buffer). *)

Definition SCProc_PipelineStages (c : nat) := [
  mkStage "Fetch"       FIFO              NoSpecialEdges;
  mkStage "Decode"      FIFO              NoSpecialEdges;
  mkStage "Execute"     FIFO              NoSpecialEdges;
  mkStage "Memory"      FIFO              NoSpecialEdges;
  mkStage "Writeback"   FIFO              NoSpecialEdges
].

Fixpoint SCProc_AllStages (n : nat) :=
  fold_left (app (A:=_)) (map SCProc_PipelineStages [0 ... n-1]) [].

Definition StagesOfCore
  (c : nat)
  (l : list nat)
  : list nat :=
  map (fun x => x + 5 * c) l.

(** ** Pipeline Paths *)

Definition SCProc_PathOptions
  (n : nat)
  (e : Event)
  : PathOptions :=
  let c := proc (iiid e) in
  match dirn e with
  | R => [
    mkPathOption (String.append "Read" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 4])
      [mkPerformStages (3 + 5 * c) [0 ... n-1] [0 ... n-1] None true]
      NoSpecialEdges
    ]
  | W => [
    mkPathOption (String.append "Write" (stringOfNat (loc e))) e
      (StagesOfCore c [0 ... 4])
      [mkPerformStages (3 + 5 * c) [0 ... n-1] [0 ... n-1] None true]
      NoSpecialEdges
    ]
  end.

(** ** Pipeline Definition *)

Definition SCProc_Pipeline (n : nat) :=
  mkPipeline
    "SCProc"
    (SCProc_AllStages n)
    (SCProc_PathOptions n).

