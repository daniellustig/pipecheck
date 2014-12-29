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
Require Import stages.
Require Import musthappenbefore.
Require Import ppo.
Require Import gem5.

(** ** Approach 1: General proof *)

Set Default Timeout 5.

Example WWAll :
  forall result,
  In result (VerifyPPOWithAnyAddresses gem5_O3_Pipeline [W; W] 0 1) ->
  exists name graph path, result = (name, MustHappenBefore graph path).
Proof.
  intros result Hpaths.  cbv in Hpaths.
  (* Handle each successfully verified case by checking that it matches the
    required "MustHappenBefore name graph path" template. *)
  repeat (destruct Hpaths as [Hpaths|Hpaths];
    try solve [eexists; eexists; eexists; rewrite <- Hpaths; cbv; auto]).
  inversion Hpaths.
Qed.

Example RRAll :
  forall result,
  In result (VerifyPPOWithAnyAddresses gem5_O3_Pipeline [R; R] 0 1) ->
  forall name graph src dst, result <> (name, Unverified graph src dst).
Proof.
  intros result Hpaths.  cbv in Hpaths.
  (* Handle each successfully verified case by checking that it matches the
    required "MustHappenBefore name graph path" template. *)
  Timeout 20 repeat (destruct Hpaths as [Hpaths|Hpaths];
    try solve [eexists; eexists; eexists; eexists;
               rewrite <- Hpaths; intro Hx; inversion Hx]).
  (** Failure! Some cases can't be verified! *)
  (** Verified as actual pipeline bug! *)
Abort.

Example RWAll :
  forall result,
  In result (VerifyPPOWithAnyAddresses gem5_O3_Pipeline [R; W] 0 1) ->
  exists name graph path, result = (name, MustHappenBefore graph path).
Proof.
  intros result Hpaths.  cbv in Hpaths.
  (* Handle each successfully verified case by checking that it matches the
    required "MustHappenBefore name graph path" template. *)
  repeat (destruct Hpaths as [Hpaths|Hpaths];
    try solve [eexists; eexists; eexists; rewrite <- Hpaths; cbv; auto]).
  inversion Hpaths.
Timeout 10 Qed.

Example WRSame :
  forall result,
  In result (VerifyPPOWithSameAddress gem5_O3_Pipeline [W; R] 0 1) ->
  exists name graph path, result = (name, MustHappenBefore graph path).
Proof.
  intros result Hpaths.  cbv in Hpaths.
  (* Handle each successfully verified case by checking that it matches the
    required "MustHappenBefore name graph path" template. *)
  repeat (destruct Hpaths as [Hpaths|Hpaths];
    try solve [eexists; eexists; eexists; rewrite <- Hpaths; cbv; auto]).
  (** Failure! Some cases can't be verified! *)
  (** FIXME *)
Abort.

