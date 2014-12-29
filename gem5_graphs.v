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
Require Import gem5.
Require Import ppo.

(** ** Approach 2: an Explicit Scenario *)

Definition gem5Graphs :=
  GraphsToVerifyTSOPPO gem5_O3_Pipeline.

(*
(** ** Approach 3: a litmus test *)

Definition evtI0 := mkev 0 (mkiiid 0 0) (Access W 0 0).
Definition evtI1 := mkev 1 (mkiiid 0 1) (Access W 1 0).
Definition evt00 := mkev 2 (mkiiid 1 0) (Access W 0 1).
Definition evt01 := mkev 3 (mkiiid 1 1) (Access W 1 1).
Definition evt10 := mkev 4 (mkiiid 2 0) (Access R 1 1).
Definition evt11 := mkev 5 (mkiiid 2 1) (Access R 0 0).

Definition LoadOrStoreReorderLitmusTest :=
  GraphsToVerifyExecution
    gem5_O3_Pipeline
    [evtI0; evtI1; evt00; evt01; evt10; evt11]
    [(3, 4); (0, 5)]
    [0; 1; 2; 3].

(** Finally, we export the computation to OCaml so we can print it to a file,
  link it in with other code, etc. *)

Extraction Language Ocaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction "gem5.ml" AllGraphs LoadOrStoreReorderLitmusTest.
*)

