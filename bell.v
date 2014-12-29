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

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import util2.

(* Bell numbers *)

Fixpoint UniqueValues'
  (l r : list nat)
  : list nat :=
  match l with
  | [] => r
  | h::t =>
    UniqueValues' t (AddUnique r h)
  end.

(** Return [l], but with all duplicates removed. *)
Definition UniqueValues
  (l : list nat)
  : list nat :=
  let r := UniqueValues' l [] in
  r ++ [length r].

(** Given a list [l], return a list of lists where each unique value used in
  [l] is appended to [l], plus one unused unique value is also appended to
  [l]. *)
Fixpoint Bell'
  (l : list nat)
  : list (list nat) :=
  let v := UniqueValues l in
  let f x := l ++ [x] in
  map f v.

Module BellExample.

Example e1 :
  Bell' [0; 1; 2] = [[0; 1; 2; 0]; [0; 1; 2; 1]; [0; 1; 2; 2]; [0; 1; 2; 3]].
Proof.
auto.
Qed.

End BellExample.

(* Return the set of all possible assignments of unique values to [n] different
  slots.  The total number of such assignments is known as the "Bell number".

  In PipeCheck, this refers to the number of unique ways that [n] addresses can
  be assigned to [n] memory instructions, such that all possible combinations
  of overlapping and non-overlapping addresses are covered.  This is necessary
  whenever the ordering properties depend on whether addresses overlap or not.
*)
Fixpoint Bell
  (n : nat)
  : list (list nat) :=
  match n with
  | 0 => [[]]
  | S n' =>
    fold_left (app (A:=_)) (map Bell' (Bell n')) []
  end.

Module BellExample2.

Example e1 : Bell 4 =
  [[0; 0; 0; 0]; [0; 0; 0; 1]; [0; 0; 1; 0]; [0; 0; 1; 1]; [0; 0; 1; 2];
   [0; 1; 0; 0]; [0; 1; 0; 1]; [0; 1; 0; 2]; [0; 1; 1; 0]; [0; 1; 1; 1];
   [0; 1; 1; 2]; [0; 1; 2; 0]; [0; 1; 2; 1]; [0; 1; 2; 2]; [0; 1; 2; 3]].
Proof.
auto.
Qed.

(* OEIS A000110 : length(Bell n) = 1, 1, 2, 5, 15, 52, ... *)

Example e2 :
  map (fun n => length (Bell n)) [0; 1; 2; 3; 4; 5; 6] = [1; 1; 2; 5; 15; 52; 203].
Proof.
auto.
Qed.

End BellExample2.

