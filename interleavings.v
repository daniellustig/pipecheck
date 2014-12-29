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

(** * Interleavings

Return a list of all possible sequential interleavings of the input lists *)

Fixpoint Interleavings''' {A : Type}
  (l' l : list (list A))
  : list (A * list (list A)) :=
  match l with
  | h::t =>
    match h with
    | hh::ht =>
      (hh, l' ++ ht :: t) :: Interleavings''' (l' ++ [h]) t
    | [] => Interleavings''' l' t
    end
  | [] => []
  end.

Definition Interleavings'' {A : Type}
  (a : A)
  (l : list (list A))
  : list (list A) :=
  match l with
  | [] => [[a]]
  | _ => map (fun x => a::x) l
  end.

Fixpoint Interleavings' {A : Type}
  (l : list (list A))
  (n : nat)
  : list (list A) :=
  match n with
  | S n' =>
    let f p := Interleavings'' (fst p) (Interleavings' (snd p) n') in
    fold_left (app (A:=_)) (map f (Interleavings''' [] l)) []
  | 0 => []
  end.

Definition Interleavings {A : Type}
  (l : list (list A))
  : list (list A) :=
  let n := fold_left plus (map (length (A:=_)) l) 0 in
  Interleavings' l n.

Module InterleavingsExample.

Example e1: Interleavings''' [] [[1; 2]; [3; 4]]
  = [(1, [[2]; [3; 4]]); (3, [[1; 2]; [4]])].
Proof.  auto.  Qed.

Example e2: Interleavings''' [] [[1; 2]; [3; 4]; []]
  = [(1, [[2]; [3; 4]; []]); (3, [[1; 2]; [4]; []])].
Proof.  auto.  Qed.

Example e3: Interleavings [[1; 2]; [3; 4]]
  = [[1; 2; 3; 4]; [1; 3; 2; 4]; [1; 3; 4; 2]; [3; 1; 2; 4]; [3; 1; 4; 2];
     [3; 4; 1; 2]].
Proof.  auto.  Qed.

Example e4: Interleavings [[0; 1; 2]; [3; 4; 5]]
  = [[0; 1; 2; 3; 4; 5]; [0; 1; 3; 2; 4; 5]; [0; 1; 3; 4; 2; 5];
     [0; 1; 3; 4; 5; 2]; [0; 3; 1; 2; 4; 5]; [0; 3; 1; 4; 2; 5];
     [0; 3; 1; 4; 5; 2]; [0; 3; 4; 1; 2; 5]; [0; 3; 4; 1; 5; 2];
     [0; 3; 4; 5; 1; 2]; [3; 0; 1; 2; 4; 5]; [3; 0; 1; 4; 2; 5];
     [3; 0; 1; 4; 5; 2]; [3; 0; 4; 1; 2; 5]; [3; 0; 4; 1; 5; 2];
     [3; 0; 4; 5; 1; 2]; [3; 4; 0; 1; 2; 5]; [3; 4; 0; 1; 5; 2];
     [3; 4; 0; 5; 1; 2]; [3; 4; 5; 0; 1; 2]].
Proof.  auto.  Qed.

End InterleavingsExample.

