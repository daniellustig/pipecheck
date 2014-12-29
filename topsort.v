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
Require Import util2.
Require Import adjacency.
Require Import Ascii.
Require Import String.

Inductive TopsortResult : Type :=
  | TotalOrdering : list nat -> TopsortResult
  | CycleFound : list nat -> TopsortResult.

(** * [EdgesWithConnections]: Given an adjacency list, return a list of bools
  such that the nth element is true if there is at least one edge connected
  to node n. *)

(** The destination of each edge is connected *)
Fixpoint EdgesWithConnections''
  (l : list nat)
  (b : list bool)
  : list bool :=
  match l with
  | h::t =>
    replaceNth (EdgesWithConnections'' t b) h true false
  | [] => b
  end.

(** Include the source and dest of each edge as connected *)
Fixpoint EdgesWithConnections'
  (g : list (list nat))
  (b : list bool)
  (n : nat)
  : list bool :=
  match g with
  | h::t =>
    let b' :=
      match h with
      | _::_ =>
        (* outgoing edge from this node - edge is connected *)
        replaceNth b n true false
      | [] =>
        (* no outgoing edge from this node *)
        b
      end in
    EdgesWithConnections' t (EdgesWithConnections'' h b') (S n)
  | [] => b
  end.

Fixpoint EdgesWithConnections
  (g : list (list nat))
  : list bool :=
  EdgesWithConnections' g [] 0.

(** * Topological Sort *)

Inductive Marking : Type :=
  Unmarked | MarkedTemp | Marked.

(** ** Debugging code *)

Open Scope string_scope.

Fixpoint natListToString
  (l : list nat)
  : string :=
  match l with
  | h::t =>
    append (append (stringOfNat h) " ") (natListToString t)
  | [] => ""
  end.

Fixpoint markingListToString
  (l : list Marking)
  : string :=
  match l with
  | Unmarked::t => append ("U") (markingListToString t)
  | MarkedTemp::t => append ("T") (markingListToString t)
  | Marked::t => append ("M") (markingListToString t)
  | [] => ""
  end.

Fixpoint topsortStateToString
  (omr : (list Marking * TopsortResult))
  : string :=
  let (lm, r) := omr in
  append
    (match r with
     | TotalOrdering r =>
       append (append "TotalOrdering " (natListToString r)) ":"
     | CycleFound r =>
       append (append "CycleFound " (natListToString r)) ":"
     end)
    (append (markingListToString lm) newline).

Fixpoint AdjacencyListToString
  (l : list (list nat))
  (n : nat)
  : string :=
  match l with
  | h::t =>
    fold_left append [
      stringOfNat n; ": ("; natListToString h; ")"; newline;
      AdjacencyListToString t (S n)
    ] ""
  | [] => ""
  end.

(** ** Topological sort *)

Fixpoint topsortVisit
  (unroll : nat)
  (g : list (list nat))
  (omr : (list Marking * TopsortResult))
  (n : nat)
  : list Marking * TopsortResult :=
  match omr with
  | (m, TotalOrdering r) =>
    match (unroll, nth n m Unmarked) with
    | (S unroll', Unmarked) =>
      let m' := replaceNth m n MarkedTemp Unmarked in
      let adj_of_n := nth n g [] in
      match fold_left (topsortVisit unroll' g) adj_of_n
        (m', TotalOrdering r) with
      | (m'', TotalOrdering r'') =>
        (replaceNth m'' n Marked Unmarked, TotalOrdering ([n] ++ r''))
      | x => x
      end
    | (S unroll', Marked) => omr
    | (0, _) => (m, CycleFound [1])
    | _ =>
      (m, CycleFound (FindPathAdj g n n))
    end
  | x => x
  end.

Fixpoint range (j : nat) : list nat :=
  match j with
  | 0 => []
  | S j' => j' :: range j'
  end.

Close Scope string_scope.

Definition topsortAdj'
  (g : list (list nat))
  : TopsortResult :=
  (* let g := PrintfHook g
    (append (append "Graph: " newline) (AdjacencyListToString g 0)) in *)
  let l := fold_left plus (map (List.length (A:=_)) g) (List.length g) in
  match fold_left (topsortVisit l g) (range l) (([], TotalOrdering [])) with
  | (_, r) => r
  end.

Fixpoint KeepIfIn
  (l : list nat)
  (b : list bool)
  : list nat :=
  match l with
  | h::t =>
    if nth h b false
      then h::KeepIfIn t b
      else KeepIfIn t b
  | [] => []
  end.

Definition topsortAdj
  (g : list (list nat))
  : TopsortResult :=
  let c := EdgesWithConnections g in
  match topsortAdj' g with
  | TotalOrdering o => TotalOrdering (KeepIfIn o c)
  | x => x
  end.

Definition topsort
  (g : list (nat * nat))
  : TopsortResult :=
  topsortAdj (AdjacencyListFromEdges g).

Module TopsortExample.

Example e1:
  EdgesWithConnections [[12; 8; 4]; []; []; []; [12; 8]; []; []; []; [12]] =
  [true; false; false; false; true; false; false; false; true; false;
   false; false; true].
Proof.
auto.
Qed.

Example e2: topsortAdj [[3]; []; [0; 3]; [1]] = TotalOrdering [2; 0; 3; 1].
Proof.
auto.
Qed.

Example e3:
  topsort [(0, 3); (2, 0); (2, 3); (3, 1)] = TotalOrdering [2; 0; 3; 1].
Proof.
auto.
Qed.

Example e4:
  topsort [(0, 1); (1, 0)] = CycleFound [1; 0; 1].
Proof.
cbv.  auto.
Qed.

End TopsortExample.

