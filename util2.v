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
Require Import Ascii.
Require Import String.

Open Scope string_scope.

Definition newline := String (ascii_of_nat 10) "".
Definition tab := String (ascii_of_nat 9) "".

(** * Hooks for OCaml functions

Functions in this section are Coq no-ops, but they are intercepted before
OCaml compilation and replaced with the function indicated by the hook name.
This allows us to embed hooks for OCaml code directly into the Coq source
without affecting the correctness of the computation. *)

Definition PrintfHook {A : Type}
  (a : A)
  (s : string)
  : A :=
  (** in OCaml, insert 'Printf.printf "%s" s;' here *)
  a.

Definition DebugPrintfHook {A : Type}
  (a : A)
  (level : nat)
  (s : string)
  : A :=
  (** in OCaml, insert 'if <debug mode> then Printf.printf "%s" s;' here *)
  a.

Definition PanicHook {A : Type}
  (msg : string)
  (a : A)
  : A :=
  (** in OCaml, insert 'Printf.printf "%s" msg; failwith "Panic called"' *)
  a.

Definition TimerStartHook {A : Type}
  (a : A)
  : nat * A :=
  (** in OCaml, return (gettimeofday(), a) *)
  (0, a).

Definition TimerStopHook {A : Type}
  (s : string)
  (t_start : nat)
  (a : A)
  : A :=
  (** in OCaml, print "Timer,<s>,<time elapsed>" *)
  a.

Close Scope string_scope.

(** Case tactics for proof organization:
http://www.cis.upenn.edu/~bcpierce/sf/current/SfLib.html
*)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Close Scope string_scope.

(** * Empty list check *)

Definition IsEmptyList {A : Type}
  (l : list A)
  : bool :=
  match l with
  | [] => true
  | _ => false
  end.

Fixpoint last_error {A : Type}
  (l : list A)
  : option A :=
  match l with
  | [] => None
  | [x] => Some x
  | h::t => last_error t
  end.

(** * List of pairs of consecutive elements *)

(** [PairConsecutive] is a helper function that converts a list
  [ [a; b; c; ...] ] into a list of pairs of consecutive elements
  [ [(a,b); (b,c); (c,d); ...] ] *)
Fixpoint PairConsecutive {A : Type}
  (l : list A)
  : list (A * A) :=
  match l with
  | h::t =>
    match t with
    | th::_ => (h, th) :: PairConsecutive t
    | _ => []
    end
  | _ => []
  end.

(** [PairConsecutiveWithLabel] is a helper function that converts a list
  [ [a; b; c; ...] ] into a list of pairs of consecutive elements
  [ [(a,b,l); (b,c,l); (c,d,l); ...] ] *)
Fixpoint PairConsecutiveWithLabel {A : Type}
  (n : string)
  (l : list A)
  : list (A * A * string) :=
  match l with
  | h::t =>
    match t with
    | th::_ => (h, th, n) :: PairConsecutiveWithLabel n t
    | _ => []
    end
  | _ => []
  end.

(** * Cartesian Product of Lists of Lists *)

(** Given a head element "h" and a list of tail lists "t", generate the
  list of lists with "h" prepended to each list in "t" *)
Definition CartesianProduct'' {A : Type}
  (h : A)
  (t : list (list A))
  : list (list A) :=
  match t with
  | [] => []
  | _ => map (fun x => h::x) t
  end.

(** Given a list of head elements "h" and a list of tail lists "t", generate
  the list of lists with each element of "h" prepended to each list in "t" *)
Fixpoint CartesianProduct' {A : Type}
  (h : list A)
  (t : list (list A))
  : list (list A) :=
  match h with
  | hh::ht => CartesianProduct'' hh t ++ CartesianProduct' ht t
  | [] => []
  end.

(** Given a list of lists, generate the Cartesian product of the lists *)
Fixpoint CartesianProduct {A : Type}
  (l : list (list A))
  : list (list A) :=
  match l with
  | [] => []
  | [h] => map (fun x => [x]) h
  | h::t => CartesianProduct' h (CartesianProduct t)
  end.

Module CartesianProductExample.

Example e :
  CartesianProduct [[0; 1]; [2]; [3; 4]]
  = [[0; 2; 3]; [0; 2; 4]; [1; 2; 3]; [1; 2; 4]].
Proof.
auto.
Qed.

Example e2 :
  CartesianProduct (A:=nat) [[]] = [].
Proof.  cbv.  auto.  Qed.

Example e3 :
  CartesianProduct [[]; [0; 1]] = [].
Proof.  cbv.  auto.  Qed.

Example e4 :
  CartesianProduct [[0; 1]; []] = [].
Proof.  cbv.  auto.  Qed.

End CartesianProductExample.

(** * Cartesian Product of Two Lists as Pairs *)

(** Given a head element "h" and a list of elements "t", generate the
  list of pairs of "h" with each element in "t" *)
Definition CartesianProductPairs' {A B : Type}
  (h : A)
  (t : list B)
  : list (A*B) :=
  map (fun x => (h, x)) t.

(** Given two lists of elements "h" and "t", generate the list of pairs of one
  element each from "h" and "t". *)
Definition CartesianProductPairs {A B : Type}
  (h : list A)
  (t : list B)
  : list (A*B) :=
  fold_left (app (A:=_)) (map (fun x => CartesianProductPairs' x t) h) [].

Module CartesianProductPairsExample.

Example e :
  CartesianProductPairs [0; 1] [2; 3] = [(0, 2); (0, 3); (1, 2); (1, 3)].
Proof.
auto.
Qed.

End CartesianProductPairsExample.

(** * [bool] versions of [In] *)

(** [bool] version of [In], specialized for [nat] *)
Fixpoint Inb_nat
  (n : nat)
  (l : list nat)
  : bool :=
  match l with
  | h::t =>
    if beq_nat n h
      then true
      else Inb_nat n t
  | [] => false
  end.

(** [bool] version of [In], specialized for [(nat * nat)] *)
Fixpoint Inb_nat_nat
  (nn : (nat * nat))
  (l : list (nat * nat))
  : bool :=
  let (n1, n2) := nn in
  match l with
  | (h1, h2)::t =>
    if beq_nat n1 h1
      then if beq_nat n2 h2
        then true
      else Inb_nat_nat nn t
    else Inb_nat_nat nn t
  | [] => false
  end.

(** [nat] version of [remove] *)
Fixpoint remove_nat
  (x : nat)
  (l : list nat)
  : list nat :=
  match l with
  | h::t =>
    if beq_nat h x
      then    remove_nat x t
      else h::remove_nat x t
  | [] => []
  end.

(** [String] from [nat] *)

Open Scope string_scope.

Definition stringOfNat'' (n : nat) : string :=
  String (ascii_of_nat (nat_of_ascii "0" + n)) "".

Fixpoint stringOfNat' (n tens ones : nat) : string :=
  match (n, tens, ones) with
  | (S n', _, S (S (S (S (S (S (S (S (S (S ones')))))))))) =>
    stringOfNat' n' (S tens) ones'
  | (S n', S t', _) => stringOfNat' n' 0 tens ++ stringOfNat'' ones
  | (S n', 0, _) => stringOfNat'' ones
  | _ => "(overflow)"
  end.

Definition stringOfNat (n : nat) : string :=
  stringOfNat' (S n) 0 n.

Module stringOfNatExample.

Example e1 : stringOfNat 123 = "123".
Proof.
cbv.  auto.
Qed.

Example e2 : stringOfNat 103 = "103".
Proof.
cbv.  auto.
Qed.

Example e3 : stringOfNat 0 = "0".
Proof.
cbv.  auto.
Qed.

Example e4 : stringOfNat 1 = "1".
Proof.
cbv.  auto.
Qed.

End stringOfNatExample.

Definition stringOfBool
  (b : bool)
  : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Close Scope string_scope.

(** * Add If Unique *)

(** Add [n] to [l] if [n] is not already in [l] *)
Fixpoint AddUnique (l : list nat) (n : nat) : list nat :=
  match l with
  | h::t =>
    if beq_nat h n then l else h :: AddUnique t n
  | [] => [n]
  end.

(** Add [nn] to [l] if [nn] is not already in [l] *)
Fixpoint AddUniquePair
  (l : list (nat * nat))
  (nn : nat * nat)
  : list (nat * nat) :=
  let (n1, n2) := nn in
  match l with
  | (h1, h2)::t =>
    if beq_nat h1 n1
      then (if beq_nat h2 n2
        then l
        else (h1, h2) :: AddUniquePair t nn)
      else (h1, h2) :: AddUniquePair t nn
  | [] => [nn]
  end.

(** Add [nn] to [l] if [nn] is not already in [l] *)
Fixpoint AddUniquePairPair
  (l : list ((nat * nat) * (nat * nat) * string))
  (nns : (nat * nat) * (nat * nat) * string)
  : list ((nat * nat) * (nat * nat) * string) :=
  let (nn, s) := nns in
  let (n1, n2) := nn in
  let (n1a, n1b) := n1 in
  let (n2a, n2b) := n2 in
  match l with
  | ((h1a, h1b), (h2a, h2b), s')::t =>
    match (nat_compare h1a n1a,
           nat_compare h1b n1b,
           nat_compare h2a n2a,
           nat_compare h2b n2b) with
    | (Eq, Eq, Eq, Eq) =>
      if string_dec s s'
        then l
        else ((h1a, h1b), (h2a, h2b), s') :: AddUniquePairPair t nns
    | _ => ((h1a, h1b), (h2a, h2b), s') :: AddUniquePairPair t nns
    end
  | [] => [nns]
  end.

(** Replace the [n]th element of [l] with [a].  If [l] is shorter than [n],
  fill in empty slots with [d]. *)
Fixpoint replaceNth {A : Type} (l : list A) (n : nat) (v d : A) : list A :=
  match (l, n) with
  | (h::t, 0   ) => v::t
  | (h::t, S n') => h :: replaceNth t n' v d
  | ([]  , 0   ) => [v]
  | ([]  , S n') => d :: replaceNth [] n' v d
  end.

(** Replace the [n]th element of [l] with [a].  If [l] is shorter than [n],
  fill in empty slots with [d]. *)
Fixpoint replaceNthIfNone {A : Type}
  (l : list (option A))
  (n : nat)
  (v : A)
  : list (option A) :=
  match (l, n) with
  | (Some h::t, 0   ) => Some h :: t
  | (Some h::t, S n') => Some h :: replaceNthIfNone t n' v
  | (None  ::t, 0   ) => Some v :: t
  | (None  ::t, S n') => None   :: replaceNthIfNone t n' v
  | ([]       , 0   ) => [Some v]
  | ([]       , S n') => None   :: replaceNthIfNone [] n' v
  end.

(** Append [a] to the [n]th sublist of [l], and create it if it doesn't already
  exist. *)
Fixpoint AppendToNth {A : Type}
  (l : list (list A))
  (n : nat)
  (a : A)
  : list (list A) :=
  match (l, n) with
  | (h::t, S n') => h :: AppendToNth t n' a
  | (h::t, 0   ) => (h ++ [a]) :: t
  | ([]  , S n') => [] :: AppendToNth [] n' a
  | ([]  , 0   ) => [[a]]
  end.

Lemma AppendToNthInNth :
  forall A (x : A) n l,
  In x (nth n (AppendToNth l n x) []).
Proof.
  intros A x.  induction n.
    simpl.  destruct l as [|lh lt].
      simpl.  auto.
    simpl.  apply in_or_app.  simpl; auto.
  simpl.  destruct l as [|lh lt].
    simpl.  auto.
  simpl.  apply IHn.
Qed.

(** Append [a] to the [n]th sublist of [l] if [a] is not already in the [n]th
  sublist of [l], and create the [n]th sublist if it doesn't already exist. *)
Fixpoint AppendUniqueToNth
  (l : list (list nat))
  (n : nat)
  (a : nat)
  : list (list nat) :=
  match (l, n) with
  | (h::t, S n') => h :: AppendToNth t n' a
  | (h::t, 0   ) => (AddUnique h a) :: t
  | ([]  , S n') => [] :: AppendToNth [] n' a
  | ([]  , 0   ) => [[a]]
  end.

(** Append [x] to the last list in the list of lists. *)
Fixpoint AppendToLast {A : Type}
  (x : list A)
  (l : list (list A))
  : list (list A) :=
  match l with
  | []   => [x]
  | [y]  => [x++y]
  | h::t => h::AppendToLast x t
  end.

Fixpoint MergeVertices
  (g : list (nat * nat))
  (v1 v2 : nat)
  : list (nat * nat) :=
  match g with
  | (h1, h2)::t =>
    match (nat_compare h1 v2, nat_compare h2 v2) with
    | (Eq, Eq) => (v1, v1)
    | (_ , Eq) => (h1, v1)
    | (Eq, _ ) => (v1, h2)
    | (_ , _ ) => (h1, h2)
    end
    :: MergeVertices t v1 v2
  | [] => []
  end.

Fixpoint MergePairVertices
  (g : list ((nat * nat) * (nat * nat) * string))
  (v1 v2 : nat * nat)
  : list ((nat * nat) * (nat * nat) * string) :=
  let (v1a, v1b) := v1 in
  let (v2a, v2b) := v2 in
  match g with
  | ((h1a, h1b), (h2a, h2b), s)::t =>
    match (nat_compare h1a v1a, nat_compare h1b v1b,
           nat_compare h2a v2a, nat_compare h2b v2b) with
    | (Eq, Eq, Eq, Eq) => ((v1a, v1b), (v1a, v1b), s)
    | (_ , _ , Eq, Eq) => ((h1a, h1b), (v1a, v1b), s)
    | (Eq, Eq, _ , _ ) => ((v1a, v1b), (h2a, h1b), s)
    | (_ , _ , _ , _ ) => ((h1a, h1b), (h2a, h1b), s)
    end
    :: MergePairVertices t v1 v2
  | [] => []
  end.

(** Ranges *)

Fixpoint Range
  (a b : nat)
  : list nat :=
  match (b, nat_compare a b) with
  | (_   , Eq) => [a]
  | (S b', _ ) => Range a b' ++ [b]
  | (0   , _ ) => [0]
  end.

Notation "[ x ... y ]" := (Range x y).

(** * Computation Tactics *)

(* begin hide *)
Ltac f_compute x H :=
let c := eval compute in x in (assert(x=c) as H by (cbv; auto)).

Ltac ComputeSubterm x H :=
  f_compute x H; rewrite H; clear H.

Ltac on_application f tac T :=
  match T with
    | context [f ?x ?y ?z ?w ?v ?u ?a ?b ?c] => tac (f x y z w v u a b c)
    | context [f ?x ?y ?z ?w ?v ?u ?a ?b] => tac (f x y z w v u a b)
    | context [f ?x ?y ?z ?w ?v ?u ?a] => tac (f x y z w v u a)
    | context [f ?x ?y ?z ?w ?v ?u] => tac (f x y z w v u)
    | context [f ?x ?y ?z ?w ?v] => tac (f x y z w v)
    | context [f ?x ?y ?z ?w] => tac (f x y z w)
    | context [f ?x ?y ?z] => tac (f x y z)
    | context [f ?x ?y] => tac (f x y)
    | context [f ?x] => tac (f x)
  end.

Ltac on_call f tac :=
  match goal with
    | |- ?T => on_application f tac T
    | H : ?T |- _ => on_application f tac T
  end.
(* end hide *)

(** Given a goal containing a subterm which is an application of function [f],
  compute (fully reduce) the subterm.  [H] is the name for a temporary
  hypothesis used during the computation; it must not conflict with existing
  names, but it will not show up after the computation completes. *)
Ltac ComputeSubtermWith f H :=
  let tac x := ComputeSubterm x H in on_call f tac.

