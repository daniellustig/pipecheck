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
Require Import wmm.
Require Import util2.
Require Import tree.
Require Import stages.

Open Scope string_scope.

(** [geid] is a helper function that assigns to each [GlobalEvent] a unique
  identifier in the global ordering graph. *)
Definition geid
  (p : Pipeline)
  (ge : GlobalEvent)
  : nat :=
  let (n, e) := ge in
  e * (List.length (stages p)) + n.

(** [gepid] applies [geid] to each value in a pair of [GlobalEvent]s. *)
Definition gepid
  (p : Pipeline)
  (gep : GlobalEvent * GlobalEvent * string)
  : (nat * nat * string) :=
  let (ge1, ge2) := fst gep in
  (geid p ge1, geid p ge2, snd gep).

(** [getid] applies [gepid] to each value in a [GraphTree] of [GlobalEvent]s. *)
Fixpoint getid
  (p : Pipeline)
  (t : GraphTree GlobalEvent)
  : GraphTree nat :=
  match t with
  | GraphTreeOr     l => GraphTreeOr   _   (map (getid p) l)
  | GraphTreeAnd    l => GraphTreeAnd  _   (map (getid p) l)
  | GraphTreeLeaf n l => GraphTreeLeaf _ n (map (gepid p) l)
  end.

(** [ungeid'] is a helper function for [ungeid] that performs division
  slowly. *)
Fixpoint ungeid'
 (p : Pipeline)
 (n s e : nat)
 : (location * program_order_index) :=
  match (n, nat_compare s (List.length (stages p))) with
  | (0   , Lt) => (s, e)
  | (0   , Eq) => (0, S e)
  | (S n', Lt) => ungeid' p n' (S s) e
  | (S n', Eq) => ungeid' p n' 1 (S e)
  | (_   , Gt) => (0, 0) (* ERROR *)
  end.

(** [ungeid] is the opposite of [geid]: it converts a global ordering vertex
  identifier and returns the corresponding [location] and [Event].  It is used
  to print human-readable information about the vertex. *)
Definition ungeid
  (p : Pipeline)
  (n : nat)
  : location * program_order_index :=
  ungeid' p n 0 0.

Definition GlobalEventString
  (p : Pipeline)
  (ge : GlobalEvent)
  : string :=
  let (n, e) := ge in
  match (nth_error (stages p) n, n - List.length (stages p)) with
  | (Some s, _) =>
    append "Event"
    (append (String (ascii_of_nat (nat_of_ascii "0" + e)) "")
     (append "at"
      (name s)))
  | (None, 0) =>
    fold_left append ["CacheLine"; stringOfNat e; "Create"] ""
  | (None, 1) =>
    fold_left append ["CacheLine"; stringOfNat e; "Invalidate"] ""
  | _ => "Unknown"
  end.

Fixpoint GraphString
  (g : list (nat * nat * string))
  : string :=
  match g with
  | h::t =>
    let (s, d) := fst h in
    fold_left append [stringOfNat s; " --"; (snd h); "-> "; stringOfNat d;
      newline]
      (GraphString t)
  | [] => ""
  end.

Fixpoint GlobalGraphString
  (g : list (GlobalEvent * GlobalEvent * string))
  : string :=
  match g with
  | h::t =>
    let (s, d) := fst h in
    fold_left append ["("; stringOfNat (fst s); ", "; stringOfNat (snd s);
      ") --"; (snd h); "-> ("; stringOfNat (fst d); ", "; stringOfNat (snd d);
      ")"; newline]
      (GlobalGraphString t)
  | [] => ""
  end.

Module GraphStringExample.

Definition ExampleGraph := [(0, 1, "a"); (0, 2, "b")].

Example e1 : GraphString ExampleGraph = "0 --b-> 2
0 --a-> 1
".
Proof.
auto.
Qed.

Definition ExampleGlobalGraph := [((0, 0), (0, 1), "a"); ((0, 0), (1, 0), "b")].

Example e2 : GlobalGraphString ExampleGlobalGraph = "(0, 0) --b-> (1, 0)
(0, 0) --a-> (0, 1)
".
Proof.
auto.
Qed.

End GraphStringExample.

