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
Require Import Ascii.
Require Import String.

(* ** GraphTree

A [GraphTree] is a data structure which is used to represent a set of
  graphs that are mostly similar, but with a few small differences.  For
  example, suppose we want to represent two graphs: one which adds an edge e1
  to a graph G, and another which adds a different edge e2 to G.  Rather than
  representing these as {G + e1, G + e2}, a [GraphTree] would represent them
  as G + {e1 or e2}.

  The motivation for a [GraphTree] is to more easily represent the case in
  which, for example, a litmus test outcome may be observable in any one of
  a number of possible graphs, some of which will generally look very similar.
  *)
Inductive GraphTree (A : Type) : Type :=
  | GraphTreeOr   : list (GraphTree A) -> GraphTree A
  | GraphTreeAnd  : list (GraphTree A) -> GraphTree A
  | GraphTreeLeaf : string -> list (A * A * string) -> GraphTree A.

Open Scope string_scope.
Open Scope list_scope.

Definition GraphTreeEmptyLeaf {A : Type} := GraphTreeLeaf A "" [].

(** The [DNFOfTree] of a [GraphTree] is an explicit list of the graphs
  represented by the tree, i.e., no longer in the compacted [GraphTree]
  format. *)
Fixpoint DNFOfTree {A : Type}
  (t : GraphTree A)
  : list (string * list (A * A * string)) :=
  let joinGraphs {A : Type}
    (a b : string * list (A * A * string))
    : string * list (A * A * string) :=
    let (an, al) := a in
    let (bn, bl) := b in
    (append an bn, al ++ bl)
  in
  match t with
  | GraphTreeOr l =>
    fold_left (app (A:=_)) (map DNFOfTree l) []
  | GraphTreeAnd l =>
    let l' := map DNFOfTree l in
    map (fun x => fold_left joinGraphs x ("", [])) (CartesianProduct l')
  | GraphTreeLeaf n g => [(n, g)]
  end.

(** [GraphTreeSimplify] tries to represent a [GraphTree] in a simpler but
  equivalent form.  It does not guarantee minimality. *)
Fixpoint GraphTreeSimplify {A : Type}
  (g : GraphTree A)
  : GraphTree A :=
  match g with
  | GraphTreeOr    [x] => GraphTreeSimplify x
  | GraphTreeOr     l  => GraphTreeOr _ (map GraphTreeSimplify l)
  | GraphTreeAnd   [x] => GraphTreeSimplify x
  | GraphTreeAnd    l  => GraphTreeAnd _ (map GraphTreeSimplify l)
  | _ => g
  end.

Lemma SimplifiedDNF {A : Type} : forall (g : GraphTree A),
  DNFOfTree (GraphTreeSimplify g) = DNFOfTree g.
Proof.
(* TODO: http://adam.chlipala.net/cpdt/html/InductiveTypes.html *)
Abort.

(** [TreeOfDNF] converts a list of graphs into [GraphTree] representation. *)
Definition TreeOfDNF {A : Type}
  (l : list (string * list (A * A * string)))
  : GraphTree A :=
  let f x := GraphTreeLeaf _ (fst x) (snd x) in
  GraphTreeSimplify (GraphTreeOr _ (map f l)).

Lemma fold1 {A : Type} : forall l (x : list A),
  fold_left (app (A:=_)) l x = x ++ fold_left (app (A:=_)) l [].
Proof.
  intros l.  induction l.
    intros x.  simpl.  rewrite app_nil_r.  auto.
  intros x.  simpl.  rewrite IHl.  symmetry.  rewrite IHl.
  rewrite app_assoc.  auto.
Qed.

Lemma fold2 {A : Type} : forall l (xh : A) (xt : list A),
  fold_left (app (A:=_)) l (xh::xt) = xh :: fold_left (app (A:=_)) l xt.
Proof.
Admitted.

Lemma DNFIdempotent {A : Type} :
  forall x,
  forall (l : list (string * list (A * A * string))),
  In x l -> In x (DNFOfTree (TreeOfDNF l)).
Proof.
  intros x.  induction l as [|lh lt].
    auto.
  intros Hx.  destruct Hx as [Hx|Hx].
    rewrite Hx in *; clear Hx.
    unfold TreeOfDNF.  unfold map.  unfold GraphTreeSimplify.  simpl.
    destruct lt.
      simpl.  left.  destruct x; auto.
    simpl.  rewrite fold1.  left.  destruct x; auto.
  apply IHlt in Hx.  clear IHlt.
  
  destruct lt.
    inversion Hx.
  simpl.  rewrite fold2.  right.
  destruct lt as [|lth ltt].
    simpl in *.  auto.
  simpl in *.  auto.
Qed.

Module TreeExample.

Example e1 :
  DNFOfTree
  (GraphTreeAnd _ [
    GraphTreeLeaf _ "A" [(1, 2, "a")];
    GraphTreeLeaf _ "B" [(3, 4, "b")]
  ])
  = [("AB", [(1, 2, "a"); (3, 4, "b")])].
Proof.
cbv.  auto.
Qed.

Example e2 :
  DNFOfTree
  (GraphTreeAnd _ [
    GraphTreeLeaf _ "A" [(1, 2, "a")];
    GraphTreeOr _ [
      GraphTreeLeaf _ "B" [(3, 4, "b")];
      GraphTreeLeaf _ "C" [(5, 6, "c")]
    ]
  ])
  = [("AB", [(1, 2, "a"); (3, 4, "b")]); ("AC", [(1, 2, "a"); (5, 6, "c")])].
Proof.
cbv.  auto.
Qed.

Example e3 :
  DNFOfTree
  (GraphTreeAnd _ [
    GraphTreeLeaf _ "A" [(1, 2, "a")];
    GraphTreeLeaf _ "B" [(7, 8, "d")];
    GraphTreeOr _ [
      GraphTreeLeaf _ "C" [(3, 4, "b")];
      GraphTreeLeaf _ "D" [(5, 6, "c")]
    ]
  ])
  = [("ABC", [(1, 2, "a"); (7, 8, "d"); (3, 4, "b")]);
     ("ABD", [(1, 2, "a"); (7, 8, "d"); (5, 6, "c")])].
Proof.
cbv.  auto.
Qed.

Example e4 :
  DNFOfTree
  (GraphTreeAnd _ [
    GraphTreeLeaf _ "A" [(1, 2, "a")];
    GraphTreeAnd _ [
      GraphTreeEmptyLeaf;
      GraphTreeLeaf _ "B" [(3, 4, "b")]
    ]
  ])
  = [("AB", [(1, 2, "a"); (3, 4, "b")])].
Proof.
cbv.  auto.
Qed.

Example e5 :
  DNFOfTree
  (GraphTreeAnd _ [
    GraphTreeLeaf _ "A" [(1, 2, "a")];
    GraphTreeOr _ []
  ])
  = [].
Proof.
unfold DNFOfTree.  unfold map.
cbv.  auto.
Qed.

End TreeExample.

Definition DNFStringOfTree' {A : Type}
  (print_node : A -> string)
  (e : A * A * string)
  : string :=
  let (sd, label) := e in
  let (s, d) := sd in
  fold_left append [": "; print_node s; "-"; label; "->"; print_node d; " "] "".

Fixpoint DNFStringOfTree {A : Type}
  (print_node : A -> string)
  (t : GraphTree A)
  : string :=
  let f_fold a b := append b (append "-" a) in
  match t with
  | GraphTreeOr l =>
    append "Or(" (append (fold_left f_fold (map (DNFStringOfTree print_node) l) "") ")")
  | GraphTreeAnd l =>
    append "And(" (append (fold_left f_fold (map (DNFStringOfTree print_node) l) "") ")")
  | GraphTreeLeaf n l => fold_left append (map (DNFStringOfTree' print_node) l) n
  end.

Close Scope string_scope.

Fixpoint GraphTreeMap {A B : Type}
  (f : A -> B)
  (g : GraphTree A)
  : GraphTree B :=
  match g with
  | GraphTreeAnd    l => GraphTreeAnd  _ (map (GraphTreeMap f) l)
  | GraphTreeOr     l => GraphTreeOr   _ (map (GraphTreeMap f) l)
  | GraphTreeLeaf n l =>
    let f' x := (f (fst (fst x)), f (snd (fst x)), snd x) in
    GraphTreeLeaf _ n (map f' l)
  end.

Fixpoint GraphTreeMapPair {A B : Type}
  (f : A * A * string -> B * B * string)
  (g : GraphTree A)
  : GraphTree B :=
  match g with
  | GraphTreeAnd    l => GraphTreeAnd  _ (map (GraphTreeMapPair f) l)
  | GraphTreeOr     l => GraphTreeOr   _ (map (GraphTreeMapPair f) l)
  | GraphTreeLeaf n l =>
    GraphTreeLeaf _ n (map f l)
  end.


