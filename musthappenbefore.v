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
Require Import tree.
Require Import adjacency.
Require Import topsort.
Require Import Ascii.
Require Import String.

Inductive MHBResult :=
  | Unverified : list (nat * nat * string) -> nat -> nat -> MHBResult
  | MustHappenBefore : list (nat * nat * string) -> list nat -> MHBResult
  | Cyclic : list (nat * nat * string) -> list nat -> MHBResult.

Definition VerifyMustHappenBeforeInGraph
  (g : list (nat * nat * string))
  (sd : nat * nat)
  : MHBResult :=
  let (src, dst) := sd in
  let g' := map (fst (A:=_) (B:=_)) g in
  match (topsort g') with
  | TotalOrdering _ =>
	let (reachable, prev) := Dijkstra g' src in
    if Inb_nat dst reachable
      then MustHappenBefore g (PathBacktrace g' prev src dst)
      else Unverified g src dst
  | CycleFound p =>
    Cyclic g p
  end.

Fixpoint TreeMustHappenBeforeInAllGraphs'''
  (g : list (nat * nat * string))
  (lsd : list (nat * nat * string))
  (lr : list MHBResult)
  (b : bool)
  : bool * list MHBResult :=
  match lsd with
  | h::t =>
    let r := VerifyMustHappenBeforeInGraph g (fst h) in
    match r with
    | Unverified _ _ _ =>
      TreeMustHappenBeforeInAllGraphs''' g t (r::lr) false
    | MustHappenBefore _ _ =>
      TreeMustHappenBeforeInAllGraphs''' g t (r::lr) b
    | Cyclic _ _ =>
      TreeMustHappenBeforeInAllGraphs''' g t (r::lr) b
    end
  | [] => (b, lr)
  end.

Fixpoint TreeMustHappenBeforeInAllGraphs''
  (n : string)
  (g : list (nat * nat * string))
  (lv : list (string * list (nat * nat * string)))
  (lr : list (string * MHBResult))
  : list (string * MHBResult) :=
  match lv with
  | (hn, hv)::t =>
    let (b, r) := TreeMustHappenBeforeInAllGraphs''' g hv [] true in
    let r' := map (fun x => (append n (append ":" hn), x)) r in
    match b with
    | true => r'
    | false => TreeMustHappenBeforeInAllGraphs'' n g t (lr ++ r')
    end
  | [] => lr
  end.

Fixpoint TreeMustHappenBeforeInAllGraphs'
  (lg : list (string * list (nat * nat * string)))
  (lv : list (string * list (nat * nat * string)))
  : list (string * MHBResult) :=
  match lg with
  | (hs, hg)::t =>
    TreeMustHappenBeforeInAllGraphs'' hs hg lv []
    ++ TreeMustHappenBeforeInAllGraphs' t lv
  | [] => []
  end.

Definition TreeMustHappenBeforeInAllGraphs
  (g : GraphTree nat)
  (v : GraphTree nat)
  : list (string * MHBResult) :=
  TreeMustHappenBeforeInAllGraphs' (DNFOfTree g) (DNFOfTree v).

Definition TreeAcyclicInSomeGraph''
  (g : list (nat * nat * string))
  : MHBResult * bool :=
  let r := VerifyMustHappenBeforeInGraph g (0, 0) in
  match r with
  | Unverified _ _ _ => (r, true)
  | MustHappenBefore _ _ => (r, true)
  | Cyclic _ _ => (r, false)
  end.

Fixpoint TreeAcyclicInSomeGraph'
  (lg : list (string * list (nat * nat * string)))
  (lr : list (string * MHBResult))
  : list (string * MHBResult) * bool :=
  match lg with
  | (hs, hg)::t =>
    let (r, b) := TreeAcyclicInSomeGraph'' hg in
    match b with
    | true => ([(hs, r)], true)
    | false => TreeAcyclicInSomeGraph' t ((hs, r) :: lr)
    end
  | [] => (lr, false)
  end.

Definition TreeAcyclicInSomeGraph
  (g : GraphTree nat)
  : list (string * MHBResult) * bool * nat :=
  let d := DNFOfTree g in
  let r := TreeAcyclicInSomeGraph' d [] in
  (fst r, snd r, List.length d).

