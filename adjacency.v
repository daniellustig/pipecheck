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

(** * Adjacency Lists *)

Definition AdjacencyList : Type := list (list nat).

Fixpoint AdjacencyListFromEdges
  (l : list (nat * nat))
  : list (list nat) :=
  match l with
  | h::t =>
    let (h1, h2) := h in
    AppendToNth (AdjacencyListFromEdges t) h1 h2
  | [] => []
  end.

(** * Dijkstra's algorithm

This is a simplification of Dijkstra's algorithm.  There is no checking if
a node has been previously visited, nor is the queue of pending vertices
sorted by weight.  Since all we care about is reachability, this doesn't
matter. *)

(** Add all nodes adjacent to vertex [v] in [g] to [queue], and update the
  list [prevs] of "previous" nodes accordingly. *)
Definition DijkstraStep
  (g : AdjacencyList)
  (src : nat)
  (queue : list nat)
  (prevs : list (option nat))
  (v : nat)
  : (list nat * list (option nat)) :=
  let adjacentNodes := nth v g [] in
  if Inb_nat src adjacentNodes
    then (* cyclic - stop here *)
      ([], replaceNthIfNone prevs src v)
    else
      let f_fold l i := replaceNthIfNone l i v in
      (fold_left AddUnique adjacentNodes queue,
          fold_left f_fold adjacentNodes prevs).

(** Perform one iteration of Dijkstra's algorithm: pop a vertex out of the
  queue and add all vertices adjacent to the popped vertex to the queue.
  The argument [unroll] is necessary to ensure that the function terminates *)
Fixpoint DijkstraAdj'
  (unroll : nat)
  (g : AdjacencyList)
  (src : nat)
  (queue reachable : list nat)
  (prevs : list (option nat))
  : (list nat * list (option nat)) :=
  match (unroll, queue) with
  | (0        , _   ) => (reachable, prevs) (* Shouldn't happen! *)
  | (S unroll', []  ) => (reachable, prevs)
  | (S unroll', h::t) =>
    let (queue', prevs') := DijkstraStep g src queue prevs h in
    DijkstraAdj' unroll' g src (tl queue') (AddUnique reachable h) prevs'
  end.

(** Given a graph [g] (in the form of an adjacency list) and a source [src],
  calculate the set of vertices reachable from [src], and list containing the
  node previous to each destination along some path from [src], or [None] if
  there is no path from [src]. *)
Definition DijkstraAdj
  (g : AdjacencyList)
  (src : nat)
  : (list nat * list (option nat)) :=
  let max_iters := fold_left plus (map (length (A:=_)) g) (length g) in
  let (r, prevs) := DijkstraAdj' max_iters g src [src] [] [] in
  (* If the source isn't reachable from itself, don't include it *)
  match (nth src prevs None) with
  | Some _ => (r, prevs)
  | None => (tl r, prevs)
  end.

(** Given a graph [g] (in the form of a list of edges) and a source [src],
  calculate the set of vertices reachable from [src], and list containing the
  node previous to each destination along some path from [src], or [None] if
  there is no path from [src]. *)
Definition Dijkstra
  (g : list (nat * nat))
  (src : nat)
  : (list nat * list (option nat)) :=
  DijkstraAdj (AdjacencyListFromEdges g) src.

(** * Examples *)

Module Example1.

Definition ExampleGraph : AdjacencyList :=
  [[3]; []; [0; 3]; [1]].

Example e1 :
  DijkstraAdj ExampleGraph 2 = ([0; 3; 1], [Some 2; Some 3; None; Some 2]).
Proof.
cbv.  auto.
Qed.

Example e2 :
  DijkstraAdj ExampleGraph 0 = ([3; 1], [None; Some 3; None; Some 0]).
Proof.
cbv.  auto.
Qed.

End Example1.

Module Example2.

Definition ExampleGraph : list (nat * nat) :=
  [(0, 3); (2, 0); (2, 3); (3, 1)].

Example e : Dijkstra ExampleGraph 0 = ([3; 1], [None; Some 3; None; Some 0]).
Proof.
auto.
Qed.

Definition ExampleGraph2 : list (nat * nat) :=
  [(0, 1); (1, 0)].

Example e2 : Dijkstra ExampleGraph2 0 = ([0; 1], [Some 1; Some 0]).
Proof.
cbv.  auto.
Qed.

End Example2.

Module Example3.

Definition ExampleGraph : list (nat * nat) :=
  [(0, 1); (0, 2); (1, 3); (2, 3)].

Example e3_1 : AdjacencyListFromEdges ExampleGraph =
  [[2; 1]; [3]; [3]].
Proof.
auto.
Qed.

Example e3_2 : Dijkstra ExampleGraph 0 = ([2; 1; 3], [None; Some 0; Some 0; Some 2]).
Proof.
auto.
Qed.

End Example3.

(** * PathBacktrace

Find a path from the source node to the target node, given the list of
"previous nodes" produced by [Dijkstra]. *)

Fixpoint PathBacktrace'
  (prev : list (option nat))
  (src dst : nat)
  (unroll : nat)
  : list nat :=
  match (unroll, nth dst prev None) with
  | (S unroll', Some prevs) =>
    match nat_compare src prevs with
    | Eq => [prevs]
    | _ => PathBacktrace' prev src prevs unroll' ++ [prevs]
    end
  | _ => PanicHook "PathBacktrace' iteration limit exceeded" []
  end.

Definition PathBacktrace
  (g : list (nat * nat))
  (prev : list (option nat))
  (src dst : nat)
  : list nat :=
  let r := PathBacktrace' prev src dst (List.length g) in
  match r with
  | [] => []
  | _ => r ++ [dst]
  end.

Definition PathBacktraceAdj
  (g : list (list nat))
  (prev : list (option nat))
  (src dst : nat)
  : list nat :=
  let r := PathBacktrace' prev src dst (List.length g) in
  match r with
  | [] => []
  | _ => r ++ [dst]
  end.

Definition FindPath
  (g : list (nat * nat))
  (src dst : nat)
  : list nat :=
  let (reachable, prev) := Dijkstra g src in
  PathBacktrace g prev src dst.

Definition FindPathAdj
  (g : list (list nat))
  (src dst : nat)
  : list nat :=
  let (reachable, prev) := DijkstraAdj g src in
  PathBacktraceAdj g prev src dst.

Module Example4.
Import Example2.

Example e3 : FindPath ExampleGraph 2 3 = [2; 3].
Proof.
cbv.  auto.
Qed.

Example e4 : PathBacktraceAdj [[1]] [None; Some 0] 0 1 = [0; 1].
Proof.
cbv.  auto.
Qed.

Example e5 :
  FindPath [(0, 1); (0, 2); (1, 2); (2, 3); (3, 0)] 0 0 = [0; 2; 3; 0].
Proof.
cbv.  auto.
Qed.

Example e6 :
  FindPath [(0, 1); (0, 2)] 1 2 = [].
Proof.
cbv.  auto.
Qed.

End Example4.

