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

Require Import Arith.
Require Import Compare_dec.
Require Import wmm.
Require Import util2.
Require Import tree.
Require Import Bool.
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.

(** * Local Ordering Graphs *)

Definition location : Type := nat.

(** ** Paths *)

(** A [Path] is a list of locations (e.g., pipeline stages), given by [nat]
  indices, through which an operation passes during its execution. *)
Definition Path : Type := list location.

(** *** Transitive Closure of a [Path] *)

(** Pair the first argument with each element of the second argument *)
Fixpoint PathTC_Pair {A : Type}
  (src : A)
  (dsts : list A)
  : list (A * A) :=
  match dsts with
  | dst_head::dsts_tail => (src, dst_head) :: PathTC_Pair src dsts_tail
  | [] => []
  end.

(** Given a path, generate the list of pairs representing the transitive
  closure of the path. *)
Fixpoint PathTC {A : Type}
  (l : list A)
  : list (A * A) :=
  match l with
  | h::t => PathTC_Pair h t ++ PathTC t
  | [] => []
  end.

Lemma PathTCPairIn :
  forall (A : Type) (x y : A) (l : list A),
  In y l -> In (x, y) (PathTC_Pair x l).
Proof.
  intros A x y.  induction l as [|lh lt].
    intros H; inversion H.
  intros H.  destruct H as [H|H].
    rewrite H in *; clear H.  left.  auto.
  apply IHlt in H.  right.  auto.
Qed.

Lemma PathTCFollows :
  forall (A : Type) (x y : A) (l : list A),
  In x l ->
  In y l ->
  x <> y ->
  In (x, y) (PathTC l) \/ In (y, x) (PathTC l).
Proof.
  intros A x y l Hx Hy Hxy.
  induction l as [|lh lt].  inversion Hx.
  destruct Hx as [Hx|Hx].
    destruct Hy as [Hy|Hy].
      rewrite Hx, Hy in *.  elim Hxy; auto.
    left.  simpl.  assert(In (x, y) (PathTC_Pair lh lt)) as Hin.
      rewrite Hx.  apply PathTCPairIn.  auto.
    apply in_or_app.  left; auto.
  destruct Hy as [Hy|Hy].
    rewrite Hy in *.  right.
    simpl.  apply in_or_app.  left.  apply PathTCPairIn.  auto.
  simpl.  destruct IHlt; auto.
    left.  apply in_or_app.  auto.
  right.  apply in_or_app.  auto.
Qed.

Module PathTCExample.

Example e :
  PathTC [1; 2; 3] = [(1, 2); (1, 3); (2, 3)].
Proof.
auto.
Qed.

End PathTCExample.

(** A [PathMap] is a list in which the nth element is the path (as pairs of
  [location]s taken by the nth Event in program order. *)
Definition PathMap : Type := list (list (location * location)).

(** ** Graphs of Happens-Before Orderings *)

(* A [LocalOrdering] is an ordering on [Event]s that is enforced with at
  a given [location] (e.g., at a particular pipeline stage) *)
Definition LocalOrdering : Type := list (Event * Event).

(** A [LocalReordering] takes a set of events and returns some other
set of events.  This represents the set of guarantees that are
maintained, restored, no longer maintained, etc. through a given location.

The first argument provides the ordering as seen by all previous locations in
the pipeline.  We use this to be able to define things like reorder buffers,
where the output ordering is defined to be equal to the output ordering of
some previous stage, e.g., the decode stage. *)
Definition LocalReordering : Type :=
  list (list (Event * Event)) -> LocalOrdering -> LocalOrdering.

(** If the [LocalOrdering] edge [(e1, e2)] is present at location (vertex) [v1],
  and if both [e1] and [e2] have [v2] as the next [location] after [v1] in the
  [Path]s they take, then [(e1, e2)] is a [TransferedEdge] from [v1] to [v2]. *)
Definition TransferedEdge
  (paths : PathMap)
  (v1 v2 : location)
  (e1 e2 : Event)
  : bool :=
  let (p1, p2) := (nth (eiid e1) paths [], nth (eiid e2) paths []) in
    andb (Inb_nat_nat (v1, v2) p1) (Inb_nat_nat (v1, v2) p2).

(** Given a set [candidates] of [LocalOrdering] edges at a vertex [v1], return
  the set of edges that are [TransferedEdge]s from [v1] to [v2]; i.e., those
  such that the source and dest of the edge both have [v2] as the next stage
  in their paths. *)
Fixpoint TransferedEdges
  (paths : PathMap)
  (candidates : list (Event * Event))
  (v1 v2 : location)
  : list (Event * Event) :=
  match candidates with
  | [] => []
  | (e1, e2)::t =>
    if (TransferedEdge paths v1 v2 e1 e2)
      then (e1, e2) :: TransferedEdges paths t v1 v2
      else TransferedEdges paths t v1 v2
  end.

(** Given a set [candidates] of [LocalOrdering] edges at a vertex [v1], return
  the set of [TransferedEdges], and apply the [local_reordering] that a
  location performs. *)
Definition TransferedReorderedEdges
  (paths : PathMap)
  (candidates : list (Event * Event))
  (edges_all : list (list (Event * Event)))
  (v1 v2 : location)
  (local_reordering : LocalReordering)
  : list (Event * Event) :=
  local_reordering edges_all (TransferedEdges paths candidates v1 v2).

(** Return the set of [TransferedReorderedEdges] from [v1] to [v2], where
  [v1] is the index into the list of list of edges [edges_all]. *)
Fixpoint EdgesToTransferedEdges'
  (paths : PathMap)
  (edges_all : list (list (Event * Event)))
  (v1 v2 : location)
  (local_reordering : LocalReordering)
  : list (list (Event * Event)) :=
  match edges_all with
  | [] => []
  | edges_h::edges_t =>
    TransferedReorderedEdges paths edges_h edges_all v1 v2 local_reordering ::
    EdgesToTransferedEdges' paths edges_t (S v1) v2 local_reordering
  end.

(** Return the union of the sets of [TransferedReorderedEdges] from every
  previous location to [v2]. *)
Definition EdgesToTransferedEdges
  (paths : PathMap)
  (edges_all : list (list (Event * Event)))
  (v2 : location)
  (local_reordering : LocalReordering) :
  list (Event * Event) :=
  fold_left (app (A:=_))
    (EdgesToTransferedEdges' paths edges_all 0 v2 local_reordering)
    [].

(** Given a list of edges at locations 0 through (n-1), calculate and append
  the list of edges at location n. *)
Definition EdgesToEdges
  (paths : PathMap)
  (local_reordering : LocalReordering)
  (edges_all : list (list (Event * Event))) :
  list (list (Event * Event)) :=
  edges_all ++
    [EdgesToTransferedEdges paths edges_all (List.length edges_all)
     local_reordering].

Module EdgesExample.

Definition ev0 : Event := mkev 0 (mkiiid 0 0) (Access W 0 1).
Definition ev1 : Event := mkev 1 (mkiiid 0 1) (Access R 0 0).
Definition ev2 : Event := mkev 2 (mkiiid 0 2) (Access R 0 0).
Definition ev3 : Event := mkev 3 (mkiiid 0 3) (Access W 0 1).

Definition pathpairs : PathMap :=
  [[(0, 1); (1, 3)]; [(0, 1); (1, 3)]; [(0, 2); (2, 3)]; [(0, 2); (2, 3)]].

Definition edges0 : list (list (Event * Event)) :=
  [PathTC [ev0; ev1; ev2; ev3]].

Definition FIFO : LocalReordering := fun _ => fun z => z.

Definition edges01 := EdgesToEdges pathpairs FIFO edges0.

Example edges0_to_01 : edges01 = edges0 ++ [[(ev0, ev1)]].
Proof.
  auto.
Qed.

Definition edges012 := EdgesToEdges pathpairs FIFO edges01.
Definition edges0123 := EdgesToEdges pathpairs FIFO edges012.

End EdgesExample.

(** Given a list of events originating at a given [location], create program
  order edges between edges from the same [poi]. *)
Definition ProgramOrderEdges
  (l : list Event)
  : list (Event * Event) :=
  let sorted_events := fold_left
    (fun l' e => AppendToNth l' (proc (iiid e)) e) l [] in
  let edges := map PathTC sorted_events in
  fold_left (app (A:=_)) edges [].

(** Given a list of locations (defined as a list of [LocalReordering]s),
  a set of [LocalOrdering] edges from the first [location], and a [PathMap]
  defining the [Path] taken by each [Event] in the scenario, calculate the
  full set of [LocalOrdering] edges in the scenario.

  [IntraLocationEdges'] handles cases other than the first, i.e., those which
  are defined in terms of previous [location]s rather than program order. *)
Fixpoint IntraLocationEdges'
  (paths : PathMap)
  (edges_all : list (list (Event * Event)))
  (po_events : list (list Event))
  (local_reorderings : list (LocalReordering))
  : list (list (Event * Event)) :=
  match (local_reorderings, po_events) with
  | (oh::ot, eh::et) =>
    IntraLocationEdges' paths
      (AppendToLast (ProgramOrderEdges eh) (EdgesToEdges paths oh edges_all))
      et ot
  | (oh::ot, _) =>
    IntraLocationEdges' paths (EdgesToEdges paths oh edges_all) [] ot
  | _ => edges_all
  end.

(** Given a list of locations (as specified as a list of [LocalReordering]s),
  a set of [LocalOrdering] edges from the first location, and a [PathMap]
  defining the [Path] taken by each [Event] in the scenario, calculate the
  full set of [LocalOrdering] edges in the scenario.

  [IntraLocationEdges] handles the base case, i.e., the stage which is defined
  in terms of program order, since there are no previous [location]s. *)
Definition IntraLocationEdges
  (paths : PathMap)
  (events : list (list Event))
  (local_reorderings : list (LocalReordering))
  : list (list (Event * Event)) :=
  IntraLocationEdges' paths [] events local_reorderings.

Module EdgesExample2.
Import EdgesExample.

Definition my_local_reorderings := [FIFO; FIFO; FIFO; FIFO].

Example edges_to_3 :
  edges0123 =
    IntraLocationEdges pathpairs [[ev0; ev1; ev2; ev3]] my_local_reorderings.
Proof.
  auto.
Qed.

End EdgesExample2.

(** ** Global Events *)

(** A [GlobalEvent] is a memory [Event] (as its [eiid]) passing through
  a particular [location] *)
Definition GlobalEvent : Type := prod location Eiid.

(** A [GlobalGraph] is a list of labeled edges between [GlobalEvent]s *)
Definition GlobalGraph : Type := list (GlobalEvent * GlobalEvent * string).

(** * Pipeline Model *)

(** ** Pipeline Stages *)

(** A SpecialEdgeMap produces a set of extra edges from a given [Event] to
  edges coming either before or after it in program order.

  For example, a store buffer might ensure that only one unacknowledged store
  is outstanding at any given time; in this case, we would add an global edge
  from the [GlobalEvent] of the first [Event] getting acknowledged to the
  subsequent [Event] leaving the store buffer. *)
Definition SpecialEdgeMap : Type :=
  list Event -> Event -> list Event -> GlobalGraph.

(** A pipeline [Stage] is defined by its name, its numerical ID (which must be
  monotonically increasing), the [LocalReordering] it performs, and a
  [SpecialEdgeMap] if applicable. *)
Record Stage := mkStage {
  name : string;
  localReordering : LocalReordering;
  specialEdges : SpecialEdgeMap
}.

(** A [PerformStages] specifies the locations at which an instruction peforms
  with respect to each core along its path.

 [observability] refers to the situation in which a particular performing
 location is only visible to stores from certain cores.  For example, a read
 forwarded from the store buffer may perform with respect to all cores wheen
 it performs, but it can only observe stores from the same core in this
 situation.
 *)
Record PerformStages := mkPerformStages {
  stage : nat;
  cores : list nat;
  observability : list nat;
  cacheLineInvLoc : option nat;
  isMainMemory : bool
}.

(** A [PathOption] is a possible [Path] for an [Event] through a given
  [Pipeline], together with a [SpecialEdgeMap] that adds any extra orderings
  associated with the option.

  For example, a cache miss may flush the pipeline, meaning that no subsequent
  (in program order) [Event]s will leave the fetch stage until the cache miss
  response is received.
*)
Record PathOption : Type := mkPathOption {
  optionName : string;
  evt : Event;
  path : Path;
  performStages : list PerformStages;
  sem : SpecialEdgeMap
}.

(** [PathOptions] represents a set of paths for a single event, such that only
  one will be chosen in any given scenario. *)
Definition PathOptions : Type := list PathOption.

(** [Scenario] represents a set of paths for different events, such that the
  set of [PathOption]s taken together represent the path of each [Event] in
  a scenario. *)
Definition Scenario : Type := list PathOption.

(** A [Pipeline] is defined as a set of [Stage]s, a function [pathsFor] that
  maps each event into a list of its possible [PathOptions] *)
Record Pipeline := mkPipeline {
  pipename : string;
  stages : list Stage;
  pathsFor : Event -> PathOptions
}.

(** ** Edges in the Global Ordering Graph *)

Open Scope string_scope.
Open Scope list_scope.

(** Given an [Event] and the [Path] it takes, produce the associated set of
  global edges for that path. *)
Fixpoint IntraEventGlobalEdges
  (e : Event)
  (p : Path)
  : GlobalGraph :=
  match p with
  | h::t =>
    match t with
    | th::_ =>
      ((h, eiid e), (th, eiid e), "IntraEvent") :: IntraEventGlobalEdges e t
    | [] => []
    end
  | [] => []
  end.

(** Calculate the [IntraEventGlobalEdges] for each [Path] in a [Scenario]. *)
Fixpoint ScenarioIntraEventGlobalEdges
  (l : Scenario)
  : GlobalGraph :=
  match l with
  | (mkPathOption _ e p _ sem)::t =>
    IntraEventGlobalEdges e p ++ ScenarioIntraEventGlobalEdges t
  | [] => []
  end.

(** Convert a list of local edges at a given [location] into the corresponding
  set of global edges. *)
Fixpoint IntraLocationGlobalEdges'
  (l : location)
  (le : list (Event * Event))
  : GlobalGraph :=
  match le with
  | (e1,e2)::t =>
    ((l, eiid e1), (l, eiid e2), "IntraLocation")
    :: IntraLocationGlobalEdges' l t
  | [] => []
  end.

(** Convert the list of local edges at each [location] in a [Scenario]
  [Pipeline] into the corresponding set of global edges. *)
Fixpoint IntraLocationGlobalEdges
  (l : location)
  (le : list (list (Event * Event)))
  : GlobalGraph :=
  match le with
  | h::t =>
    IntraLocationGlobalEdges' l h ++ IntraLocationGlobalEdges (S l) t
  | [] => []
  end.

(** Given a set of events, sort them into a list of lists based on the first
  location in their paths. *)
Fixpoint EventsSortedByFirstLocation'
  (l : list (list Event))
  (s : Scenario)
  : list (list Event) :=
  match s with
  | h::t =>
    let e := evt h in
    let p := path h in
    match p with
    | h::_ => EventsSortedByFirstLocation' (AppendToNth l h e) t
    | [] => EventsSortedByFirstLocation' l t
    end
  | [] => l
  end.

(** Given a set of events, sort them into a list of lists based on their
  processor ID. *)
Definition EventsSortedByFirstLocation
  (s : Scenario)
  : list (list Event) :=
  EventsSortedByFirstLocation' [] s.

Module EventsSortedByFirstLocationExample.

Definition ev0 := mkev 0 (mkiiid 0 0) (Access W 0 1).
Definition ev1 := mkev 1 (mkiiid 0 1) (Access W 0 2).
Definition ev2 := mkev 2 (mkiiid 2 0) (Access W 0 3).

Definition NoSpecialEdges : SpecialEdgeMap := fun _ _ _ => [].
Definition DummyScenario e := mkPathOption "Dummy" e [1; 2] [] NoSpecialEdges.

Example e1 : EventsSortedByFirstLocation (map DummyScenario [ev0; ev1; ev2]) =
  [[]; [ev0; ev1; ev2]].
Proof.  cbv.  auto.  Qed.

End EventsSortedByFirstLocationExample.

(** Convert the list of local edges at each location in a [Scenario] into the
  corresponding set of global edges. *)
Definition ScenarioIntraLocationGlobalEdges
  (s : Scenario)
  (pipeline : Pipeline)
  : GlobalGraph :=
  let path_pairs := map PairConsecutive (map path s) in
  let local_reorderings := map localReordering (stages pipeline) in
  IntraLocationGlobalEdges 0
    (IntraLocationEdges path_pairs (EventsSortedByFirstLocation s) local_reorderings).

Fixpoint PartitionAtEvent'
  (h t : list Event)
  (e : Event)
  : list Event * list Event :=
  match t with
  | th::t' =>
    if beq_nat (eiid e) (eiid th)
      then (h, t')
      else PartitionAtEvent' (h ++ [th]) t' e
  | [] => ([], [])
  end.

(** Given a list [l] of [Event]s, return the list of [Event]s before [e] and
  after [e], with before and after determined by program order index. *)
Definition PartitionAtEvent
  (l : list Event)
  (e : Event)
  : list Event * list Event :=
  PartitionAtEvent' [] l e.

Fixpoint LocalEvents
  (l : list Event)
  (e : Event)
  : list Event :=
  match l with
  | h::t =>
    match (nat_compare (proc (iiid h)) (proc (iiid e))) with
    | Eq => h :: LocalEvents t e
    | _  =>      LocalEvents t e
    end
  | [] => []
  end.

(** Calculate the set of all special global edges due to the [Event] path
  choices in a given [Scenario] *)
Fixpoint ScenarioPathSpecialEdges'
  (s : Scenario)
  (prev_events : list Event)
  : GlobalGraph :=
  match s with
  | (mkPathOption _ e p _ sem)::t =>
    let local_events := LocalEvents (prev_events ++ map evt s) e in
    let (e_before, e_after) := PartitionAtEvent local_events e in
    sem e_before e e_after
    ++ ScenarioPathSpecialEdges' t (prev_events ++ [e])
  | [] => []
  end.

(** Calculate the set of all special global edges due to the [Event] path
  choices in a given [Scenario] *)
Fixpoint ScenarioPathSpecialEdges
  (s : Scenario)
  : GlobalGraph :=
  ScenarioPathSpecialEdges' s [].

(** Calculate the set of all special global edges at a given [location] *)
Definition LocationSpecialEdges
  (e : Event)
  (events : list Event)
  (m : SpecialEdgeMap)
  : GlobalGraph :=
  let local_events := LocalEvents events e in
  let (e_before, e_after) := PartitionAtEvent local_events e in
  m e_before e e_after.

(** Calculate the set of all special global edges due to the pipelines in a
  given [PathOption] *)
Fixpoint PathPipelineSpecialEdges
  (l : list location)
  (e : Event)
  (events : list Event)
  (p : Pipeline)
  : GlobalGraph :=
  match l with
  | h::t =>
    let m := nth h (map specialEdges (stages p)) (fun _ _ _ => []) in
    LocationSpecialEdges e events m
    ++ PathPipelineSpecialEdges t e events p
  | [] => []
  end.

(** Calculate the set of all special global edges due to the pipelines in a
  given [Scenario] *)
Fixpoint ScenarioPipelineSpecialEdges
  (s : Scenario)
  (p : Pipeline)
  : GlobalGraph :=
  match s with
  | h::t =>
    PathPipelineSpecialEdges (path h) (evt h) (map evt s) p
    ++ ScenarioPipelineSpecialEdges t p
  | [] => []
  end.

(** Calculate the set of all global edges in a [Scenario] *)
Definition ScenarioEdges
  (t : string)
  (p : Pipeline)
  (s : Scenario)
  : GraphTree GlobalEvent :=
  let (t_start, t) := TimerStartHook t in
  let result := GraphTreeLeaf _ t (
    ScenarioIntraLocationGlobalEdges s p
    ++
    ScenarioIntraEventGlobalEdges s
    ++
    ScenarioPipelineSpecialEdges s p
    ++
    ScenarioPathSpecialEdges s) in
  TimerStopHook "ScenarioEdges" t_start result.

Module EdgesExample3.
Import EdgesExample.
Import EdgesExample2.

Definition NoSpecialEdges : SpecialEdgeMap := fun _ _ _ => [].

Definition my_stages := [
  mkStage "F"  FIFO NoSpecialEdges;
  mkStage "FL" FIFO NoSpecialEdges;
  mkStage "FS" FIFO NoSpecialEdges;
  mkStage "L"  FIFO NoSpecialEdges;
  mkStage "S"  FIFO NoSpecialEdges;
  mkStage "LC" FIFO NoSpecialEdges;
  mkStage "SC" FIFO NoSpecialEdges;
  mkStage "C"  FIFO NoSpecialEdges].

Definition my_paths_for (e : Event) :=
  match dirn e with
  | R =>
    [mkPathOption "Read"  e [0; 1; 3; 5; 7] [mkPerformStages 3 [0] [0] None true]
     NoSpecialEdges]
  | W =>
    [mkPathOption "Write" e [0; 2; 4; 6; 7] [mkPerformStages 4 [0] [0] None true]
     NoSpecialEdges]
  end.

Definition my_pipeline :=
  mkPipeline "SamplePipeline" my_stages my_paths_for.

(** Since each event only has one possible [PathOption] in this pipeline, there
  is only one [Scenario] to consider. *)
Definition my_scenarios := [[
    mkPathOption "Write" ev0 [0; 2; 4; 6; 7] [mkPerformStages 4 [0] [0] None true]
      NoSpecialEdges;
    mkPathOption "Read"  ev1 [0; 1; 3; 5; 7] [mkPerformStages 3 [0] [0] None true]
      NoSpecialEdges;
    mkPathOption "Read"  ev2 [0; 1; 3; 5; 7] [mkPerformStages 3 [0] [0] None true]
      NoSpecialEdges;
    mkPathOption "Write" ev3 [0; 2; 4; 6; 7] [mkPerformStages 4 [0] [0] None true]
      NoSpecialEdges
  ]].

Definition my_scenario : Scenario := hd [] my_scenarios.

Definition my_global_edges :=
  ScenarioEdges "my_sample " my_pipeline my_scenario.

Example e_my_global_edges :
  my_global_edges = GraphTreeLeaf _ "my_sample " [
   (** location 0 *)
   ((0, 0), (0, 1), "IntraLocation"); ((0, 0), (0, 2), "IntraLocation");
   ((0, 0), (0, 3), "IntraLocation"); ((0, 1), (0, 2), "IntraLocation");
   ((0, 1), (0, 3), "IntraLocation"); ((0, 2), (0, 3), "IntraLocation");
   (** location 1 *)
   ((1, 1), (1, 2), "IntraLocation");
   (** location 2 *)
   ((2, 0), (2, 3), "IntraLocation");
   (** location 3 *)
   ((3, 1), (3, 2), "IntraLocation");
   (** location 4 *)
   ((4, 0), (4, 3), "IntraLocation");
   (** location 5 *)
   ((5, 1), (5, 2), "IntraLocation");
   (** location 6 *)
   ((6, 0), (6, 3), "IntraLocation");
   (** location 7 *)
   ((7, 1), (7, 2), "IntraLocation"); ((7, 0), (7, 3), "IntraLocation");
   (** event 0 *)
   ((0, 0), (2, 0), "IntraEvent"); ((2, 0), (4, 0), "IntraEvent");
   ((4, 0), (6, 0), "IntraEvent"); ((6, 0), (7, 0), "IntraEvent");
   (** event 1 *)
   ((0, 1), (1, 1), "IntraEvent"); ((1, 1), (3, 1), "IntraEvent");
   ((3, 1), (5, 1), "IntraEvent"); ((5, 1), (7, 1), "IntraEvent");
   (** event 2 *)
   ((0, 2), (1, 2), "IntraEvent"); ((1, 2), (3, 2), "IntraEvent");
   ((3, 2), (5, 2), "IntraEvent"); ((5, 2), (7, 2), "IntraEvent");
   (** event 3 *)
   ((0, 3), (2, 3), "IntraEvent"); ((2, 3), (4, 3), "IntraEvent");
   ((4, 3), (6, 3), "IntraEvent"); ((6, 3), (7, 3), "IntraEvent")].
Proof.
cbv.  auto.
Qed.

End EdgesExample3.

