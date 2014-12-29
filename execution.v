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
Require Import Compare_dec.
Require Import util2.
Require Import tree.
Require Import adjacency.
Require Import topsort.
Require Import interleavings.
Require Import wmm.
Require Import bell.
Require Import dot.
Require Import stages.
Require Import globalgraph.
Require Import musthappenbefore.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.

(** ** Debugging/Printing functions *)

Fixpoint PrintGraph'
  (l : list (GlobalEvent * GlobalEvent * string))
  : string :=
  match l with
  | h::t =>
    let (sd, n) := h in
    let (s, d) := sd in
    let (s1, s2) := s in
    let (d1, d2) := d in
    fold_left append ["(("; stringOfNat s1; ", "; stringOfNat s2; "), (";
      stringOfNat d1; ", "; stringOfNat d2; "), "; n; ") ";
      PrintGraph' t] ""
  | [] => newline
  end.

Definition PrintGraph
  (l : list (GlobalEvent * GlobalEvent * string))
  : string :=
  fold_left append [newline; "Graph: "; PrintGraph' l] "".

Fixpoint natPairListToString
  (l : list GlobalEvent)
  : string :=
  match l with
  | h::t =>
    fold_left append [
      "("; stringOfNat (fst h); ", "; stringOfNat (snd h); ") ";
      natPairListToString t] ""
  | [] => newline
  end.

Fixpoint PrintRFList'
  (l : list (Eiid * Eiid))
  : string :=
  match l with
  | (h1, h2)::t =>
    fold_left append [
      "("; stringOfNat h1; "-rf->"; stringOfNat h2; ") ";
      PrintRFList' t] ""
  | [] => newline
  end.

Definition PrintRFList
  (l : list (Eiid * Eiid))
  : string :=
  fold_left append ["RF list for execution: "; PrintRFList' l] "".

Definition PrintReachableNodesList
  (n : nat)
  (p : Pipeline)
  (src : GlobalEvent)
  (l : list GlobalEvent)
  : string :=
  fold_left append [
    "("; stringOfNat n; ") Nodes reachable from "; stringOfNat (geid p src);
    "=("; stringOfNat (fst src); ", "; stringOfNat (snd src);
    "): "; natPairListToString l] "".

(** * Calculation of uhb graphs *)

Fixpoint pathOfEvent
  (s : Scenario)
  (e : Eiid)
  : option PathOption :=
  match s with
  | h::t =>
    match (nat_compare (eiid (evt h)) e) with
    | Eq => Some h
    | _ => pathOfEvent t e
    end
  | [] => None
  end.

(** Given the list of [PerformStages] for an event, and a core [c], calculate
  the set of stages at the event has performed with respect to core [c] *)
Fixpoint PerformStagesWRTCore'
  (c : nat)
  (l : list PerformStages)
  : list nat :=
  match l with
  | mkPerformStages h_stage h_cores _ _ _::t =>
    if Inb_nat c h_cores
      then h_stage::PerformStagesWRTCore' c t
      else PerformStagesWRTCore' c t
  | [] => []
  end.

(** Given the list of [PerformStages] for an event, and a core [c], calculate
  the set of stages at the event has performed with respect to core [c] *)
Definition PerformStagesWRTCore
  (c : nat)
  (po : PathOption)
  : list nat :=
  PerformStagesWRTCore' c (performStages po).

Fixpoint PerformOrInvStagesWRTCore'
  (c : nat)
  (l : list PerformStages)
  : list nat :=
  match l with
  | mkPerformStages h_stage h_cores _ None _::t =>
    if Inb_nat c h_cores
      then h_stage::PerformOrInvStagesWRTCore' c t
      else PerformOrInvStagesWRTCore' c t
  | mkPerformStages h_stage h_cores _ (Some i) _::t =>
    if Inb_nat c h_cores
      then i::PerformOrInvStagesWRTCore' c t
      else PerformOrInvStagesWRTCore' c t
  | [] => []
  end.

Fixpoint PerformOrInvStagesWRTCore
  (c : nat)
  (po : PathOption)
  : list nat :=
  PerformOrInvStagesWRTCore' c (performStages po).

(** Given the list of [PerformStages] for an event, and a core [c], calculate
  the set of stages at which core [c] can observe that the event has
  performed. *)
Fixpoint VisibleStagesWRTCore'
  (c : nat)
  (l : list PerformStages)
  : list nat :=
  match l with
  | mkPerformStages h_stage _ h_cores _ _::t =>
    if Inb_nat c h_cores
      then h_stage::VisibleStagesWRTCore' c t
      else VisibleStagesWRTCore' c t
  | [] => []
  end.

Fixpoint VisibleStagesWRTCore
  (c : nat)
  (po : PathOption)
  : list nat :=
  VisibleStagesWRTCore' c (performStages po).

Fixpoint RFPerformPairs
  (src dst : PathOption)
  : list (location * location) :=
  let src_core := proc (iiid (evt src)) in
  let dst_core := proc (iiid (evt dst)) in
  let src_perf_stages := PerformStagesWRTCore dst_core src in
  let dst_perf_stages := VisibleStagesWRTCore src_core dst in
  CartesianProductPairs src_perf_stages dst_perf_stages.

Fixpoint FRinitialPerformPairs
  (src dst : PathOption) (* src R -> dst W *)
  : list (location * location) :=
  let src_core := proc (iiid (evt src)) in
  let dst_core := proc (iiid (evt dst)) in
  let src_perf_stages := PerformOrInvStagesWRTCore dst_core src in
  let dst_perf_stages := PerformStagesWRTCore src_core dst in
  CartesianProductPairs src_perf_stages dst_perf_stages.

Fixpoint FRfwPerformPairs
  (src dst : PathOption)
  : list (location * location) :=
  let src_core := proc (iiid (evt src)) in
  let dst_core := proc (iiid (evt dst)) in
  let src_perf_stages := PerformOrInvStagesWRTCore dst_core src in
  let dst_perf_stages := PerformStagesWRTCore src_core dst in
  CartesianProductPairs src_perf_stages dst_perf_stages.

Definition ReachableVertices
  (pipeline : Pipeline)
  (src : GlobalEvent)
  (g : list (GlobalEvent * GlobalEvent * string))
  : list GlobalEvent :=
  let g2 := map (gepid pipeline) g in
  let g3 := map (fst (A:=_) (B:=_)) g2 in
  let (reachable, _) := Dijkstra g3 (geid pipeline src) in
  map (ungeid pipeline) reachable.

Definition nthEventInScenarioIsWrite
  (s : Scenario)
  (ge : nat * Eiid)
  : bool :=
  match (nth_error s (snd ge)) with
  | Some po =>
    match dirn (evt po) with
    | R => false
    | W => true
    end
  | None => false
  end.

Definition VertexHasSameAddress
  (s : Scenario)
  (l : Location)
  (e : GlobalEvent)
  : bool :=
  match (nth_error s (snd e)) with
  | Some po =>
    beq_nat (loc (evt po)) l
  | None => false
  end.

Definition ReachableVerticesAtSameLocation
  (p : Pipeline)
  (s : Scenario)
  (src : GlobalEvent)
  (g : list (GlobalEvent * GlobalEvent * string))
  : list Eiid :=
  match (nth_error s (snd src)) with
  | Some po =>
    let f x := VertexHasSameAddress s (loc (evt po)) x in
    let f2 x := nthEventInScenarioIsWrite s x in
    let l := ReachableVertices p src g in
    let l' := filter f l in
    let l'' := filter f2 l' in
    let l''' := map (snd (A:=_) (B:=_)) l'' in
    let l'''' := fold_left AddUnique l''' [] in
    let l''''' := remove_nat (snd src) l'''' in
    l'''''
  | None => []
  end.

Definition WritesToSameLocation
  (l : Location)
  (s : Scenario)
  : list PathOption :=
  let f x := if (dirn (evt x)) (* = R *)
    then false
    else beq_nat l (loc (evt x)) in
  filter f s.

Fixpoint ExecutionEdgeLabel
  (n : string)
  (l : list (GlobalEvent * GlobalEvent * string))
  : string :=
  match l with
  | h::t =>
    let e1 := snd (fst (fst h)) in
    let e2 := snd (snd (fst h)) in
    fold_left append ["("; stringOfNat e1; "-"; n; "->"; stringOfNat e2; ") ";
    ExecutionEdgeLabel n t] ""
  | [] => ""
  end.

Definition ExecutionOrderEdges_FR_initial'
  (p : Pipeline)
  (es ed : Eiid)
  (ll : location * location)
  : GraphTree GlobalEvent :=
  let (ls, ld) := ll in
  let s := (ls, es) in
  let d := (ld, ed) in
  let l := [(s, d, "FRi")] in
  let PrintPossibility t :=
    append (DNFStringOfTree (GlobalEventString p) t) newline in
  let l := DebugPrintfHook l 3 (PrintPossibility (GraphTreeLeaf _ "fr_uhb" l)) in
  GraphTreeLeaf _ (ExecutionEdgeLabel "fr" l) l.

Definition ExecutionOrderEdges_FR_initial
  (p : Pipeline)
  (src : PathOption)
  (g_uhb : GraphTree GlobalEvent)
  (dst : PathOption)
  : GraphTree GlobalEvent :=
  GraphTreeAnd _
    (g_uhb ::
      (map (ExecutionOrderEdges_FR_initial' p
          (eiid (evt src)) (eiid (evt dst)))
        (FRinitialPerformPairs src dst))).

Definition ScenarioExecutionEdges_FR_initial
  (p : Pipeline)
  (s : Scenario)
  (g_uhb : GraphTree GlobalEvent)
  (e : Eiid)
  : GraphTree GlobalEvent :=
  match pathOfEvent s e with
  | Some pr => (* Found PathOptions for r *)
    let ws := WritesToSameLocation (loc (evt pr)) s in
    fold_left (ExecutionOrderEdges_FR_initial p pr) ws g_uhb
  | _ => PanicHook
    "ScenarioExecutionEdges_FR_initial: event is not actually in scenario"
    g_uhb
  end.

Fixpoint ExecutionOrderEdges_FR_fromwrite'''
  (s : Scenario)
  (l : list Eiid)
  : list PathOption :=
  match l with
  | h::t =>
    match pathOfEvent s h with
    | Some p => p :: ExecutionOrderEdges_FR_fromwrite''' s t
    | None   =>      ExecutionOrderEdges_FR_fromwrite''' s t
    end
  | [] => []
  end.

Definition ExecutionOrderEdges_FR_fromwrite''
  (s : Scenario)
  (r w : PathOption)
  : list (GlobalEvent * GlobalEvent * string) :=
  let f p := ((fst p, eiid (evt r)), (snd p, eiid (evt w)), "FRfw") in
  map f (FRfwPerformPairs r w).

(** Given a uhb RF edge (w, r), for all vertices w' in [g_uhb] such that
  (w, w') is an edge in [g_uhb] between events at the same location, add the
  FR edge (r, w'). *)
Definition ExecutionOrderEdges_FR_fromwrite'
  (p : Pipeline)
  (s : Scenario)
  (w r : GlobalEvent)
  (nl : string * list (GlobalEvent * GlobalEvent * string))
  : string * list (GlobalEvent * GlobalEvent * string) :=
  let (n, l) := nl in
  let w_reachable := ReachableVerticesAtSameLocation p s w l in
  let w_reachable' := ExecutionOrderEdges_FR_fromwrite''' s w_reachable in
  match pathOfEvent s (snd r) with
  | Some p =>
    let l' := fold_left (app (A:=_))
      (map (ExecutionOrderEdges_FR_fromwrite'' s p) w_reachable') [] in
    (n, l ++ l')
  | None => nl
  end.

Definition ExecutionOrderEdges_FR_fromwrite
  (p : Pipeline)
  (s : Scenario)
  (w r : GlobalEvent)
  (g_uhb : GraphTree GlobalEvent)
  : GraphTree GlobalEvent :=
  TreeOfDNF (map (ExecutionOrderEdges_FR_fromwrite' p s w r) (DNFOfTree g_uhb)).

(** Given a source and destination event for a particular uhb interpretation of
  an RF edge, create the corresponding uhb edge(s) *)
Definition ExecutionOrderEdges_RFandFR_fromwrite'
  (p : Pipeline)
  (s : Scenario)
  (g_uhb : GraphTree GlobalEvent)
  (es ed : Eiid)
  (ll : location * location)
  : GraphTree GlobalEvent :=
  let (ls, ld) := ll in
  let src := (ls, es) in
  let dst := (ld, ed) in
  let l := [(src, dst, "RF")] in
  let PrintPossibility t :=
    append (DNFStringOfTree (GlobalEventString p) t) newline in
  let l := DebugPrintfHook l 3 (PrintPossibility (GraphTreeLeaf _ "rf_uhb" l)) in
  GraphTreeAnd _ [ExecutionOrderEdges_FR_fromwrite p s src dst g_uhb;
    (GraphTreeLeaf _ (ExecutionEdgeLabel "rf" l) l)].

(** Given a source and destination event for an architectural RF edge, create
  the corresponding uhb edge(s) *)
Definition ExecutionOrderEdges_RFandFR_fromwrite
  (p : Pipeline)
  (s : Scenario)
  (g_uhb : GraphTree GlobalEvent)
  (src dst : PathOption)
  : GraphTree GlobalEvent :=
  let rf_possibilities := map
    (ExecutionOrderEdges_RFandFR_fromwrite' p s g_uhb
      (eiid (evt src)) (eiid (evt dst)))
    (RFPerformPairs src dst) in
  let rf_possibilities := DebugPrintfHook rf_possibilities 3
    (fold_left append ["Source path "; optionName src;
      ", Dest path "; optionName dst; newline] "") in
  let rf_possibilities := DebugPrintfHook rf_possibilities 2 (fold_left append [
    "Architectural RF edge: "; stringOfNat (List.length rf_possibilities);
    " uhb candidates"; newline] "") in
  let result := GraphTreeOr _ rf_possibilities in
  result.

Definition ScenarioExecutionEdges_RF_fromwrite
  (p : Pipeline)
  (s : Scenario)
  (g_uhb : GraphTree GlobalEvent)
  (rf : Eiid * Eiid)
  : GraphTree GlobalEvent :=
  let (w, r) := rf in
  match (pathOfEvent s w, pathOfEvent s r) with
  | (Some pw, Some pr) => (* Found PathOptions for each event *)
    ExecutionOrderEdges_RFandFR_fromwrite p s g_uhb pw pr
  | _ => PanicHook
    "ScenarioExecutionEdges_RF_fromwrite: event not in scenario"
    g_uhb
  end.

(** [ReadsFromInitial]

Given: events: the list of all events in the scenario
Given: rf_fromwrite: the list of all rf edges which have a non-initial write as
  their source
Return: the list of all events which are reads from the initial state (i.e.,
  those reads which are not in rf_fromwrite)
*)
Fixpoint ReadsFromInitial
  (events : list Event)
  (rf_fromwrite : list (Eiid * Eiid))
  : list Eiid :=
  let edgeDests := map (snd (A:=_) (B:=_)) rf_fromwrite in
  match events with
  | h::t =>
    match (Inb_nat (eiid h) edgeDests, dirn h) with
    | (false, R) => (eiid h)::ReadsFromInitial t rf_fromwrite
    | _  => ReadsFromInitial t rf_fromwrite
    end
  | [] => []
  end.

Fixpoint ScenarioExecutionEdges_RF
  (p : Pipeline)
  (g_uhb : GraphTree GlobalEvent)
  (s : Scenario)
  (rf_fromwrite : list (Eiid * Eiid))
  : GraphTree GlobalEvent :=
  let rf_initial_reads := ReadsFromInitial (map evt s) rf_fromwrite in
  let g_after_rf :=
    fold_left (ScenarioExecutionEdges_RF_fromwrite p s) rf_fromwrite g_uhb in
  fold_left (ScenarioExecutionEdges_FR_initial p s) rf_initial_reads g_after_rf.

Module ScenarioExecutionEdgesExample.

Import EdgesExample.
Import EdgesExample3.

Example e1:
  TreeOfDNF (DNFOfTree (
    ScenarioExecutionEdges_RF my_pipeline my_global_edges my_scenario [(0, 1)]))
  = GraphTreeLeaf _ "my_sample (0-rf->1) (2-fr->0) (2-fr->3) " [
   (** the old edges *)
   ((0, 0), (0, 1), "IntraLocation"); ((0, 0), (0, 2), "IntraLocation");
   ((0, 0), (0, 3), "IntraLocation"); ((0, 1), (0, 2), "IntraLocation");
   ((0, 1), (0, 3), "IntraLocation"); ((0, 2), (0, 3), "IntraLocation");
   ((1, 1), (1, 2), "IntraLocation");
   ((2, 0), (2, 3), "IntraLocation");
   ((3, 1), (3, 2), "IntraLocation");
   ((4, 0), (4, 3), "IntraLocation");
   ((5, 1), (5, 2), "IntraLocation");
   ((6, 0), (6, 3), "IntraLocation");
   ((7, 1), (7, 2), "IntraLocation"); ((7, 0), (7, 3), "IntraLocation");
   ((0, 0), (2, 0), "IntraEvent"); ((2, 0), (4, 0), "IntraEvent");
   ((4, 0), (6, 0), "IntraEvent"); ((6, 0), (7, 0), "IntraEvent");
   ((0, 1), (1, 1), "IntraEvent"); ((1, 1), (3, 1), "IntraEvent");
   ((3, 1), (5, 1), "IntraEvent"); ((5, 1), (7, 1), "IntraEvent");
   ((0, 2), (1, 2), "IntraEvent"); ((1, 2), (3, 2), "IntraEvent");
   ((3, 2), (5, 2), "IntraEvent"); ((5, 2), (7, 2), "IntraEvent");
   ((0, 3), (2, 3), "IntraEvent"); ((2, 3), (4, 3), "IntraEvent");
   ((4, 3), (6, 3), "IntraEvent"); ((6, 3), (7, 3), "IntraEvent");
   (** RF and FR - the new edges *)
   ((3, 1), (4, 3), "FRfw"); ((4, 0), (3, 1), "RF");
   ((3, 2), (4, 0), "FRi"); ((3, 2), (4, 3), "FRi")].
Proof.
cbv.  auto.
Qed.

End ScenarioExecutionEdgesExample.

(** * ScenarioExecutionEdges_WS

To calculate all of the WS edges, we do the following:

1) Sort the events in the scenario by location
2) Sort each per-location list of events by issuing core, so that we have a list
   of lists of events in per-location, per-core program order
3) Calculate the set of all interleavings of stores to each location among the
   different cores
4) Generate the list of WS edges for each interleaving
5) Combine the results for each individual location into a GraphTree
*)

Fixpoint ScenarioExecutionEdges_WS_SortByCore
  (s : Scenario)
  : list (list GlobalEvent) :=
  match s with
  | h::t =>
    match last_error (performStages h) with
    | Some (mkPerformStages l _ _ _ _) =>
      AppendToNth
        (ScenarioExecutionEdges_WS_SortByCore t)
        (proc (iiid (evt h)))
        (l, eiid (evt h))
    | None => ScenarioExecutionEdges_WS_SortByCore t
    end
  | [] => []
  end.

Fixpoint ScenarioExecutionEdges_WS_SortByLoc
  (s : Scenario)
  : list (list PathOption) :=
  match s with
  | h::t =>
    match (dirn (evt h), loc (evt h)) with
    | (W, l) =>
      AppendToNth
        (ScenarioExecutionEdges_WS_SortByLoc t)
        l
        h
    | _ => ScenarioExecutionEdges_WS_SortByLoc t
    end
  | [] => []
  end.

Definition ScenarioExecutionEdges_WS_SortByLocThenCore
  (s : Scenario)
  : list (list (list GlobalEvent)) :=
  let l := ScenarioExecutionEdges_WS_SortByLoc s in
  map ScenarioExecutionEdges_WS_SortByCore l.

Definition ScenarioExecutionEdges_WS_Interleavings
  (s : Scenario)
  : list (list (list GlobalEvent)) :=
  map Interleavings (ScenarioExecutionEdges_WS_SortByLocThenCore s).

Definition ScenarioExecutionEdges_WS_EdgesPerInterleaving
  (s : Scenario)
  : list (list (list (GlobalEvent * GlobalEvent * string))) :=
  let i := ScenarioExecutionEdges_WS_Interleavings s in
  let AddLabel x := map (PairConsecutiveWithLabel (A:=GlobalEvent) "WS") x in
  map AddLabel i.

Definition ScenarioExecutionEdges_WS_EdgesPerLocation
  (l : list (list (GlobalEvent * GlobalEvent * string)))
  : GraphTree GlobalEvent :=
  let MakeLeaf l := GraphTreeLeaf _ (ExecutionEdgeLabel "ws" l) l in
  let l' := map MakeLeaf l in
  let l' := DebugPrintfHook l' 2 (fold_left append [
    "WS @ location: "; stringOfNat (List.length l'); " candidates"; newline]
    "") in
  GraphTreeOr _ l'.

Definition ScenarioExecutionEdges_WS
  (s : Scenario)
  : GraphTree GlobalEvent :=
  let l := ScenarioExecutionEdges_WS_EdgesPerInterleaving s in
  GraphTreeAnd _ (map ScenarioExecutionEdges_WS_EdgesPerLocation l).

Module WSExample.

Import EdgesExample3.

Example e1: ScenarioExecutionEdges_WS_SortByLocThenCore my_scenario
  = [[[(4, 0); (4, 3)]]].
Proof.  auto.  Qed.

Example e2: GraphTreeSimplify (ScenarioExecutionEdges_WS my_scenario)
  = GraphTreeLeaf (nat * nat) "(0-ws->3) " [(4, 0, (4, 3), "WS")].
Proof.  cbv.  auto.  Qed.

End WSExample.

Definition ScenarioExecutionEdges
  (p : Pipeline)
  (s : Scenario)
  (rf : list (Eiid * Eiid))
  (g_uhb : GraphTree GlobalEvent)
  : GraphTree GlobalEvent :=
  let (t_start, rf) := TimerStartHook rf in
  let g' := GraphTreeAnd _ [g_uhb; ScenarioExecutionEdges_WS s] in
  let result := ScenarioExecutionEdges_RF p g' s rf in
  TimerStopHook "ScenarioExecutionEdges" t_start result.

(** * Verification *)

Definition GraphForScenarioAcyclic
  (t : string)
  (s : Scenario)
  (pipeline : Pipeline)
  (rf : list (Eiid * Eiid))
  : GraphTree GlobalEvent :=
  let e := ScenarioEdges t pipeline s in
  ScenarioExecutionEdges pipeline s rf e.

Definition GraphCheckIfAcyclic
  (p : Pipeline)
  (g : GraphTree GlobalEvent)
  : list (string * MHBResult) * bool * nat :=
  TreeAcyclicInSomeGraph (getid p g).

Definition ScenarioCheckAcyclic
  (t : string)
  (s : Scenario)
  (pipeline : Pipeline)
  (rf : list (Eiid * Eiid))
  : list (string * MHBResult) * bool * nat :=
  let scenario_graph :=
    GraphForScenarioAcyclic t s pipeline rf in
  GraphCheckIfAcyclic pipeline scenario_graph.

Definition VerifyExecutionScenario
  (pipeline : Pipeline)
  (s : string * Scenario)
  (rf : list (Eiid * Eiid))
  : list (string * MHBResult) * bool * nat :=
  ScenarioCheckAcyclic (fst s) (snd s) pipeline rf.

Fixpoint ScenarioTitle
  (l : list PathOption)
  : string :=
  match l with
  | h::t =>
    let h_name := optionName h in
    match t with
    | _::_ =>
      append h_name (append " -> " (ScenarioTitle t))
    | [] => h_name
    end
  | [] => ""
  end.

Definition ScenariosForEvents
  (pipeline : Pipeline)
  (events : list Event)
  : list (string * Scenario) :=
  let pathsForEvent e := pathsFor pipeline e in
  let all_paths := map pathsForEvent events in
  let f s := (ScenarioTitle s, s) in
  map f (CartesianProduct all_paths).

Fixpoint VerifyExecution'
  (pipeline : Pipeline)
  (events : list Event)
  (rf : list (Eiid * Eiid))
  (ls : list (string * Scenario))
  (lr : list (string * MHBResult))
  (n : nat)
  : bool * nat * list (string * MHBResult) :=
  match ls with
  | h::t =>
    let (rb, n') := VerifyExecutionScenario pipeline h rf in
    let (r, b) := rb in
    match b with
    | true => (true, n + n', r)
    | false => VerifyExecution' pipeline events rf t (lr ++ r) (n + n')
    end
  | [] => (false, n, lr)
  end.

Definition VerifyExecution
  (pipeline : Pipeline)
  (events : list Event)
  (rf : list (Eiid * Eiid))
  : bool * nat * list (string * MHBResult) :=
  let scenarios := ScenariosForEvents pipeline events in
  let scenarios := DebugPrintfHook scenarios 2 (fold_left append [
    "Found "; stringOfNat (List.length scenarios); " scenarios"; newline] "") in
  VerifyExecution' pipeline events rf scenarios [] 0.

Definition GraphOfExecutionVerificationResult
  (title : string)
  (pipeline : Pipeline)
  (nr : string * MHBResult)
  : string * string :=
  let (n, r) := nr in
  let f x := GlobalEventString pipeline (ungeid pipeline x) in
  let n' := fold_left append [pipename pipeline; ": "; title; ": "; n] "" in
  (n',
    match r with
    | Unverified g _ _ =>
      dot_graph (append "Permitted: " n') g (ungeid pipeline) f [] []
      (List.length (stages pipeline))
    | MustHappenBefore g _ =>
      dot_graph (append "Permitted: " n') g (ungeid pipeline) f [] []
      (List.length (stages pipeline))
    | Cyclic g p =>
      dot_graph (append "Forbidden: " n') g (ungeid pipeline) f p
        (PairConsecutive p) (List.length (stages pipeline))
    end).

Definition GraphsToVerifyExecution
  (title : string)
  (pipeline : Pipeline)
  (events : list Event)
  (rf : list (Eiid * Eiid))
  : bool * nat * list (string * string) :=
  let rf := DebugPrintfHook rf 2 (PrintRFList rf) in
  let (b, lv) := VerifyExecution pipeline events rf in
  (b, map (GraphOfExecutionVerificationResult title pipeline) lv).

Module EdgesExample5.

Import EdgesExample.
Import EdgesExample2.
Import EdgesExample3.

Definition evt00 := mkev 0 (mkiiid 0 0) (Access W 0 1).
Definition evt10 := mkev 1 (mkiiid 1 0) (Access R 0 1).

Definition SampleValidation :=
  GraphsToVerifyExecution "Sample" my_pipeline [evt00; evt10] [(0, 1)].

End EdgesExample5.

