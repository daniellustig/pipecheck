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
Require Import util2.
Require Import adjacency.
Require Import topsort.
Require Import wmm.
Require Import bell.
Require Import dot.
Require Import tree.
Require Import stages.
Require Import globalgraph.
Require Import musthappenbefore.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.

Fixpoint PerfWRTiAtStage
  (l : list PerformStages)
  (c : nat)
  : option location :=
  match l with
  | mkPerformStages stg cores vis cli imm :: t =>
    if Inb_nat c cores
      then Some stg
      else PerfWRTiAtStage t c
  | [] => None
  end.

Fixpoint PerfWRTiBeforePerfWRTj
  (po1 po2 : PathOption)
  (local_core : nat)
  (cores : list nat)
  : list (GlobalEvent * GlobalEvent * string) :=
  let ps1 := performStages po1 in
  let ps2 := performStages po2 in
  match cores with
  | h::t =>
    match (PerfWRTiAtStage ps1 h, PerfWRTiAtStage ps2 local_core) with
    | (Some l1, Some l2) =>
      ((l1, eiid (evt po1)), (l2, eiid (evt po2)), "PPO")
      :: PerfWRTiBeforePerfWRTj po1 po2 local_core t
    | _ => PerfWRTiBeforePerfWRTj po1 po2 local_core t
    end
  | [] => []
  end.

Definition PPOMustHappenBeforeGlobalEvents
  (s : Scenario)
  (e1 e2 : nat)
  : GraphTree GlobalEvent :=
  match (nth_error s e1, nth_error s e2) with
  | (Some po1, Some po2) =>
    let local_core := proc (iiid (evt po1)) in
    let ps1 := performStages po1 in
    let all_cores := match last_error ps1 with
    | Some (mkPerformStages _ cores _ _ _) => cores
    | _ => []
    end in
    let remote_cores := remove_nat local_core all_cores in
    GraphTreeLeaf _ "PPO" (PerfWRTiBeforePerfWRTj po1 po2 local_core remote_cores)
  | _ => GraphTreeEmptyLeaf
  end.

Definition PPOMustHappenBeforeLocalEvents
  (s : Scenario)
  (e1 e2 : nat)
  : GraphTree GlobalEvent :=
  match (nth_error s e1, nth_error s e2) with
  | (Some po1, Some po2) =>
    let local_core := proc (iiid (evt po1)) in
    let ps1 := performStages po1 in
    GraphTreeLeaf _ "PPO" (PerfWRTiBeforePerfWRTj po1 po2 local_core [local_core])
  | _ => GraphTreeEmptyLeaf
  end.

Definition PPOGlobalEvents
  (s : Scenario)
  (p : Pipeline)
  (e1 e2 : nat)
  : GraphTree GlobalEvent :=
  let dirs := map dirn (map evt s) in
  match (nth e1 dirs W, nth e2 dirs W) with
  | (R, R) =>
    GraphTreeOr _
      [PPOMustHappenBeforeGlobalEvents s e1 e2  (*;
       PPOSpeculativeLoadReorderEvents s p e1 e2 *)]
  | _ => PPOMustHappenBeforeGlobalEvents s e1 e2
  end.

Definition PPOLocalEvents
  (s : Scenario)
  (p : Pipeline)
  (e1 e2 : nat)
  : GraphTree GlobalEvent :=
  let dirs := map dirn (map evt s) in
  match (nth e1 dirs W, nth e2 dirs W) with
  | (R, R) =>
    GraphTreeOr _
      [PPOMustHappenBeforeLocalEvents s e1 e2 (*;
       PPOSpeculativeLoadReorderEvents s p e1 e2 *)]
  | _ => PPOMustHappenBeforeLocalEvents s e1 e2
  end.

(** * Verification Scenarios *)

Definition GraphToVerifyPPOGlobalScenario
  (p : Pipeline)
  (s : Scenario)
  (e1 e2 : nat)
  : GraphTree GlobalEvent * GraphTree GlobalEvent :=
  let g := ScenarioEdges "PPO " p s in
  let v := PPOGlobalEvents s p e1 e2 in
  (g, v).

Definition GraphToVerifyPPOLocalScenario
  (p : Pipeline)
  (s : Scenario)
  (e1 e2 : nat)
  : GraphTree GlobalEvent * GraphTree GlobalEvent :=
  let g := ScenarioEdges "PPOLocal " p s in
  let v := PPOLocalEvents s p e1 e2 in
  (g, v).

Definition VerifyPPOScenario
  (g v : GraphTree GlobalEvent)
  (p : Pipeline)
  : list (string * MHBResult) :=
  TreeMustHappenBeforeInAllGraphs (getid p g) (getid p v).

Definition AddTitle
  (t : string)
  (r : string * MHBResult)
  : string * MHBResult :=
  let (rn, rr) := r in
  (* (append t (append ":" rn), rr) *)
  (t, rr).

Fixpoint VerifyPPOGlobalScenarios
  (l : list (string * Scenario))
  (p : Pipeline)
  (e1 e2 : nat)
  : list (string * MHBResult) :=
  match l with
  | (title, h)::t =>
    let (g, v) := GraphToVerifyPPOGlobalScenario p h e1 e2 in
    let g' := g (* AddCacheEdgesToGraphTree p g e1 e2 *) in
    map (AddTitle title) (VerifyPPOScenario g v p)
    ++ VerifyPPOGlobalScenarios t p e1 e2
  | [] => []
  end.

Fixpoint VerifyPPOLocalScenarios
  (l : list (string * Scenario))
  (p : Pipeline)
  (e1 e2 : nat)
  : list (string * MHBResult) :=
  match l with
  | (title, h)::t =>
    let (g, v) := GraphToVerifyPPOLocalScenario p h e1 e2 in
    let g' := g (* AddCacheEdgesToGraphTree p g e1 e2 *) in
    map (AddTitle title) (VerifyPPOScenario g v p)
    ++ VerifyPPOLocalScenarios t p e1 e2
  | [] => []
  end.

(** * Verification Scenarios *)

Fixpoint GenerateEventsFromDirns'
  (l : list Dirn)
  (n : nat)
  : list Event :=
  match l with
  | h::t =>
    (** Address will be adjusted by [ReplaceLocs] later *)
    (** Value will be ignored *)
    mkev n (mkiiid 0 n) (Access h 0 0)
    :: GenerateEventsFromDirns' t (S n)
  | [] => []
  end.

Fixpoint GenerateEventsFromDirns
  (l : list Dirn)
  : list Event :=
  GenerateEventsFromDirns' l 0.

(** Replace the [Location] accessed by each [Event] in [le] with the [Location]
  in the corresponding position in [ll]. *)
Fixpoint ReplaceLocs
  (le : list Event)
  (ll : list Location)
  : list Event :=
  match (le, ll) with
  | (mkev eeiid eiiid (Access d _  v) :: et, lh::lt) =>
     mkev eeiid eiiid (Access d lh v) :: ReplaceLocs et lt
  | _ => []
  end.

(** Given a list of [Event]s, return a list of lists of [Event]s in which
  the [Location]s accessed by the [Event]s are replaced by each possible
  assignment of overlapping vs. non-overlapping [Location]s.

  For example, given a list of two [Event]s of directions [R] and [R], return
  the the pair of lists (R 0, R 0) and (R 0, R 1), i.e., the overlapping case
  and the non-overlapping case.  Scenarios with more than two events will have
  more than two possibilities. *)
Definition AllLocationCombos
  (l : list Event)
  : list (list Event) :=
  let b := Bell (List.length l) in
  map (ReplaceLocs l) b.

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

(** [AllScenariosForPO'] calculates the set of all possible [Scenario]s for
  a given [Pipeline] and given [dirn]s of [Event]s in program order. *)
Definition AllScenariosForPO'
  (pipeline : Pipeline)
  (events : list Event)
  : list (string * Scenario) :=
  let all_paths := map (fun e => pathsFor pipeline e) events in
  let f s := (ScenarioTitle s, s) in
  map f (CartesianProduct all_paths).

(** [AllScenariosForPOWithAnyAddress] calculates the set of all possible [Scenario]s for
  a given [Pipeline] and given [dirn]s of [Event]s in program order. *)
Definition AllScenariosForPOWithAnyAddress
  (pipeline : Pipeline)
  (program_order : list Dirn)
  : list (string * Scenario) :=
  let program_order' := GenerateEventsFromDirns program_order in
  let program_orders := AllLocationCombos program_order' in
  let f po := AllScenariosForPO' pipeline po in
  fold_left (app (A:=_)) (map f program_orders) [].

Definition AllScenariosForPOWithSameAddress
  (pipeline : Pipeline)
  (program_order : list Dirn)
  : list (string * Scenario) :=
  let program_order' := GenerateEventsFromDirns program_order in
  AllScenariosForPO' pipeline program_order'.

Definition VerifyPPOWithAnyAddresses
  (pipeline : Pipeline)
  (program_order : list Dirn)
  (e1 e2 : nat)
  : list (string * MHBResult) :=
  let scenarios := AllScenariosForPOWithAnyAddress pipeline program_order in
  VerifyPPOGlobalScenarios scenarios pipeline e1 e2.

Definition VerifyPPOWithSameAddress
  (pipeline : Pipeline)
  (program_order : list Dirn)
  (e1 e2 : nat)
  : list (string * MHBResult) :=
  let scenarios := AllScenariosForPOWithSameAddress pipeline program_order in
  VerifyPPOLocalScenarios scenarios pipeline e1 e2.

Definition GraphOfPPOVerificationResult
  (pipeline : Pipeline)
  (e1 e2 : nat)
  (tr : string * MHBResult)
  : string * string :=
  let (t, r) := tr in
  let f x := GlobalEventString pipeline (ungeid pipeline x) in
  (fold_left append [pipename pipeline; ": PPO: "; t] "",
    match r with
    | MustHappenBefore g p =>
      dot_graph
        (fold_left append ["PPO Verified: "; pipename pipeline; ": "; t] "") g
        (ungeid pipeline) f p (PairConsecutive p) (List.length (stages pipeline))
    | Unverified g s d =>
      dot_graph
        (fold_left append ["PPO Unverified! "; pipename pipeline; ": "; t] "") g
        (ungeid pipeline) f [s; d] [] (List.length (stages pipeline))
    | Cyclic g p =>
      dot_graph
        (fold_left append ["PPO Ruled out (cyclic): "; pipename pipeline; ": "; t] "") g
        (ungeid pipeline) f p (PairConsecutive p) (List.length (stages pipeline))
    end).

Definition GraphsToVerifyPPOWithAnyAddresses
  (pipeline : Pipeline)
  (program_order : list Dirn)
  (e1 e2 : nat)
  : list (string * string) :=
  let lv := VerifyPPOWithAnyAddresses pipeline program_order e1 e2 in
  map (GraphOfPPOVerificationResult pipeline e1 e2) lv.

Definition GraphsToVerifyPPOWithSameAddress
  (pipeline : Pipeline)
  (program_order : list Dirn)
  (e1 e2 : nat)
  : list (string * string) :=
  let lv := VerifyPPOWithSameAddress pipeline program_order e1 e2 in
  map (GraphOfPPOVerificationResult pipeline e1 e2) lv.

Module EdgesExample5.

Import EdgesExample.
Import EdgesExample2.
Import EdgesExample3.

Definition SampleValidation :=
  GraphsToVerifyPPOWithAnyAddresses my_pipeline [W; R; R; W] 0 3.

End EdgesExample5.

Definition GraphsToVerifyTSOPPO
  (pipeline : Pipeline)
  : list (string * string) :=
  GraphsToVerifyPPOWithAnyAddresses pipeline [R; R] 0 1 ++
  GraphsToVerifyPPOWithAnyAddresses pipeline [R; W] 0 1 ++
  GraphsToVerifyPPOWithAnyAddresses pipeline [W; W] 0 1 ++
  GraphsToVerifyPPOWithSameAddress  pipeline [R; R] 0 1 ++
  GraphsToVerifyPPOWithSameAddress  pipeline [R; W] 0 1 ++
  GraphsToVerifyPPOWithSameAddress  pipeline [W; R] 0 1 ++
  GraphsToVerifyPPOWithSameAddress  pipeline [W; W] 0 1.

