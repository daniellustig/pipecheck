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
Require Import wmm.
Require Import util2.
Require Import stages.
Require Import execution.
Require Import String.

Fixpoint Permutations' {A : Type}
  (a : A)
  (l1 l2 : list A)
  : list (list A) :=
  match l2 with
  | h::t =>
    (l1 ++ a::l2) :: Permutations' a (l1 ++ [h]) t
  | [] => [l1 ++ [a]]
  end.

Fixpoint Permutations {A : Type}
  (l : list A)
  : list (list A) :=
  match l with
  | [] => []
  | [h] => [[h]]
  | h::t =>
    fold_left (app (A:=_)) (map (Permutations' h []) (Permutations t)) []
  end.

Module PermutationsExample.

Example e1 : Permutations [1; 2; 3] =
  [[1; 2; 3]; [2; 1; 3]; [2; 3; 1]; [1; 3; 2]; [3; 1; 2]; [3; 2; 1]].
Proof.
cbv.  auto.
Qed.

Example e2 : List.length (Permutations [1; 2; 3; 4; 5]) = 120.
Proof.
cbv.  auto.
Qed.

End PermutationsExample.

Definition IsWrite
  (e : Event)
  : bool :=
  match dirn e with
  | R => false
  | W => true
  end.

Fixpoint MatchingWrites
  (r : Event)
  (l : list Event)
  : list (option Event * Event) :=
  match l with
  | w::t =>
    match (action r, action w) with
    | (Access dr lr vr, Access dw lw vw) =>
      match (dr, dw, nat_compare lr lw, nat_compare vr vw) with
      | (R, W, Eq, Eq) => (Some w, r) :: MatchingWrites r t
      | _ => MatchingWrites r t
      end
    end
  | [] =>
    match (action r) with
    | (Access R _ 0) => [(None, r)]
    | _ => []
    end
  end.

Module MatchingWritesExamples.

Example e1 : MatchingWrites (mkev 0 (mkiiid 0 0) (Access R 0 0))
    [mkev 1 (mkiiid 1 0) (Access W 0 0);
     mkev 2 (mkiiid 1 1) (Access W 0 1)]
 = [(Some (mkev 1 (mkiiid 1 0) (Access W 0 0)),
     mkev 0 (mkiiid 0 0) (Access R 0 0));
    (None, mkev 0 (mkiiid 0 0) (Access R 0 0))].
Proof.
cbv.  auto.
Qed.

End MatchingWritesExamples.

Inductive LitmusTestResult : Type := Forbidden | Permitted.

Definition LitmusTestResultString
  (r : LitmusTestResult)
  : string :=
  match r with
  | Forbidden => "(exp: Forbidden)"
  | Permitted => "(exp: Permitted)"
  end.

Fixpoint LitmusTestCandidateRF
  (rf : Eiid * Eiid)
  : string :=
  let (w, r) := rf in
  fold_left append ["("; stringOfNat w; "-rf->"; stringOfNat r; ")"] "".

Fixpoint LitmusTestCandidateWS
  (w : Eiid)
  : string :=
  append " " (stringOfNat w).

Fixpoint LitmusTestCandidateName
  (r : LitmusTestResult)
  (rf : list (Eiid * Eiid))
  : string :=
  fold_left append
    [LitmusTestResultString r;
     fold_left append (map LitmusTestCandidateRF rf) " RF: "]
    "".

Fixpoint LitmusTest'''
  (l : list (option Event * Event))
  : list (Eiid * Eiid) :=
  match l with
  | h::t =>
    match h with
    | (Some w, r) => (eiid w, eiid r) :: LitmusTest''' t
    | _ => LitmusTest''' t
    end
  | [] => []
  end.

(** Given a litmus test and a particular RF candidate, generate the result
  for that litmus test. *)
Definition LitmusTest''
  (name : string)
  (expected : LitmusTestResult)
  (pipeline : Pipeline)
  (events : list Event)
  (rf : list (option Event * Event))
  : bool * nat * list (string * string) :=
  let rf' := LitmusTest''' rf in
  let name' := append name (LitmusTestCandidateName expected rf') in
  GraphsToVerifyExecution name' pipeline events rf'.

(** Given a litmus test and a list of RF edge candidates, either find a
  legal execution, or return the list of all forbidden cases. *)
Fixpoint LitmusTest'
  (name : string)
  (expected : LitmusTestResult)
  (pipeline : Pipeline)
  (events : list Event)
  (l_rf : list (list (option Event * Event)))
  (lr : list (string * string))
  (n : nat)
  : bool * nat * list (string * string) :=
  match l_rf with
  | h::t =>
    match LitmusTest'' name expected pipeline events h with
    | (true, n', r) => (true, n + n', r)
    | (false, n', r) =>
      LitmusTest' name expected pipeline events t (lr ++ r) (n + n')
    end
  | [] => (false, n, lr)
  end.

Fixpoint StringOfRFCandidates'
  (l_rf : list (option Event * Event))
  : string :=
  match l_rf with
  | h::t =>
    append (
      match h with
      | (Some e1, e2) =>
        fold_left append [
          stringOfNat (eiid e1); "-rf->"; stringOfNat (eiid e2)] " "
      | (None, e2) =>
        fold_left append ["i-rf->"; stringOfNat (eiid e2)] " "
      end
    ) (StringOfRFCandidates' t)
  | [] => ""
  end.

Fixpoint StringOfRFCandidates
  (l_rf : list (list (option Event * Event)))
  : string :=
  match l_rf with
  | h::t =>
    fold_left append ["("; StringOfRFCandidates' h; " ) ";
      StringOfRFCandidates t] "RF Candidates: "
  | [] => newline
  end.

Definition LitmusTest2
  (name : string)
  (expected : LitmusTestResult)
  (pipeline : Pipeline)
  (events : list Event)
  : bool * nat * list (string * string) :=
  let (writes, reads) := partition IsWrite events in
  let l_rf_candidates := map (fun f => f writes) (map MatchingWrites reads) in
  let l_rf_candidates := DebugPrintfHook l_rf_candidates 2
    (StringOfRFCandidates l_rf_candidates) in
  let l_rf := CartesianProduct l_rf_candidates in
  let l_rf := DebugPrintfHook l_rf 2 (StringOfRFCandidates l_rf) in
  LitmusTest' name expected pipeline events l_rf [] 0.

Definition LitmusTest
  (name : string)
  (expected : LitmusTestResult)
  (pipeline : Pipeline)
  (events : list Event)
  : list (string * string) :=
  let events := PrintfHook events (fold_left append [
    "Litmus Test,"; pipename pipeline; ","; name; newline] newline) in
  let (t_start, events) := TimerStartHook events in
  let (bn, r) := LitmusTest2 name expected pipeline events in
  let (b, n) := TimerStopHook "LitmusTest" t_start bn in
  let r := PrintfHook r (fold_left append [
    "Litmus Test Result,"; stringOfNat n; ","; stringOfBool b; newline; newline]
    "") in
  r.

Open Scope string_scope.

Definition amd1
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "iwp2.1/amd1" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access W 1 1);
    mkev 2 (mkiiid 1 0) (Access R 1 1);
    mkev 3 (mkiiid 1 1) (Access R 0 0)
  ].

Definition amd2
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "iwp2.2/amd2" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access R 0 1);
    mkev 1 (mkiiid 0 1) (Access W 1 1);
    mkev 2 (mkiiid 1 0) (Access R 1 1);
    mkev 3 (mkiiid 1 1) (Access W 0 1)
  ].

Definition amd3
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "amd3" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access W 0 2);
    mkev 2 (mkiiid 0 2) (Access R 1 1);
    mkev 3 (mkiiid 1 0) (Access W 1 1);
    mkev 4 (mkiiid 1 1) (Access W 1 2);
    mkev 5 (mkiiid 1 2) (Access R 0 1)
  ].

Definition amd4
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "iwp2.3a/amd4" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access R 1 0);
    mkev 2 (mkiiid 1 0) (Access W 1 1);
    mkev 3 (mkiiid 1 1) (Access R 0 0)
  ].

(*
Definition amd5
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "amd5" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access F 0 0);
    mkev 2 (mkiiid 0 2) (Access R 0 ?);
    mkev 3 (mkiiid 0 3) (Access R 0 0);
    mkev 4 (mkiiid 1 0) (Access W 1 1);
    mkev 5 (mkiiid 1 1) (Access F 0 0);
    mkev 6 (mkiiid 1 2) (Access R 1 ?);
    mkev 7 (mkiiid 1 2) (Access R 0 0)
  ].
*)

Definition amd8
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "iwp2.5/amd8" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 1 0) (Access R 0 1);
    mkev 2 (mkiiid 1 1) (Access W 1 1);
    mkev 3 (mkiiid 2 0) (Access R 1 1);
    mkev 4 (mkiiid 2 1) (Access R 0 0)
  ].

Definition amd9
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "iwp2.4/amd9" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 0) (Access R 0 1);
    mkev 2 (mkiiid 0 1) (Access R 1 0);
    mkev 3 (mkiiid 1 0) (Access W 1 1);
    mkev 4 (mkiiid 1 1) (Access R 1 1);
    mkev 5 (mkiiid 1 2) (Access R 0 0)
  ].

Definition iwp23b1 (* REQUIRE *)
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "iwp2.3b1" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access R 0 1);
    mkev 2 (mkiiid 1 0) (Access W 1 1);
    mkev 3 (mkiiid 1 1) (Access R 1 1)
  ].

Definition iwp26
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "iwp2.6" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 1 0) (Access W 0 2);
    mkev 2 (mkiiid 2 0) (Access R 0 1);
    mkev 3 (mkiiid 2 0) (Access R 0 2);
    mkev 4 (mkiiid 3 0) (Access R 0 2);
    mkev 5 (mkiiid 3 0) (Access R 0 1)
  ].

Definition amd6
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "amd6/IRIW" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 1 0) (Access W 1 1);
    mkev 2 (mkiiid 2 0) (Access R 0 1);
    mkev 3 (mkiiid 2 1) (Access R 1 0);
    mkev 4 (mkiiid 3 0) (Access R 1 1);
    mkev 5 (mkiiid 3 1) (Access R 0 0)
  ].

Definition n1
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "n1" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 2);
    mkev 1 (mkiiid 0 1) (Access R 1 0);
    mkev 2 (mkiiid 1 0) (Access W 1 1);
    mkev 3 (mkiiid 1 1) (Access W 0 1);
    mkev 4 (mkiiid 2 0) (Access R 0 1);
    mkev 5 (mkiiid 2 1) (Access R 0 2)
  ].

Definition n2
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "n2" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 1 1);
    mkev 1 (mkiiid 0 1) (Access W 0 1);
    mkev 2 (mkiiid 1 0) (Access W 0 2);
    mkev 3 (mkiiid 1 1) (Access W 2 1);
    mkev 4 (mkiiid 2 0) (Access R 0 1);
    mkev 5 (mkiiid 2 1) (Access R 0 2);
    mkev 6 (mkiiid 3 0) (Access R 2 1);
    mkev 7 (mkiiid 3 1) (Access R 1 0)
  ].

Definition n4
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "n4" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access R 0 2);
    mkev 1 (mkiiid 0 1) (Access W 0 1);
    mkev 2 (mkiiid 0 2) (Access R 0 1);
    mkev 3 (mkiiid 1 0) (Access R 0 1);
    mkev 4 (mkiiid 1 1) (Access W 0 2);
    mkev 5 (mkiiid 1 2) (Access R 0 2)
  ].

Definition n5
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "n5" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access R 0 2);
    mkev 2 (mkiiid 1 0) (Access W 0 2);
    mkev 3 (mkiiid 1 1) (Access R 0 1)
  ].

Definition n6
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "n6" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access R 0 1);
    mkev 2 (mkiiid 0 2) (Access R 1 0);
    mkev 3 (mkiiid 1 0) (Access W 1 2);
    mkev 4 (mkiiid 1 1) (Access W 0 2)
  ].

Definition n7 (* ALLOW *)
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "n7" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access R 0 1);
    mkev 2 (mkiiid 0 2) (Access R 1 0);
    mkev 3 (mkiiid 1 0) (Access W 1 1);
    mkev 4 (mkiiid 2 0) (Access R 1 1);
    mkev 5 (mkiiid 2 1) (Access R 0 0)
  ].

(*
Definition n8
  (pipeline : Pipeline)
  : list (string * string) :=
  (* initial state: [1] = 1 *)
  LitmusTest "n8" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access X 0 1);
    mkev 1 (mkiiid 0 1) (Access R 1 0);
    mkev 2 (mkiiid 1 0) (Access W 1 1);
    mkev 3 (mkiiid 0 1) (Access R 0 0)
  ].
*)

Definition rwcunfenced
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "rwc-unfenced" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 1 0) (Access R 0 1);
    mkev 2 (mkiiid 1 1) (Access R 1 0);
    mkev 3 (mkiiid 2 0) (Access W 1 1);
    mkev 4 (mkiiid 2 1) (Access R 0 0)
  ].

(** Ensure that po-loc is respected *)
Definition d1
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "d1" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access W 0 2);
    mkev 2 (mkiiid 0 2) (Access R 0 1)
  ].

(** Make sure that reading from the initial state is permitted. *)
Definition d2
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "d2" Permitted pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access W 0 0);
    mkev 2 (mkiiid 1 0) (Access R 0 0);
    mkev 3 (mkiiid 1 1) (Access R 0 1)
  ].

(** Same-address version of amd1/iwp2.1 *)
Definition d3
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "d3" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access W 0 2);
    mkev 2 (mkiiid 1 0) (Access R 0 2);
    mkev 3 (mkiiid 1 1) (Access R 0 1)
  ].

(** Ensure that po-loc is respected *)
Definition d4
  (pipeline : Pipeline)
  : list (string * string) :=
  LitmusTest "d4" Forbidden pipeline [
    mkev 0 (mkiiid 0 0) (Access W 0 1);
    mkev 1 (mkiiid 0 1) (Access R 0 1);
    mkev 2 (mkiiid 0 2) (Access R 0 0)
  ].

Definition AllLitmusTests :=
  [amd1; amd2; amd3; amd4; (*amd5;*) amd6; (*amd7;*) amd8; amd9; (*amd10;*)
   iwp23b1; iwp26; (*iwp28a; iwp28b; *)
   n1; n2; (*n3;*) n4; n5; n6; n7; (*n8;*)
   rwcunfenced; (*rwcfenced;*)
   d1; d2; d3; d4].

Close Scope string_scope.

