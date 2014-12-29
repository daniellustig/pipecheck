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
Require Import util2.
Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import wmm.
Require Import adjacency.
Require Import globalgraph.

Open Scope string_scope.

Definition quote := String (ascii_of_nat 34) "".

Definition startcolor := "#d6fced".
Definition middlecolor := "#8dfbe4".
Definition finishcolor := "#83e0d8".

(** Edge types:
  Program order
  Execution: RF, WS, FR
  Path
  Derived

  Program order  : Blue
  RF             : Bright red
  WS             : Med red
  FR             : Dark red
  Intra-Event    : Black
  Intra-Location : Green
  Other          : Yellow
*)

Definition EdgeColor
  (l1 e1 l2 e2 : nat)
  (edgeString : string)
  : string :=
  if andb (beq_nat 0 l1) (beq_nat 0 l2)
    then "color=" ++ quote ++ "#ff0000" ++ quote
  else if string_dec edgeString "IntraLocation"
    then "color=" ++ quote ++ "#00cc00" ++ quote
  else if string_dec edgeString "IntraEvent"
    then "color=" ++ quote ++ "#000000" ++ quote
  else if string_dec edgeString "RF"
    then "color=" ++ quote ++ "#ff0000" ++ quote
  else if string_dec edgeString "WS"
    then "color=" ++ quote ++ "#ff0000" ++ quote
  else if string_dec edgeString "FR"
    then "color=" ++ quote ++ "#ff0000" ++ quote
  else "color=" ++ quote ++ "#0000ff" ++ quote.

Definition EdgeDotted
  (n1 n2 : nat)
  (l_thick : list (nat * nat))
  : string :=
  match l_thick with
  | [] => ""
  | _ =>
    if Inb_nat_nat (n1, n2) l_thick
      then ""
      else "style=dashed"
  end.

(* the extra leading semicolon is removed by [FormatString] below *)
Fixpoint FormatString'
  (l : list string)
  : string :=
  match l with
  | [] => ""
  | h::t =>
    if string_dec h ""
      then FormatString' t
      else append (append "," h) (FormatString' t)
  end.

Definition FormatString
  (l : list string)
  : string :=
  match FormatString' l with
  | EmptyString => ""
  | String _ s => "[" ++ s ++ "]"
    (* remove the extra leading semicolon from [FormatString'] above *)
  end.

Module FormatStringExample.

Example e0 : FormatString [""; ""] = "".
Proof.  auto.  Qed.

Example e1 : FormatString ["a"] = "[a]".
Proof.  auto.  Qed.

Example e2 : FormatString ["a"; ""] = "[a]".
Proof.  cbv.  auto.  Qed.

Example e3 : FormatString ["a"; "b"] = "[a,b]".
Proof.  cbv.  auto.  Qed.

End FormatStringExample.

Definition natPairToString
  (f_string : nat -> string)
  (f_stage_event : nat -> (nat * nat))
  (l_thick : list (nat * nat))
  (np : nat * nat * string)
  : string :=
  let (n1, n2) := fst np in
  let (l1, e1) := f_stage_event n1 in
  let (l2, e2) := f_stage_event n2 in
  let format_string := FormatString (
    [EdgeDotted n1 n2 l_thick] ++
    [EdgeColor l1 e1 l2 e2 (snd np)] ++
    (if Inb_nat_nat (fst np) l_thick then ["penwidth=5"] else []) ++
    (if beq_nat e1 e2 then [] else ["constraint=false"])) in
  "  " ++ f_string n1 ++ " -> " ++ f_string n2 ++ format_string ++ ";"
  ++ " // (" ++ stringOfNat n1 ++ ", " ++ stringOfNat n2 ++ ") " ++ snd np
  ++ newline.

Fixpoint GroupNodesByEvent
  (f : nat -> nat * nat)
  (l : list nat)
  : list (list nat) :=
  match l with
  | h::t =>
    let (n, e) := f h in
    AppendUniqueToNth (GroupNodesByEvent f t) e h
  | [] => []
  end.

Fixpoint EdgeListToNodeList
  (l : list (nat * nat * string))
  (f : nat -> nat * nat)
  (r_nodes : list nat)
  : list nat :=
  match l with
  | h::t =>
    let (h1, h2) := fst h in
    let r_nodes' := AddUnique (AddUnique r_nodes h1) h2 in
    EdgeListToNodeList t f r_nodes'
  | [] => r_nodes
  end.

Definition SubgraphClusterEntry
  (nodeToString : nat -> string)
  (l_bold : list nat)
  (nodeNumber : nat)
  : string :=
  let format :=
    if IsEmptyList l_bold
      then ""
    else if beq_nat nodeNumber (hd 0 l_bold)
      then " [style=filled,color=" ++ quote ++ startcolor ++ quote ++ "]"
    else if beq_nat nodeNumber (last l_bold 0)
      then " [style=filled,color=" ++ quote ++ finishcolor ++ quote ++ "]"
    else if Inb_nat nodeNumber l_bold
      then " [style=filled,color=" ++ quote ++ middlecolor ++ quote ++ "]"
    else "" in
  "    " ++ nodeToString nodeNumber ++ format ++ "; // " ++
    stringOfNat nodeNumber ++ newline.

Definition SubgraphCluster
  (eventNumber : nat)
  (nodeToString : nat -> string)
  (l_bold : list nat)
  (listOfNodesForEvent : list nat)
  : string :=
  "  subgraph cluster_" ++ stringOfNat eventNumber
  ++ "  {" ++ newline
  ++ "    style=filled;" ++ newline
  ++ "    color=white;" ++ newline
  ++ "    label=" ++ quote ++ "Event" ++
    stringOfNat eventNumber ++ quote ++ newline
  ++ fold_left append
    (map (SubgraphClusterEntry nodeToString l_bold) listOfNodesForEvent) ""
  ++ "  }" ++ newline.

Fixpoint SubgraphClusters'
  (eventNumber : nat)
  (nodeToString : nat -> string)
  (l_bold : list nat)
  (listOfNodesForEachEvent : list (list nat))
  : string :=
  match listOfNodesForEachEvent with
  | h::t =>
    SubgraphCluster eventNumber nodeToString l_bold h ++
    SubgraphClusters' (S eventNumber) nodeToString l_bold t
  | [] => ""
  end.

Definition SubgraphClusters
  (nodeToString : nat -> string)
  (l_bold : list nat)
  (listOfNodesForEachEvent : list (list nat))
  : string :=
  SubgraphClusters' 0 nodeToString l_bold listOfNodesForEachEvent.

Fixpoint rank_nodes'
  (f : nat -> nat)
  (p_max : nat)
  (l : list nat)
  (r1 : list (list nat))
  (r2 : list nat)
  : list (list nat) * list nat :=
  match l with
  | h::t =>
    if leb p_max (f h)
      then rank_nodes' f p_max t r1 (AddUnique r2 h)
      else rank_nodes' f p_max t (AppendToNth r1 (f h) h) r2
  | [] => (r1, r2)
  end.

Definition rank_nodes
  (f : nat -> nat)
  (p_max : nat)
  (l : list nat)
  : list (list nat) * list nat :=
  rank_nodes' f p_max l [] [].

Definition standalone_node
  (f : nat -> string)
  (l_bold : list nat)
  (n : nat)
  : string :=
  let format :=
    if IsEmptyList l_bold
      then ""
    else if beq_nat n (hd 0 l_bold)
      then " [style=filled,color=" ++ quote ++ startcolor ++ quote ++ "]"
    else if beq_nat n (last l_bold 0)
      then " [style=filled,color=" ++ quote ++ finishcolor ++ quote ++ "]"
    else if Inb_nat n l_bold
      then " [style=filled,color=" ++ quote ++ middlecolor ++ quote ++ "]"
    else "" in
  "    " ++ f n ++ format ++ "; // node "
  ++ stringOfNat n
  ++ newline.

Definition rank
  (f_string : nat -> string)
  (l_bold l : list nat)
  : string :=
  "  {rank=same;" ++ newline
  ++ fold_left append (map (standalone_node f_string l_bold) l) ""
  ++ "  }" ++ newline.

Definition ranks
  (f_string : nat -> string)
  (l_bold : list nat)
  (l : list (list nat))
  : string :=
  fold_left append (map (rank f_string l_bold) l) "".

Definition unranked
  (f_string : nat -> string)
  (l_bold l : list nat)
  : string :=
  fold_left append (map (standalone_node f_string l_bold) l) "".

Definition EdgeStrings
  (f_string : nat -> string)
  (f_stage_event : nat -> (nat * nat))
  (l : list (nat * nat * string))
  (l_thick : list (nat * nat))
  : string :=
  fold_left append (map (natPairToString f_string f_stage_event l_thick) l) "".

(** Build a dot graph from the description of the graph, plus some formatting
  options.

  name: the title of the graph

  l_normal: the set of edges in the graph

  f_stage_event: given a vertex, return the location and event the vertex
    represents

  f_string: given a vertex, return a label for the vertex

  l_bold: a list of nodes that should be bolded/filled in

  l_thick: a list of edges that should be colored and thickened

  p_max: the length of the pipeline.  Vertices with locations > p_max (i.e.,
    cache events) will not necessarily be clustered with the pipeline.
  *)
Definition dot_graph
  (name : string)
  (l_normal : list (nat * nat * string))
  (f_stage_event : nat -> (nat * nat))
  (f_string : nat -> string)
  (l_bold : list nat)
  (l_thick : list (nat * nat))
  (p_max : nat)
  : string :=
  let (t_start, f_stage_event) := TimerStartHook f_stage_event in
  let f_stage x := fst (f_stage_event x) in
  let f_event x := snd (f_stage_event x) in
  let l_nodes := EdgeListToNodeList l_normal f_stage_event [] in
  let l_same_event := GroupNodesByEvent f_stage_event l_nodes in
  let (l_ranked, l_unranked) := rank_nodes f_stage p_max l_nodes in
  let result := "// nodes per column: " ++ stringOfNat p_max ++ newline
  ++ "digraph PipeCheck {" ++ newline
  ++ "  labelloc=" ++ quote ++ "t" ++ quote ++ ";" ++ newline
  ++ "  label=" ++ quote ++ "" ++ name ++ "" ++ quote ++ ";" ++ newline
  ++ "  newrank=true;" ++ newline
  ++ SubgraphClusters f_string l_bold l_same_event
  ++ ranks f_string l_bold l_ranked
  ++ unranked f_string l_bold l_unranked
  ++ EdgeStrings f_string f_stage_event l_normal l_thick
  ++ "}" ++ newline in
  TimerStopHook "dot_graph" t_start result.

Module DotGraphExample.

Definition ev0 := mkev 0 (mkiiid 0 0) (Access R 0 0).
Definition ev1 := mkev 1 (mkiiid 0 1) (Access R 1 0).

Definition my_graph :=
  [((0, ev0), (0, ev1), "a"); ((0, ev0), (1, ev0), "b")].

Fixpoint my_n_string' (n e : nat) : string :=
  match (e, n) with
  | (S (S (S (S (S (S (S (S (S (S e'))))))))), _) =>
    "Overflow"
  | (_, S (S (S (S (S n'))))) =>
    my_n_string' n' (S e)
  | _ =>
    "Event"
    ++ stringOfNat e ++ "AtLocation" ++ stringOfNat n
  end.

Definition my_n_string (n : nat) : string :=
  my_n_string' n 0.

Definition my_geid (ne : nat * Event) : nat :=
  let (n, e) := ne in
  (eiid e) * 5 + n.

Definition my_gepid
  (nep : (nat * Event) * (nat * Event) * string)
  : (nat * nat * string) :=
  let (ne1, ne2) := fst nep in
  (my_geid ne1, my_geid ne2, snd nep).

Fixpoint my_ungeid (g : nat) : nat * nat :=
  match g with
  | S (S (S (S (S g')))) =>
    let (n, e) := my_ungeid g' in
    (n, S e)
  | _ => (g, 0)
  end.

Definition my_graph' := map my_gepid my_graph.

Definition my_dot_file :=
  dot_graph "sample" my_graph' my_ungeid my_n_string [] [] 5.

End DotGraphExample.

