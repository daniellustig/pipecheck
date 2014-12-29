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
Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import util2.
Require Import gem5.
Require Import ppo.
Require Import litmus.

Definition AllPPOGraphs := GraphsToVerifyTSOPPO (gem5_O3_Pipeline 1).

Definition AllLitmusTestGraphs :=
    map (fun t => t (gem5_O3_Pipeline 4)) AllLitmusTests.

Definition AllGraphs :=
  AllPPOGraphs ++
  fold_left (app (A:=_))
    (AllLitmusTestGraphs)
    [].

Extraction Language Ocaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "(fun x -> x + 1)" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant beq_nat => "( = )".

(*
Extract Constant zero => "'λ000'".
Extract Constant one => "'λ001'".
Extract Constant shift =>
 "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec => "(=)".
*)
Extraction "gem5graphs.ml" AllGraphs.

