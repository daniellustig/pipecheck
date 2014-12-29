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
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import wmm.
Require Import util2.
Require Import stages.
Require Import ppo.
Require Import execution.
Require Import risc.
Require Import litmus.

(** [GraphsToVerifyPPO] generates a GraphViz DOT graph which can be used
  to generate the pictorial form of the above graph. *)

Definition RISCGraphs :=
  GraphsToVerifyTSOPPO RISC_Pipeline.

Definition RISCLLSS := LLSS RISC_Pipeline.

Definition RISCSLSL := SLSL RISC_Pipeline.

Definition RISCIRIW := IRIW RISC_Pipeline.

Definition RISCAll := RISCGraphs ++ RISCLLSS ++ RISCSLSL ++ RISCIRIW.

