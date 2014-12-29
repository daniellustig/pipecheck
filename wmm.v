(*********************************************************************)
(*             A Formal Hierarchy of Weak Memory Models              *)
(*                                                                   *)
(*   Jade Alglave INRIA Paris-Rocquencourt, France.                  *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique. All rights reserved. This file is distributed    *)
(*  under the terms of the Lesser GNU General Public License.        *)
(*********************************************************************)

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

(******************************************************************************)
(* This file contains the pieces of Alglave's CAV 2010 Weak Memory Model      *)
(* analysis framework that have been adapted for use in PipeCheck.  The full  *)
(* contents of the original framework are available at                        *)
(* http://www0.cs.ucl.ac.uk/staff/j.alglave/wmm                               *)
(******************************************************************************)

Set Implicit Arguments.

(** * Basic types *)

(** ** Words *)
  (** We abstract from word-size and alignment issues for now,
        modelling both memory addresses and the values that may be
        stored in them by natural numbers. *) 

Definition Word := nat.

(** *** Addresses *)
Definition Address := Word.

(** *** Values *)
Definition Value := Word.

(** ** Processors *)
  (** Processors are indexed by natural numbers. *)

Definition Proc := nat.

(** The model is expressed in terms of allowable orderings on events:
      individual reads and writes to memory, and
      memory barrier events.  Each instance of an instruction in a
      program execution may give rise to multiple events, as described
      by the instruction semantics.  We abstract from
      the details of instructions, but we record in each event the
      instruction instance id (an iiid) that gave rise to it, so that
      we can refer to the program order over the instruction
      instances.  An instruction instance id specifies the processor
      on which the instruction was executed together with the index of
      the program-order point at which it was executed (represented by
      a natural number).*)

(** ** Index in program order *)

Definition program_order_index := nat.

(** ** Iiid: instruction identifier *)

Record Iiid  : Set := mkiiid {
  proc : Proc;
  poi: program_order_index }.

(** Each event has an event instance id (eiid), the associated
      instruction instance id (iiid), and an action.  An action is
      either an access, with a direction (read or write),
      a memory location specified by an address, and a value. *)

(** ** Eiid: unique event identifier *)

Definition Eiid := nat.

(** ** Directions
          i.e. read or write*)

Inductive Dirn : Set :=
  | R : Dirn
  | W : Dirn.

(** ** Location:
          - a memory location is specified by an address*)

Definition Location := Address.

(** ** Action:
          - an access specified by a polarity, a location and a value *)

Inductive Action : Set :=
  | Access : Dirn -> Location -> Value -> Action.

(** ** Event:
      - an unique identifier; 
      - the associated index in program order and the proc; 
      - the associated action *)

Record Event : Set := mkev {
  eiid : Eiid; 
  iiid : Iiid;
  action : Action}.

Definition dirn (e : Event) : Dirn :=
  match e with mkev _ _ (Access d _ _) => d end.
(** * Basic operations on data types *)

(** ** Location of an event *)

 Definition loc (e:Event) : (*option*) Location :=
  match e.(action) with
  | Access _ l _ => (*Some*) l
  end. 

