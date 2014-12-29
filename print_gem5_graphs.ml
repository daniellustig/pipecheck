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

open Printf
open Gem5graphs2

let rec stringOfString s =
  match s with
  | String (c, s') -> String.make 1 c ^ stringOfString s'
  | EmptyString -> ""

let printableCharOf c =
  if (
    (c >= 'a' && c <= 'z') ||
    (c >= 'A' && c <= 'Z') ||
    (c >= '0' && c <= '9') ||
    (c == '-') ||
    (c == '_'))
  then c
  else '_'

let graphFilename t n =
  "graphs/" ^ (sprintf "%02d" n) ^ "_" ^
  (String.map printableCharOf (stringOfString t)) ^ ".gv"

let rec printCase n l =
  match l with
  | Pair (title, graph) :: t ->
    let oc = open_out (graphFilename title n) in
    fprintf oc "%s" (stringOfString graph);
    close_out oc;
    printCase (n+1) t
  | [] -> print_string "Output "; print_int n; print_string " graphs\n"

let _ = printCase 0 Gem5graphs2.allGraphs

