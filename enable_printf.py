#!/usr/bin/env python
################################################################################
## PipeCheck: Specifying and Verifying Microarchitectural                     ##
## Enforcement of Memory Consistency Models                                   ##
##                                                                            ##
## Copyright (c) 2014 Daniel Lustig, Princeton University                     ##
## All rights reserved.                                                       ##
##                                                                            ##
## This library is free software; you can redistribute it and/or              ##
## modify it under the terms of the GNU Lesser General Public                 ##
## License as published by the Free Software Foundation; either               ##
## version 2.1 of the License, or (at your option) any later version.         ##
##                                                                            ##
## This library is distributed in the hope that it will be useful,            ##
## but WITHOUT ANY WARRANTY; without even the implied warranty of             ##
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          ##
## Lesser General Public License for more details.                            ##
##                                                                            ##
## You should have received a copy of the GNU Lesser General Public           ##
## License along with this library; if not, write to the Free Software        ##
## Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  ##
## USA                                                                        ##
################################################################################


import sys

printf_pre_string = """let rec stringOfString s =
  match s with
  | String (c, s') -> String.make 1 c ^ stringOfString s'
  | EmptyString -> ""
"""

printf_post_string = '  Printf.printf "%s" (stringOfString s);\n'

debugprintf_post_string = """  try
    if int_of_string (Sys.getenv "PIPECHECK_DEBUG") > level  then
      (Printf.printf "%s" (stringOfString s); a)
    else
      a
  with
    | Not_found -> a
    | Failure "int_of_string" -> a
"""

panic_post_string = """  Printf.printf "\\nPanic!\\n%s\\n" (stringOfString msg);
  failwith "Panic called"\n
"""

timerStartHook_post_string = """  let t_start = Unix.gettimeofday() in Pair (t_start, a)

"""

timerStopHook_post_string = """  let t_stop = Unix.gettimeofday() in
  let _ = Printf.printf "Timer,%s,%f\\n" (stringOfString s) (t_stop -. t_start) in
  a

"""

def parse(f_in, f_out):
  for ln in f_in:
    if "let printfHook" in ln:
      f_out.write(printf_pre_string)
    f_out.write(ln)
    if "let printfHook" in ln:
      f_out.write(printf_post_string)
    if "let debugPrintfHook" in ln:
      f_out.write(debugprintf_post_string)
      for ln in f_in:
        if ln == "\n":
          break
    if "let panicHook" in ln:
      f_out.write(panic_post_string)
      for ln in f_in:
        if ln == "\n":
          break
    elif "let timerStartHook" in ln:
      f_out.write(timerStartHook_post_string)
      for ln in f_in:
        if ln == "\n":
          break
    elif "let timerStopHook" in ln:
      f_out.write(timerStopHook_post_string)
      for ln in f_in:
        if ln == "\n":
          break

parse(sys.stdin, sys.stdout)

