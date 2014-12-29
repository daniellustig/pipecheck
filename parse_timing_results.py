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
import re

results = {}
tests = set()
timers = set()

def parse(f_in, f_out):
  uarch = None
  test = None
  for ln in f_in:
    if ln[-1] == '\n':
      ln = ln[:-1]
    ls = ln.split(',')
    if ls[0] == "Litmus Test":
      uarch = ls[1]
      test = ls[2]
      if uarch not in results:
        results[uarch] = {}
      results[uarch][test] = {}
      if test not in tests:
        tests.add(test)
    elif ls[0] == "Litmus Test Result":
      uarch = None
      test = None
    elif ls[0] == "Timer":
      if not uarch or not test:
        continue
      timer = ls[1]
      time = float(ls[2])
      if timer not in timers:
        timers.add(timer)
      results[uarch][test].setdefault(timer, 0.0)
      results[uarch][test][timer] += time
    else:
      sys.stderr.write("Could not parse line: %s\n" % ln)

  f_out.write(",,")
  for timer in timers:
    f_out.write("%s," % timer)
  f_out.write("\n")
  for uarch in results:
    for test in tests:
      f_out.write("%s,%s," % (uarch, test))
      for timer in timers:
        try:
          f_out.write("%f," % results[uarch][test][timer])
        except KeyError:
          f_out.write("0,")
      f_out.write("\n")

parse(sys.stdin, sys.stdout)


