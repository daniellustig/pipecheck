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

idens = {}
results = {}
expecteds = {}

for ln in sys.stdin:
  match = re.search("(^[0-9]*)_([A-Za-z0-9-]*_*[A-Za-z0-9*]*)__([A-Za-z0-9-]*_*[A-Za-z0-9-]*)_.*label=.(....).*exp: (....)", ln)
  if not match:
    sys.stderr.write("Could not parse line: %s" % ln)
    continue

  iden = match.group(1)
  proc = match.group(2)
  test = match.group(3)
  result = match.group(4)
  expected = match.group(5)

  #sys.stdout.write("Line: %sResult: %s: %s: %s (%s)\n" % (ln, proc, test, result, expected))
  
  if proc not in results:
    idens[proc] = {}
    results[proc] = {}
    expecteds[proc] = {}

  if test in results[proc]:
    if result <> results[proc][test]:
      sys.stderr.write("Inconsistency! %s" % ln)
      results[proc][test] = "?"
  else:
    idens[proc][test] = iden
    results[proc][test] = result
    expecteds[proc][test] = expected

for (proc, s) in results.items():
  try:
    for (test, result) in sorted(s.items()):
      expected = expecteds[proc][test]
      iden = idens[proc][test]
      if expected == "Forb" and result == "Perm":
        sys.stdout.write("(bug?)  \t")
      elif expected == "Perm" and result == "Forb":
        sys.stdout.write("(strict)\t")
      elif expected <> result:
        sys.stdout.write("??      \t")
      else:
        sys.stdout.write("        \t")
      sys.stdout.write("%s: %s: %s (test %s) (expected: %s)\n" %
          (proc, test, result, iden, expected))
  except:
    print s

