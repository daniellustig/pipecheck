# PipeCheck

PipeCheck is a methodology and automated tool for verifying that a particular
microarchitecture correctly implements the memory consistency model defined
by the architectural specification.

### Citing PipeCheck

If you use PipeCheck in your work, we would appreciate it if you cite our paper:

Daniel Lustig, Michael Pellauer, and Margaret Martonosi.  "PipeCheck:
  Specifying and Verifying Microarchitectural Enforcement of Memory Consistency
  Models", *47th International Symposium on Microarchitecture (MICRO)*,
  Cambridge UK, December 2014.

### Contacting the authors

If you have any comments, questions, or feedback, please contact Daniel Lustig
at dlustig@princeton.edu, or visit our GitHub page,
github.com/daniellustig/pipecheck.

### Status

At this point, PipeCheck is a research tool rather than an industry-strength
verification toolchain.  We do appreciate any suggestions or feedback either
in approach or in implementation.  If you are interested in any particular
feature, missing item, or implementation detail, please contact the authors and
we will try to help out as best we can.

## Building and Using PipeCheck

### Prerequisites

PipeCheck is written in Coq and extracted to OCaml for compilation to a native
executable.  PipeCheck requires Coq (v4.0 or later) and OCaml (tested on
versions 8.4pl3 and 8.4pl5).  The authors have compiled and executed PipeCheck
successfully on both Linux and Mac.

Optionally, the PipeCheck results can be visualized using the `dot` tool.  The
authors have tested dot version 2.36.

PipeCheck reuses some data structures from the CAV 2010 Weak Memory Model
analysis framework developed by Jade Alglave.  These structures are contained
within the file wmm.v.  The complete CAV 2010 framework is available at
http://www0.cs.ucl.ac.uk/staff/j.alglave/wmm

### Using PipeCheck As-Is

0. Make sure `ocamlc` and `coqc` (and `dot` if desired) are in your `PATH`.
1. `make`
    - This compiles PipeCheck, extracts it to OCaml, and compiles the extracted
      OCaml code into native binaries.
2. `make graphs`
    - This executes the PipeCheck tool on the pre-defined pipelines.  To test
      individual pipelines, execute the following:
      - `./print_<pipeline name>_graphs.native`
3. `make results`
    - This checks the PipeCheck results against the expected behaviors, and
      highlights any mismatches (be they stronger or weaker than expected).
4. (Optional) `make pdf`
    - This converts all of the results into PDFs using dot.  At this point,
      the layout of the graphs is chosen entirely by the dot tool, so the
      layout may not always be as pretty as it could be.  Individual results
      can be visualized by doing the following:
      - `cd graphs`
      - `dot -Tpdf <result filename> -o <graph output filename.pdf>`

## Design Approach

PipeCheck is written in Coq, a theorem prover/verification assistant.  For
example, Coq has been used to rigorously and formally verify mathematical
theorems such as the four color theorem, and it has been used to produce
C compilers which provably produce correct C code.  PipeCheck itself does not
yet contain any verified theorems or processes.  Nevertheless, we chose Coq to
make for easier integration with other formal models written using Coq, and to
leave open the possiblity of making PipeCheck more rigorous in the future.

In practice, we are also interested in using PipeCheck as a practical tool.
For this reason, we auto-extract our code from Coq to OCaml (using built-in
Coq methodology for doing so), and we compile this code to run natively.  So
far, we have not put much effort into optimizing for performance of this code,
partially because of PipeCheck's current status as a research tool, but more
importantly because we haven't yet found performance to be a bottleneck.  All
of PipeCheck's tests run within a few minutes even without special optimization
effort, and so optimization at this point would likely be premature anyway.

## Extending PipeCheck

TO DO.

For now, the easiest approach is to duplicate one of the existing pipelines,
modifying stage definitions as appropriate.  From there, search the code and
Makefile to find all references to the original pipeline, duplicate them, and
change the new entries to refer to the new pipeline.

We apologize that this process currently requires pipelines to be hardcoded.
We are planning to develop an easier-to-use front end to PipeCheck in the near
future.  If there are any questions or thoughts, please don't hesitate to
contact the authors.

### Wish List

Known bugs:

 - PipeCheck PPO Verification Tests do not yet support speculative load
   reordering.  Litmus tests do support it, however.

Planned future features:

 - Memory fences
   - and cumulative fences, for ARM/Power
 - Read-modify-write atomics
 - Nicer front end for specifying pipelines.
   - and maybe even litmus tests too.

Longer-term hopes:

 - Verify some of PipeCheck within Coq
 - Integrate PipeCheck with other external tools at different levels of the
   programming stack, so that we might e.g., have a complete verifiable
   flow from C to architecture to microarchitecture.

