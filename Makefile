.PHONY: all coq clean graphs html pdf results

all: coq ml

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	mkdir -p graphs

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

ml: coq printgraphs.native print_risc_graphs.native \
	print_gem5_graphs.native print_opensparc_graphs.native \
	print_scproc_graphs.native print_gem5fixed_graphs.native

allgraphs2.ml: coq
	python enable_printf.py < allgraphs.ml > allgraphs2.ml

riscgraphs2.ml: coq
	python enable_printf.py < riscgraphs.ml > riscgraphs2.ml

scprocgraphs2.ml: coq
	python enable_printf.py < scprocgraphs.ml > scprocgraphs2.ml

gem5graphs2.ml: coq
	python enable_printf.py < gem5graphs.ml > gem5graphs2.ml

gem5fixedgraphs2.ml: coq
	python enable_printf.py < gem5fixedgraphs.ml > gem5fixedgraphs2.ml

opensparcgraphs2.ml: coq
	python enable_printf.py < opensparcgraphs.ml > opensparcgraphs2.ml

printgraphs.native: allgraphs2.ml printgraphs.ml coq
	ocamlbuild -lib unix $@

print_risc_graphs.native: riscgraphs2.ml print_risc_graphs.ml coq
	ocamlbuild -lib unix $@

print_scproc_graphs.native: scprocgraphs2.ml print_scproc_graphs.ml coq
	ocamlbuild -lib unix $@

print_gem5_graphs.native: gem5graphs2.ml print_gem5_graphs.ml coq
	ocamlbuild -lib unix $@

print_gem5fixed_graphs.native: gem5fixedgraphs2.ml print_gem5fixed_graphs.ml coq
	ocamlbuild -lib unix $@

print_opensparc_graphs.native: opensparcgraphs2.ml print_opensparc_graphs.ml coq
	ocamlbuild -lib unix $@

clean: Makefile.coq
	rm -f printgraphs.native
	rm -f print_risc_graphs.native
	rm -f print_scproc_graphs.native
	rm -f print_gem5_graphs.native
	rm -f print_gem5fixed_graphs.native
	rm -f print_opensparc_graphs.native
	rm -rf _build
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

graphs:
	time ./print_risc_graphs.native
	time ./print_scproc_graphs.native
	time ./print_gem5_graphs.native
	time ./print_gem5fixed_graphs.native
	time ./print_opensparc_graphs.native

pdf:
	cd graphs && ls *.gv | sed "s/\(.*\).gv/dot -Tpdf \1.gv -o \1.pdf/" | bash

results:
	@echo "Unverified graphs (if any):"
	@grep Unverified graphs/*.gv | wc -l
	@-grep Unverified graphs/*.gv
	cd graphs && egrep "Perm|Forb" *.gv | python ../parse_litmus_test_results.py

