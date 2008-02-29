# GNUmakefile for compiling the cgtests using Tock.

tests = $(patsubst %.occ,%,$(wildcard cgtests/cgtest??.occ))

all: $(tests)

checkout:
	svn co http://projects.cs.kent.ac.uk/projects/kroc/svn/kroc/trunk/tests/cgtests

cgtests/%: cgtests/%.occ
	./tock -v --backend=cppcsp -o $@ $<

run-all: $(addprefix run-,$(tests))

run-cgtests/%: cgtests/%
	cgtests/$*
