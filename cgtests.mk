# GNUmakefile for compiling the cgtests using Tock.

tests = $(patsubst %.occ,%,$(wildcard cgtests/cgtest??.occ))

all: $(tests)

cgtests/%: cgtests/%.occ
	./tock -v --backend=cppcsp -o $@ $<

run-all: $(addprefix run-,$(tests))

run-cgtests/%: cgtests/%
	cgtests/$*
