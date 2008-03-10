# GNUmakefile for compiling the cgtests using Tock.

BACKEND ?= cppcsp
tests = $(patsubst %.occ,%,$(wildcard cgtests/cgtest??.occ))

all: $(tests)

clean:
	rm $(tests)

checkout:
	svn co http://projects.cs.kent.ac.uk/projects/kroc/svn/kroc/trunk/tests/cgtests

%: %.occ
	./tock -vk --backend=$(BACKEND) -o $@ $<

run-all: $(addprefix run-,$(tests))

run-cgtests/%: cgtests/%
	cgtests/$*
