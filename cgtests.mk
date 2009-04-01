# GNUmakefile for compiling the cgtests using Tock.

BACKEND ?= cppcsp
tests = $(patsubst %.occ,%,$(wildcard cgtests/cgtest??.occ))

all: $(tests)

clean:
	rm -f $(tests) cgtests/cglib.inc

checkout:
	svn co http://projects.cs.kent.ac.uk/projects/kroc/svn/kroc/trunk/tests/cgtests

%: %.occ cgtests/cglib.inc
	./tock -vk --backend=$(BACKEND) --usage-checking=off --run-indent -o $@ $<

cgtests/cglib.inc: cgtests/cglib.occ
	./tock -vk --backend=$(BACKEND) --usage-checking=off --run-indent --no-main $<

run: $(tests)
	cd cgtests && ./run-tests

run-all: $(addprefix run-,$(tests))

run-cgtests/%: cgtests/%
	cgtests/$*

profile-all: $(addprefix profile-,$(tests))

# On Debian/Ubuntu, you will need the "tth" and "netpbm" packages for ps2png
profile-cgtests/%: cgtests/%.occ
	./tock -vk --backend=$(BACKEND) --mode=compile cgtests/$*.occ +RTS -hc -p -s > /dev/null
	mv tock.hp tock-$*.hp
	mv tock.stat tock-$*.stat
	mv tock.prof tock-$*.prof
	hp2ps -c -s -g tock-$*.hp
	ps2png tock-$*.ps tock-$*.png

