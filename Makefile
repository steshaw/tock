targets = tock raintest

all: $(targets)

sources = $(wildcard *.hs)

# profile_opts = -prof -auto-all
ghc_opts = \
	-fglasgow-exts \
	-fallow-undecidable-instances \
	-fwarn-unused-binds \
	$(profile_opts)

tock: $(sources)
	ghc $(ghc_opts) -o tock --make Main

raintest: $(sources)
	ghc $(ghc_opts) -o raintest -main-is RainParseTest --make RainParseTest

CFLAGS = \
	-O2 \
	-g -Wall \
	-std=gnu99 -fgnu89-inline \
	`kroc --cflags` `kroc --ccincpath`

%.tock.c: %.occ tock
	./tock -v -o $@ $<
	indent -kr -pcs $@

%: %.tock.o tock_support.h kroc-wrapper-c.o kroc-wrapper.occ
	kroc -o $@ kroc-wrapper.occ $< kroc-wrapper-c.o -lcif

cgtests = $(wildcard cgtests/cgtest??.occ)
cgtests_targets = $(patsubst %.occ,%,$(cgtests))

get-cgtests:
	svn co https://subversion.frmb.org/svn/cgtests/trunk cgtests

all-cgtests: $(cgtests_targets)

clean-cgtests:
	rm -f cgtests/cgtest?? cgtests/*.tock.*

haddock:
	@mkdir -p doc
	haddock -o doc --html $(sources)

clean:
	rm -f $(targets) *.o *.hi

# Don't delete intermediate files.
.SECONDARY:
