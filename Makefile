targets = tock tocktest lextest

all: $(targets)

sources = $(wildcard *.hs) $(patsubst %.x,%.hs,$(wildcard *.x))

%.hs: %.x
	alex $<

# profile_opts = -prof -auto-all
ghc_opts = \
	-fglasgow-exts \
	-fallow-undecidable-instances \
	-fwarn-unused-binds \
	$(profile_opts)

tock: $(sources)
	ghc $(ghc_opts) -o tock --make Main

tocktest: $(sources)
	ghc $(ghc_opts) -o tocktest -main-is TestMain --make TestMain

lextest: $(sources)
	ghc $(ghc_opts) -o lextest -main-is PreprocessOccam --make PreprocessOccam

CFLAGS = \
	-O2 \
	-g -Wall \
	-std=gnu99 -fgnu89-inline \
	`kroc --cflags` `kroc --ccincpath`

%.tock.c: %.occ tock
	./tock -v -o $@ $<
	indent -kr -pcs $@

%.tock.post.c: %.tock.c tock
	$(CC) $(CFLAGS) -S -o $(patsubst %.c,%.s,$<) $<
	./tock -vv --mode=post-c -o $@ $(patsubst %.c,%.s,$<)

%: %.tock.o %.tock.post.o tock_support.h kroc-wrapper-c.o kroc-wrapper.occ
	kroc -o $@ kroc-wrapper.occ $< $(patsubst %.o,%.post.o,$<) kroc-wrapper-c.o -lcif

cgtests = $(wildcard cgtests/cgtest??.occ)
cgtests_targets = $(patsubst %.occ,%,$(cgtests))

get-cgtests:
	svn co https://subversion.frmb.org/svn/cgtests/trunk cgtests

all-cgtests: $(cgtests_targets)

clean-cgtests:
	rm -f cgtests/cgtest?? cgtests/*.tock.*

haddock:
	@mkdir -p doc
	haddock -o doc --html $(filter-out LexOccam.hs,$(sources))

clean:
	rm -f $(targets) *.o *.hi

# Don't delete intermediate files.
.SECONDARY:
