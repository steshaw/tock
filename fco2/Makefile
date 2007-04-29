targets = tock

all: $(targets)

sources = \
	AST.hs \
	Errors.hs \
	EvalConstants.hs \
	EvalLiterals.hs \
	GenerateC.hs \
	Indentation.hs \
	Intrinsics.hs \
	Main.hs \
	Metadata.hs \
	Parse.hs \
	ParseState.hs \
	Pass.hs \
	PrettyShow.hs \
	SimplifyExprs.hs \
	SimplifyProcs.hs \
	TLP.hs \
	Types.hs \
	Unnest.hs \
	Utils.hs

$(targets): $(sources)
	ghc -fglasgow-exts -fallow-undecidable-instances -o tock --make Main

CFLAGS = -g -std=gnu99 -Wall `kroc --cflags` `kroc --ccincpath`

%.tock.c: %.occ tock
	./tock -v -o $@ $<
	indent -kr -pcs $@

%: %.tock.o tock_support.h kroc-wrapper-c.o kroc-wrapper.occ
	kroc -o $@ kroc-wrapper.occ $< kroc-wrapper-c.o -lcif

cgtests = $(wildcard cgtests/cgtest??.occ)
cgtests_targets = $(patsubst %.occ,%,$(cgtests))

all-cgtests: $(cgtests_targets)

haddock:
	@mkdir -p doc
	haddock -o doc --html $(sources)

clean:
	rm -f $(targets) *.o *.hi

# Don't delete intermediate files.
.SECONDARY:

