targets = fco

all: $(targets)

sources = \
	AST.hs \
	Errors.hs \
	EvalConstants.hs \
	GenerateC.hs \
	Indentation.hs \
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
	ghc -fglasgow-exts -fallow-undecidable-instances -o fco --make Main

CFLAGS = -g -std=gnu99 -Wall `kroc --cflags` `kroc --ccincpath`

%.fco.c: %.occ fco
	./fco -v $< >$@ || ( rm -f $@; exit 1 )
	indent -kr -pcs $@

%.fco: %.fco.o fco_support.h kroc-wrapper-c.o kroc-wrapper.occ
	kroc -o $@ kroc-wrapper.occ $< kroc-wrapper-c.o -lcif

tests = $(wildcard testcases/*.occ)

test: $(targets) $(tests)
	@set -e; for x in $(tests); do \
		echo -n "$$x: " ; \
		if ! ./fco --parse-tree $$x >$$x.log 2>&1 ; then \
			echo "parse failed" ; \
		elif ! ./fco -v $$x >$$x.log 2>&1 ; then \
			echo "full failed" ; \
		else \
			echo "ok" ; \
		fi ; \
	done

clean:
	rm -f $(targets) *.o *.hi

