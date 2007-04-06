targets = fco

all: $(targets)

sources = \
	AST.hs \
	Errors.hs \
	GenerateC.hs \
	Indentation.hs \
	Main.hs \
	Metadata.hs \
	Parse.hs \
	ParseState.hs \
	PrettyShow.hs \
	Types.hs

$(targets): $(sources)
	ghc -fglasgow-exts -o fco --make Main

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

