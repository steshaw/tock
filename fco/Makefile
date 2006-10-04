all: fco

sources = \
	AST.hs \
	ASTPasses.hs \
	Parse.hs \
	Pass.hs \
	PrettyShow.hs \
	PT.hs \
	PTPasses.hs \
	SExpression.hs \
	PTToAST.hs \
	Main.hs

fco: $(sources)
	ghc -fglasgow-exts -o fco --make Main

tests = $(wildcard test*.occ)

test: fco $(tests)
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
