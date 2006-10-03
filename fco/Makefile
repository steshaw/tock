all: fco

sources = \
	BaseTransforms.hs \
	OccamTypes.hs \
	Parse.hs \
	Pass.hs \
	PhaseIntermediate.hs \
	PhaseOutput.hs \
	PhaseSource.hs \
	SExpression.hs \
	Tree.hs \
	TreeToAST.hs \
	Main.hs

fco: $(sources)
	ghc -fglasgow-exts -o fco --make Main

BaseTransforms.hs: Tree.hs make-passthrough.py
	python make-passthrough.py

tests = $(wildcard test*.occ)

test: fco $(tests)
	@set -e; for x in $(tests); do \
		echo -n "$$x: " ; \
		if ! ./fco --raw-parse-tree $$x >/dev/null ; then \
			echo "parse failed" ; \
		elif ! ./fco --ast $$x >/dev/null ; then \
			echo "ast failed" ; \
		else \
			echo "ok" ; \
		fi ; \
	done
