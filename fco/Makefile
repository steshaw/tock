all: fco

sources = \
	AST.hs \
	ASTPasses.hs \
	Parse.hs \
	Pass.hs \
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
		if ! ./fco --raw-parse-tree $$x >/dev/null ; then \
			echo "parse failed" ; \
		elif ! ./fco --ast $$x >/dev/null ; then \
			echo "ast failed" ; \
		else \
			echo "ok" ; \
		fi ; \
	done
