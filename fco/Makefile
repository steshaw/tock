all: fco

sources = \
	BaseTransforms.hs \
	Parse.hs \
	Pass.hs \
	PhaseIntermediate.hs \
	PhaseOutput.hs \
	PhaseSource.hs \
	SExpression.hs \
	Tree.hs \
	Main.hs

fco: $(sources)
	ghc -o fco --make Main

BaseTransforms.hs: Tree.hs make-passthrough.py
	python make-passthrough.py

