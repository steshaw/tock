all: fco

fco: Main.hs Parse.hs Tree.hs Pass.hs BasePasses.hs \
		PhaseSource.hs PhaseIntermediate.hs PhaseOutput.hs
	ghc -o fco --make Main

BasePasses.hs: Tree.hs make-passthrough.py
	python make-passthrough.py

