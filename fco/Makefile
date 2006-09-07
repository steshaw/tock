all: fco

fco: Main.hs Parse.hs Tree.hs Pass.hs PhaseSource.hs PhaseOutput.hs BasePasses.hs
	ghc -o fco --make Main

BasePasses.hs: Tree.hs make-passthrough.py
	python make-passthrough.py

