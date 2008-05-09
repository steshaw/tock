GHC_OPTS = \
	-fglasgow-exts \
	-fwarn-deprecations \
	-fwarn-duplicate-exports \
	-fwarn-incomplete-record-updates \
	-fwarn-missing-fields \
	-fwarn-missing-methods \
	-fwarn-missing-signatures \
	-fwarn-overlapping-patterns \
	-fwarn-simple-patterns \
	-fwarn-type-defaults \
	-fwarn-unused-binds \
	-fwarn-unused-imports \
	\
	-ibackends \
	-ichecks \
	-icommon \
	-iconfig \
	-idata \
	-iflow \
	-ifrontends \
	-ipass \
	-ipregen \
	-itransformations

if GHC68
GHC_OPTS += -XUndecidableInstances -fwarn-tabs -fwarn-monomorphism-restriction
else
GHC_OPTS += -fallow-undecidable-instances
endif

tock$(EXEEXT): $(BUILT_SOURCES) $(tock_SOURCES) $(config_sources)
	@MKDIR_P@ obj
	ghc $(GHC_OPTS) -o tock$(EXEEXT) --make Main -odir obj -hidir obj

#The order of the -main-is and --make flags is important here:
tocktest$(EXEEXT): $(BUILT_SOURCES) $(tocktest_SOURCES) $(config_sources)
	@MKDIR_P@ obj
	ghc $(GHC_OPTS) -o tocktest$(EXEEXT) -main-is TestMain --make TestMain -odir obj -hidir obj

GenNavAST$(EXEEXT): $(GenNavAST_SOURCES)
	@MKDIR_P@ obj
	ghc $(GHC_OPTS) -o GenNavAST$(EXEEXT) -main-is GenNavAST --make GenNavAST -odir obj -hidir obj

GenOrdAST$(EXEEXT): $(GenOrdAST_SOURCES)
	@MKDIR_P@ obj
	ghc $(GHC_OPTS) -o GenOrdAST$(EXEEXT) -main-is GenOrdAST --make GenOrdAST -odir obj -hidir obj

GenTagAST$(EXEEXT): $(GenTagAST_SOURCES)
	@MKDIR_P@ obj
	ghc $(GHC_OPTS) -o GenTagAST$(EXEEXT) -main-is GenTagAST --make GenTagAST -odir obj -hidir obj

# Both these results are near-identical.  The -g flag to alex tells it to generate
# a lexer optimised for GHC.  The other part of the rule inserts the
# -fno-warn-tabs flag under GHC >= 6.8, but doesn't add anything under previous
# versions of GHC

frontends/LexOccam.hs: frontends/LexOccam.x
	alex -g frontends/LexOccam.x -o frontends/LexOccam.temphs
if GHC68
	echo "{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-monomorphism-restriction #-}" > frontends/LexOccam.hs
	cat frontends/LexOccam.temphs >> frontends/LexOccam.hs
	rm frontends/LexOccam.temphs
else
	mv frontends/LexOccam.temphs frontends/LexOccam.hs
endif

frontends/LexRain.hs: frontends/LexRain.x
	alex -g frontends/LexRain.x -o frontends/LexRain.temphs
if GHC68
	echo "{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-monomorphism-restriction #-}" > frontends/LexRain.hs
	cat frontends/LexRain.temphs >> frontends/LexRain.hs
	rm frontends/LexRain.temphs
else
	mv frontends/LexRain.temphs frontends/LexRain.hs
endif

config/Paths.hs: config/Paths.hs.in
	@sed -e 's,@@pkgincludedir@@,$(pkgincludedir),g' \
		config/Paths.hs.in >config/Paths.hs

data/NavAST.hs: GenNavAST$(EXEEXT)
	./GenNavAST$(EXEEXT) > data/NavAST.hs

data/OrdAST.hs: GenOrdAST$(EXEEXT)
	./GenOrdAST$(EXEEXT) > data/OrdAST.hs

data/TagAST.hs: GenTagAST$(EXEEXT)
	./GenTagAST$(EXEEXT) > data/TagAST.hs

config_sources = config/CompilerCommands.hs
config_sources += config/Paths.hs
config_sources += config/TypeSizes.hs

BUILT_SOURCES = data/NavAST.hs
BUILT_SOURCES += data/OrdAST.hs
BUILT_SOURCES += data/TagAST.hs
BUILT_SOURCES += frontends/LexOccam.hs
BUILT_SOURCES += frontends/LexRain.hs

CLEANFILES = $(BUILT_SOURCES) $(config_sources)

EXTRA_DIST = docextra testcases/automatic

#One entry per line makes it easier to read and easier to modify, even if it is longer

tock_SOURCES_hs = Main.hs
tock_SOURCES_hs += backends/AnalyseAsm.hs
tock_SOURCES_hs += backends/BackendPasses.hs
tock_SOURCES_hs += backends/GenerateC.hs
tock_SOURCES_hs += backends/GenerateCBased.hs
tock_SOURCES_hs += backends/GenerateCPPCSP.hs
tock_SOURCES_hs += backends/TLP.hs
tock_SOURCES_hs += checks/ArrayUsageCheck.hs
tock_SOURCES_hs += checks/Check.hs
tock_SOURCES_hs += checks/Omega.hs
tock_SOURCES_hs += checks/UsageCheckAlgorithms.hs
tock_SOURCES_hs += checks/UsageCheckUtils.hs
tock_SOURCES_hs += common/Errors.hs
tock_SOURCES_hs += common/EvalConstants.hs
tock_SOURCES_hs += common/EvalLiterals.hs
tock_SOURCES_hs += common/GenericUtils.hs
tock_SOURCES_hs += common/Intrinsics.hs
tock_SOURCES_hs += common/Pattern.hs
tock_SOURCES_hs += common/PrettyShow.hs
tock_SOURCES_hs += common/ShowCode.hs
tock_SOURCES_hs += common/TreeUtils.hs
tock_SOURCES_hs += common/Types.hs
tock_SOURCES_hs += common/Utils.hs
tock_SOURCES_hs += data/AST.hs
tock_SOURCES_hs += data/CompState.hs
tock_SOURCES_hs += data/Metadata.hs
tock_SOURCES_hs += data/NavAST.hs
tock_SOURCES_hs += data/OrdAST.hs
tock_SOURCES_hs += data/TagAST.hs
tock_SOURCES_hs += flow/FlowGraph.hs
tock_SOURCES_hs += flow/FlowAlgorithms.hs
tock_SOURCES_hs += frontends/OccamPasses.hs
tock_SOURCES_hs += frontends/OccamTypes.hs
tock_SOURCES_hs += frontends/ParseOccam.hs
tock_SOURCES_hs += frontends/ParseRain.hs
tock_SOURCES_hs += frontends/ParseUtils.hs
tock_SOURCES_hs += frontends/PreprocessOccam.hs
tock_SOURCES_hs += frontends/RainPasses.hs
tock_SOURCES_hs += frontends/RainTypes.hs
tock_SOURCES_hs += frontends/StructureOccam.hs
tock_SOURCES_hs += pass/Pass.hs
tock_SOURCES_hs += pass/PassList.hs
tock_SOURCES_hs += pass/Properties.hs
tock_SOURCES_hs += pass/Traversal.hs
tock_SOURCES_hs += transformations/SimplifyComms.hs
tock_SOURCES_hs += transformations/SimplifyExprs.hs
tock_SOURCES_hs += transformations/SimplifyProcs.hs
tock_SOURCES_hs += transformations/SimplifyTypes.hs
tock_SOURCES_hs += transformations/Unnest.hs

tock_SOURCES = $(tock_SOURCES_hs) frontends/LexOccam.x frontends/LexRain.x

tocktest_SOURCES = $(tock_SOURCES)
tocktest_SOURCES += TestMain.hs
tocktest_SOURCES += backends/AnalyseAsmTest.hs
tocktest_SOURCES += backends/BackendPassesTest.hs
tocktest_SOURCES += backends/GenerateCTest.hs
tocktest_SOURCES += checks/ArrayUsageCheckTest.hs
tocktest_SOURCES += checks/UsageCheckTest.hs
tocktest_SOURCES += common/CommonTest.hs
tocktest_SOURCES += common/TestFramework.hs
tocktest_SOURCES += common/TestHarness.hs
tocktest_SOURCES += common/TestUtils.hs
tocktest_SOURCES += flow/FlowGraphTest.hs
tocktest_SOURCES += frontends/OccamPassesTest.hs
tocktest_SOURCES += frontends/OccamTypesTest.hs
tocktest_SOURCES += frontends/ParseRainTest.hs
tocktest_SOURCES += frontends/PreprocessOccamTest.hs
tocktest_SOURCES += frontends/RainPassesTest.hs
tocktest_SOURCES += frontends/RainTypesTest.hs
tocktest_SOURCES += frontends/StructureOccamTest.hs
tocktest_SOURCES += transformations/PassTest.hs

pregen_sources = data/AST.hs
pregen_sources += pregen/PregenUtils.hs

GenNavAST_SOURCES = pregen/GenNavAST.hs $(pregen_sources)
GenOrdAST_SOURCES = pregen/GenOrdAST.hs $(pregen_sources)
GenTagAST_SOURCES = pregen/GenTagAST.hs $(pregen_sources)

#The programs to actually build:	
bin_PROGRAMS = tock
noinst_PROGRAMS = tocktest GenNavAST GenOrdAST GenTagAST
TESTS = tocktest

pkginclude_HEADERS = support/tock_support.h
pkginclude_HEADERS += support/tock_support_cif.h
pkginclude_HEADERS += support/tock_support_cppcsp.h

clean-local:
	rm -f obj/*.o obj/*.hi
	rmdir obj

# We post-process the Haddock output with M4 so that we can include SVG images.
haddock:
	@MKDIR_P@ doc
	haddock -o doc --html -p docextra/description -t Tock $(tock_SOURCES_hs)
	cp docextra/*.svg doc/
	@for x in doc/*.html; do \
		echo ">>> Post-processing $$x"; \
		cat docextra/tock-docs.m4 $$x | m4 -P >$${x}_ && mv $${x}_ $$x; \
	done
