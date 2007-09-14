targets = tock tocktest

all: $(targets)

sources = $(wildcard *.hs frontends/*.hs backends/*.hs transformations/*.hs common/*.hs) $(patsubst %.x,%.hs,$(wildcard frontends/*.x))

builtfiles = $(patsubst %.x,%.hs,$(wildcard frontends/*.x))

%.hs: %.x
	alex $<

# profile_opts = -prof -auto-all
ghc_opts = \
	-fglasgow-exts \
	-fallow-undecidable-instances \
	-fwarn-unused-binds \
	-icommon -itransformations -ifrontends -ibackends \
	$(profile_opts)

tock: $(sources)
	mkdir -p obj
	ghc $(ghc_opts) -o tock --make Main -odir obj -hidir obj

tocktest: $(sources)
	mkdir -p obj
	ghc $(ghc_opts) -o tocktest -main-is TestMain --make TestMain -odir obj -hidir obj

CFLAGS = \
	-O2 \
	-g -Wall \
	-std=gnu99 -fgnu89-inline \
	`kroc --cflags` `kroc --ccincpath`

CXXFLAGS = -I. -O2 -ggdb3 -Wall

%x.tock.cpp: %.rain tock
	./tock -v --backend=cppcsp --frontend=rain -o $@ $<
	indent -nut -bli0 -pcs $@

%x: %x.tock.o tock
	g++ $@.tock.o -pthread -lcppcsp2 -o $@

%.tock.c: %.occ tock
	./tock -v -o $@ $<
	indent -kr -pcs $@

%.tock.post.c: %.tock.c tock
	$(CC) $(CFLAGS) -S -o $(patsubst %.c,%.s,$<) $<
	./tock -vv --mode=post-c -o $@ $(patsubst %.c,%.s,$<)

%: %.tock.o %.tock.post.o tock_support.h kroc-wrapper-c.o kroc-wrapper.occ
	kroc -o $@ kroc-wrapper.occ $< $(patsubst %.o,%.post.o,$<) kroc-wrapper-c.o -lcif

cgtests = $(wildcard cgtests/cgtest??.occ)
cgtests_targets = $(patsubst %.occ,%,$(cgtests))

get-cgtests:
	svn co https://subversion.frmb.org/svn/cgtests/branches/tock cgtests

all-cgtests: $(cgtests_targets)

clean-cgtests:
	rm -f cgtests/cgtest?? cgtests/*.tock.*

#Haddock does allow you to customise the description section of a file, but only with more Haskell comments
#Since I want to use an HTML description (with links to SVG using object tags) I have to perform the following hack
#to use my own custom HTML description.  Fixes to make the hack nicer are welcome :-)

haddock:
	@mkdir -p doc
	@echo "putmycustomdocumentationhere" > .temp-haddock-file
	haddock -o doc --html -p temp-haddock-file -t Tock $(filter-out LexOccam.hs LexRain.hs,$(sources))
	cp docextra/*.svg doc/
	@rm .temp-haddock-file
	@grep -B 10000 putmycustomdocumentationhere doc/index.html | sed "s/putmycustomdocumentationhere//" > doc/index.html-2	
	@cat docextra/description.html >> doc/index.html-2
	@grep -A 10000 putmycustomdocumentationhere doc/index.html | tail -n +2 >> doc/index.html-2
	@rm doc/index.html
	@mv doc/index.html-2 doc/index.html

clean:
	rm -f $(targets) $(builtfiles) obj/*.o obj/*.hi

#This generates the ASTXML module, which is not currently used anywhere in Tock.
#It requires the HaXml modules (1.13.x or earlier), and the DrIFT preprocessor, urls:
# http://www.cs.york.ac.uk/fp/HaXml/
# http://repetae.net/~john/computer/haskell/DrIFT/
#I had to exclude a few other definitions from the imports because AST has entries like True,
#and we cannot get DrIFT to import AST qualified.  The alternative would be to append the 
#instances from DrIFT to AST.hs itself, but I didn't want to do that just yet:

common/ASTXML.hs: common/AST.hs common/Metadata.hs
	echo -e "module ASTXML where\n" > common/ASTXML.hs
	echo -e "import AST\n" >> common/ASTXML.hs
	echo -e "import Metadata\n" >> common/ASTXML.hs
	echo -e "import Text.XML.HaXml.Haskell2Xml hiding (Seq, TagName, Name, Plus, Choice)\n" >> common/ASTXML.hs
	echo -e "import Prelude hiding (True,False)\n" >> common/ASTXML.hs
	cd common && DrIFT -r AST.hs >> ASTXML.hs
	cd common && DrIFT -r Metadata.hs >> ASTXML.hs


# Don't delete intermediate files.
.SECONDARY:
