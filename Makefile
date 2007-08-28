targets = tock tocktest

all: $(targets)

sources = $(wildcard *.hs) $(patsubst %.x,%.hs,$(wildcard *.x))

%.hs: %.x
	alex $<

# profile_opts = -prof -auto-all
ghc_opts = \
	-fglasgow-exts \
	-fallow-undecidable-instances \
	-fwarn-unused-binds \
	$(profile_opts)

tock: $(sources)
	ghc $(ghc_opts) -o tock --make Main

tocktest: $(sources)
	ghc $(ghc_opts) -o tocktest -main-is TestMain --make TestMain

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
	rm -f $(targets) *.o *.hi

# Don't delete intermediate files.
.SECONDARY:
