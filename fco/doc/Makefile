all: writeup.dvi writeup.pdf fco-pres.dvi fco-pres.pdf

LATEX = latex -interaction=nonstopmode

writeup.dvi: writeup.tex the.bib
	rm -f writeup.bbl
	$(LATEX) writeup.tex
	bibtex writeup
	$(LATEX) writeup.tex
	$(LATEX) writeup.tex
	rm -f writeup.aux writeup.bbl writeup.blg writeup.log writeup.toc

fco-pres.dvi: fco-pres.tex
	$(LATEX) fco-pres.tex
	$(LATEX) fco-pres.tex
	$(LATEX) fco-pres.tex
	rm -f fco-pres.aux fco-pres.log fco-pres.toc

%.pdf: %.dvi
	dvipdf $<

