all: writeup.dvi writeup.pdf

LATEX = latex -interaction=nonstopmode

writeup.dvi: writeup.tex the.bib
	rm -f writeup.bbl
	$(LATEX) writeup.tex
	bibtex writeup
	$(LATEX) writeup.tex
	$(LATEX) writeup.tex
	rm -f writeup.aux writeup.bbl writeup.blg writeup.log writeup.toc

%.pdf: %.dvi
	dvipdf $<

