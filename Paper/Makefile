DOCNAME = BSV_Semantics
SOURCES = Makefile $(DOCNAME).tex

.PHONY: default
default: $(SOURCES)
	pdflatex  $(DOCNAME)

.PHONY: full
full: $(SOURCES)
	pdflatex  $(DOCNAME)
	bibtex    $(DOCNAME)
	pdflatex  $(DOCNAME)
	pdflatex  $(DOCNAME)

.PHONY: bib
bib:
	bibtex  $(DOCNAME)

.PHONY: clean
clean:
	rm -f  *~  *.toc  *.aux  *.blg  *.bbl  *.log  *.out  *.dvi  */*.aux  */*~

.PHONY: fullclean
fullclean:
	make clean
	rm  $(DOCNAME).pdf
