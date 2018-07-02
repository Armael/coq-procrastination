# ----------------------------------------------------------------------------
# Set any paper-specific variables.

include Makefile.local

# ----------------------------------------------------------------------------
# Definitions.

SOURCES  := \
  $(wildcard *.tex) \
  $(wildcard *.sty) \
  $(wildcard *.bib) \
  $(wildcard *.cls) \

# ----------------------------------------------------------------------------
# Generic rules.

%.pdf: $(SOURCES)
	xelatex $(DOC).tex
	bibtex $(DOC)
	xelatex $(DOC).tex
	xelatex $(DOC).tex

# ----------------------------------------------------------------------------
# Targets.

.PHONY: pdf loop clean log export

pdf: $(DOC).pdf

loop:
	latexmk -pdfxe -pvc $(DOC)

clean::
	rm -f `cat .gitignore`

log: pdf
	./decrypt.sh $(DOC).log

export: pdf
	scp -p -B -C $(DOC).pdf $(WWW)
