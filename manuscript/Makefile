SHELL := /bin/bash

export SOURCE_DATE_EPOCH := 1788739200
export FORCE_SOURCE_DATE := 1

.PHONY: all clean check

all: main.pdf

main.pdf: main.tex references.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

check: main.pdf
	@if rg -n 'LaTeX Warning|Package .* Warning|Overfull|Underfull|undefined references|undefined citations' main.log; then \
		echo 'LaTeX diagnostics found.' >&2; \
		exit 1; \
	fi
	@pdfinfo main.pdf | rg '^Pages:'

clean:
	latexmk -C main.tex

