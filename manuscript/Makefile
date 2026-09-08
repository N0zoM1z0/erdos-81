SHELL := /bin/bash

export SOURCE_DATE_EPOCH := 1788825600
export FORCE_SOURCE_DATE := 1

.PHONY: all clean check

all: main.pdf

main.pdf: main.tex references.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

check:
	@$(MAKE) clean
	@$(MAKE) main.pdf
	@test -s main.log || { echo 'Missing LaTeX build log.' >&2; exit 1; }
	@if diagnostics="$$(rg -n 'LaTeX Warning|Package .* Warning|Overfull|Underfull|undefined references|undefined citations' main.log 2>&1)"; then \
		printf '%s\n' "$$diagnostics"; \
		echo 'LaTeX diagnostics found.' >&2; \
		exit 1; \
	else \
		status=$$?; \
		if [ $$status -ne 1 ]; then \
			printf '%s\n' "$$diagnostics" >&2; \
			echo 'Failed to scan the LaTeX build log.' >&2; \
			exit $$status; \
		fi; \
	fi
	@pdfinfo main.pdf | rg '^Pages:'

clean:
	latexmk -C main.tex
	$(RM) main.bbl
