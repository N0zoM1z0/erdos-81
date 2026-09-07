# Manuscript

`main.tex` is the publication manuscript for the proposed solution of Erdős
Problem 81.  It uses the standard `amsart` class and a BibTeX bibliography.

Build and check it with:

```bash
cd manuscript
make check
```

The build requires `latexmk`, `pdflatex`, BibTeX, and the commonly packaged
LaTeX modules `amsart`, `lmodern`, `microtype`, `mathtools`, `amssymb`,
`booktabs`, `enumitem`, `hyperref`, and `cleveref`.  The root README gives a
Debian/Ubuntu installation command.

The Makefile fixes `SOURCE_DATE_EPOCH` so that clean builds are reproducible
with the same TeX distribution.  `main.pdf` is committed for convenient
review; `main.tex` and `references.bib` remain the authoritative sources.

Before external submission, replace the `Anonymous` author placeholder and
add the final affiliations, acknowledgements, contact information, and
licence selected by the authors.
