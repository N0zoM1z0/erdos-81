# Erdős Problem 81: proposed complete solution

This repository contains a proposed complete proof of [Erdős Problem
81](https://www.erdosproblems.com/81), a publication manuscript, exact finite
certificate replays, independent review records, and a staged Lean 4
formalization.

The proposed theorem is stronger than the asymptotic question.  For every
sufficiently large chordal graph `G` on `n` vertices, it constructs an edge
partition into cliques of orders two, three, and four with at most

```text
floor(n(n + 1) / 6)
```

parts.  Consequently, one absolute constant `C` gives
`cp(G) <= n^2 / 6 + Cn` for every order.

The mathematical argument has survived two independent model reviews, a
separate line-by-line audit, exact certificate replay, and broad finite
regression testing.  No substantive gap is currently known.  It should still
be described as a **proposed complete proof** until it has received independent
human specialist review.  The Lean development is useful and sorry-free, but
is not yet an end-to-end formal proof; its exact boundary is documented below.

## Repository map

- `manuscript/main.tex` is the standard `amsart` publication manuscript;
  `manuscript/main.pdf` is a reproducibly built review copy.
- `preparations/erdos81_stability_closure/PROOF.md` is the authoritative
  supplied proof artifact.
- `preparations/erdos81_rigidity_addendum/PROOF.md` is the rigidity and exact
  near-extremizer addendum.
- `docs/VERIFICATION_STATUS.md` records the independent audit, logical
  dependency ledger, corrections incorporated into the manuscript, and
  release blockers.
- `lean/` contains the pinned Lean 4 project.  All Lean/Lake project files are
  kept inside that directory.
- `references/SOURCES.md` records primary literature and immutable reference
  snapshots; `scripts/fetch_references.sh` retrieves them into the ignored
  `.reference-cache/` directory.
- `preparations/gpt_chat_solver/` and `preparations/gpt_chat_auditor/` preserve
  provenance.  They are not authoritative mathematical sources because the
  chat export omitted some displayed formulae.
- `preparations/erdos81_elimination_batches/` is historical exploratory work.
  The final proof does not depend on it.

## Trust and verification boundary

The conventional proof uses three published external inputs:

1. Vizing's `Delta + 1` edge-colouring theorem.
2. The Häggkvist--Janssen bound `chi'_ell(K_p) <= p` for arbitrary edge lists
   of size `p`.
3. The uniform finite-family fractional-to-integral packing transfer of
   Rohatgi--Urschel--Wellens, applied to triangles of gain `2` and four-cliques
   of gain `5`.

The new local construction, root regularization, mixed-functional copying,
single-vertex symmetrization, complete-split terminal analysis, first-entry
argument, and near/far assembly are written out in the manuscript.  The finite
computations are regression tests and exact certificates; they are not used as
a substitute for any all-`n` theorem.

The current Lean project machine-checks:

- the exact forbidden-induced-cycle definition of chordality;
- clique edge partitions with unique edge coverage;
- the exact Erdős 81 statement and the stronger eventual upper-bound
  statement;
- the floor identity between `(2n+1)^2/24` and `n(n+1)/6`, including its
  modulo-six remainder argument;
- the universal partition into two-vertex cliques and the implication from
  the eventual bound to `n^2 / 6 + O(n)` for every order;
- the rational stability identities and all decisive numerical margins
  formalized so far, including the complete root-regularization constant chain;
- finite packing/covering weak duality and its mixed triangle--`K_4` model;
- the exact two-direction edge-count identity for vertex copying and
  preservation of simpliciality and chordality under the required copy;
- the discrete-convexity step used by the single-vertex copy path;
- the complete-split averaged dual LP, including attainment at its three
  relevant vertices and the resulting three-branch potential formula;
- the least-index first-entry barrier and the normalized step-size inequality
  at the manuscript's explicit threshold `n >= 10^32`;
- the algebraic extraction of defect and root-displacement control from the
  local deficit inequality, including the final integrality step.
- the finite chordal-graph characterization by perfect-elimination order,
  including minimal-separator clique and Dirac simplicial-vertex theorems;
- the chordal edge bound and its complement missing-pair consequence used in
  the manuscript.

The remaining chordal symmetrization, terminal construction, local structural
lemmas, and the three external inputs are not yet fully formalized.  No
custom axiom or `sorry` hides that boundary.  See `lean/README.md` for the
build guide and `lean/FORMALIZATION_STATUS.md` for the theorem-by-theorem
ledger.

## System requirements

The commands below were rerun on Python 3.11.2, Lean 4.31.0, and Mathlib pinned
by `lean/lake-manifest.json`.  On Debian or Ubuntu, the non-Python build tools
can be installed with:

```bash
sudo apt-get update
sudo apt-get install -y \
  git curl unzip ripgrep python3 python3-venv python3-pip \
  latexmk lmodern poppler-utils \
  texlive-latex-base texlive-latex-recommended texlive-latex-extra \
  texlive-fonts-recommended
```

Install Lean through [elan](https://github.com/leanprover/elan).  Entering the
`lean/` directory makes elan select the repository-pinned toolchain
automatically.

## Python environment

Only the full finite audits need third-party Python packages.  Create the
pinned environment from the repository root:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install --upgrade pip
.venv/bin/python -m pip install -r requirements-audit.txt
```

The dependency-free replays use only the Python standard library:

```bash
python3 preparations/erdos81_stability_closure/replay.py
python3 preparations/erdos81_rigidity_addendum/replay.py
```

Equivalently, run `make replay`.  The root `Makefile` also provides `lean`,
`paper`, `audit`, `references`, and a quick aggregate `check` target.

Expected summaries are:

```text
main replay:     PASS, 7,964 LP certificates and 1,889 copy steps
rigidity replay: PASS, 94 partition certificates and 94,617 clique-type checks
```

Run the substantially larger regeneration audits with the virtual environment:

```bash
.venv/bin/python preparations/erdos81_stability_closure/audit.py
.venv/bin/python preparations/erdos81_rigidity_addendum/audit.py
```

The main audit checks 531 nonempty chordal graph-atlas graphs, 5,394
two-direction copy inequalities, 19,986 integer colour bounds, and 711,246
terminal comparisons.  The rigidity audit replays 815,824 edge incidences.
Both scripts regenerate tracked JSON reports; elapsed-time fields can differ
between machines.

The historical, non-closing audit can be run separately:

```bash
.venv/bin/python preparations/erdos81_elimination_batches/audit.py
```

Its witness ordering or choice of a valid partition need not be byte-identical
across runs; verify its assertions and report semantically.

## Lean verification

From a clean clone with elan installed:

```bash
cd lean
lake update
lake exe cache get
./check.sh
```

`check.sh` rejects source-level `axiom` and `sorry` declarations, builds the
library, and runs `#print axioms` on the principal theorems.  The expected
reported assumptions are Lean/Mathlib's ordinary foundational primitives
(`propext`, `Classical.choice`, and `Quot.sound`), not project-specific axioms.

## Manuscript build

Build the paper and reject unresolved references, citation warnings, and box
overflow diagnostics with:

```bash
make -C manuscript clean check
```

With the pinned `SOURCE_DATE_EPOCH` and the TeX installation used for this
audit, the 16-page PDF has SHA-256:

```text
04a7a6ea71d7a1cf52ed6b79ac83bd74a08baf30db1085b583facab2c4ea7eb6
```

TeX engine or package-version changes can alter PDF bytes without altering the
typeset mathematics.  `main.tex` and `references.bib` are authoritative.

## Source and reference integrity

Check the three supplied source archives:

```bash
sha256sum preparations/*.zip
unzip -t preparations/erdos81_stability_closure.zip
unzip -t preparations/erdos81_rigidity_addendum.zip
unzip -t preparations/erdos81_elimination_batches.zip
(cd preparations/erdos81_stability_closure && sha256sum --check SHA256SUMS)
(cd preparations/erdos81_rigidity_addendum && sha256sum --check SHA256SUMS)
```

Expected archive digests are recorded in `docs/VERIFICATION_STATUS.md`.

Retrieve the exact third-party papers and reference repository snapshots used
by the audit with:

```bash
./scripts/fetch_references.sh
```

The script checks every downloaded paper/archive digest and checks out the
recorded immutable repository commit.  These references are evidence and
prior-art context; neither their proofs nor their formal models are treated as
trusted automatically.

## Before public submission

Replace the manuscript's `Anonymous` placeholder with the final authors and
affiliations, choose explicit repository and manuscript licences, obtain human
specialist review, and create a stable archive/DOI.  A release claiming a fully
formal proof must additionally close the remaining Lean boundary; otherwise
that limitation should remain prominent in the abstract-facing release notes.
