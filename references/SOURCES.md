# External reference sources

This directory records the exact third-party material consulted while
preparing the proposed solution of Erdős Problem 81.  Run

```bash
./scripts/fetch_references.sh
```

to populate the ignored `.reference-cache/` directory.  The cache is not
committed because the sources have their own licences and, in the Overleaf
case, no redistribution licence was identified.

## Current partial claims

### Juan Pablo Traverso

- Concept DOI: <https://doi.org/10.5281/zenodo.21273143>
- Exact snapshot: Zenodo record `22064657`, DOI
  <https://doi.org/10.5281/zenodo.22064657>, version `v3`, published
  2026-08-23.
- Repository: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions>
- Inspected commit: `cdd0b98c0c663b98e1be020b4ef23becc50d22e5`.
- Declared licence: CC BY-NC 4.0.

The exact snapshot contains the following English preprints:

| Paper | Version | SHA-256 |
|---|---:|---|
| *Affine Profile Reduction for Fractional Triangle Packings in Split Graphs* | 1.3 | `37626b68bfc9c908b9e08ac563635cb422e68369e1f4aacda1b7dd9e71716fb6` |
| *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs* | 1.2 | `67bf3490cab8c54356850215a739b92a8007e48509707f64f622d5f6b402f4eb` |
| *Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing* | 1.5 | `077a12da4db42ecbe6bcc25333539bf7ee3e63fa20bc7a46d8e801120ac9bb27` |

These papers establish fractional extremal results and the split-graph case.
They do not claim the general chordal result proved in the present manuscript.
Their Lean sources are useful for comparison, but their definitions and proof
interfaces are not imported into this repository.

### Ricky Cipollini

- Proof-claim page:
  <https://www.erdosproblems.com/forum/thread/81/proof-claims>
- Public Overleaf source:
  <https://www.overleaf.com/read/thjptfhgnmxc#cc1388>
- Retrieved: 2026-09-07.
- Source-archive SHA-256:
  `ed61b083e68b0bb111d0b5e5c063dc57fe0e01d83783d88ba5ab890d84eacefe`.
- Licence: no explicit redistribution licence was found in the downloaded
  source.

The three-page manuscript proves the asymptotic partial bound
\(\operatorname{cp}(G)\le n^2/6+o(n^2)\).  Its weighted symmetrization gives
an independent comparison point, but it does not address the linear-error
closure.

## Lean chordal-structure comparison

### Reconstruction conjecture project

- Repository:
  <https://github.com/SamuelSchlesinger/reconstruction-conjecture>
- Inspected commit: `419d639395bd5e3bc32f7e6e220a6c2c371e1ea5`.
- Relevant modules: `MinimalSeparatorClique.lean`, `Dirac.lean`, and
  `PEO.lean`.
- Pinned environment: Lean `v4.28.0`, Mathlib `v4.28.0`.
- Local audit: `lake build Reconstruction.PEO` completed all 1,200 jobs.
  `#print axioms` for the minimal-separator, Dirac, and PEO theorems reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Licence: no explicit software licence was found at the inspected commit.

This is useful independent evidence that the standard separator-to-Dirac-to-PEO
route can be kernel checked.  The repository as a whole contains an unrelated
`sorry` for the open reconstruction conjecture, and it targets an older
Mathlib release.  It is therefore neither imported nor copied into this
formalization; all declarations used here are proved in this repository and
pass its own source and axiom gates.

## Use policy

The files above are prior work and comparison material.  Nothing in the
proposed proof is accepted merely because a partial manuscript or a Lean file
asserts an analogous result.  Definitions, quantifiers, objective functions,
and theorem dependencies are checked independently.  Any reused mathematical
idea is cited; no third-party source code is copied into the formalization.
