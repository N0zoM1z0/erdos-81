# Lean formalization

This directory contains the staged Lean 4 formalization accompanying the
Erdős Problem 81 manuscript.  It is deliberately self-contained under
`lean/`; Lake files and Lean sources do not spill into the repository root.

## What is machine checked now

- `Erdos81/Statement.lean` defines chordal graphs by excluding induced cycles
  of length at least four, defines clique edge partitions with unique edge
  coverage, and states both Erdős Problem 81 and the manuscript's stronger
  eventual upper bound.
- The same file constructs the universal partition into edge-sized cliques
  and proves that the eventual sharp upper bound implies the original
  `n^2 / 6 + O(n)` statement for every order.
- `Erdos81/Arithmetic.lean` proves the exact stability square identity, root
  regularization constants, terminal-branch gaps, first-entry numerical
  inequality, and far-case closing arithmetic.
- `Erdos81/SharpBound.lean` proves the exact floor identity relating the
  continuous envelope to `floor(n(n+1)/6)`, including the required modulo-six
  argument.
- `Erdos81/FiniteLP.lean` proves finite packing/covering weak duality from
  first principles.
- `Erdos81/MixedModel.lean` instantiates that LP with graph edges as resources,
  triangles and four-cliques as items, and gains `2` and `5`.
- `Erdos81/DiscreteConvexity.lean` checks the direction choice, propagation to
  an endpoint, and the sign algebra in the single-vertex copying argument.
- `Erdos81/Copying.lean` fixes the orientation of Mathlib's vertex-replacement
  operation, proves preservation of simpliciality at the copied vertex, and
  proves the exact two-direction edge-count identity.
- `Erdos81/SplitDual.lean` solves the averaged two-variable dual on a
  complete-split graph, proves attainment at one of its three lower-boundary
  vertices, and derives the manuscript's three-branch potential formula.
- `Erdos81/AxiomAudit.lean` prints the assumptions of the principal theorems.

The long chordal symmetrization, local structural lemma, and the applications
of Vizing, Häggkvist--Janssen, and Rohatgi--Urschel--Wellens are **not yet fully
formalized**.  No placeholder axiom or `sorry` is used to hide this boundary.
Accordingly, the Lean project is not yet a kernel proof of the complete result.

## Reproduce

Install `elan` (which supplies Lean and Lake), then run:

```sh
cd lean
lake update
lake exe cache get
./check.sh
```

The toolchain is pinned in `lean-toolchain`; all Mathlib dependency revisions
are pinned in `lake-manifest.json`.  `./check.sh` rejects source-level `axiom`
or `sorry` declarations, builds the library, and runs the assumption audit.

To inspect a single module interactively:

```sh
cd lean
lake env lean Erdos81/Arithmetic.lean
```
