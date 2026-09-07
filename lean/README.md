# Lean formalization

This directory contains the staged Lean 4 formalization accompanying the
Erdős Problem 81 manuscript.  It is deliberately self-contained under
`lean/`; Lake files and Lean sources do not spill into the repository root.
See `FORMALIZATION_STATUS.md` for a manuscript-to-Lean theorem ledger.

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
- `Erdos81/Chordal.lean` derives directly from the induced-cycle definition
  that induced subgraphs remain chordal and that the common neighborhood of
  two distinct nonadjacent vertices is a clique.  It then proves the full
  cardinal estimate `d_U(u) <= D + w - 2` used in the manuscript's
  nonadjacency lemma.
- `Erdos81/ChordalWalk.lean` proves that shortest paths are chordless and
  packages two internally chordless, mutually separated arcs as an induced
  cycle embedding.
- `Erdos81/Separator.lean` and `Erdos81/ChordalSeparator.lean` construct an
  inclusion-minimal separator, prove that each separator vertex reaches both
  selected components, and prove from the induced-cycle definition that every
  such separator in a chordal graph is a clique.
- `Erdos81/Dirac.lean` proves the strong finite Dirac theorem: a chordal graph
  is complete or has two nonadjacent simplicial vertices.
- `Erdos81/PerfectElimination.lean` defines both a fixed
  perfect-elimination order on `Fin n` and the label-independent existence of
  one under relabelling.  It proves directly that either condition implies
  chordality, counts every edge by its earlier endpoint, and establishes
  `e(G) + choose(p,2) <= (p-1)n` and
  `e(complement G) >= choose(n-p+1,2)` for a graph admitting such an order.
- `Erdos81/PEOExistence.lean` repeatedly peels simplicial vertices, converts
  the resulting duplicate-free list to a relabelling of `Fin n`, and proves
  the converse chordal-to-PEO direction.  It also proves that the elimination
  list may be chosen to end in any prescribed clique, and therefore discharges
  both edge bounds directly from chordality.
- `Erdos81/FiniteLP.lean` proves finite packing/covering weak duality from
  first principles.
- `Erdos81/MixedModel.lean` instantiates that LP with graph edges as resources,
  triangles and four-cliques as items, and gains `2` and `5`.
- `Erdos81/CliquePartitionCounting.lean` proves the exact edge double count
  `sum_K choose(|K|,2) = e(G)` for every clique partition.
- `Erdos81/IntegralPacking.lean` gives explicit inverse objective
  transformations between mixed integral packings and clique partitions with
  blocks of order at most four.  It proves both exact size formulas and the
  attained-optimum identity `cp_{<=4}(G) = e(G) - W_int(G)`.
- `Erdos81/DiscreteConvexity.lean` checks the direction choice, propagation to
  an endpoint, and the sign algebra in the single-vertex copying argument.
- `Erdos81/EditDistance.lean` defines labelled edge-edit distance and the
  family of complete-split templates with clique side `floor(n/3)`, proves
  the triangle inequality, and proves that a single vertex copy changes both
  the graph and its distance to that family by at most `n - 2`.
- `Erdos81/Copying.lean` fixes the orientation of Mathlib's vertex-replacement
  operation, proves preservation of simpliciality at the copied vertex, and
  proves the exact two-direction edge-count identity.  It also proves directly
  from the forbidden-induced-cycle definition that copying a simplicial source
  preserves chordality.  Its canonical collapse homomorphism maps every clique
  in a replaced graph injectively to a clique of the same order in the source
  graph, preparing the mixed-dual transport argument.
- `Erdos81/CopyCover.lean` proves the required edge-set bijection on each
  triangle or four-clique, reindexes its incidence sum, and constructs a
  feasible mixed-cover pullback along any graph homomorphism.  In particular,
  applying it to the replacement-collapse homomorphism gives the copied cover
  used in the manuscript.  The same module proves the exact two-direction
  objective identity and the resulting mixed-potential copy inequality for
  certified dual optima; general optimum existence remains part of the finite
  LP boundary.
- `Erdos81/SplitDual.lean` solves the averaged two-variable dual on a
  complete-split graph, proves attainment at one of its three lower-boundary
  vertices, and derives the manuscript's three-branch potential formula.
- `Erdos81/FirstEntry.lean` uses a genuine least path index to prove the
  first-entry barrier argument and verifies the normalized one-step bound at
  `n >= 10^32`.
- `Erdos81/FirstEntryGraph.lean` instantiates that barrier on an actual path
  of legal `replaceVertex` steps, using `splitEditDistance` and the exact
  `n - 2` edit bound.  It also specializes the result to the manuscript's
  values `rho = 10^-12` and `n >= 10^32`.
- `Erdos81/RootArithmetic.lean` checks the complete exact-constant chain in
  strict root demotion/promotion, including the ceiling and final host-list
  margins.
- `Erdos81/LocalStability.lean` derives defect and root-displacement control
  from the regularized deficit inequality and checks the final integrality
  step from `Q(n)` to `sharpBound n`.
- `Erdos81/AxiomAudit.lean` prints the assumptions of the principal theorems.

The long chordal symmetrization, the full root and local structural lemmas, and
the applications of Vizing, Häggkvist--Janssen, and
Rohatgi--Urschel--Wellens are **not yet fully formalized**.  No placeholder
axiom or `sorry` is used to hide this boundary.  Accordingly, the Lean project
is not yet a kernel proof of the complete result.

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
