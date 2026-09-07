# Formalization status

Date: 2026-09-07

This ledger maps the mathematical manuscript to the Lean project.  “Checked”
means Lean has compiled a proof with no project-specific axiom and no `sorry`.
“Modeled” means the exact objects or proposition have been defined, but the
manuscript theorem about them is not yet proved.  “Pending” and “external” are
not included in the transitive proof of any claimed end-to-end Lean theorem,
because no such theorem is claimed yet.

| Manuscript component | Lean declaration/module | Status |
|---|---|---|
| Chordal graph (no induced `C_k`, `k >= 4`) | `Erdos81.IsChordal` | Modeled exactly |
| Chordality is hereditary under induced subgraphs | `Erdos81.Chordal.induce_isChordal` | Checked |
| Shortest paths have no nonconsecutive chord | `Erdos81.ChordalWalk.geodesic_not_adj_of_gap` | Checked |
| Two separated chordless arcs induce a cycle | `Erdos81.ChordalWalk.inducedCycleEmbedding_of_two_arcs` | Checked |
| Clique edge partition and block-size restriction | `Erdos81.CliquePartition` | Modeled exactly |
| Erdős Problem 81 statement | `Erdos81.Erdos81Statement` | Modeled exactly |
| Eventual `floor(n(n+1)/6)` upper bound | `Erdos81.EventualSharpUpperBound` | Modeled exactly |
| Edge-by-edge fallback partition | `Erdos81.pairPartition` | Checked |
| Eventual bound implies every-order Erdős 81 | `Erdos81.eventualSharpUpperBound_implies_erdos81` | Checked |
| Finite primal/dual weak duality | `Erdos81.FiniteLP.weak_duality` | Checked |
| Triangle/`K_4` mixed LP incidence and gains | `Erdos81.MixedModel` | Modeled exactly; weak duality checked |
| Strong duality and existence of an optimum | — | Pending (standard finite LP result) |
| Clique-partition edge double count | `Erdos81.CliquePartitionCounting.sum_choose_eq_card_edges` | Checked |
| Packing-to-partition and partition-to-packing constructions | `Erdos81.IntegralPacking.toCliquePartition`, `ofCliquePartition` | Checked |
| Identity `cp_{<=4}=e-W_4` for attained extrema | `Erdos81.IntegralPacking.isIntegralOptimum_iff_isRestrictedPartitionMinimum` | Checked |
| Attainment of the integral maximum and restricted partition minimum | `Erdos81.IntegralPacking.exists_integralOptimum_and_restrictedPartitionMinimum` | Checked |
| Integral packing embeds in the mixed fractional LP with equal objective | `Erdos81.IntegralFractional.toFractional`, `packingValue_toFractional` | Checked |
| Comparison `Phi <= cp_{<=3}` | `Erdos81.IntegralFractional.potential_le_size_of_orderAtMost_three` | Checked conditional on a certified fractional primal optimum |
| Vizing edge colouring | — | External theorem; not yet imported/formalized |
| Häggkvist--Janssen list edge colouring | — | External theorem; not yet formalized |
| Rohatgi--Urschel--Wellens uniform transfer | — | External theorem; not yet formalized |
| Terminal host construction | — | Pending |
| Demotion/promotion numerical chain | `Erdos81.RootArithmetic` | Checked |
| Common-neighbor clique and nonadjacency degree bound | `Erdos81.Chordal.commonNeighbors_isClique_of_chordal`, `root_nonadjacency_degree_bound` | Checked |
| Minimal separators of chordal graphs are cliques | `Erdos81.ChordalSeparator.minimal_separator_isClique` | Checked from the induced-cycle definition |
| Strong finite Dirac simplicial-vertex theorem | `Erdos81.Dirac.complete_or_two_simplicial` | Checked |
| Perfect-elimination ordering conditions | `Erdos81.PerfectElimination.IsPEO`, `HasPEO` | Modeled exactly for a fixed order and label-independently |
| PEO implies the forbidden-induced-cycle definition of chordality | `Erdos81.PerfectElimination.isChordal_of_peo`, `isChordal_of_hasPEO` | Checked |
| Every finite chordal graph admits a PEO | `Erdos81.PEOExistence.hasPEO_of_chordal` | Checked |
| Chordal iff PEO | `Erdos81.PEOExistence.isChordal_iff_hasPEO` | Checked |
| A PEO can be chosen to end in a prescribed clique | `Erdos81.PEOExistence.exists_elimination_list_ending_clique` | Checked |
| Edge count from chordality and a clique-order bound | `Erdos81.PEOExistence.edge_bound_of_chordal` | Checked |
| Missing-pair consequence `e(complement G) >= choose(n-p+1,2)` | `Erdos81.PEOExistence.complement_edge_bound_of_chordal` | Checked directly from chordality |
| Full strict root-regularization lemma | — | Pending |
| Stability square identity and second-branch square identity | `Erdos81.Arithmetic` | Checked |
| Exact floor identity for `Q(n)` | `Erdos81.SharpBound.floor_Q_eq_sharpBound` | Checked |
| Local-deficit algebra and integer rounding | `Erdos81.LocalStability` | Checked |
| Labelled edge-edit distance and triangle inequality | `Erdos81.EditDistance.edgeEditDistance_triangle` | Checked |
| Distance to the `floor(n/3)` complete-split family | `Erdos81.EditDistance.splitEditDistance` | Modeled exactly; minimum attainment checked |
| A single vertex copy changes split distance by at most `n-2` | `Erdos81.EditDistance.splitEditDistance_replaceVertex_dist_le` | Checked |
| Local root extraction in edit distance | — | Pending |
| Orientation and edge count of opposite vertex copies | `Erdos81.Copying` | Checked |
| Simpliciality of the copied vertex | `Erdos81.Copying.simplicial_target_of_simplicial_source` | Checked |
| Chordality preservation under the required copy | `Erdos81.Copying.chordal_replaceVertex_of_simplicial_source` | Checked |
| Replacement-collapse homomorphism and clique-order preservation | `Erdos81.Copying.collapseHom`, `card_finset_image_of_isClique` | Checked |
| Feasible mixed-dual pullback through the replacement collapse | `Erdos81.CopyCover.pullbackCover` applied to `Copying.collapseHom` | Checked |
| Opposite pulled-cover objective identity | `Erdos81.CopyCover.coverValue_opposite_pullbacks` | Checked |
| Mixed-potential copy inequality | `Erdos81.CopyCover.potential_opposite_copy_inequality` | Checked for certified dual optima; their general existence remains pending with finite LP duality |
| Copy-potential sign algebra | `Erdos81.DiscreteConvexity.potential_copy_inequality` | Checked |
| Discrete-convex endpoint propagation | `Erdos81.DiscreteConvexity` | Checked |
| Complete-split terminal characterization | — | Pending |
| Averaged complete-split two-variable dual | `Erdos81.SplitDual` | Algebraic LP checked; averaging pending |
| Terminal branch separation | `Erdos81.Arithmetic` | Checked |
| First-entry least-index barrier | `Erdos81.FirstEntry.barrier` | Checked |
| First-entry explicit numerical scale | `Erdos81.Arithmetic.first_entry_numerics`, `Erdos81.FirstEntry.inverse_order_lt_quarter_radius` | Checked |
| First-entry barrier instantiated on a legal graph-copy path | `Erdos81.FirstEntryGraph.copyPath_barrier_at_manuscript_scale` | Checked, conditional on the separately tracked path endpoint and local-stability hypotheses |
| Far-case closing arithmetic | `Erdos81.Arithmetic.far_case_closure` | Checked |
| Full eventual sharp upper bound | — | Pending |
| Rigidity addendum | Python exact certificates only | Pending in Lean |

## Progress estimate

The current engineering estimate is **60% of the local conditional-proof
formalization**.  This percentage is a weighted dependency-block estimate,
not a theorem and not a count of source lines.  It excludes proofs of the
three published external inputs: those remain separate projects and will be
represented by explicit hypotheses at the first end-to-end milestone.

| Dependency block | Weight | Checked contribution |
|---|---:|---:|
| Statements, fallback partition, floor and numerical arithmetic | 10 | 10 |
| Chordal infrastructure: induced cycles, separators, Dirac, and PEOs | 15 | 15 |
| Mixed LP, integral identity, and the `Phi <= cp_{<=3}` interface | 15 | 12 |
| Copying, edit distance, discrete convexity, and first-entry kernel | 18 | 13 |
| Terminal construction and strict root regularization | 18 | 4 |
| Local/terminal stability and complete-split analysis | 14 | 4 |
| Full symmetrization and final conditional assembly | 10 | 2 |
| **Total** | **100** | **60** |

The unearned portions correspond to named pending rows in the ledger above.
Reaching 100% on this metric will mean a sorry-free theorem deriving
`EventualSharpUpperBound` from explicit statements of Vizing,
Häggkvist--Janssen, and the finite-family transfer theorem.  It will still not
mean that those three external results themselves have been proved in Lean.

## Honest theorem boundary

The strongest graph-theoretic implication currently proved in Lean is

```text
EventualSharpUpperBound -> Erdos81Statement
```

The antecedent is not yet proved in Lean.  Consequently, this repository must
not be advertised as containing a complete formal proof of Erdős Problem 81.
The conventional manuscript is complete subject to its three published
inputs; the Lean project currently verifies a growing set of its delicate
subarguments.

## Verification gate

Run:

```bash
cd lean
./check.sh
```

The script first rejects source lines declaring `axiom` or `sorry`, then builds
all modules and prints the transitive assumptions of representative theorems.
The source tree intentionally contains no theorem whose proof is merely an
unproved manuscript hypothesis packaged as a project axiom.
