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
| Clique edge partition and block-size restriction | `Erdos81.CliquePartition` | Modeled exactly |
| Erdős Problem 81 statement | `Erdos81.Erdos81Statement` | Modeled exactly |
| Eventual `floor(n(n+1)/6)` upper bound | `Erdos81.EventualSharpUpperBound` | Modeled exactly |
| Edge-by-edge fallback partition | `Erdos81.pairPartition` | Checked |
| Eventual bound implies every-order Erdős 81 | `Erdos81.eventualSharpUpperBound_implies_erdos81` | Checked |
| Finite primal/dual weak duality | `Erdos81.FiniteLP.weak_duality` | Checked |
| Triangle/`K_4` mixed LP incidence and gains | `Erdos81.MixedModel` | Modeled exactly; weak duality checked |
| Strong duality and existence of an optimum | — | Pending (standard finite LP result) |
| Identity `cp_{<=4}=e-W_4` | — | Pending |
| Comparison `Phi <= cp_{<=3}` | — | Pending |
| Vizing edge colouring | — | External theorem; not yet imported/formalized |
| Häggkvist--Janssen list edge colouring | — | External theorem; not yet formalized |
| Rohatgi--Urschel--Wellens uniform transfer | — | External theorem; not yet formalized |
| Terminal host construction | — | Pending |
| Demotion/promotion numerical chain | `Erdos81.RootArithmetic` | Checked |
| Common-neighbor clique and nonadjacency degree bound | `Erdos81.Chordal.commonNeighbors_isClique_of_chordal`, `root_nonadjacency_degree_bound` | Checked |
| Full strict root-regularization lemma | — | Pending |
| Stability square identity and second-branch square identity | `Erdos81.Arithmetic` | Checked |
| Exact floor identity for `Q(n)` | `Erdos81.SharpBound.floor_Q_eq_sharpBound` | Checked |
| Local-deficit algebra and integer rounding | `Erdos81.LocalStability` | Checked |
| Local root extraction in edit distance | — | Pending |
| Orientation and edge count of opposite vertex copies | `Erdos81.Copying` | Checked |
| Simpliciality of the copied vertex | `Erdos81.Copying.simplicial_target_of_simplicial_source` | Checked |
| Chordality preservation under the required copy | `Erdos81.Copying.chordal_replaceVertex_of_simplicial_source` | Checked |
| Replacement-collapse homomorphism and clique-order preservation | `Erdos81.Copying.collapseHom`, `card_finset_image_of_isClique` | Checked |
| Feasible mixed-dual pullback through the replacement collapse | `Erdos81.CopyCover.pullbackCover` applied to `Copying.collapseHom` | Checked |
| Pulled-cover objective identity and full copy inequality | — | Pending |
| Copy-potential sign algebra | `Erdos81.DiscreteConvexity.potential_copy_inequality` | Checked |
| Discrete-convex endpoint propagation | `Erdos81.DiscreteConvexity` | Checked |
| Complete-split terminal characterization | — | Pending |
| Averaged complete-split two-variable dual | `Erdos81.SplitDual` | Algebraic LP checked; averaging pending |
| Terminal branch separation | `Erdos81.Arithmetic` | Checked |
| First-entry least-index barrier | `Erdos81.FirstEntry.barrier` | Checked |
| First-entry explicit numerical scale | `Erdos81.Arithmetic.first_entry_numerics`, `Erdos81.FirstEntry.inverse_order_lt_quarter_radius` | Checked |
| Far-case closing arithmetic | `Erdos81.Arithmetic.far_case_closure` | Checked |
| Full eventual sharp upper bound | — | Pending |
| Rigidity addendum | Python exact certificates only | Pending in Lean |

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
