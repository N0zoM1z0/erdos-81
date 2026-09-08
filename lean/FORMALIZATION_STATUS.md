# Formalization status

Date: 2026-09-08

## Result

The Lean project checks the complete conditional proof perimeter declared by
the following theorem surfaces:

```text
Erdos81.eventualSharpUpperBound_of_inputs :
  Erdos81.ExternalInputs.Inputs -> Erdos81.EventualSharpUpperBound

Erdos81.eventualSharpEquality_of_inputs :
  Erdos81.ExternalInputs.Inputs -> Erdos81.EventualSharpEquality

Erdos81.erdos81_of_inputs :
  Erdos81.ExternalInputs.Inputs -> Erdos81.Erdos81Statement
```

`EventualSharpEquality` states both sides of the extremal result: every large
chordal graph has a partition with at most `sharpBound n` blocks, and for each
large `n` a chordal graph exists whose every clique partition has at least
that many blocks.

## Manuscript-to-Lean ledger

“Checked” means accepted by Lean 4.31.0 with no project axiom or `sorry`.

| Mathematical component | Principal declaration or module | Status |
|---|---|---|
| Chordal graph, clique partition, and theorem statements | `Statement.lean` | Defined |
| Exact floor and numerical identities | `Arithmetic.lean`, `SharpBound.lean` | Checked |
| Chordal separators, Dirac, and PEO equivalence | `ChordalSeparator.lean`, `Dirac.lean`, `PEOExistence.lean` | Checked |
| Chordal edge and complement bounds | `PEOExistence.edge_bound_of_chordal`, `complement_edge_bound_of_chordal` | Checked |
| Finite mixed LP and weak duality | `FiniteLP.lean`, `MixedModel.lean` | Checked |
| Clique-partition incidence counts | `CliquePartitionCounting.lean` | Checked |
| Integral packing/partition identity and finite extrema | `IntegralPacking.lean` | Checked |
| Integral-to-fractional comparison | `IntegralFractional.lean` | Checked |
| Root decomposition and terminal triangle construction | `RootedGraph.lean`, `TerminalConstruction.lean`, `StrictTerminalBound.lean` | Checked |
| Root demotion, optimization, and regularization | `RootDemotion.lean`, `RootOptimization.lean`, `RootRegularization.lean` | Checked |
| Edit-distance root extraction and local numerics | `RootDistance.lean`, `LocalRoot.lean`, `LocalRootArithmetic.lean` | Checked |
| Local partition bound and potential contraction | `LocalRegularization.lean`, `LocalPotential.lean` | Checked |
| Vertex-copy graph and cover transport | `Copying.lean`, `CopyCover.lean` | Checked |
| Discrete convexity and terminal characterization | `DiscreteConvexity.lean`, `TerminalCharacterization.lean` | Checked |
| Monotone fine-copy path | `Symmetrization.exists_completeSplit_finePath` | Checked |
| Complete-split dual and branch calculation | `SplitDual.lean`, `CompleteSplitPotential.lean` | Checked |
| One-copy movement and first-entry barrier | `FirstEntry.lean`, `FirstEntryGraph.lean` | Checked |
| Global stability | `GlobalStability.near_extremal_implies_close` | Checked |
| Conditional eventual upper bound | `eventualSharpUpperBound_of_inputs` | Checked |
| Complete-split matching lower bound | `CompleteSplitLowerBound.partition_size_ge`, `exists_completeSplit_sharp_lower_bound` | Checked |
| Conditional exact eventual extremal value | `eventualSharpEquality_of_inputs` | Checked |
| All-order Erdős 81 consequence | `erdos81_of_inputs` | Checked |

## Trust boundary

The proof takes `ExternalInputs.Inputs`, a record with three fields:

- `VizingInput` and `HaggkvistJanssenInput` state the two edge-colouring
  results used by the terminal construction.
- `PackingTransferInput` states the uniform subquadratic integral--fractional
  gap and returns certified rational primal/dual optima plus an attained
  integral optimum for every graph in the relevant finite family.

The packing interface is deliberately stronger than a bare asymptotic
transfer statement: it bundles finite rational LP attainment/strong duality
with the published transfer. Lean proves weak duality and the downstream
comparison, but does not independently derive the supplied primal/dual
optimality witnesses. Accordingly, these are best described as three
external interfaces, not literally as three already-formalized papers.

The following items are outside the checked theorem perimeter:

- proofs of the three external interfaces themselves;
- the manuscript's unused auxiliary bound `L <= n(n-1)` on copy-path length;
- the separate rigidity addendum and its linear-window classification, which
  currently have exact Python certificate replay rather than Lean proofs.

## Verification gate

Run:

```bash
cd lean
lake exe cache get
./check.sh
```

The gate builds the library and audits every public `Erdos81.*` declaration
against an explicit transitive-axiom allowlist. It also rejects source
occurrences of `axiom`, `sorry`, and `admit`. The permitted kernel primitives
are:

```text
propext, Classical.choice, Quot.sound
```

Because the external interfaces are explicit parameters rather than global
axioms, review must inspect the theorem types as well as their axiom output.
