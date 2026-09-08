# Formalization status

Date: 2026-09-08

## Result

The conditional-proof formalization is **100% complete**. Lean proves

```text
Erdos81.eventualSharpUpperBound_of_inputs :
  Erdos81.ExternalInputs.Inputs -> Erdos81.EventualSharpUpperBound

Erdos81.erdos81_of_inputs :
  Erdos81.ExternalInputs.Inputs -> Erdos81.Erdos81Statement
```

`ExternalInputs.Inputs` consists of exactly three published results:

1. Vizing's `Delta + 1` edge-colouring theorem;
2. the Häggkvist--Janssen list-edge-colouring theorem for complete graphs;
3. the Rohatgi--Urschel--Wellens uniform finite-family packing-transfer
   theorem for the triangle/`K_4` gains used here.

These are ordinary hypotheses in the theorem statement. They are not Lean
axioms, `sorry` declarations, or opaque assumptions introduced inside a
proof. Formalizing or importing those three published theorems would be a
separate upstream project and is not included in the 100% figure.

## Manuscript-to-Lean ledger

“Checked” means Lean 4.31.0 compiled a proof with no project-specific axiom and
no `sorry`.

| Manuscript component | Principal Lean declaration/module | Status |
|---|---|---|
| Chordal graph and clique partitions | `Statement.lean` | Defined exactly |
| Erdős 81 and eventual sharp statements | `Erdos81Statement`, `EventualSharpUpperBound` | Defined exactly |
| Small-order edge partition and all-order reduction | `pairPartition`, `eventualSharpUpperBound_implies_erdos81` | Checked |
| Rational identities, margins, and near/far arithmetic | `Arithmetic.lean`, `SharpBound.lean` | Checked |
| Finite mixed LP and weak duality | `FiniteLP.lean`, `MixedModel.lean` | Checked |
| Integral packing/partition identity and attainment | `IntegralPacking.lean` | Checked |
| Integral-to-fractional embedding and `Phi <= cp_{<=3}` | `IntegralFractional.lean` | Checked |
| Vizing input | `ExternalInputs.VizingInput` | Exact external hypothesis |
| Häggkvist--Janssen input | `ExternalInputs.HaggkvistJanssenInput` | Exact external hypothesis |
| Uniform packing-transfer input | `ExternalInputs.PackingTransferInput` | Exact external hypothesis |
| Chordal separators, Dirac, and PEO characterization | `ChordalSeparator.lean`, `Dirac.lean`, `PEOExistence.lean` | Checked |
| Chordal edge and complement missing-pair bounds | `PEOExistence.edge_bound_of_chordal`, `complement_edge_bound_of_chordal` | Checked |
| Root edge decomposition and triangle completion | `RootedGraph.lean`, `TrianglePacking.lean` | Checked |
| Terminal host construction | `TerminalConstruction.lean`, `StrictTerminalBound.lean` | Checked |
| Root demotion, optimization, and strict regularization | `RootDemotion.lean`, `RootOptimization.lean`, `RootRegularization.lean` | Checked |
| Exact rooted defects as labelled edit distance | `RootDistance.edgeEditDistance_completeSplitGraph` | Checked |
| Clique-root extraction from split distance | `LocalRoot.exists_initialRoot` | Checked |
| Integer-scale local-root numerics | `LocalRootArithmetic.initialRoot_numerics` | Checked |
| Local strict and sharp partition bounds | `LocalRegularization.lean` | Checked |
| Vertex copying and chordality preservation | `Copying.lean`, `CopyCover.lean` | Checked |
| Complete-split terminal characterization | `TerminalCharacterization.isCompleteSplit_of_terminal` | Checked |
| Monotone terminating fine-copy path | `Symmetrization.exists_completeSplit_finePath` | Checked |
| Complete-split dual and branch analysis | `SplitDual.lean`, `CompleteSplitPotential.lean` | Checked |
| Split edit distance and one-copy movement | `EditDistance.lean`, `FirstEntryGraph.lean` | Checked |
| Local potential contraction | `LocalPotential.near_extremal_split_contraction` | Checked |
| Complete-split endpoint contraction | `LocalPotential.terminal_near_extremal_split_contraction` | Checked |
| Global first-entry stability | `GlobalStability.near_extremal_implies_close` | Checked |
| Near/far eventual sharp upper bound | `eventualSharpUpperBound_of_inputs` | Checked, conditional on the three inputs |
| Erdős Problem 81 | `erdos81_of_inputs` | Checked, conditional on the three inputs |

The separate rigidity addendum has exact Python certificate replays but is not
part of the theorem needed to resolve Erdős Problem 81 and is not included in
this 100% conditional-proof milestone.

## Trust boundary

The strongest checked conclusion is not merely an implication from an
unproved local lemma. It is the complete manuscript conclusion from a record
whose fields state the three named published results. Thus:

- all definitions and all new graph-theoretic, optimization, stability,
  symmetrization, and assembly arguments are inside the Lean kernel;
- the three published inputs remain visible in the type of the final theorem;
- the repository does not claim that those external papers have themselves
  been re-proved in Lean.

## Verification gate

From the repository root, run:

```bash
cd lean
lake update
lake exe cache get
./check.sh
```

`check.sh` rejects source lines declaring `axiom` or `sorry`, builds the whole
library, and runs `#print axioms` on the principal declarations, including the
two final theorems. The expected transitive assumptions are only
Lean/Mathlib's standard logical primitives:

```text
propext, Classical.choice, Quot.sound
```

The published assumptions do not appear in `#print axioms` because they are
explicit arguments to the final theorems rather than global axioms. Inspect
both `#check` and `#print axioms` when reviewing the trust boundary.
