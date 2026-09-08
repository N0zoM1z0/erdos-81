# Lean formalization

This directory contains the Lean 4 companion to the Erdős Problem 81
manuscript. The toolchain and Mathlib revision are pinned locally, and the
formal project is self-contained under `lean/`.

The main declarations are

```text
eventualSharpUpperBound_of_inputs :
  ExternalInputs.Inputs -> EventualSharpUpperBound

eventualSharpEquality_of_inputs :
  ExternalInputs.Inputs -> EventualSharpEquality

erdos81_of_inputs :
  ExternalInputs.Inputs -> Erdos81Statement
```

The second theorem combines the conditional universal upper bound with an
internally proved complete-split lower witness, so it represents the exact
eventual extremal value rather than only its upper half.

## Checked proof perimeter

The final conditional theorem depends on kernel-checked developments for:

- chordal graphs, clique partitions, perfect-elimination orders, minimal
  separators, and Dirac's simplicial-vertex theorem;
- exact clique-partition counting and the mixed triangle/`K₄` packing model;
- the packing/partition objective identities and finite weak duality;
- vertex copying, copied-cover transport, discrete convexity, and a
  terminating monotone path to a complete-split graph;
- the complete-split dual calculation and separation of its three branches;
- labelled edit distance, first entry, root extraction, demotion/promotion,
  terminal construction, and all rational constant checks;
- the near/far assembly yielding `EventualSharpUpperBound`;
- the signed edge-count lower bound for complete-split graphs, its exact
  arithmetic maximization, and `EventualSharpEquality`;
- the reduction from the eventual bound to the all-order
  `n²/6 + O(n)` statement.

The implementation is theorem-equivalent to the manuscript but is not a
line-by-line transcription. In particular, the terminal characterization is
proved with minimal separators rather than clique trees, and termination uses
a finite lexicographic measure. The manuscript's auxiliary numerical path
bound `L <= n(n-1)` is not needed by the final theorem and is not formalized.
The separate rigidity addendum is outside this Lean perimeter.

See [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) for the
manuscript-to-Lean ledger.

## External interfaces

`ExternalInputs.Inputs` contains three explicit interfaces:

1. Vizing's `Δ + 1` edge-colouring theorem;
2. the Häggkvist--Janssen list-edge-colouring theorem for complete graphs;
3. uniform finite-family fractional-to-integral packing transfer for the
   triangle/`K₄` gains used here.

The third interface also supplies attained rational primal and dual witnesses
for each finite graph. This makes the finite LP optimality data used by the
proof explicit, but means the interface packages standard finite rational LP
attainment/strong duality together with the published transfer conclusion.

These interfaces occur as ordinary theorem arguments. They are not project
axioms or placeholders, but they have not been discharged inside this
repository. The result is therefore an end-to-end conditional formalization,
not a proof from Mathlib alone.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then run:

```bash
cd lean
lake exe cache get
./check.sh
```

`check.sh` first rejects common source forms of `axiom`, `sorry`, or `admit`,
builds the complete library, and then performs an environment-level audit of
every public declaration whose name and source module begin with `Erdos81`.
The audit fails on any transitive assumption outside this allowlist:

```text
propext, Classical.choice, Quot.sound
```

It also type-pins and prints the assumptions of all three public theorem
surfaces above. The external interfaces do not appear in `#print axioms`
because they are explicit parameters in the theorem types.
