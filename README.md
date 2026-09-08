# Erdős Problem 81

This repository contains a proposed complete solution of [Erdős Problem
81](https://www.erdosproblems.com/81), together with a publication manuscript,
a Lean 4 formalization, and reproducible finite certificates.

For all sufficiently large `n`, the proposed result determines the exact
extremal value

```text
max cp(G) = floor(n(n + 1) / 6),
```

where the maximum is over all `n`-vertex chordal graphs and `cp(G)` is the
minimum number of cliques whose edge sets partition `E(G)`. In particular,
every chordal graph satisfies `cp(G) <= n²/6 + O(n)`.

The proof and its formalization are complete within the trust boundary below.
Because the result would resolve a long-standing open problem, it should be
treated as a proposed proof until it has received independent review by
specialists in extremal or probabilistic graph theory.

## Proof idea

The proof combines a global fractional argument with a local integral one.

1. Pack triangles and copies of `K₄` fractionally, with gains `2` and `5`.
   The `K₄` term pushes complete graphs below the extremal quadratic scale,
   leaving the complete-split family as the relevant terminal branch.
2. A vertex-copy inequality and discrete convexity produce a monotone path of
   single-vertex copies from any chordal graph to a complete-split graph.
3. Near the extremal complete-split family, root regularization and balanced
   edge-colouring construct an actual `K₂/K₃` partition with a strict saving
   for every missing spoke or outside edge. A first-entry argument transfers
   this local stability back along the copy path.
4. Away from the extremal family, a fixed quadratic deficit absorbs the
   subquadratic loss in fractional-to-integral packing transfer. A signed
   edge count on complete-split graphs supplies the matching lower bound.

The manuscript gives the conventional proof and explains the relation to
earlier complete-split and clone-copy work.

## Repository layout

- [`manuscript/main.tex`](manuscript/main.tex) is the paper source;
  [`manuscript/main.pdf`](manuscript/main.pdf) is the built review copy.
- [`lean/`](lean/) contains the pinned Lean 4 project and its verification
  gate.
- [`preparations/erdos81_stability_closure/`](preparations/erdos81_stability_closure/)
  contains the main exact finite certificates.
- [`preparations/erdos81_rigidity_addendum/`](preparations/erdos81_rigidity_addendum/)
  contains a separate rigidity addendum and its replayable certificates; it is
  not part of the Lean theorem perimeter.
- [`references/SOURCES.md`](references/SOURCES.md) records primary sources and
  immutable reference snapshots.
- [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) gives the
  detailed proof and formalization ledger.

## Lean theorem and trust boundary

The principal checked declarations are

```text
eventualSharpUpperBound_of_inputs :
  ExternalInputs.Inputs -> EventualSharpUpperBound

eventualSharpEquality_of_inputs :
  ExternalInputs.Inputs -> EventualSharpEquality

erdos81_of_inputs :
  ExternalInputs.Inputs -> Erdos81Statement
```

The complete-split lower bound and the passage from the eventual result to
`n²/6 + O(n)` are proved inside Lean. The conditional upper bound uses three
explicit interfaces:

1. Vizing's edge-colouring theorem;
2. the Häggkvist--Janssen list-edge-colouring bound for complete graphs;
3. the uniform finite-family packing transfer specialized to triangles and
   `K₄`.

The third interface packages the transfer conclusion with attained rational
primal and dual witnesses. These assumptions are theorem arguments, not Lean
axioms or hidden placeholders. The project therefore checks the complete
conditional reduction, but does not claim a self-contained kernel proof of
the three external interfaces.

`lean/check.sh` builds the project and performs a fail-closed environment
audit of every public `Erdos81.*` declaration. The only permitted transitive
kernel assumptions are `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce the checks

The dependency-free certificate replays need only Python 3:

```bash
make replay
```

For a first Lean build, install [elan](https://github.com/leanprover/elan) and
fetch the manifest-pinned Mathlib cache:

```bash
cd lean
lake exe cache get
./check.sh
```

Build the manuscript and reject unresolved references, citations, and box
overflow diagnostics with:

```bash
make -C manuscript clean check
```

From a prepared checkout, `make check` runs both certificate replays, the Lean
gate, and the manuscript check. The larger regeneration audits use the pinned
packages in `requirements-audit.txt` and can be run with `make audit` after
creating a virtual environment.

## Credits

The mathematical proof was developed by
[Morluto](https://github.com/morluto) ([X](https://x.com/morluto)), with GPT
assistance. [Jacobian](https://github.com/morluto/jacobian), a research tool
developed at Preference Labs, played a substantial role in the derivation and
verification workflow.

The manuscript and Lean 4 formalization were written by
[N0zoM1z0](https://github.com/N0zoM1z0/)
([X](https://x.com/r00tth3w0r1d)).

This is a Preference Labs research project.

## Publication status

Before submission, the anonymous author placeholder and affiliations should
be finalized, appropriate licences selected, the artifact archived at a
stable version, and independent specialist review obtained. Any public claim
about the Lean development should retain the conditional boundary stated
above.
