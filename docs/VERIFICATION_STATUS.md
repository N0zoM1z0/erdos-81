# Verification status

Date: 2026-09-08

## Executive conclusion

The manuscript presents a proposed complete solution of Erdős Problem 81. It
proves the stronger eventual identity

\[
  \max_{\substack{|V(G)|=n\\G\text{ chordal}}}\operatorname{cp}(G)
  =\left\lfloor\frac{n(n+1)}6\right\rfloor
\]

and hence `cp(G) <= n²/6 + O(n)` for every finite chordal graph. No known gap
remains within the stated proof and trust boundary. Because this would resolve
a long-standing problem, the work remains a proposed proof pending independent
review by specialists in extremal or probabilistic graph theory.

The Lean companion checks the full conditional upper-bound reduction, the
matching complete-split lower witness, the eventual equality statement, and
the all-order Erdős 81 consequence. Three external interfaces remain explicit
parameters of the final theorems.

## Mathematical dependency map

| Layer | Result | Status |
|---|---|---|
| External | Vizing's `Δ + 1` edge-colouring theorem | Published theorem; explicit Lean input |
| External | Häggkvist--Janssen: `χ'ₗ(K_p) <= p` | Published theorem; explicit Lean input |
| External | Uniform finite-family transfer for triangle gain 2 and `K₄` gain 5 | Rohatgi--Urschel--Wellens specialization; explicit Lean input |
| Local | Terminal `K₂/K₃` construction with defect savings | Manuscript proof; Lean checked |
| Local | Root demotion/promotion and labelled stability | Manuscript proof; Lean checked |
| Global | Mixed-functional copy inequality and fine monotone path | Manuscript proof; Lean checked |
| Global | Complete-split terminal calculation and branch separation | Manuscript proof; Lean checked |
| Closure | First entry into the local stability ball | Manuscript proof; Lean checked |
| Assembly | Near/far eventual upper bound | Conditional on the three interfaces; Lean checked |
| Sharpness | Signed complete-split lower bound and integer maximization | Lean checked without additional inputs |
| Consequence | All-order `n²/6 + O(n)` bound | Lean checked |

The clone-copy, class interpolation, and complete-split terminal strategy are
credited in the manuscript to Traverso's Paper II. The present argument adapts
that method to the mixed triangle/`K₄` functional and adds the quantitative
local stability and fine first-entry mechanism needed for linear error.

## Critical proof checks

1. The terminal construction retains the `p` largest classes of a balanced
   proper edge-colouring, assigns them to root vertices, and accounts for all
   invalid hosts. The remaining root-edge lists satisfy the exact
   Häggkvist--Janssen hypothesis.
2. Root selection performs no graph edit. All edges created in the outside
   graph by demotion are included in the new defect count, and the numerical
   margins used for later promotion are exact rational inequalities.
3. The universally valid fractional comparison is
   `Phi(G) <= cp_{<=3}(G)`, not `Phi(G) <= cp(G)`.
4. Pulling back dual covers through opposite vertex copies gives the copy
   inequality in the required direction. Every recorded single-vertex copy
   preserves chordality and changes at most `n-2` pairs.
5. The argument does not charge total copy-path length. It uses the first
   path vertex entering a fixed edit ball, where the one-step lower bound and
   local contraction are incompatible.
6. The general transfer theorem is used only in the far case, where a fixed
   quadratic deficit absorbs its subquadratic error.
7. On a complete-split witness, root edges have signed weight `-1` and spokes
   weight `+1`; every clique has total weight at most one. This proves the
   matching lower bound for arbitrary clique sizes, not merely blocks of
   order at most four.

## Reproducible evidence

The dependency-free replay commands are:

```bash
python3 preparations/erdos81_stability_closure/replay.py
python3 preparations/erdos81_rigidity_addendum/replay.py
```

Current tracked reports record:

| Artifact | Result |
|---|---|
| Main replay | PASS: 7,964 LP certificates and 1,889 copy steps |
| Main regeneration audit | PASS: 531 chordal atlas graphs, 5,394 two-direction copy checks, 19,986 colour checks, and 711,246 terminal comparisons |
| Rigidity replay | PASS: 94 partition certificates, one negative size-cap test, and 94,617 clique-type checks |
| Rigidity regeneration audit | PASS: 1,643 instances, 3,286 partitions, and 815,824 edge incidences |

These are exact finite regression tests. They are not premises for the
infinite theorem or replacements for the three external interfaces.

The rigidity verifier now enforces each certificate's declared maximum block
size. Its negative control deliberately presents a `K₄` block under a cap of
three and requires rejection.

## Lean boundary and gate

The principal theorem surfaces are:

```text
eventualSharpUpperBound_of_inputs :
  ExternalInputs.Inputs -> EventualSharpUpperBound

eventualSharpEquality_of_inputs :
  ExternalInputs.Inputs -> EventualSharpEquality

erdos81_of_inputs :
  ExternalInputs.Inputs -> Erdos81Statement
```

The packing-transfer field bundles attained rational primal/dual witnesses
with the uniform transfer gap. Thus the formal boundary includes standard
finite rational LP attainment/strong duality in addition to the published
asymptotic transfer conclusion; this is why the documentation calls the
fields three interfaces rather than simply three formalized published
theorems.

Run the gate with:

```bash
cd lean
lake exe cache get
./check.sh
```

The gate builds the project, type-pins the public theorem surfaces, and audits
every public declaration whose name and source module begin with `Erdos81`.
It fails on any transitive axiom outside `propext`, `Classical.choice`, and
`Quot.sound`, and has a fast guard for common source forms of `axiom`,
`sorry`, and `admit`.

The formal proof architecture differs from the prose in two documented ways:
the terminal characterization uses minimal separators rather than clique
trees, and path termination uses a finite lexicographic measure. The unused
manuscript estimate `L <= n(n-1)` is not separately formalized. The rigidity
addendum is also outside the Lean theorem perimeter.

## Corrections incorporated in this revision

- The rigidity replay now enforces the advertised block-size cap and includes
  a failing negative control.
- The Lean check is fail-closed rather than relying on displayed
  `#print axioms` output.
- The complete-split matching lower bound and eventual equality are now
  explicit Lean theorems.
- The manuscript now gives paper-specific attribution for earlier clone-copy
  symmetrization, explains the role of the mixed `K₄` term, records the RUW
  weight specialization, and fixes the neighborhood notation in the
  nonadjacency lemma.
- The formalization ledger now distinguishes theorem interfaces from
  internally proved claims and records the alternate proof architecture.

## Before publication

- Obtain independent review from at least one relevant graph-theory
  specialist.
- Finalize author names, affiliations, and corresponding-author information.
- Select explicit repository and manuscript licences.
- Archive a stable release and update the priority search at submission time.
- Keep the three-interface conditional boundary prominent unless those inputs
  are later formalized or imported.
