# Verification status of the proposed solution to Erdős Problem 81

Date of this audit: 2026-09-07

## Executive conclusion

The file `preparations/erdos81_stability_closure/PROOF.md` contains a proposed
complete proof of Erdős Problem 81, conditional only on three published
external inputs that it states explicitly.  The proof establishes the stronger
eventual estimate

\[
  \operatorname{cp}_{\le 4}(G)
  \le \left\lfloor \frac{n(n+1)}6 \right\rfloor
\]

for every sufficiently large chordal graph \(G\) on \(n\) vertices.  The
individual-edge partition for the finitely many smaller orders then gives one
absolute constant \(C\) such that

\[
  \operatorname{cp}(G) \le \frac{n^2}{6}+Cn
\]

for every finite chordal graph.

The argument has been checked line by line in this repository audit, and both
supplied independent GPT-6-Pro reviews reached the same positive conclusion.
No unpaid case, circular threshold, or missing error term has been identified.
This is nevertheless a **proposed complete proof**, not yet a theorem validated
by an independent human specialist or by an end-to-end proof assistant.

## Authoritative sources

The authoritative mathematical source is
`preparations/erdos81_stability_closure/PROOF.md`.  It is byte-for-byte
identical to
`preparations/erdos81_rigidity_addendum/closure_PROOF.md` and has SHA-256

```text
db87bc1c20aca1b1e444e19e87695d40f141824f8ec1e1d0209abda29e150d47
```

The rigidity addendum is
`preparations/erdos81_rigidity_addendum/PROOF.md`.  The long `.txt` chat
exports are provenance records, not mathematical source files: their export
format dropped displayed equations.

The source archives have SHA-256 digests

```text
faf853b41fef9c68cda043e9b9810284186a9bc2c860af513f9718b5ce95a79b  erdos81_stability_closure.zip
a0796fa8c4e58baeb7dc8714d3db8a31e37174f1c6687d14c172d1bf87c656e9  erdos81_rigidity_addendum.zip
c9fafa5729c8d6c39e0542133e113908684a5e733d0c0f3ac7b53ba57be85e56  erdos81_elimination_batches.zip
```

The elimination-batch archive is historical exploratory work.  Its own proof
ledger expressly says that it does not solve the problem, and the final proof
does not depend on it.

## Logical dependency map

| Layer | Result | Status |
|---|---|---|
| Published input | Vizing's \(\Delta+1\) edge-colouring theorem | Standard published theorem |
| Published input | Häggkvist--Janssen: \(\chi'_{\ell}(K_p)\le p\) | Published theorem; the proof needs arbitrary lists of size \(p\) |
| Published input | Uniform finite-family fractional-to-integral packing transfer for triangle gain 2 and \(K_4\) gain 5 | Rohatgi--Urschel--Wellens, Theorem 3.4; uniform use is explicit in their proof of Theorem 3.6 |
| New local step | Integral terminal construction with strict savings in outside edges and missing incidences | Checked; every edge and every used spoke is accounted for |
| New local step | Root demotion/promotion at threshold \(7p/4\) | Checked; chordality makes every promoted vertex complete to the current root |
| New local step | Quantitative local stability in actual labelled edit distance | Checked; follows from the strict terminal estimate and the chordal edge bound |
| New global step | Mixed-functional copy inequality and a monotone path of single-vertex copies | Checked; the inequality direction is correct and every intermediate graph remains chordal |
| New global step | Complete-split terminal characterization and branch separation | Checked; the competing mixed-cover branches have fixed quadratic slack |
| New closure step | First entry into the local stability ball | Checked; one copy changes at most \(n-2\) pairs, producing the required contradiction |
| Final assembly | Near/far split, followed by the small-order edge partition | Checked; one fixed transfer threshold defines one absolute constant |

## Critical checks performed

1. In the terminal construction, a balanced proper \(c\)-edge-colouring of the
   outside graph has classes of size at most \(\lceil m/c\rceil\).  A random
   bijection of the \(p\) largest classes to root vertices loses at most
   \((\omega(H)-1)A/p\) edges in expectation, where \(A\) is the number of
   missing root--outside incidences.  The remaining root-edge host lists have
   the advertised size, so the Häggkvist--Janssen theorem applies.
2. Demoted root vertices contribute all their new outside edges to \(m_0\).
   The bounds \(m_0<p^2/400\), \(\bar D<p/3\), and \(h<p/693\) imply the final
   list margin.  No edit or partition is performed during root selection.
3. The mixed functional is
   \(\Phi(G)=e(G)-W_4^*(G)\).  The universally valid comparison used by the
   proof is \(\Phi(G)\le \operatorname{cp}_{\le3}(G)\), not
   \(\Phi(G)\le\operatorname{cp}(G)\).
4. Copying an optimal dual cover gives upper bounds for the copied packing
   optima.  Subtraction from the exact edge-count identity gives
   \(\Phi(G_{u\to v})+\Phi(G_{v\to u})\ge2\Phi(G)\), in the required direction.
5. Discrete convexity is used at single-vertex resolution.  Once a
   nondecreasing adjacent direction is selected, all remaining moves to that
   endpoint are nondecreasing.  The proof does not charge the total length of
   the symmetrization path.
6. The first-entry graph is simultaneously near the boundary of the fixed
   edit ball and subject to the local inequality.  The two quantitative bounds
   are incompatible for \(n\ge10^{32}\).
7. The transfer theorem is spent only in the case with a fixed quadratic
   deficit.  The proof never treats an \(o(n^2)\) error as an \(O(n)\) error.

## Reproduced computational evidence

The following checks were rerun locally on Python 3.11.2.

| Artifact | Reproduced result |
|---|---|
| Main dependency-free replay | PASS: 7,964 LP certificates, 14,134 positive packing entries, 36,743 triangle/\(K_4\) dual constraints, and 1,889 copy steps |
| Main full regeneration audit | PASS: 531 chordal atlas graphs, 5,394 two-direction copy checks, 1,889 monotone steps, 19,986 colour-count checks, and 711,246 terminal comparisons |
| Rigidity dependency-free replay | PASS: 94 partition certificates and 94,617 universal clique-type checks |
| Rigidity full audit | PASS: 1,643 instances, 3,286 partitions, and 815,824 replayed edge incidences |
| Historical elimination audit | PASS with a structurally identical report; it remains non-closing exploratory evidence |

The main regenerated certificate files were byte-for-byte identical to the
archived files; the report differed only in elapsed time.  The historical
elimination witness can differ in ordering or in the selected valid partition,
so it must be checked semantically rather than by generated-file equality.

These computations are regression tests and exact finite certificates.  They
do not prove the infinite theorem, the list-edge-colouring theorem, or the
asymptotic packing-transfer theorem.

## Corrections required before circulation

1. State \(p\ge1\) in the terminal construction.  Its formula divides by
   \(p\); every application already has \(p\ge128\).
2. Use a symbol such as \(A\) for missing root--outside incidences.  Do not use
   \(M\), which is also used for the extremal integer \(M(n)\).
3. State the two distinct inequalities involving \(\Phi\) explicitly:
   \(\Phi\le\operatorname{cp}_{\le3}\), and
   \(\Phi\ge\operatorname{cp}-(W_4^*-W_4)\).
4. State the uniform quantifiers in the packing-transfer input and define the
   threshold \(T(\varepsilon)\) before defining \(N\).
5. Cite the original Erdős--Ordman--Zalcstein paper, the earlier split-graph
   result, the two current partial claims, and the exact published sources of
   all external inputs.  Logical independence does not erase intellectual
   provenance.
6. Keep computational evidence in a separate verification section and do not
   describe finite enumeration as establishing the general theorem.

## Formalization decision

A conventional proof does not require Lean in order to be mathematically
valid.  For this particular result, however, comprehensive formalization is
strongly recommended because the proof is new, AI-assisted, quantitatively
delicate, and would resolve a long-standing open problem.

The staged project now lives entirely under `lean/` and builds with Lean
4.31.0 against a manifest-pinned Mathlib revision.  It currently checks the
exact graph-theoretic statement, a universal partition into edge-sized
cliques, the implication from the eventual sharp bound to the original
all-order assertion, the main rational identities and margins, finite LP weak
duality, the mixed triangle--four-clique incidence model, and the discrete
convexity mechanism behind single-vertex copying.  It also verifies the exact
two-direction copy edge count and solves the averaged complete-split dual LP,
including the three-branch formula.  Its check script rejects source-level
`axiom` and `sorry` declarations and prints the assumptions of the principal
theorems.

This is meaningful progress but not yet the first milestone below: the full
new chordal reduction has not all been expressed in Lean.  In particular, the
terminal construction, structural symmetrization lemmas, and copied-cover map
remain to be completed.  The project README states this boundary explicitly.

The work should be released in two accurately labelled milestones:

1. **Formalized new reduction.** Formalize all definitions and all new
   arguments, with the three external theorems passed as explicit hypotheses.
   This verifies the novel local-to-global closure but is not an end-to-end
   formal proof of Erdős 81.
2. **End-to-end formal theorem.** Import or formalize the external theorems and
   discharge those hypotheses.  Häggkvist--Janssen and the weighted packing
   transfer do not currently have an identified upstream Mathlib theorem in
   the required form; closing them is a substantial independent project.

A theorem can be sorry-free and have only foundational axioms while still
being conditional because assumptions may occur in its statement.  Every
release must therefore publish both `#check` output for the exact statement and
`#print axioms` output for the transitive proof dependencies.

## Release blockers

- Independent review by at least one human specialist in extremal or
  probabilistic graph theory.
- Final author names, affiliations, contribution statement, and corresponding
  author contact.
- A deliberate repository and manuscript licence selected by the authors.
- A stable public archive or DOI and a priority search updated on the release
  date.
- End-to-end Lean verification if the release is to claim a fully formal proof;
  otherwise the exact conditional formalization boundary must remain visible.
