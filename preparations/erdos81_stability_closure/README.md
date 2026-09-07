# Erdős #81: local-to-global stability closure

`PROOF.md` gives a proposed complete proof that every sufficiently large chordal graph has an edge partition into at most floor(n(n+1)/6) cliques of orders 2, 3, and 4. It supplies one absolute constant for every order, defined via the fixed weighted-packing transfer threshold.

The new bridge has two parts:

* Strict root regularization gives a quantitative local edit-distance stability inequality.
* Full-class symmetrization can be executed through single-vertex moves that are all nondecreasing for the mixed fractional functional. A first-entry argument propagates local stability to every near-extremal chordal graph.

External inputs: Vizing's theorem, the Häggkvist–Janssen complete-graph list-edge-colouring theorem, and weighted finite-family fractional-to-integral packing transfer (Rohatgi–Urschel–Wellens, Theorem 3.4). Standard PEO/clique-tree facts are used. No general stability theorem or Delcourt–Postle decomposition theorem is invoked.

This is not a machine-verified proof and has not been independently peer-reviewed. The threshold from packing transfer is not numerically evaluated.

## Files

* `PROOF.md`: all constants, lemmas, the global stability argument, and every-order conclusion.
* `audit.py`: finite graph and exact-rational audit. Requires NetworkX, SciPy, NumPy, and SymPy. Floating solvers only supply candidates; exact rational primal and dual replay validates all reported LP optima.
* `mixed_lp_certificates.json`: 7,964 source-bound rational LP certificates.
* `paths.json`: monotone copying paths for all 531 nonempty chordal graphs through seven vertices.
* `replay.py`: dependency-free replay of all saved LP certificates and copying paths.
* `audit_report.json`, `replay_report.json`: exact audit counts and scope.
* `jacobian_lp_certificate.json`: independently returned exact mixed-cover seed optimum (380).
* `jacobian_partition_input.json`: a 12-vertex, 25-part incident-compatible terminal construction; checked by the local exact edge counter. Jacobian's partition calls failed at the network layer, so no successful remote partition check is claimed.
* `finite_partition_report.json`: the independent exact partition check.

Run the independent replay with:

    python replay.py

The finite audit is supporting evidence for the lemmas. It does not prove the asymptotic transfer theorem or substitute for review of `PROOF.md`.
