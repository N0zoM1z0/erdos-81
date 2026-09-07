# Erdős 81: automatically hostable PEO batches

This archive contains finite induced-reduction results, exact code, and
current-run checks. It does **not** prove Erdős #81.

- `PROOF.md`: definitions, proofs, limitations, and the external list-colouring input.
- `batches.py`: PEO domains, elimination-forest oracle, exact small list colouring,
  all-clique recursion, signed objective encoding, conditional-expectation selection,
  and edge-edit certificate repair.
- `audit.py`: run with `python audit.py` (requires NetworkX).
- `audit_report.json`: actual counts from this run.
- `jacobian_margin_request.json`: complete signed induced-weight request.
- `jacobian_partition_request.json`: complete incident-edge partition request.
- `jacobian_results.json`: the returned verdict and exact extremum summary.
- `large_incident_witness.json`: a verified 546-part partition of the incident-edge
  graph for a 12-vertex batch in a 144-vertex graph. This is intentionally **not**
  a partition of the whole original graph; the induced remainder is untouched.

The reference PEO finder and optional PEO validation are not claimed linear.
The subtree score accumulation, given a valid PEO, is linear in n+e.
The bounded-domain exact optimizer and exact list-colouring search are exponential.
Conditional-expectation selection is a polynomial-time sufficient test, not an
exact optimum computation.
