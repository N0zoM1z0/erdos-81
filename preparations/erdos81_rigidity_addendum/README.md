# Rigidity and exact near-extremizer accounting

Read `PROOF.md` for the new addendum. `closure_PROOF.md` is the supplied main proof, unchanged; the global corollaries rely on its local-to-global closure. Neither has been independently refereed or formally verified.

The finite construction in `construct.py` needs no third-party package. It handles any graph satisfying `a+2m <= min(p,q-p)`, and returns an attaining clique partition and signed dual. `certify_near_extremizer` supplies a checkable canonical-root certificate.

Run `python replay.py` for dependency-free replay of the 94 saved partition and dual certificates. Run `python audit.py` for the larger audit; it requires NetworkX. No numerical optimizer is used.

`jacobian_partition_input.json` and `jacobian_dual_input.json` are the payloads used in successful live Jacobian checks. `jacobian_result_summary.json` records the returned mathematical verdicts.

The linear-window threshold is the original absolute N, which includes the independently supplied asymptotic weighted-packing threshold. No numerical evaluation of N is claimed.
