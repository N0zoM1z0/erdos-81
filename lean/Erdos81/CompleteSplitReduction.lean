import Erdos81.CompleteSplitPotential
import Erdos81.ExternalInputs
import Erdos81.Symmetrization
import Mathlib.Tactic

/-!
# Quantitative output of fine symmetrization

This module joins the finite copying path to the complete-split calculation.
For any graph-by-graph family of certified mixed fractional optima, the
potential of a chordal graph is bounded by the terminal envelope.  In the
near-extremal case, the same path ends at a first-regime complete-split graph
whose root order satisfies the exact square stability estimate.
-/

namespace Erdos81
namespace CompleteSplitReduction

open SimpleGraph MixedModel ExternalInputs EditDistance Arithmetic
  Symmetrization CompleteSplitPotential TerminalCharacterization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Mathlib currently exposes the rational order both through its direct
`LE` instance and through the bundled preorder.  They reduce to the same
relation; this bridge keeps inequalities imported from the lexicographic
symmetrization module interoperable with ordinary rational arithmetic. -/
private theorem rat_preorder_le_iff_le (a b : ℚ) :
    @LE.le ℚ Rat.instPreorder.toLE a b ↔ @LE.le ℚ Rat.instLE a b := by
  rfl

/-- Fine symmetrization plus the terminal calculation gives the global
potential envelope for every chordal graph. -/
theorem chordal_certifiedPotential_le_Q
    (value : SimpleGraph V → ℚ)
    (hcert : ∀ H : SimpleGraph V, CertifiedFractionalOptimum H (value H))
    {G : SimpleGraph V} [Nonempty V] (hchordal : IsChordal G)
    (hn : 100 ≤ Fintype.card V) :
    certifiedPotential value G ≤ Q (Fintype.card V) := by
  obtain ⟨H, ⟨P⟩, ⟨K, rfl⟩⟩ :=
    exists_completeSplit_finePath value (fun J ↦ (hcert J).dual) hchordal
  have hpath := P.certifiedPotential_le
  have hend := potential_le_Q K (value (completeSplitGraph K))
    (hcert (completeSplitGraph K)).primal hn
  have hend' := (rat_preorder_le_iff_le _ _).mpr hend
  exact hpath.trans hend'

/-- Near-extremality propagates forward along the fine path and forces its
complete-split endpoint into the first regime. -/
theorem exists_stable_completeSplit_endpoint
    (value : SimpleGraph V → ℚ)
    (hcert : ∀ H : SimpleGraph V, CertifiedFractionalOptimum H (value H))
    {G : SimpleGraph V} [Nonempty V] (hchordal : IsChordal G)
    (hn : 100 ≤ Fintype.card V) (δ : ℚ)
    (hδnonneg : 0 ≤ δ) (hδ : δ ≤ 1 / 40)
    (hnear : Q (Fintype.card V) - δ * (Fintype.card V : ℚ) ^ 2 ≤
      certifiedPotential value G) :
    ∃ K : Finset V,
      Nonempty (FinePath value G (completeSplitGraph K)) ∧
      4 ≤ K.card ∧
      K.card - 1 ≤ (RootedGraph.outsideVertices K).card ∧
      (6 * (K.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1) ^ 2 ≤
        24 * δ * (Fintype.card V : ℚ) ^ 2 := by
  obtain ⟨H, hpathNonempty, ⟨K, hHK⟩⟩ :=
    exists_completeSplit_finePath value (fun J ↦ (hcert J).dual) hchordal
  subst H
  obtain ⟨P⟩ := hpathNonempty
  have hmono := P.certifiedPotential_le
  have hterminalNear :
      Q (Fintype.card V) - δ * (Fintype.card V : ℚ) ^ 2 ≤
        potential (completeSplitGraph K) (value (completeSplitGraph K)) := by
    have hterminalPreorder := hnear.trans hmono
    unfold certifiedPotential at hterminalPreorder
    exact (rat_preorder_le_iff_le _ _).mp hterminalPreorder
  have hstable := near_extremal_forces_firstRegime K
    (value (completeSplitGraph K)) δ
    (hcert (completeSplitGraph K)).primal hn hδnonneg hδ hterminalNear
  exact ⟨K, ⟨P⟩, hstable⟩

end CompleteSplitReduction
end Erdos81
