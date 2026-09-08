import Erdos81.CompleteSplitReduction
import Erdos81.FirstEntryGraph
import Erdos81.LocalPotential

/-!
# Global stability by first entry

The monotone fine-copy path ends at a complete-split graph.  Near-extremality
puts that endpoint inside the contracted radius, while local potential
stability contracts every path graph that enters the radius.  The checked
first-entry barrier then forces the original graph inside half the radius.
-/

namespace Erdos81
namespace GlobalStability

open EditDistance MixedModel Symmetrization

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Mathlib's direct and bundled rational orders are definitionally the same;
this bridge makes the order chosen by the lexicographic path explicit. -/
private theorem rat_preorder_le_iff_le (a b : ℚ) :
    @LE.le ℚ Rat.instPreorder.toLE a b ↔ @LE.le ℚ Rat.instLE a b := by
  rfl

/-- The graph potential does not depend on which proof supplies decidable
adjacency; this bridges the classical instance stored by `certifiedPotential`
to a caller's local instance. -/
private theorem certifiedPotential_eq_potential
    (value : SimpleGraph V → ℚ) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    certifiedPotential value G = potential G (value G) := by
  unfold certifiedPotential potential
  congr 1

/-- The manuscript's fixed-neighbourhood global stability theorem. -/
theorem near_extremal_implies_close
    (value : SimpleGraph V → ℚ)
    (hcert : ∀ H : SimpleGraph V,
      ExternalInputs.CertifiedFractionalOptimum H (value H))
    (hv : ExternalInputs.VizingInput)
    (hHJ : ExternalInputs.HaggkvistJanssenInput)
    {G : SimpleGraph V} [Nonempty V]
    (hchordal : IsChordal G)
    (hlarge : 10 ^ 32 ≤ Fintype.card V)
    (hnear : (Fintype.card V : ℚ) ^ 2 / 6 -
        (Fintype.card V : ℚ) ^ 2 / (10 : ℚ) ^ 30 ≤
      certifiedPotential value G) :
    FirstEntryGraph.normalizedSplitDistance G <
      ((1 : ℚ) / 10 ^ 12) / 2 := by
  classical
  let n : ℚ := Fintype.card V
  have hlargeQ : (10 : ℚ) ^ 32 ≤ n := by
    dsimp only [n]
    exact_mod_cast hlarge
  have hnearQ : Arithmetic.Q n - 2 * n ^ 2 / (10 : ℚ) ^ 30 ≤
      certifiedPotential value G := by
    exact (Arithmetic.Q_sub_two_eta_le_near_threshold hlargeQ).trans
      (by simpa only [n] using hnear)
  obtain ⟨H, ⟨P⟩, ⟨K, rfl⟩⟩ :=
    exists_completeSplit_finePath value (fun J ↦ (hcert J).dual) hchordal
  have hterminalPreorder := hnearQ.trans P.certifiedPotential_le
  have hterminalNear :
      Arithmetic.Q (Fintype.card V : ℚ) -
          2 * (Fintype.card V : ℚ) ^ 2 / (10 : ℚ) ^ 30 ≤
        potential (completeSplitGraph K) (value (completeSplitGraph K)) := by
    have hterminalOrd := (rat_preorder_le_iff_le _ _).mp
      (by simpa only [n] using hterminalPreorder)
    rwa [certifiedPotential_eq_potential] at hterminalOrd
  have hterminalContracted :=
    LocalPotential.terminal_near_extremal_split_contraction K hlarge
      (hcert (completeSplitGraph K)).primal hterminalNear
  have hend : FirstEntryGraph.normalizedSplitDistance (P.graph P.length) <
      ((1 : ℚ) / 10 ^ 12) / 2 := by
    rw [P.finish]
    exact hterminalContracted.trans (by norm_num)
  have hcopy : ∀ i : ℕ, i < P.length →
      ∃ a b : V, a ≠ b ∧ ¬(P.graph i).Adj a b ∧
        P.graph (i + 1) = (P.graph i).replaceVertex a b :=
    fun i hi ↦ P.copy_step i hi
  have hlocal : ∀ i : ℕ, i ≤ P.length →
      FirstEntryGraph.normalizedSplitDistance (P.graph i) <
        (1 : ℚ) / 10 ^ 12 →
      FirstEntryGraph.normalizedSplitDistance (P.graph i) <
        ((1 : ℚ) / 10 ^ 12) / 4 := by
    intro i hi hclose
    have hpathPreorder := hnearQ.trans (P.certifiedPotential_le_at i hi)
    have hpathNear :
        Arithmetic.Q (Fintype.card V : ℚ) -
            2 * (Fintype.card V : ℚ) ^ 2 / (10 : ℚ) ^ 30 ≤
          potential (P.graph i) (value (P.graph i)) := by
      have hpathOrd := (rat_preorder_le_iff_le _ _).mp
        (by simpa only [n] using hpathPreorder)
      rwa [certifiedPotential_eq_potential] at hpathOrd
    exact LocalPotential.near_extremal_split_contraction
      hv hHJ (P.chordal_at hchordal i hi) hlarge
      (hcert (P.graph i)).primal hpathNear hclose
  have hbarrier := FirstEntryGraph.copyPath_barrier_at_manuscript_scale
    P.graph P.length hlarge hend hcopy hlocal
  simpa only [P.start] using hbarrier

end GlobalStability
end Erdos81
