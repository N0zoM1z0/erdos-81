import Erdos81.EditDistance
import Erdos81.FirstEntry

/-!
# First entry along a graph-copy path

This module connects the abstract least-index barrier to the actual labelled
complete-split edit distance and to paths whose steps are Mathlib vertex
replacements.  It includes the manuscript's explicit values
`rho = 10^-12` and `n >= 10^32`.
-/

namespace Erdos81
namespace FirstEntryGraph

open EditDistance

theorem normalized_movement_of_dist_le {a b n : ℕ} (hn : 0 < n)
    (h : Nat.dist a b ≤ n - 2) :
    (a : ℚ) / (n : ℚ) ^ 2 - 1 / (n : ℚ) ≤
      (b : ℚ) / (n : ℚ) ^ 2 := by
  have hdist : a ≤ Nat.dist a b + b := Nat.dist_tri_left' a b
  have hab : a ≤ n + b := by omega
  have habQ : (a : ℚ) ≤ (n : ℚ) + (b : ℚ) := by exact_mod_cast hab
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  field_simp [ne_of_gt hnQ]
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Split edit distance normalized by the square of the graph order. -/
noncomputable def normalizedSplitDistance (G : SimpleGraph V) : ℚ :=
  (splitEditDistance G : ℚ) / (Fintype.card V : ℚ) ^ 2

/--
The abstract first-entry barrier instantiated on a path of legal single-vertex
copies and the actual complete-split edit distance.
-/
theorem copyPath_barrier
    (graphs : ℕ → SimpleGraph V) (L : ℕ) (rho : ℚ)
    (hcard : 0 < Fintype.card V) (hrho : 0 < rho)
    (hstepSmall : 1 / (Fintype.card V : ℚ) < rho / 4)
    (hend : normalizedSplitDistance (graphs L) < rho / 2)
    (hcopy : ∀ i : ℕ, i < L →
      ∃ a b : V, a ≠ b ∧ ¬(graphs i).Adj a b ∧
        graphs (i + 1) = (graphs i).replaceVertex a b)
    (hlocal : ∀ i : ℕ, i ≤ L →
      normalizedSplitDistance (graphs i) < rho →
      normalizedSplitDistance (graphs i) < rho / 4) :
    normalizedSplitDistance (graphs 0) < rho / 2 := by
  apply FirstEntry.barrier
    (distance := fun i ↦ normalizedSplitDistance (graphs i))
    (L := L) (rho := rho) (step := 1 / (Fintype.card V : ℚ))
    hrho hstepSmall hend
  · intro i hi
    obtain ⟨a, b, hab, hnab, hnext⟩ := hcopy i hi
    have hdist := splitEditDistance_replaceVertex_dist_le (graphs i) hab hnab
    rw [hnext]
    exact normalized_movement_of_dist_le hcard hdist
  · exact hlocal

/-- The graph-path barrier with the numerical scale fixed in the manuscript. -/
theorem copyPath_barrier_at_manuscript_scale
    (graphs : ℕ → SimpleGraph V) (L : ℕ)
    (hlarge : 10 ^ 32 ≤ Fintype.card V)
    (hend : normalizedSplitDistance (graphs L) < ((1 : ℚ) / 10 ^ 12) / 2)
    (hcopy : ∀ i : ℕ, i < L →
      ∃ a b : V, a ≠ b ∧ ¬(graphs i).Adj a b ∧
        graphs (i + 1) = (graphs i).replaceVertex a b)
    (hlocal : ∀ i : ℕ, i ≤ L →
      normalizedSplitDistance (graphs i) < (1 : ℚ) / 10 ^ 12 →
      normalizedSplitDistance (graphs i) < ((1 : ℚ) / 10 ^ 12) / 4) :
    normalizedSplitDistance (graphs 0) < ((1 : ℚ) / 10 ^ 12) / 2 := by
  have hcard : 0 < Fintype.card V := by omega
  have hlargeQ : (10 : ℚ) ^ 32 ≤ (Fintype.card V : ℚ) := by
    exact_mod_cast hlarge
  exact copyPath_barrier graphs L ((1 : ℚ) / 10 ^ 12) hcard (by positivity)
    (FirstEntry.inverse_order_lt_quarter_radius hlargeQ) hend hcopy hlocal

end FirstEntryGraph
end Erdos81
