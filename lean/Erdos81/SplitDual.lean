import Mathlib.Tactic

/-!
# The mixed dual on complete-split graphs

After averaging over automorphisms, a mixed fractional cover of a
complete-split graph has one price `x` on clique-side edges and one price `y`
on spokes.  This file proves the resulting two-variable LP exactly.
-/

namespace Erdos81
namespace SplitDual

/-- The four nonredundant constraints of the averaged dual. -/
structure Feasible (x y : ℚ) : Prop where
  rootEdge : (5 : ℚ) / 6 ≤ x
  spoke : 0 ≤ y
  rootOutsideTriangle : 2 ≤ x + 2 * y
  mixedFourClique : (5 : ℚ) / 3 ≤ x + y

/-- Objective with `A` clique-side edges and `B` spokes. -/
def objective (A B x y : ℚ) : ℚ :=
  A * x + B * y

/-- The three candidate objective values from the lower boundary. -/
def minimumValue (A B : ℚ) : ℚ :=
  min (2 * A) (min ((4 * A + B) / 3) (5 * (A + B) / 6))

theorem feasible_two_zero : Feasible 2 0 := by
  constructor <;> norm_num

theorem feasible_four_thirds_one_third : Feasible (4 / 3) (1 / 3) := by
  constructor <;> norm_num

theorem feasible_five_sixths : Feasible (5 / 6) (5 / 6) := by
  constructor <;> norm_num

/-- Every feasible averaged cover has at least the claimed minimum value. -/
theorem minimumValue_le_objective {A B x y : ℚ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hxy : Feasible x y) :
    minimumValue A B ≤ objective A B x y := by
  by_cases hBA : B ≤ A
  · have hAB : 0 ≤ A - B := sub_nonneg.mpr hBA
    have hroot := mul_le_mul_of_nonneg_left hxy.rootEdge hAB
    have hmixed := mul_le_mul_of_nonneg_left hxy.mixedFourClique hB
    have hcandidate : 5 * (A + B) / 6 ≤ objective A B x y := by
      simp only [objective]
      nlinarith
    exact (min_le_right _ _).trans ((min_le_right _ _).trans hcandidate)
  · have hAB : A ≤ B := le_of_not_ge hBA
    by_cases h2AB : 2 * A ≤ B
    · have hextra : 0 ≤ B - 2 * A := sub_nonneg.mpr h2AB
      have htriangle := mul_le_mul_of_nonneg_left hxy.rootOutsideTriangle hA
      have hspoke := mul_nonneg hextra hxy.spoke
      have hcandidate : 2 * A ≤ objective A B x y := by
        simp only [objective]
        nlinarith
      exact (min_le_left _ _).trans hcandidate
    · have hB2A : B ≤ 2 * A := le_of_not_ge h2AB
      have hc1 : 0 ≤ B - A := sub_nonneg.mpr hAB
      have hc2 : 0 ≤ 2 * A - B := sub_nonneg.mpr hB2A
      have htriangle := mul_le_mul_of_nonneg_left hxy.rootOutsideTriangle hc1
      have hmixed := mul_le_mul_of_nonneg_left hxy.mixedFourClique hc2
      have hcandidate : (4 * A + B) / 3 ≤ objective A B x y := by
        simp only [objective]
        nlinarith
      exact (min_le_right _ _).trans ((min_le_left _ _).trans hcandidate)

/-- The lower bound is attained by one of the three displayed feasible points. -/
theorem minimumValue_attained (A B : ℚ) :
    ∃ x y : ℚ, Feasible x y ∧ objective A B x y = minimumValue A B := by
  by_cases hfirst : 2 * A ≤ min ((4 * A + B) / 3) (5 * (A + B) / 6)
  · refine ⟨2, 0, feasible_two_zero, ?_⟩
    rw [minimumValue, min_eq_left hfirst]
    simp only [objective]
    ring
  · have houter : min ((4 * A + B) / 3) (5 * (A + B) / 6) ≤ 2 * A :=
      (lt_of_not_ge hfirst).le
    by_cases hsecond : (4 * A + B) / 3 ≤ 5 * (A + B) / 6
    · refine ⟨4 / 3, 1 / 3, feasible_four_thirds_one_third, ?_⟩
      rw [minimumValue, min_eq_right houter, min_eq_left hsecond]
      simp only [objective]
      ring
    · have hinner : 5 * (A + B) / 6 ≤ (4 * A + B) / 3 :=
        (lt_of_not_ge hsecond).le
      refine ⟨5 / 6, 5 / 6, feasible_five_sixths, ?_⟩
      rw [minimumValue, min_eq_right houter, min_eq_right hinner]
      simp only [objective]
      ring

/-- Exact optimality statement for the averaged complete-split dual. -/
theorem exact_minimum {A B : ℚ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∀ x y : ℚ, Feasible x y → minimumValue A B ≤ objective A B x y) ∧
      (∃ x y : ℚ, Feasible x y ∧ objective A B x y = minimumValue A B) :=
  ⟨fun _ _ ↦ minimumValue_le_objective hA hB, minimumValue_attained A B⟩

/-- Subtracting the dual minimum from the edge count gives the three branches. -/
theorem potential_three_branch_formula (A B : ℚ) :
    A + B - minimumValue A B =
      max (B - A) (max ((2 * B - A) / 3) ((A + B) / 6)) := by
  simp only [minimumValue]
  rw [← max_sub_sub_left, ← max_sub_sub_left]
  congr 1
  · ring
  · congr 1 <;> ring

end SplitDual
end Erdos81
