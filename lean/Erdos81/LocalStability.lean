import Erdos81.Arithmetic
import Erdos81.SharpBound
import Mathlib.Tactic

/-!
# Algebraic core of quantitative local stability

The structural root-regularization lemma supplies one lower bound for the
deficit.  The consequences extracted here are independent of graph notation
and are checked over exact rationals.
-/

namespace Erdos81
namespace LocalStability

/-- The regularized deficit lower bound forces a nonnegative deficit. -/
theorem deficit_nonnegative
    {delta squareTerm outsideEdges missingIncidences : ℚ}
    (hm : 0 ≤ outsideEdges) (hA : 0 ≤ missingIncidences)
    (hdeficit : squareTerm ^ 2 / 24 + outsideEdges / 9 +
      missingIncidences / 2 ≤ delta) :
    0 ≤ delta := by
  nlinarith [sq_nonneg squareTerm]

/-- Both kinds of edit defects together cost at most nine times the deficit. -/
theorem defect_sum_le_nine_delta
    {delta squareTerm outsideEdges missingIncidences : ℚ}
    (_hm : 0 ≤ outsideEdges) (hA : 0 ≤ missingIncidences)
    (hdeficit : squareTerm ^ 2 / 24 + outsideEdges / 9 +
      missingIncidences / 2 ≤ delta) :
    outsideEdges + missingIncidences ≤ 9 * delta := by
  nlinarith [sq_nonneg squareTerm]

/-- The square term itself is controlled by twenty-four times the deficit. -/
theorem squareTerm_le_twenty_four_delta
    {delta squareTerm outsideEdges missingIncidences : ℚ}
    (hm : 0 ≤ outsideEdges) (hA : 0 ≤ missingIncidences)
    (hdeficit : squareTerm ^ 2 / 24 + outsideEdges / 9 +
      missingIncidences / 2 ≤ delta) :
    squareTerm ^ 2 ≤ 24 * delta := by
  nlinarith

/-- The manuscript's root displacement bound, in squared form. -/
theorem root_displacement_squared
    {n p delta : ℚ}
    (hroot : (6 * p - 2 * n - 1) ^ 2 / 24 ≤ delta) :
    (p - (2 * n + 1) / 6) ^ 2 ≤ 2 * delta / 3 := by
  nlinarith [sq_nonneg (6 * p - 2 * n - 1)]

/-- The edit-distance terms assemble into the displayed local bound. -/
theorem edit_distance_assembly
    {distance outsideEdges missingIncidences delta n displacement : ℚ}
    (hdefects : outsideEdges + missingIncidences ≤ 9 * delta)
    (hroles : distance ≤ outsideEdges + missingIncidences + n * (displacement + 1)) :
    distance ≤ 9 * delta + n * displacement + n := by
  nlinarith

/-- The deliberately separated manuscript scales turn the local root bounds
into a strict contraction from radius `10^-12` to radius `10^-12 / 4`. -/
theorem manuscript_contraction_numerics
    {n delta defects displacement distance : ℚ}
    (hn : (10 : ℚ) ^ 32 ≤ n)
    (hdelta : delta ≤ 2 * n ^ 2 / (10 : ℚ) ^ 30)
    (hdefects : defects ≤ 9 * delta)
    (hdisplacement : displacement ^ 2 ≤ 2 * delta / 3)
    (hdistance : distance ≤ defects + n * (|displacement| + 1)) :
    distance / n ^ 2 < ((1 : ℚ) / 10 ^ 12) / 4 := by
  have hn0 : 0 < n := by
    have : (0 : ℚ) < 10 ^ 32 := by positivity
    exact this.trans_le hn
  have hn2pos : 0 < n ^ 2 := sq_pos_of_pos hn0
  have habsSmall : |displacement| < n / (10 : ℚ) ^ 14 := by
    by_contra hnot
    have hlarge : n / (10 : ℚ) ^ 14 ≤ |displacement| :=
      le_of_not_gt hnot
    have htargetNonneg : 0 ≤ n / (10 : ℚ) ^ 14 := by positivity
    have hsquare :=
      (sq_le_sq₀ htargetNonneg (abs_nonneg displacement)).2 hlarge
    rw [sq_abs] at hsquare
    nlinarith
  have hmul := mul_lt_mul_of_pos_left habsSmall hn0
  have hnProduct : (10 : ℚ) ^ 32 * n ≤ n * n :=
    mul_le_mul_of_nonneg_right hn (le_of_lt hn0)
  have hnSmall : n ≤ n ^ 2 / (10 : ℚ) ^ 32 := by
    nlinarith
  apply (div_lt_iff₀ hn2pos).2
  nlinarith

/-- Integrality converts the continuous `Q(n)` upper bound to the sharp target. -/
theorem nat_le_sharpBound_of_le_Q (n value : ℕ)
    (hvalue : (value : ℚ) ≤ Arithmetic.Q (n : ℚ)) :
    value ≤ sharpBound n := by
  have hfloor : value ≤ ⌊Arithmetic.Q (n : ℚ)⌋₊ := Nat.le_floor hvalue
  simpa [SharpBound.floor_Q_eq_sharpBound] using hfloor

end LocalStability
end Erdos81
