import Mathlib.Tactic

/-!
# Exact constants in strict root regularization

Every declaration in this file corresponds to a numerical comparison in the
demotion/promotion argument.  The calculations use only exact rationals or
Presburger arithmetic on naturals.
-/

namespace Erdos81
namespace RootArithmetic

theorem demotion_edge_coefficient :
    (1 : ℚ) / 65536 + 129 / (64 * 1024) + 1 / (2 * 1024 ^ 2) =
      4161 / 2097152 := by
  norm_num

theorem demotion_edge_margin :
    (4161 : ℚ) / 2097152 < 1 / 400 := by
  norm_num

theorem fixed_defect_coefficient :
    (17 : ℚ) / 64 + 11 / 4096 = 1099 / 4096 := by
  norm_num

theorem fixed_defect_margin :
    (1099 : ℚ) / 4096 < 1 / 3 := by
  norm_num

theorem defect_and_outside_clique_margin :
    (1099 : ℚ) / 4096 + 1 / 10 < 13 / 30 := by
  norm_num

theorem promotion_threshold_separation :
    (13 : ℚ) / 30 < (7 / 4) * (99 / 100) := by
  norm_num

/-- The exact coefficient available before the convenient `p/693` weakening. -/
theorem promotion_count_coefficient :
    4 * ((4161 : ℚ) / 2097152) / (7 * (99 / 100)) < 1 / 693 := by
  norm_num

/-- The ceiling estimate used for the final Vizing colour count. -/
theorem ceil_seven_quarters_le_nine_fifths {p : ℕ} (hp : 15 ≤ p) :
    5 * ((7 * p + 3) / 4) ≤ 9 * p := by
  omega

theorem outside_clique_ratio_margin :
    (20 : ℚ) / 99 < 1 / 2 := by
  norm_num

theorem final_host_coefficient :
    (63 : ℚ) / 64 - 2 / 693 - 2 / 3 - 1 / 99 = 4505 / 14784 := by
  norm_num

theorem final_host_coefficient_margin :
    (1 : ℚ) / 4 < 4505 / 14784 := by
  norm_num

/-- At the minimum root order, the final host-list margin is nonnegative. -/
theorem final_host_margin_nonnegative {p : ℚ} (hp : 128 ≤ p) :
    0 ≤ ((63 : ℚ) / 64 - 2 / 693 - 2 / 3 - 1 / 99) * p - 4 := by
  rw [final_host_coefficient]
  have hcoeff := final_host_coefficient_margin
  nlinarith

/-- The weakened margin displayed in the manuscript is already nonnegative. -/
theorem quarter_margin_nonnegative {p : ℚ} (hp : 128 ≤ p) :
    0 ≤ p / 4 - 4 := by
  linarith

/-- Rational square certificate for `sqrt(2 rho) < 3/(2*10^6)`. -/
theorem local_sqrt_proxy_squared :
    (2 : ℚ) / 10 ^ 12 < (3 / (2 * 10 ^ 6)) ^ 2 := by
  norm_num

/-- The local defect budget fits below `p^2/65536` when `p >= 0.33n`. -/
theorem local_defect_budget_margin :
    (1 : ℚ) / 10 ^ 12 + 3 / (2 * 10 ^ 6) < (33 / 100) ^ 2 / 65536 := by
  norm_num

/-- Numerical margin used to put `q-2p` below `p/64`. -/
theorem local_balance_margin :
    (3 : ℚ) / 1000 + 9 / (2 * 10 ^ 6) < 33 / 6400 := by
  norm_num

end RootArithmetic
end Erdos81
