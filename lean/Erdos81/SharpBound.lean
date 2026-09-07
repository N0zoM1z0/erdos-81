import Erdos81.Arithmetic
import Erdos81.Statement
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# The exact integer target

The manuscript uses both `Q(n) = (2n+1)^2/24` and
`floor(n(n+1)/6)`.  This file verifies their floor identity for every natural
number `n`; no floating-point approximation is involved.
-/

namespace Erdos81
namespace SharpBound

/-- A product of consecutive naturals has remainder at most four modulo six. -/
theorem consecutive_product_mod_six_le_four (n : ℕ) :
    n * (n + 1) % 6 ≤ 4 := by
  have hrange : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  rw [Nat.mul_mod, Nat.add_mod]
  interval_cases h : n % 6 <;> norm_num [h] at *

/-- Division by six leaves at most four for a consecutive product. -/
theorem consecutive_product_le_six_mul_div_add_four (n : ℕ) :
    n * (n + 1) ≤ 6 * (n * (n + 1) / 6) + 4 := by
  have hmod := consecutive_product_mod_six_le_four n
  have hdecomp := Nat.mod_add_div (n * (n + 1)) 6
  omega

/-- The continuous envelope and the manuscript's integer target have the same floor. -/
theorem floor_Q_eq_sharpBound (n : ℕ) :
    ⌊Arithmetic.Q (n : ℚ)⌋₊ = sharpBound n := by
  apply (Nat.floor_eq_iff (show 0 ≤ Arithmetic.Q (n : ℚ) by
    simp only [Arithmetic.Q]
    positivity)).2
  constructor
  · have hdiv := Nat.div_mul_le_self (n * (n + 1)) 6
    have hdiv' : 6 * (n * (n + 1) / 6) ≤ n * (n + 1) := by
      simpa [Nat.mul_comm] using hdiv
    have hdivQ' : (6 : ℚ) * ((n * (n + 1) / 6 : ℕ) : ℚ) ≤
        (n : ℚ) * ((n : ℚ) + 1) := by
      exact_mod_cast hdiv'
    have hdivQ : (6 : ℚ) * (sharpBound n : ℚ) ≤
        (n : ℚ) * ((n : ℚ) + 1) := by
      simpa [sharpBound] using hdivQ'
    simp only [Arithmetic.Q]
    nlinarith
  · have hupper := consecutive_product_le_six_mul_div_add_four n
    have hupperQ' : (n : ℚ) * ((n : ℚ) + 1) ≤
        6 * ((n * (n + 1) / 6 : ℕ) : ℚ) + 4 := by
      exact_mod_cast hupper
    have hupperQ : (n : ℚ) * ((n : ℚ) + 1) ≤
        6 * (sharpBound n : ℚ) + 4 := by
      simpa [sharpBound] using hupperQ'
    simp only [Arithmetic.Q]
    nlinarith

end SharpBound
end Erdos81
