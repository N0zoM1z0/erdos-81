import Erdos81.RootArithmetic
import Mathlib.Tactic

/-!
# Numerical certificate for local root extraction

This file isolates the integer arithmetic which converts the PEO missing-pair
bound and the manuscript-scale split-distance hypothesis into the balance and
defect assumptions used by strict root regularization.
-/

namespace Erdos81
namespace LocalRootArithmetic

/-- Exact integer form of the local-root numerical calculation. -/
theorem initialRoot_numerics {n a p E d : ℕ}
    (hn : 1000 ≤ n)
    (ha : a = n / 3)
    (hp : p ≤ a)
    (hchoose : Nat.choose (a - p + 1) 2 ≤ E)
    (hscale : 10 ^ 12 * E ≤ n * n)
    (hdefect : d ≤ E + (a - p) * n) :
    128 ≤ p ∧
      127 * p ≤ 64 * (n - p) ∧
      64 * (n - p) ≤ 129 * p ∧
      65536 * d ≤ p * p := by
  let u := a - p
  have hau : a = p + u := by
    dsimp only [u]
    omega
  have htwo : 2 * Nat.choose (u + 1) 2 = (u + 1) * u := by
    rw [Nat.choose_two_right, Nat.mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (u + 1))]
    congr 1
  have huChoose : Nat.choose (u + 1) 2 ≤ E := by
    simpa only [u] using hchoose
  have huSquare : u * u ≤ 2 * E := by
    have hmul := Nat.mul_le_mul_left 2 huChoose
    rw [htwo] at hmul
    have hself : u * u ≤ (u + 1) * u := by nlinarith
    exact hself.trans hmul
  have hnpos : 0 < n := by omega
  have hscaledSquare :
      (2000000 * u) * (2000000 * u) < (3 * n) * (3 * n) := by
    nlinarith
  have huSmall : 2000000 * u < 3 * n := by
    nlinarith
  have hp332 : 332 * n ≤ 1000 * p := by
    omega
  have hp128 : 128 ≤ p := by
    nlinarith
  have hlower : 127 * p ≤ 64 * (n - p) := by
    omega
  have hupper : 64 * (n - p) ≤ 129 * p := by
    omega
  have huProduct : 2000000 * (u * n) ≤ 3 * (n * n) := by
    have hmul := Nat.mul_le_mul_right n (Nat.le_of_lt huSmall)
    nlinarith
  have hp33 : 33 * n ≤ 100 * p := by
    nlinarith
  have hpSquare : 1089 * (n * n) ≤ 10000 * (p * p) := by
    nlinarith
  have hdefect' : d ≤ E + u * n := by
    simpa only [u] using hdefect
  have hbudget : 65536 * d ≤ p * p := by
    nlinarith
  exact ⟨hp128, hlower, hupper, hbudget⟩

end LocalRootArithmetic
end Erdos81
