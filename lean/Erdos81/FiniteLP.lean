import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# A finite packing/covering linear-programming kernel

This module isolates the weak-duality calculation used by the mixed
triangle--`K₄` functional.  It deliberately does not invoke an LP solver.
-/

open scoped BigOperators

namespace Erdos81
namespace FiniteLP

variable {Item Resource : Type*} [Fintype Item] [Fintype Resource]

/-- A feasible fractional packing for a finite incidence matrix. -/
structure PrimalFeasible (incidence : Item → Resource → ℚ) where
  weight : Item → ℚ
  weight_nonnegative : ∀ i, 0 ≤ weight i
  capacity : ∀ e, ∑ i, incidence i e * weight i ≤ 1

/-- A feasible fractional cover dual to `PrimalFeasible`. -/
structure DualFeasible (incidence : Item → Resource → ℚ) (gain : Item → ℚ) where
  price : Resource → ℚ
  price_nonnegative : ∀ e, 0 ≤ price e
  demand : ∀ i, gain i ≤ ∑ e, incidence i e * price e

/-- Objective value of a feasible fractional packing. -/
def primalValue (gain : Item → ℚ) {incidence : Item → Resource → ℚ}
    (p : PrimalFeasible incidence) : ℚ :=
  ∑ i, gain i * p.weight i

/-- Objective value of a feasible fractional cover. -/
def dualValue {incidence : Item → Resource → ℚ} {gain : Item → ℚ}
    (d : DualFeasible incidence gain) : ℚ :=
  ∑ e, d.price e

/-- Every feasible packing has value at most every feasible cover. -/
theorem weak_duality
    {incidence : Item → Resource → ℚ} {gain : Item → ℚ}
    (p : PrimalFeasible incidence) (d : DualFeasible incidence gain) :
    primalValue gain p ≤ dualValue d := by
  calc
    primalValue gain p ≤
        ∑ i, (∑ e, incidence i e * d.price e) * p.weight i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (d.demand i) (p.weight_nonnegative i)
    _ = ∑ e, d.price e * (∑ i, incidence i e * p.weight i) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ e, d.price e * 1 := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (p.capacity e) (d.price_nonnegative e)
    _ = dualValue d := by simp [dualValue]

end FiniteLP
end Erdos81
