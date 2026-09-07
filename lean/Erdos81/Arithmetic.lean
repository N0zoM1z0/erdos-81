import Mathlib.Tactic

/-!
# Arithmetic kernel for the Erdős 81 proof

The graph-theoretic argument reduces several decisive steps to exact rational
identities and inequalities.  This file checks those computations in Lean.
All constants are rationals, so `norm_num` and the ring normalizer produce
kernel-checkable certificates rather than floating-point evidence.
-/

namespace Erdos81
namespace Arithmetic

/-- The continuous envelope used in the stability argument. -/
def Q (n : ℚ) : ℚ :=
  (2 * n + 1) ^ 2 / 24

/-- The first complete-split branch, written over the rationals. -/
def splitFirstBranch (n p : ℚ) : ℚ :=
  p * (n - p) - p * (p - 1) / 2

/-- The second complete-split branch. -/
def splitSecondBranch (n p : ℚ) : ℚ :=
  (2 * p * (n - p) - p * (p - 1) / 2) / 3

/-- The continuous envelope of the second complete-split branch. -/
def secondBranchEnvelope (n : ℚ) : ℚ :=
  (4 * n + 1) ^ 2 / 120

/-- The exact square identity behind local stability. -/
theorem square_identity (n p : ℚ) :
    Q n - splitFirstBranch n p = (6 * p - 2 * n - 1) ^ 2 / 24 := by
  simp only [Q, splitFirstBranch]
  ring

/-- The first complete-split branch never exceeds its continuous envelope. -/
theorem splitFirstBranch_le_Q (n p : ℚ) : splitFirstBranch n p ≤ Q n := by
  rw [← sub_nonneg]
  rw [square_identity]
  positivity

/-- The exact square identity for the second terminal branch. -/
theorem second_branch_square_identity (n p : ℚ) :
    secondBranchEnvelope n - splitSecondBranch n p =
      (10 * p - 4 * n - 1) ^ 2 / 120 := by
  simp only [secondBranchEnvelope, splitSecondBranch]
  ring

/-- The second terminal branch never exceeds its own continuous envelope. -/
theorem splitSecondBranch_le_envelope (n p : ℚ) :
    splitSecondBranch n p ≤ secondBranchEnvelope n := by
  rw [← sub_nonneg, second_branch_square_identity]
  positivity

/-- The exact coefficient accumulated when irregular root vertices are moved. -/
theorem root_regularization_coefficient :
    (1 : ℚ) / 65536 + 129 / (64 * 1024) + 1 / (2 * 1024 ^ 2) =
      4161 / 2097152 := by
  norm_num

/-- The preceding exact coefficient has the strict margin used in the proof. -/
theorem root_regularization_margin :
    (4161 : ℚ) / 2097152 < 1 / 400 := by
  norm_num

/-- Algebraic form of the gap separating the second terminal branch. -/
theorem second_branch_gap_identity (n : ℚ) :
    n ^ 2 / 6 - n ^ 2 / 40 - (4 * n + 1) ^ 2 / 120 =
      (n ^ 2 - 8 * n - 1) / 120 := by
  ring

/-- For the range used in the manuscript, the second branch is strictly separated. -/
theorem second_branch_strict_gap {n : ℚ} (hn : 100 ≤ n) :
    (4 * n + 1) ^ 2 / 120 < n ^ 2 / 6 - n ^ 2 / 40 := by
  rw [← sub_pos, second_branch_gap_identity]
  have hn0 : 0 < n := by linarith
  have hn8 : 0 < n - 8 := by linarith
  have hprod : 0 < n * (n - 8) := mul_pos hn0 hn8
  nlinarith

/-- The degenerate `3n` terminal estimate is also strictly separated. -/
theorem linear_terminal_strict_gap {n : ℚ} (hn : 100 ≤ n) :
    3 * n < n ^ 2 / 6 - n ^ 2 / 40 := by
  have hn0 : 0 < n := by linarith
  have h17 : 0 < 17 * n - 360 := by linarith
  nlinarith [mul_pos hn0 h17]

/-- Exact numerical inequality used at the end of the first-entry argument. -/
theorem first_entry_numerics :
    (18 : ℚ) / 10 ^ 30 + 2 / 10 ^ 15 + 1 / 10 ^ 32 <
      (1 / 10 ^ 12) / 4 := by
  norm_num

/-- The near-extremal threshold leaves room for the transfer error. -/
theorem half_threshold_lt_threshold :
    (1 : ℚ) / 10 ^ 30 / 2 < 1 / 10 ^ 30 := by
  norm_num

/--
The exact arithmetic of the far case.  The names mirror the decomposition
`cp_{≤4} = Phi + (W₄* - W₄)` in the manuscript.
-/
theorem far_case_closure
    {potential integralityGap cliquePartition target n eta : ℚ}
    (_hn : 0 ≤ n) (heta : 0 < eta)
    (hdecomp : cliquePartition = potential + integralityGap)
    (hfar : potential < n ^ 2 / 6 - eta * n ^ 2)
    (htransfer : integralityGap ≤ eta / 2 * n ^ 2)
    (htarget : n ^ 2 / 6 ≤ target) :
    cliquePartition < target := by
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  rw [hdecomp]
  nlinarith [mul_pos heta (show (0 : ℚ) < 1 / 2 by norm_num),
    mul_nonneg heta.le hn2]

/-- Clearing the denominator in the eventual integer target loses nothing. -/
theorem six_mul_floor_six_le (a : ℕ) : 6 * (a / 6) ≤ a := by
  simpa [Nat.mul_comm] using Nat.div_mul_le_self a 6

end Arithmetic
end Erdos81
