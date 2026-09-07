import Mathlib.Tactic

/-!
# Discrete convexity used by the single-vertex copy path

The copy inequality makes the mixed potential a discretely convex function of
the number of vertices assigned to one of two false-twin classes.  These
lemmas verify the direction choice and the fact that a nondecreasing step
continues nondecreasingly to the endpoint.
-/

namespace Erdos81
namespace DiscreteConvexity

/-- Convexity for a rational sequence indexed by natural numbers. -/
def IsConvexSequence (f : ℕ → ℚ) : Prop :=
  ∀ i, 2 * f (i + 1) ≤ f i + f (i + 2)

/-- At an interior point of a discretely convex sequence, one neighbor is no lower. -/
theorem neighbor_choice {a b c : ℚ} (h : 2 * b ≤ a + c) :
    b ≤ a ∨ b ≤ c := by
  by_contra hnot
  push Not at hnot
  linarith

/-- A nondecreasing step propagates one position to the right. -/
theorem right_step_propagates {f : ℕ → ℚ} (hconvex : IsConvexSequence f)
    {i : ℕ} (hstep : f i ≤ f (i + 1)) :
    f (i + 1) ≤ f (i + 2) := by
  have h := hconvex i
  linarith

/-- A nonincreasing forward step propagates one position to the left. -/
theorem left_step_propagates {f : ℕ → ℚ} (hconvex : IsConvexSequence f)
    {i : ℕ} (hstep : f (i + 2) ≤ f (i + 1)) :
    f (i + 1) ≤ f i := by
  have h := hconvex i
  linarith

/-- Once the right direction is nondecreasing, every later right step is too. -/
theorem monotone_to_right_endpoint {f : ℕ → ℚ}
    (hconvex : IsConvexSequence f) {j : ℕ}
    (hstart : f j ≤ f (j + 1)) :
    ∀ d : ℕ, f (j + d) ≤ f (j + d + 1) := by
  intro d
  induction d with
  | zero => simpa using hstart
  | succ d ih =>
      have hnext := right_step_propagates hconvex ih
      simpa [Nat.add_assoc] using hnext

/--
The algebraic sign check behind the copy inequality for
`Phi = edgeCount - fractionalCoverValue`.
-/
theorem potential_copy_inequality
    {edges originalCover leftEdges leftCover rightEdges rightCover : ℚ}
    (hedges : leftEdges + rightEdges = 2 * edges)
    (hcovers : leftCover + rightCover ≤ 2 * originalCover) :
    2 * (edges - originalCover) ≤
      (leftEdges - leftCover) + (rightEdges - rightCover) := by
  linarith

end DiscreteConvexity
end Erdos81
