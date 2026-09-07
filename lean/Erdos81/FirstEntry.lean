import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# The first-entry barrier argument

This is the abstract finite-sequence mechanism used to propagate local
stability back along the monotone single-vertex copy path.  The proof chooses
the first index entering the half-radius ball and compares it with its
predecessor.
-/

namespace Erdos81
namespace FirstEntry

/--
If the endpoint is inside the half-radius ball, each step changes normalized
distance by at most `step`, and every point in the full-radius ball is in fact
inside the quarter-radius ball, then the start is inside the half-radius ball
provided `step < rho/4`.
-/
theorem barrier
    (distance : ℕ → ℚ) (L : ℕ) (rho step : ℚ)
    (hrho : 0 < rho)
    (hstepSmall : step < rho / 4)
    (hend : distance L < rho / 2)
    (hmovement : ∀ i : ℕ, i < L → distance i - step ≤ distance (i + 1))
    (hlocal : ∀ i : ℕ, i ≤ L → distance i < rho → distance i < rho / 4) :
    distance 0 < rho / 2 := by
  by_contra hstartNot
  have hstart : rho / 2 ≤ distance 0 := le_of_not_gt hstartNot
  let enters : ℕ → Prop := fun i ↦ distance i < rho / 2
  have hexists : ∃ i : ℕ, enters i := ⟨L, hend⟩
  let first := Nat.find hexists
  have hfirst : enters first := Nat.find_spec hexists
  change distance first < rho / 2 at hfirst
  have hfirstLe : first ≤ L := Nat.find_min' hexists hend
  have hfirstPos : 0 < first := by
    by_contra hnot
    have hzero : first = 0 := Nat.eq_zero_of_not_pos hnot
    exact (not_lt_of_ge hstart) (hzero ▸ hfirst)
  let previous := first - 1
  have hpreviousLt : previous < first := by
    dsimp only [previous]
    omega
  have hpreviousNot : ¬enters previous := Nat.find_min hexists hpreviousLt
  have hprevious : rho / 2 ≤ distance previous := le_of_not_gt hpreviousNot
  have hpreviousL : previous < L := lt_of_lt_of_le hpreviousLt hfirstLe
  have hmove := hmovement previous hpreviousL
  have hpreviousSucc : previous + 1 = first := by
    dsimp only [previous]
    omega
  rw [hpreviousSucc] at hmove
  have hhalfLt : rho / 2 < rho := div_lt_self hrho (by norm_num)
  have hinsideFull : distance first < rho := hfirst.trans hhalfLt
  have hquarter := hlocal first hfirstLe hinsideFull
  linarith

/-- At the manuscript's scale, a one-pair-normalized step is below `rho/4`. -/
theorem inverse_order_lt_quarter_radius {n : ℚ} (hn : 10 ^ 32 ≤ n) :
    1 / n < ((1 : ℚ) / 10 ^ 12) / 4 := by
  have hden : (4 * 10 ^ 12 : ℚ) < n := by
    norm_num at hn ⊢
    linarith
  have hrecip := one_div_lt_one_div_of_lt
    (show (0 : ℚ) < 4 * 10 ^ 12 by norm_num) hden
  calc
    1 / n < 1 / (4 * 10 ^ 12) := hrecip
    _ = ((1 : ℚ) / 10 ^ 12) / 4 := by norm_num

end FirstEntry
end Erdos81
