import Erdos81.Arithmetic
import Erdos81.CompleteSplitPacking
import Mathlib.Tactic

/-!
# Potential bounds and stability for complete-split graphs

The explicit primal witnesses from `CompleteSplitPacking` are converted here
to the three terminal branches in the variables `n = |V|` and `p = |K|`.
For `n >= 100`, every branch lies below the continuous envelope `Q(n)`.  A
terminal graph within `delta n^2` of that envelope, for `delta <= 1/40`, must
lie in the first regime; the exact square identity then controls its root
order.
-/

namespace Erdos81
namespace CompleteSplitPotential

open SimpleGraph MixedModel RootedGraph EditDistance CompleteSplit
  CompleteSplitPacking Arithmetic

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cast_card_outsideVertices (K : Finset V) :
    ((outsideVertices K).card : ℚ) =
      (Fintype.card V : ℚ) - K.card := by
  rw [card_outsideVertices, Nat.cast_sub (Finset.card_le_univ K)]

theorem cast_choose_two_eq (K : Finset V) (hk : 1 ≤ K.card) :
    (Nat.choose K.card 2 : ℚ) =
      (K.card : ℚ) * ((K.card : ℚ) - 1) / 2 := by
  have h := two_mul_cast_choose_two K.card
  have hsub : ((K.card - 1 : ℕ) : ℚ) = (K.card : ℚ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hsub] at h
  linarith

theorem first_expression_eq_splitFirstBranch (K : Finset V)
    (hk : 1 ≤ K.card) :
    (K.card : ℚ) * (outsideVertices K).card -
        (Nat.choose K.card 2 : ℚ) =
      splitFirstBranch (Fintype.card V : ℚ) K.card := by
  rw [cast_card_outsideVertices, cast_choose_two_eq K hk]
  unfold splitFirstBranch
  ring

theorem second_expression_eq_splitSecondBranch (K : Finset V)
    (hk : 1 ≤ K.card) :
    (2 * (K.card : ℚ) * (outsideVertices K).card -
        (Nat.choose K.card 2 : ℚ)) / 3 =
      splitSecondBranch (Fintype.card V : ℚ) K.card := by
  rw [cast_card_outsideVertices, cast_choose_two_eq K hk]
  unfold splitSecondBranch
  ring

/-- The third branch is at most `n^2/12`, leaving a large gap below the main
envelope. -/
theorem third_expression_le_sq_div_twelve (K : Finset V)
    (hk : 1 ≤ K.card) :
    ((Nat.choose K.card 2 : ℚ) +
        (K.card : ℚ) * (outsideVertices K).card) / 6 ≤
      (Fintype.card V : ℚ) ^ 2 / 12 := by
  let n : ℚ := Fintype.card V
  let p : ℚ := K.card
  have hn : 0 ≤ n := by positivity
  have hp : 0 ≤ p := by positivity
  have hpn : p ≤ n := by
    dsimp only [p, n]
    exact_mod_cast Finset.card_le_univ K
  rw [cast_card_outsideVertices, cast_choose_two_eq K hk]
  dsimp only [n, p] at hn hp hpn ⊢
  nlinarith [sq_nonneg ((Fintype.card V : ℚ) - K.card)]

theorem sq_div_twelve_lt_Q_sub_gap {n : ℚ} (hn : 100 ≤ n) :
    n ^ 2 / 12 < Q n - n ^ 2 / 40 := by
  unfold Q
  nlinarith [sq_nonneg n]

theorem Q_ge_sq_div_six (n : ℚ) (hn : 0 ≤ n) :
    n ^ 2 / 6 ≤ Q n := by
  unfold Q
  nlinarith

/-- Every complete-split terminal graph obeys the global continuous
envelope. -/
theorem potential_le_Q (K : Finset V) (w : ℚ)
    (hopt : IsPackingOptimum (G := completeSplitGraph K) w)
    (hn : 100 ≤ Fintype.card V) :
    potential (completeSplitGraph K) w ≤ Q (Fintype.card V) := by
  let n : ℚ := Fintype.card V
  have hnQ : 100 ≤ n := by
    dsimp only [n]
    exact_mod_cast hn
  have hn0 : 0 ≤ n := by positivity
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  change potential (completeSplitGraph K) w ≤ Q n
  by_cases hsmall : K.card ≤ 3
  · have hlinear := potential_le_three_mul_order_of_small_root K w hopt hsmall
    change potential (completeSplitGraph K) w ≤ 3 * n at hlinear
    have hgap := linear_terminal_strict_gap hnQ
    have hQ := Q_ge_sq_div_six n hn0
    linarith
  · have hk4 : 4 ≤ K.card := by omega
    by_cases hfirst : K.card - 1 ≤ (outsideVertices K).card
    · have hout : 0 < (outsideVertices K).card := by omega
      have hpotential := potential_le_firstRegime K w hopt hout hfirst
      rw [first_expression_eq_splitFirstBranch K (by omega)] at hpotential
      exact hpotential.trans (splitFirstBranch_le_Q _ _)
    · have hhigh : (outsideVertices K).card ≤ K.card - 1 := by omega
      by_cases hmiddle : K.card - 1 ≤ 2 * (outsideVertices K).card
      · have hout : 0 < (outsideVertices K).card := by omega
        have hpotential := potential_le_secondRegime K w hopt
          (by omega) hout hmiddle hhigh
        rw [second_expression_eq_splitSecondBranch K (by omega)] at hpotential
        change potential (completeSplitGraph K) w ≤
          splitSecondBranch n (K.card : ℚ) at hpotential
        have henvelope := splitSecondBranch_le_envelope n (K.card : ℚ)
        unfold secondBranchEnvelope at henvelope
        have hgap := second_branch_strict_gap hnQ
        have hQ := Q_ge_sq_div_six n hn0
        linarith
      · have hthird : 2 * (outsideVertices K).card ≤ K.card - 1 := by
          omega
        have hpotential := potential_le_thirdRegime K w hopt hk4 hthird
        have hthirdBound := third_expression_le_sq_div_twelve K (by omega)
        change ((Nat.choose K.card 2 : ℚ) +
          (K.card : ℚ) * (outsideVertices K).card) / 6 ≤
            n ^ 2 / 12 at hthirdBound
        have hgap := sq_div_twelve_lt_Q_sub_gap hnQ
        linarith

/-- Quantitative terminal stability.  Near the envelope, the complete-split
root lies in the first LP regime and satisfies the exact square control. -/
theorem near_extremal_forces_firstRegime (K : Finset V) (w δ : ℚ)
    (hopt : IsPackingOptimum (G := completeSplitGraph K) w)
    (hn : 100 ≤ Fintype.card V)
    (hδnonneg : 0 ≤ δ) (hδ : δ ≤ 1 / 40)
    (hnear : Q (Fintype.card V) - δ * (Fintype.card V : ℚ) ^ 2 ≤
      potential (completeSplitGraph K) w) :
    4 ≤ K.card ∧
      K.card - 1 ≤ (outsideVertices K).card ∧
      (6 * (K.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1) ^ 2 ≤
        24 * δ * (Fintype.card V : ℚ) ^ 2 := by
  let n : ℚ := Fintype.card V
  have hnQ : 100 ≤ n := by
    dsimp only [n]
    exact_mod_cast hn
  have hn0 : 0 ≤ n := by positivity
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hδn2 : 0 ≤ δ * n ^ 2 := mul_nonneg hδnonneg hn2
  change Q n - δ * n ^ 2 ≤ potential (completeSplitGraph K) w at hnear
  have hnearGap : Q n - n ^ 2 / 40 ≤
      potential (completeSplitGraph K) w := by
    nlinarith
  have hnotSmall : ¬K.card ≤ 3 := by
    intro hsmall
    have hlinear := potential_le_three_mul_order_of_small_root K w hopt hsmall
    change potential (completeSplitGraph K) w ≤ 3 * n at hlinear
    have hgap := linear_terminal_strict_gap hnQ
    have hQ := Q_ge_sq_div_six n hn0
    linarith
  have hk4 : 4 ≤ K.card := by omega
  have hfirst : K.card - 1 ≤ (outsideVertices K).card := by
    by_contra hnotFirst
    have hhigh : (outsideVertices K).card ≤ K.card - 1 := by omega
    by_cases hmiddle : K.card - 1 ≤ 2 * (outsideVertices K).card
    · have hout : 0 < (outsideVertices K).card := by omega
      have hpotential := potential_le_secondRegime K w hopt
        (by omega) hout hmiddle hhigh
      rw [second_expression_eq_splitSecondBranch K (by omega)] at hpotential
      change potential (completeSplitGraph K) w ≤
        splitSecondBranch n (K.card : ℚ) at hpotential
      have henvelope := splitSecondBranch_le_envelope n (K.card : ℚ)
      unfold secondBranchEnvelope at henvelope
      have hgap := second_branch_strict_gap hnQ
      have hQ := Q_ge_sq_div_six n hn0
      linarith
    · have hthird : 2 * (outsideVertices K).card ≤ K.card - 1 := by
        omega
      have hpotential := potential_le_thirdRegime K w hopt hk4 hthird
      have hthirdBound := third_expression_le_sq_div_twelve K (by omega)
      change ((Nat.choose K.card 2 : ℚ) +
        (K.card : ℚ) * (outsideVertices K).card) / 6 ≤
          n ^ 2 / 12 at hthirdBound
      have hgap := sq_div_twelve_lt_Q_sub_gap hnQ
      linarith
  refine ⟨hk4, hfirst, ?_⟩
  have hout : 0 < (outsideVertices K).card := by omega
  have hpotential := potential_le_firstRegime K w hopt hout hfirst
  rw [first_expression_eq_splitFirstBranch K (by omega)] at hpotential
  change potential (completeSplitGraph K) w ≤
    splitFirstBranch n (K.card : ℚ) at hpotential
  have hsquare := square_identity n (K.card : ℚ)
  change (6 * (K.card : ℚ) - 2 * n - 1) ^ 2 ≤ 24 * δ * n ^ 2
  nlinarith

end CompleteSplitPotential
end Erdos81
