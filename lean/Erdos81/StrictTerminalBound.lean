import Erdos81.TerminalConstruction
import Mathlib.Tactic

/-!
# The strict numerical consequence of the terminal construction

`TerminalConstruction.Certificate` deliberately stores subtraction-free
natural-number inequalities.  This module converts those data to the strict
rational estimate used by root regularization.  No rounding or asymptotic
notation is involved.
-/

namespace Erdos81
namespace StrictTerminalBound

open SimpleGraph MixedModel RootedGraph TerminalConstruction

attribute [-instance] MixedModel.resourceFintype

variable {V : Type} [Fintype V] [DecidableEq V]

theorem natCard_outside_resources {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) :
    Nat.card (Resource (outsideGraph G P)) = (outsideEdges G P).card := by
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    outsideGraph_edgeFinset]

/-- The two strict coefficient hypotheses turn the cleared retained-triangle
bound into the linear estimate needed in the final accounting. -/
theorem retained_linear_bound
    {p c m A f w : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hcolorRatio : 5 * c ≤ 9 * p)
    (hcliqueRatio : 4 * w ≤ p)
    (hretained : p * p * m ≤ c * p * f + c * (w * A)) :
    (20 : ℚ) * m ≤ 36 * f + 9 * A := by
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
  have hmQ : (0 : ℚ) ≤ m := by positivity
  have hAQ : (0 : ℚ) ≤ A := by positivity
  have hcolorQ : (5 : ℚ) * c ≤ 9 * p := by exact_mod_cast hcolorRatio
  have hcliqueQ : (4 : ℚ) * w ≤ p := by exact_mod_cast hcliqueRatio
  have hretainedQ : (p : ℚ) * p * m ≤
      (c : ℚ) * p * f + c * (w * A) := by
    exact_mod_cast hretained
  have hcolorScaled := mul_le_mul_of_nonneg_right hcolorQ
    (mul_nonneg (show (0 : ℚ) ≤ p by positivity) hmQ)
  have hretainedScaled := mul_le_mul_of_nonneg_left hretainedQ
    (show (0 : ℚ) ≤ 9 by norm_num)
  have hcoredWithC : (c : ℚ) * (5 * p * m) ≤
      c * (9 * p * f + 9 * w * A) := by
    nlinarith
  have hcore : (5 : ℚ) * p * m ≤ 9 * p * f + 9 * w * A := by
    have hscaled : (c : ℚ) * ((5 : ℚ) * p * m) ≤
        c * (9 * p * f + 9 * w * A) := by
      simpa only [mul_assoc] using hcoredWithC
    exact le_of_mul_le_mul_left hscaled hcQ
  have hcliqueScaled := mul_le_mul_of_nonneg_right hcliqueQ
    (mul_nonneg (show (0 : ℚ) ≤ 9 by norm_num) hAQ)
  have hbeforeCancel : (p : ℚ) * (20 * m) ≤
      p * (36 * f + 9 * A) := by
    nlinarith
  exact le_of_mul_le_mul_left hbeforeCancel hpQ

/-- Strict terminal bound in the exact form used by the local argument. -/
theorem certificate_strict_bound
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) (c : ℕ) (C : Certificate (G := G) P c)
    (hp : 0 < P.card) (hc : 0 < c)
    (hcolorRatio : 5 * c ≤ 9 * P.card)
    (hcliqueRatio : 4 * ((outsideGraph G P).cliqueNum - 1) ≤ P.card) :
    (C.partition.size : ℚ) ≤
      (P.card : ℚ) * (outsideVertices P).card -
        (Nat.choose P.card 2 : ℚ) -
        (outsideEdges G P).card / 9 - missingIncidences G P / 2 := by
  have hretained := C.retained_lower
  rw [natCard_outside_resources P] at hretained
  have hlinear := retained_linear_bound hp hc hcolorRatio hcliqueRatio hretained
  have haccount : (C.partition.size : ℚ) +
      2 * ((C.retained : ℚ) + Nat.choose P.card 2) +
        missingIncidences G P =
      (Nat.choose P.card 2 : ℚ) +
        (P.card : ℚ) * (outsideVertices P).card +
          (outsideEdges G P).card := by
    exact_mod_cast C.accounting
  linarith

end StrictTerminalBound
end Erdos81
