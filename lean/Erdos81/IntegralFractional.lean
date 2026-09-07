import Erdos81.IntegralPacking
import Mathlib.Tactic

/-!
# Embedding integral mixed packings into the fractional model

This module sends every edge-disjoint triangle--four-clique packing to the
corresponding zero--one feasible point of the mixed rational LP.  It proves
exact preservation of the objective and derives the manuscript comparison
`Phi(G) <= cp_{<=3}(G)` relative to a certified fractional optimum.
-/

namespace Erdos81
namespace IntegralFractional

open scoped BigOperators
open MixedModel
open IntegralPacking

-- Use the adjacency-derived fintype on graph edges, consistently with the
-- integral accounting modules.
attribute [-instance] MixedModel.resourceFintype

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The rational mixed gain is the natural integral gain after coercion. -/
theorem fractionalGain_eq_itemGain {G : SimpleGraph V} (i : Item G) :
    MixedModel.gain i = (IntegralPacking.itemGain i : ℚ) := by
  cases i <;> rfl

/-- The zero--one point associated with an integral packing is feasible for
the mixed fractional packing LP. -/
noncomputable def toFractional {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) : FractionalPacking G := by
  classical
  refine
    { weight := fun i ↦ if i ∈ p.items then 1 else 0
      weight_nonnegative := ?_
      capacity := ?_ }
  · intro i
    by_cases hi : i ∈ p.items <;> simp [hi]
  · intro e
    change (∑ i : Item G,
      (if Uses i e then (1 : ℚ) else 0) *
        (if i ∈ p.items then 1 else 0)) ≤ 1
    by_cases hUsed : ∃ i ∈ p.items, Uses i e
    · obtain ⟨i, hi, hie⟩ := hUsed
      have hSum : (∑ j : Item G,
          (if Uses j e then (1 : ℚ) else 0) *
            (if j ∈ p.items then 1 else 0)) = 1 := by
        calc
          (∑ j : Item G,
              (if Uses j e then (1 : ℚ) else 0) *
                (if j ∈ p.items then 1 else 0)) =
              (if Uses i e then (1 : ℚ) else 0) *
                (if i ∈ p.items then 1 else 0) := by
            apply Finset.sum_eq_single i
            · intro j hj hji
              by_cases hjItems : j ∈ p.items
              · by_cases hje : Uses j e
                · exact (hji (p.exclusive hjItems hi e hje hie)).elim
                · simp [hje]
              · simp [hjItems]
            · simp
          _ = 1 := by simp [hi, hie]
      rw [hSum]
    · have hZero : ∀ j : Item G,
          (if Uses j e then (1 : ℚ) else 0) *
            (if j ∈ p.items then 1 else 0) = 0 := by
        intro j
        by_cases hjItems : j ∈ p.items
        · have hNotUses : ¬ Uses j e := fun hje ↦
            hUsed ⟨j, hjItems, hje⟩
          simp [hjItems, hNotUses]
        · simp [hjItems]
      rw [Finset.sum_eq_zero fun j _ ↦ hZero j]
      norm_num

/-- Passing to the fractional LP preserves the mixed objective exactly. -/
theorem packingValue_toFractional {G : SimpleGraph V}
    [DecidableRel G.Adj] (p : Packing G) :
    MixedModel.packingValue (toFractional p) =
      (IntegralPacking.gain p : ℚ) := by
  classical
  unfold MixedModel.packingValue FiniteLP.primalValue IntegralPacking.gain
  change (∑ i : Item G, MixedModel.gain i *
      (if i ∈ p.items then 1 else 0)) =
    ((∑ i ∈ p.items, IntegralPacking.itemGain i : ℕ) : ℚ)
  simp_rw [fractionalGain_eq_itemGain]
  push_cast
  simp

/-- A certified optimum of the mixed fractional packing gives the manuscript
comparison `Phi(G) <= |P|` for every clique partition with blocks of order at
most three. -/
theorem potential_le_size_of_orderAtMost_three
    {G : SimpleGraph V} [DecidableRel G.Adj] {w : ℚ}
    (hOpt : MixedModel.IsPackingOptimum (G := G) w)
    (P : CliquePartition G) (hOrder : P.OrderAtMost 3) :
    MixedModel.potential G w ≤ (P.size : ℚ) := by
  have hOrderFour : P.OrderAtMost 4 := by
    intro K hK
    exact (hOrder K hK).trans (by omega)
  have hPackingBound := hOpt.2 (toFractional (ofCliquePartition P))
  rw [packingValue_toFractional,
    IntegralPacking.gain_ofCliquePartition P hOrderFour] at hPackingBound
  have hSizeLe := CliquePartitionCounting.size_le_card_edges P
  rw [Nat.cast_sub hSizeLe] at hPackingBound
  have hEdgeCard :
      (@SimpleGraph.edgeFinset V G (MixedModel.resourceFintype G)).card =
        G.edgeFinset.card := by
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  unfold MixedModel.potential
  rw [hEdgeCard]
  rw [sub_le_iff_le_add] at hPackingBound ⊢
  simpa [add_comm] using hPackingBound

end IntegralFractional
end Erdos81
