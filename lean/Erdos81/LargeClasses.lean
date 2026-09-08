import Mathlib.Tactic

/-!
# Selecting large classes

The terminal construction retains `p` colour classes.  This file proves the
finite averaging statement in a form which avoids probability: among `c`
nonnegative class weights, some `p` classes carry at least the fraction
`p / c` of the total weight.
-/

namespace Erdos81
namespace LargeClasses

open scoped BigOperators

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

/-- A maximum-weight `p`-subset carries at least the proportional share of
the total weight.  The inequality is stated with denominators cleared. -/
theorem exists_subset_mul_total_le_card_mul_sum (weight : Color → ℕ)
    (p : ℕ) (hp : p ≤ Fintype.card Color) :
    ∃ S : Finset Color, S.card = p ∧
      p * (∑ a : Color, weight a) ≤
        Fintype.card Color * (∑ a ∈ S, weight a) := by
  classical
  let family := (Finset.univ : Finset Color).powersetCard p
  have hfamily : family.Nonempty := by
    dsimp only [family]
    apply Finset.powersetCard_nonempty.mpr
    simpa only [Finset.card_univ] using hp
  obtain ⟨S, hSfamily, hSmax⟩ :=
    Finset.exists_max_image family (fun T ↦ ∑ a ∈ T, weight a) hfamily
  have hSsub : S ⊆ (Finset.univ : Finset Color) :=
    (Finset.mem_powersetCard.mp hSfamily).1
  have hScard : S.card = p :=
    (Finset.mem_powersetCard.mp hSfamily).2
  let T := (Finset.univ : Finset Color) \ S
  have hpair : ∀ x ∈ S, ∀ y ∈ T, weight y ≤ weight x := by
    intro x hx y hy
    have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
    let S' := insert y (S.erase x)
    have hyErase : y ∉ S.erase x := by simp [hyS]
    have hpPos : 0 < p := by
      have : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
      simpa [hScard] using this
    have hS'card : S'.card = p := by
      dsimp only [S']
      rw [Finset.card_insert_of_notMem hyErase,
        Finset.card_erase_of_mem hx, hScard]
      omega
    have hS'family : S' ∈ family := by
      change S' ∈ (Finset.univ : Finset Color).powersetCard p
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hS'card⟩
    have hmax := hSmax S' hS'family
    have hsumErase :
        (∑ z ∈ S.erase x, weight z) + weight x =
          ∑ z ∈ S, weight z := by
      exact Finset.sum_erase_add S weight hx
    have hsumInsert :
        ∑ z ∈ S', weight z =
          weight y + ∑ z ∈ S.erase x, weight z := by
      change ∑ z ∈ insert y (S.erase x), weight z = _
      rw [Finset.sum_insert hyErase]
    rw [hsumInsert] at hmax
    omega
  have hcross :
      S.card * (∑ y ∈ T, weight y) ≤
        T.card * (∑ x ∈ S, weight x) := by
    calc
      S.card * (∑ y ∈ T, weight y) =
          ∑ x ∈ S, ∑ y ∈ T, weight y := by simp
      _ ≤ ∑ x ∈ S, ∑ y ∈ T, weight x := by
        exact Finset.sum_le_sum fun x hx ↦
          Finset.sum_le_sum fun y hy ↦ hpair x hx y hy
      _ = T.card * (∑ x ∈ S, weight x) := by
        simp only [Finset.sum_const_nat, Finset.mul_sum]
  have hTcard : T.card = Fintype.card Color - p := by
    change ((Finset.univ : Finset Color) \ S).card = _
    rw [Finset.card_sdiff_of_subset hSsub, Finset.card_univ, hScard]
  have htotal :
      (∑ a : Color, weight a) =
        (∑ a ∈ S, weight a) + ∑ a ∈ T, weight a := by
    have h := Finset.sum_sdiff hSsub (f := weight)
    change (∑ a ∈ (Finset.univ : Finset Color) \ S, weight a) +
      ∑ a ∈ S, weight a = ∑ a ∈ (Finset.univ : Finset Color), weight a at h
    change (∑ a : Color, weight a) =
      (∑ a ∈ S, weight a) +
        ∑ a ∈ (Finset.univ : Finset Color) \ S, weight a
    omega
  refine ⟨S, hScard, ?_⟩
  rw [hScard, hTcard] at hcross
  rw [htotal]
  have hcardSplit :
      Fintype.card Color = p + (Fintype.card Color - p) := by omega
  calc
    p * ((∑ a ∈ S, weight a) + ∑ a ∈ T, weight a) =
        p * (∑ a ∈ S, weight a) +
          p * (∑ a ∈ T, weight a) := Nat.mul_add ..
    _ ≤ p * (∑ a ∈ S, weight a) +
        (Fintype.card Color - p) * (∑ a ∈ S, weight a) :=
      Nat.add_le_add_left hcross _
    _ = (p + (Fintype.card Color - p)) *
        (∑ a ∈ S, weight a) := (Nat.add_mul ..).symm
    _ = Fintype.card Color * (∑ a ∈ S, weight a) := by
      rw [← hcardSplit]

end LargeClasses
end Erdos81
