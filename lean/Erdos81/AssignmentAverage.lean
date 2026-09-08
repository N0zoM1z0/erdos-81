import Mathlib.Tactic

/-!
# Averaging bijective assignments

The terminal proof assigns `p` selected colour classes bijectively to `p`
root vertices.  Cyclic shifts already form a sufficiently symmetric family:
across the `p` shifts, every class--root pair occurs exactly once.  This gives
the required average without probability theory or a factorial count of all
permutations.
-/

namespace Erdos81
namespace AssignmentAverage

open scoped BigOperators

/-- Among the cyclic assignments of a square cost matrix, one has at most the
average total cost.  Denominators are cleared. -/
theorem exists_cyclic_shift (p : ℕ) (hp : 0 < p)
    (cost : Fin p → Fin p → ℕ) :
    ∃ shift : Fin p,
      p * (∑ i : Fin p, cost i (i + shift)) ≤
        ∑ i : Fin p, ∑ j : Fin p, cost i j := by
  letI : NeZero p := ⟨hp.ne'⟩
  let shear : Fin p × Fin p ≃ Fin p × Fin p :=
    (Equiv.prodComm (Fin p) (Fin p)).trans
      (Equiv.prodShear (Equiv.refl (Fin p)) fun i ↦ Equiv.addLeft i)
  have hsum :
      (∑ shift : Fin p, ∑ i : Fin p, cost i (i + shift)) =
        ∑ i : Fin p, ∑ j : Fin p, cost i j := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv shear
      (fun z ↦ cost z.2 (z.2 + z.1))
      (fun z ↦ cost z.1 z.2) (fun _ ↦ rfl)
  have hsumMul :
      (∑ shift : Fin p,
          p * (∑ i : Fin p, cost i (i + shift))) =
        ∑ _shift : Fin p, (∑ i : Fin p, ∑ j : Fin p, cost i j) := by
    rw [← Finset.mul_sum, hsum]
    simp
  obtain ⟨shift, _hshiftMem, hshift⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin p)))
      Finset.univ_nonempty hsumMul.le
  exact ⟨shift, hshift⟩

/-- Finset form: two `p`-element sets admit a bijective assignment whose
diagonal cost is at most the average of all pair costs. -/
theorem exists_equiv_with_small_cost
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (P : Finset B) (p : ℕ)
    (hS : S.card = p) (hP : P.card = p) (hp : 0 < p)
    (cost : A → B → ℕ) :
    ∃ assign : ↑S ≃ ↑P,
      p * (∑ s : ↑S, cost s (assign s)) ≤
        ∑ s ∈ S, ∑ x ∈ P, cost s x := by
  classical
  letI : NeZero p := ⟨hp.ne'⟩
  let eS : Fin p ≃ ↑S := Fintype.equivOfCardEq (by simp [hS])
  let eP : Fin p ≃ ↑P := Fintype.equivOfCardEq (by simp [hP])
  let costFin : Fin p → Fin p → ℕ :=
    fun i j ↦ cost (eS i) (eP j)
  obtain ⟨shift, hshift⟩ := exists_cyclic_shift p hp costFin
  let assign : ↑S ≃ ↑P :=
    eS.symm.trans ((Equiv.addRight shift).trans eP)
  refine ⟨assign, ?_⟩
  have hdiag :
      (∑ s : ↑S, cost s (assign s)) =
        ∑ i : Fin p, costFin i (i + shift) := by
    symm
    exact Fintype.sum_equiv eS
      (fun i ↦ costFin i (i + shift))
      (fun s ↦ cost s (assign s)) (fun i ↦ by
        simp [assign, costFin])
  have hrows :
      (∑ i : Fin p, ∑ j : Fin p, costFin i j) =
        ∑ s : ↑S, ∑ x : ↑P, cost s x := by
    calc
      (∑ i : Fin p, ∑ j : Fin p, costFin i j) =
          ∑ i : Fin p, ∑ x : ↑P, cost (eS i) x := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Fintype.sum_equiv eP
          (fun j ↦ costFin i j) (fun x ↦ cost (eS i) x) (fun _ ↦ rfl)
      _ = ∑ s : ↑S, ∑ x : ↑P, cost s x := by
        exact Fintype.sum_equiv eS
          (fun i ↦ ∑ x : ↑P, cost (eS i) x)
          (fun s ↦ ∑ x : ↑P, cost s x) (fun _ ↦ rfl)
  have hfinsetRows :
      (∑ s ∈ S, ∑ x ∈ P, cost s x) =
        ∑ s : ↑S, ∑ x : ↑P, cost s x := by
    rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl)]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [Finset.sum_subtype P (fun _ ↦ Iff.rfl)]
  rw [hdiag, hfinsetRows, ← hrows]
  exact hshift

end AssignmentAverage
end Erdos81
