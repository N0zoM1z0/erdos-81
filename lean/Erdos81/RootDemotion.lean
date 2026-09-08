import Erdos81.RootedGraph
import Mathlib.Tactic

/-!
# Demoting heavy root columns

Given a clique root `P`, we remove every root vertex whose missing column is
larger than `|P|/64`.  This file proves the exact finite-set bookkeeping for
that operation.  In particular it charges the newly exposed outside edges;
they are not silently discarded.
-/

namespace Erdos81
namespace RootDemotion

open SimpleGraph RootedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Root vertices whose original missing column is larger than `|P|/64`. -/
noncomputable def heavyColumns (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset V := by
  classical
  exact P.filter fun x ↦ P.card < 64 * (missingColumn G P x).card

/-- The clique left after all heavy columns are demoted simultaneously. -/
noncomputable def retainedRoot (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset V :=
  P \ heavyColumns G P

@[simp]
theorem mem_heavyColumns {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x : V} :
    x ∈ heavyColumns G P ↔
      x ∈ P ∧ P.card < 64 * (missingColumn G P x).card := by
  classical
  simp [heavyColumns]

@[simp]
theorem mem_retainedRoot {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x : V} :
    x ∈ retainedRoot G P ↔
      x ∈ P ∧ 64 * (missingColumn G P x).card ≤ P.card := by
  classical
  rw [retainedRoot, Finset.mem_sdiff, mem_heavyColumns]
  constructor
  · rintro ⟨hxP, hxNotHeavy⟩
    have hxBound : ¬P.card < 64 * (missingColumn G P x).card :=
      fun h ↦ hxNotHeavy ⟨hxP, h⟩
    exact ⟨hxP, by omega⟩
  · rintro ⟨hxP, hxBound⟩
    exact ⟨hxP, fun hxHeavy ↦ by omega⟩

theorem retainedRoot_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : retainedRoot G P ⊆ P := by
  intro x hx
  exact (mem_retainedRoot.mp hx).1

theorem heavyColumns_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : heavyColumns G P ⊆ P := by
  intro x hx
  exact (mem_heavyColumns.mp hx).1

theorem retainedRoot_isClique {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V)) :
    G.IsClique (retainedRoot G P : Set V) :=
  hP.subset (retainedRoot_subset G P)

theorem card_retained_add_card_heavy
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    (retainedRoot G P).card + (heavyColumns G P).card = P.card := by
  unfold retainedRoot
  exact Finset.card_sdiff_add_card_eq_card (heavyColumns_subset G P)

/-- Demotion introduces no new missing entry in a retained column, because
the demoted vertices were in the original clique. -/
theorem missingColumn_retained_subset {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (hP : G.IsClique (P : Set V)) {x : V}
    (hx : x ∈ retainedRoot G P) :
    missingColumn G (retainedRoot G P) x ⊆ missingColumn G P x := by
  intro y hy
  have hyData := mem_missingColumn.mp hy
  have hxP := (mem_retainedRoot.mp hx).1
  apply mem_missingColumn.mpr
  refine ⟨?_, hyData.2⟩
  apply mem_outsideVertices.mpr
  intro hyP
  have hxy : x ≠ y := by
    intro hxy
    subst y
    exact (mem_outsideVertices.mp hyData.1) hx
  exact hyData.2 (hP hxP hyP hxy)

theorem maxMissingColumn_retained_le {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (hP : G.IsClique (P : Set V)) :
    maxMissingColumn G (retainedRoot G P) ≤ P.card / 64 := by
  unfold maxMissingColumn
  apply Finset.sup_le
  intro x hx
  have hsubset := missingColumn_retained_subset hP hx
  have hxBound := (mem_retainedRoot.mp hx).2
  have hcard := Finset.card_le_card hsubset
  omega

theorem missingIncidences_retained_le {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (hP : G.IsClique (P : Set V)) :
    missingIncidences G (retainedRoot G P) ≤ missingIncidences G P := by
  rw [← sum_card_missingColumn, ← sum_card_missingColumn]
  calc
    ∑ x ∈ retainedRoot G P, (missingColumn G (retainedRoot G P) x).card
        ≤ ∑ x ∈ retainedRoot G P, (missingColumn G P x).card := by
          exact Finset.sum_le_sum fun x hx ↦
            Finset.card_le_card (missingColumn_retained_subset hP hx)
    _ ≤ ∑ x ∈ P, (missingColumn G P x).card := by
      exact Finset.sum_le_sum_of_subset (retainedRoot_subset G P)

/-- Markov counting for the simultaneously demoted columns. -/
theorem heavy_count_charge (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    (heavyColumns G P).card * (P.card + 1) ≤
      64 * missingIncidences G P := by
  rw [← sum_card_missingColumn]
  calc
    (heavyColumns G P).card * (P.card + 1) =
        ∑ _x ∈ heavyColumns G P, (P.card + 1) := by simp
    _ ≤ ∑ x ∈ heavyColumns G P,
        64 * (missingColumn G P x).card := by
      exact Finset.sum_le_sum fun x hx ↦ by
        have hx' := (mem_heavyColumns.mp hx).2
        omega
    _ ≤ ∑ x ∈ P, 64 * (missingColumn G P x).card := by
      exact Finset.sum_le_sum_of_subset (heavyColumns_subset G P)
    _ = 64 * ∑ x ∈ P, (missingColumn G P x).card := by
      simp [Finset.mul_sum]

/-- The elementary binomial identity used to account for the pairs exposed
by moving `r` clique vertices outside. -/
theorem choose_two_add (a r : ℕ) :
    Nat.choose (a + r) 2 =
      Nat.choose a 2 + a * r + Nat.choose r 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, Nat.choose_succ_succ, ih,
        Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      ring

theorem card_outside_retained
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    (outsideVertices (retainedRoot G P)).card =
      (outsideVertices P).card + (heavyColumns G P).card := by
  have hparts := card_retained_add_card_heavy G P
  have hout := card_outsideVertices P
  have houtRetained := card_outsideVertices (retainedRoot G P)
  have hPcard : P.card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ P
  have hP₀card : (retainedRoot G P).card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ (retainedRoot G P)
  omega

/-- Exact pair-count identity after `r` clique vertices change roles from
root to outside. -/
theorem root_pair_count_demotion_identity
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    Nat.choose P.card 2 + P.card * (outsideVertices P).card =
      Nat.choose (retainedRoot G P).card 2 +
        (retainedRoot G P).card *
          (outsideVertices (retainedRoot G P)).card +
        (heavyColumns G P).card * (outsideVertices P).card +
        Nat.choose (heavyColumns G P).card 2 := by
  have hparts := card_retained_add_card_heavy G P
  have hout := card_outside_retained G P
  rw [← hparts, choose_two_add, hout]
  ring

/-- Every outside edge newly exposed by demotion is charged to either a
demoted--old-outside pair or a pair of demoted vertices. -/
theorem outsideEdges_retained_le {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (hP : G.IsClique (P : Set V)) :
    (outsideEdges G (retainedRoot G P)).card ≤
      (outsideEdges G P).card +
        (heavyColumns G P).card * (outsideVertices P).card +
        Nat.choose (heavyColumns G P).card 2 := by
  have hP₀ : G.IsClique (retainedRoot G P : Set V) :=
    retainedRoot_isClique hP
  have hedge := edge_count_identity G P hP
  have hedge₀ := edge_count_identity G (retainedRoot G P) hP₀
  have hmissing := missingIncidences_retained_le hP
  have hcross := crossing_add_missing G P
  have hcross₀ := crossing_add_missing G (retainedRoot G P)
  have haccount :
      G.edgeFinset.card + missingIncidences G P =
        Nat.choose P.card 2 +
          P.card * (outsideVertices P).card +
          (outsideEdges G P).card := by
    omega
  have haccount₀ :
      G.edgeFinset.card + missingIncidences G (retainedRoot G P) =
        Nat.choose (retainedRoot G P).card 2 +
          (retainedRoot G P).card *
            (outsideVertices (retainedRoot G P)).card +
          (outsideEdges G (retainedRoot G P)).card := by
    omega
  have hbase := root_pair_count_demotion_identity G P
  omega

end RootDemotion
end Erdos81
