import Erdos81.EditDistance
import Erdos81.RootedGraph
import Mathlib.Tactic

/-!
# Labelled complete-split graphs

Elementary structural and counting facts for the graph whose clique side is a
finset `K` and whose complement is independent.
-/

namespace Erdos81
namespace CompleteSplit

open SimpleGraph EditDistance RootedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

instance completeSplitGraphDecidableAdj (K : Finset V) :
    DecidableRel (completeSplitGraph K).Adj := fun x y ↦
  inferInstanceAs (Decidable (x ≠ y ∧ (x ∈ K ∨ y ∈ K)))

/-- A set is a clique in a complete-split graph exactly when it contains at
most one vertex outside the clique side. -/
theorem isClique_iff_card_sdiff_le_one (K L : Finset V) :
    (completeSplitGraph K).IsClique (L : Set V) ↔ (L \ K).card ≤ 1 := by
  classical
  constructor
  · intro hclique
    by_contra hnot
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (L \ K).card)
    have hadj := hclique
      (show x ∈ L from (Finset.mem_sdiff.mp hx).1)
      (show y ∈ L from (Finset.mem_sdiff.mp hy).1) hxy
    exact (Finset.mem_sdiff.mp hx).2
      (((completeSplitGraph_adj K x y).mp hadj).2.resolve_right
        (Finset.mem_sdiff.mp hy).2)
  · intro hcard x hx y hy hxy
    rw [completeSplitGraph_adj]
    refine ⟨hxy, ?_⟩
    by_contra hneither
    push Not at hneither
    have hsubset : {x, y} ⊆ L \ K := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hx, hneither.1⟩
      · exact Finset.mem_sdiff.mpr ⟨hy, hneither.2⟩
    have hpair : ({x, y} : Finset V).card = 2 := by simp [hxy]
    have hle := Finset.card_le_card hsubset
    omega

/-- The designated side is a clique. -/
theorem root_isClique (K : Finset V) :
    (completeSplitGraph K).IsClique (K : Set V) := by
  rw [isClique_iff_card_sdiff_le_one]
  simp

/-- There are no graph edges wholly outside the designated clique side. -/
theorem outsideEdges_eq_empty (K : Finset V) :
    outsideEdges (completeSplitGraph K) K = ∅ := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heGraph, heOutside⟩ := Finset.mem_filter.mp he
    revert heGraph heOutside
    refine Sym2.inductionOn e ?_
    intro x y hxy houtside
    have hx : x ∈ outsideVertices K := houtside (by simp)
    have hy : y ∈ outsideVertices K := houtside (by simp)
    have hadj := (completeSplitGraph K).mem_edgeFinset.mp hxy
    exact ((mem_outsideVertices.mp hx)
      (((completeSplitGraph_adj K x y).mp hadj).2.resolve_right
        (mem_outsideVertices.mp hy))).elim
  · simp

/-- Every root--outside incidence is present. -/
theorem missingIncidences_eq_zero (K : Finset V) :
    missingIncidences (completeSplitGraph K) K = 0 := by
  classical
  rw [missingIncidences, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨xy, hxy⟩
  have h := Rel.mem_interedges_iff.mp hxy
  have hroot : xy.1 ∈ K := h.1
  have hout : xy.2 ∉ K := mem_outsideVertices.mp h.2.1
  have hne : xy.1 ≠ xy.2 := by
    intro heq
    exact hout (heq ▸ hroot)
  exact h.2.2.2 ((completeSplitGraph_adj K xy.1 xy.2).mpr
    ⟨hne, Or.inl hroot⟩)

/-- Exact edge count of a labelled complete-split graph. -/
theorem card_edgeFinset (K : Finset V) :
    (completeSplitGraph K).edgeFinset.card =
      Nat.choose K.card 2 + K.card * (Fintype.card V - K.card) := by
  classical
  have h := edge_count_identity (completeSplitGraph K) K (root_isClique K)
  rw [missingIncidences_eq_zero, outsideEdges_eq_empty,
    Finset.card_empty, card_outsideVertices] at h
  simpa using h

/-- Every edge is either a clique-side edge or a spoke. -/
theorem edge_root_or_spoke (K : Finset V)
    (e : (completeSplitGraph K).edgeSet) :
    e.1.toFinset ⊆ K ∨ (e.1.toFinset \ K).card = 1 := by
  classical
  obtain ⟨e, he⟩ := e
  revert he
  refine Sym2.inductionOn e ?_
  intro x y hxy
  have hadj : (completeSplitGraph K).Adj x y :=
    (completeSplitGraph K).mem_edgeSet.mp hxy
  have hdata := (completeSplitGraph_adj K x y).mp hadj
  rcases hdata.2 with hx | hy
  · by_cases hyK : y ∈ K
    · left
      simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      exact ⟨hx, hyK⟩
    · right
      rw [Sym2.toFinset_mk_eq]
      have heq : ({x, y} : Finset V) \ K = {y} := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hzK⟩
          · exact (hzK hx).elim
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, hyK⟩
      rw [heq]
      simp
  · by_cases hxK : x ∈ K
    · left
      simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      exact ⟨hxK, hy⟩
    · right
      rw [Sym2.toFinset_mk_eq]
      have heq : ({x, y} : Finset V) \ K = {x} := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hzK⟩
          · rfl
          · exact (hzK hy).elim
        · rintro rfl
          exact ⟨Or.inl rfl, hxK⟩
      rw [heq]
      simp

end CompleteSplit
end Erdos81
