import Erdos81.Copying
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Dist

/-!
# Labelled edit distance and complete-split templates

This module models the manuscript's distance to the family of labelled
complete-split graphs whose clique side has order `floor(n / 3)`.  It proves
the triangle inequality and the exact fact needed by the first-entry
argument: one copy of a distinct nonadjacent vertex changes this distance by
at most `n - 2`.
-/

open scoped symmDiff

namespace Erdos81
namespace EditDistance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge pairs on which two finite graphs differ. -/
noncomputable def changedEdges (G H : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e ↦ e ∈ G.edgeSet ∆ H.edgeSet

omit [DecidableEq V] in
@[simp]
theorem mem_changedEdges {G H : SimpleGraph V} {e : Sym2 V} :
    e ∈ changedEdges G H ↔ e ∈ G.edgeSet ∆ H.edgeSet := by
  classical
  simp [changedEdges]

/-- Labelled edge-edit distance. -/
noncomputable def edgeEditDistance (G H : SimpleGraph V) : ℕ :=
  (changedEdges G H).card

omit [DecidableEq V] in
theorem changedEdges_comm (G H : SimpleGraph V) :
    changedEdges G H = changedEdges H G := by
  classical
  ext e
  simp only [mem_changedEdges, Set.mem_symmDiff]
  tauto

omit [DecidableEq V] in
theorem edgeEditDistance_comm (G H : SimpleGraph V) :
    edgeEditDistance G H = edgeEditDistance H G := by
  unfold edgeEditDistance
  rw [changedEdges_comm]

theorem changedEdges_triangle_subset (G H K : SimpleGraph V) :
    changedEdges G K ⊆ changedEdges G H ∪ changedEdges H K := by
  classical
  intro e he
  simp only [Finset.mem_union, mem_changedEdges, Set.mem_symmDiff] at he ⊢
  tauto

theorem edgeEditDistance_triangle (G H K : SimpleGraph V) :
    edgeEditDistance G K ≤ edgeEditDistance G H + edgeEditDistance H K := by
  unfold edgeEditDistance
  calc
    (changedEdges G K).card ≤
        (changedEdges G H ∪ changedEdges H K).card :=
      Finset.card_le_card (changedEdges_triangle_subset G H K)
    _ ≤ (changedEdges G H).card + (changedEdges H K).card :=
      Finset.card_union_le _ _

/-- Candidate changed pairs in a copy replacing `b` by `a`. -/
noncomputable def copySupport (a b : V) : Finset (Sym2 V) := by
  classical
  exact (((Finset.univ.erase a).erase b).image fun x ↦ s(x, b))

theorem changedEdges_replaceVertex_subset (G : SimpleGraph V) {a b : V}
    (hn : ¬G.Adj a b) :
    changedEdges G (G.replaceVertex a b) ⊆ copySupport a b := by
  classical
  intro e he
  revert he
  refine Sym2.inductionOn e ?_
  intro x y he
  rw [mem_changedEdges] at he
  simp only [Set.mem_symmDiff, SimpleGraph.mem_edgeSet] at he
  by_cases hxb : x = b
  · subst x
    have hyb : y ≠ b := by
      intro h
      subst y
      simp at he
    have hya : y ≠ a := by
      intro h
      subst y
      simp [SimpleGraph.replaceVertex, hn, G.adj_comm] at he
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, ?_⟩
    simp [hya, hyb]
    exact Sym2.eq_swap
  · by_cases hyb : y = b
    · subst y
      have hxa : x ≠ a := by
        intro h
        subst x
        simp [SimpleGraph.replaceVertex, hn, G.adj_comm] at he
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp [hxa, hxb]
    · have hs := G.adj_replaceVertex_iff_of_ne a hxb hyb
      tauto

theorem card_copySupport (a b : V) (hab : a ≠ b) :
    (copySupport a b).card = Fintype.card V - 2 := by
  classical
  rw [copySupport, Finset.card_image_of_injective]
  · have ha : a ∈ (Finset.univ : Finset V) := Finset.mem_univ a
    have hb : b ∈ (Finset.univ.erase a : Finset V) := by simp [hab.symm]
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha,
      Finset.card_univ]
    omega
  · intro x y hxy
    apply (Sym2.mkEmbedding b).injective
    simpa [Sym2.eq_swap] using hxy

theorem edgeEditDistance_replaceVertex_le (G : SimpleGraph V) {a b : V}
    (hab : a ≠ b) (hn : ¬G.Adj a b) :
    edgeEditDistance G (G.replaceVertex a b) ≤ Fintype.card V - 2 := by
  classical
  unfold edgeEditDistance
  calc
    (changedEdges G (G.replaceVertex a b)).card ≤ (copySupport a b).card :=
      Finset.card_le_card (changedEdges_replaceVertex_subset G hn)
    _ = Fintype.card V - 2 := card_copySupport a b hab

theorem fixed_graph_distance_after_replaceVertex_le
    (G T : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    edgeEditDistance (G.replaceVertex a b) T ≤
      Fintype.card V - 2 + edgeEditDistance G T := by
  calc
    edgeEditDistance (G.replaceVertex a b) T ≤
        edgeEditDistance (G.replaceVertex a b) G + edgeEditDistance G T :=
      edgeEditDistance_triangle _ _ _
    _ = edgeEditDistance G (G.replaceVertex a b) + edgeEditDistance G T := by
      rw [edgeEditDistance_comm (G.replaceVertex a b) G]
    _ ≤ Fintype.card V - 2 + edgeEditDistance G T :=
      Nat.add_le_add_right (edgeEditDistance_replaceVertex_le G hab hn) _

theorem fixed_graph_distance_before_replaceVertex_le
    (G T : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    edgeEditDistance G T ≤
      Fintype.card V - 2 + edgeEditDistance (G.replaceVertex a b) T := by
  calc
    edgeEditDistance G T ≤
        edgeEditDistance G (G.replaceVertex a b) +
          edgeEditDistance (G.replaceVertex a b) T :=
      edgeEditDistance_triangle _ _ _
    _ ≤ Fintype.card V - 2 + edgeEditDistance (G.replaceVertex a b) T :=
      Nat.add_le_add_right (edgeEditDistance_replaceVertex_le G hab hn) _

/-- Minimum edit distance to a specified nonempty finite graph family. -/
noncomputable def distanceToFamily (G : SimpleGraph V)
    (family : Finset (SimpleGraph V)) (hfamily : family.Nonempty) : ℕ :=
  (family.image (edgeEditDistance G)).min' (hfamily.image _)

omit [DecidableEq V] in
theorem distanceToFamily_le (G T : SimpleGraph V)
    (family : Finset (SimpleGraph V)) (hfamily : family.Nonempty)
    (hT : T ∈ family) :
    distanceToFamily G family hfamily ≤ edgeEditDistance G T := by
  unfold distanceToFamily
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨T, hT, rfl⟩

omit [DecidableEq V] in
theorem exists_distanceToFamily_minimizer (G : SimpleGraph V)
    (family : Finset (SimpleGraph V)) (hfamily : family.Nonempty) :
    ∃ T ∈ family, edgeEditDistance G T = distanceToFamily G family hfamily := by
  unfold distanceToFamily
  have hmem := Finset.min'_mem (family.image (edgeEditDistance G)) (hfamily.image _)
  obtain ⟨T, hT, hEq⟩ := Finset.mem_image.mp hmem
  exact ⟨T, hT, hEq⟩

theorem distanceToFamily_change_le (G H : SimpleGraph V)
    (family : Finset (SimpleGraph V)) (hfamily : family.Nonempty) :
    distanceToFamily H family hfamily ≤
      edgeEditDistance G H + distanceToFamily G family hfamily := by
  obtain ⟨T, hT, hmin⟩ := exists_distanceToFamily_minimizer G family hfamily
  calc
    distanceToFamily H family hfamily ≤ edgeEditDistance H T :=
      distanceToFamily_le H T family hfamily hT
    _ ≤ edgeEditDistance H G + edgeEditDistance G T :=
      edgeEditDistance_triangle _ _ _
    _ = edgeEditDistance G H + distanceToFamily G family hfamily := by
      rw [edgeEditDistance_comm H G, hmin]

theorem distanceToFamily_after_replaceVertex_le
    (G : SimpleGraph V) (family : Finset (SimpleGraph V))
    (hfamily : family.Nonempty) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    distanceToFamily (G.replaceVertex a b) family hfamily ≤
      Fintype.card V - 2 + distanceToFamily G family hfamily := by
  calc
    distanceToFamily (G.replaceVertex a b) family hfamily ≤
        edgeEditDistance G (G.replaceVertex a b) +
          distanceToFamily G family hfamily :=
      distanceToFamily_change_le G (G.replaceVertex a b) family hfamily
    _ ≤ Fintype.card V - 2 + distanceToFamily G family hfamily :=
      Nat.add_le_add_right (edgeEditDistance_replaceVertex_le G hab hn) _

theorem distanceToFamily_before_replaceVertex_le
    (G : SimpleGraph V) (family : Finset (SimpleGraph V))
    (hfamily : family.Nonempty) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    distanceToFamily G family hfamily ≤
      Fintype.card V - 2 +
        distanceToFamily (G.replaceVertex a b) family hfamily := by
  calc
    distanceToFamily G family hfamily ≤
        edgeEditDistance (G.replaceVertex a b) G +
          distanceToFamily (G.replaceVertex a b) family hfamily :=
      distanceToFamily_change_le (G.replaceVertex a b) G family hfamily
    _ = edgeEditDistance G (G.replaceVertex a b) +
          distanceToFamily (G.replaceVertex a b) family hfamily := by
      rw [edgeEditDistance_comm (G.replaceVertex a b) G]
    _ ≤ Fintype.card V - 2 +
          distanceToFamily (G.replaceVertex a b) family hfamily :=
      Nat.add_le_add_right (edgeEditDistance_replaceVertex_le G hab hn) _

/-- The labelled complete-split graph with clique side `A`. -/
def completeSplitGraph (A : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (x ∈ A ∨ y ∈ A)
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem completeSplitGraph_adj (A : Finset V) (x y : V) :
    (completeSplitGraph A).Adj x y ↔ x ≠ y ∧ (x ∈ A ∨ y ∈ A) :=
  Iff.rfl

/-- All labelled complete-split templates with clique side of order `floor(n/3)`. -/
noncomputable def splitTemplates : Finset (SimpleGraph V) := by
  classical
  exact (Finset.univ.powersetCard (Fintype.card V / 3)).image completeSplitGraph

omit [DecidableEq V] in
theorem splitTemplates_nonempty : (splitTemplates (V := V)).Nonempty := by
  classical
  apply Finset.Nonempty.image
  exact Finset.powersetCard_nonempty.mpr (Nat.div_le_self _ _)

omit [DecidableEq V] in
theorem mem_splitTemplates {H : SimpleGraph V} :
    H ∈ splitTemplates (V := V) ↔
      ∃ A : Finset V, A.card = Fintype.card V / 3 ∧ H = completeSplitGraph A := by
  classical
  simp [splitTemplates, eq_comm]

/-- Edit distance to the labelled complete-split templates used in the manuscript. -/
noncomputable def splitEditDistance (G : SimpleGraph V) : ℕ :=
  distanceToFamily G splitTemplates splitTemplates_nonempty

theorem splitEditDistance_after_replaceVertex_le
    (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    splitEditDistance (G.replaceVertex a b) ≤
      Fintype.card V - 2 + splitEditDistance G := by
  exact distanceToFamily_after_replaceVertex_le G splitTemplates
    splitTemplates_nonempty hab hn

theorem splitEditDistance_before_replaceVertex_le
    (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    splitEditDistance G ≤
      Fintype.card V - 2 + splitEditDistance (G.replaceVertex a b) := by
  exact distanceToFamily_before_replaceVertex_le G splitTemplates
    splitTemplates_nonempty hab hn

/-- One vertex copy changes distance to the split family by at most `n - 2`. -/
theorem splitEditDistance_replaceVertex_dist_le
    (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    Nat.dist (splitEditDistance G) (splitEditDistance (G.replaceVertex a b)) ≤
      Fintype.card V - 2 := by
  have hbefore := splitEditDistance_before_replaceVertex_le G hab hn
  have hafter := splitEditDistance_after_replaceVertex_le G hab hn
  unfold Nat.dist
  omega

end EditDistance
end Erdos81
