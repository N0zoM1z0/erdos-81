import Erdos81.EditDistance
import Erdos81.RootedGraph

/-!
# Edit distance from a rooted graph to its complete-split template

This file identifies the two root-relative defects with the labelled edge
edits needed to turn a graph into the complete-split graph on the same root.
It also bounds the distance between two nested complete-split templates.
-/

namespace Erdos81
namespace RootDistance

open EditDistance RootedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Missing crossing edges, represented as unordered pairs. -/
noncomputable def missingCrossingEdges (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) : Finset (Sym2 V) :=
  crossingEdges Gᶜ P

theorem card_missingCrossingEdges (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    (missingCrossingEdges G P).card = missingIncidences G P := by
  rw [missingCrossingEdges, card_crossingEdges]
  rfl

theorem mem_missingCrossingEdges_mk {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V} {x y : V} :
    s(x, y) ∈ missingCrossingEdges G P ↔
      ((x ∈ P ∧ y ∉ P) ∨ (y ∈ P ∧ x ∉ P)) ∧ ¬ G.Adj x y := by
  classical
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp h
    have hab' := mem_crossingIncidences.mp hab
    change s(a, b) = s(x, y) at heq
    rw [Sym2.eq, Sym2.rel_iff] at heq
    rcases heq with hdir | hswap
    · rcases hdir with ⟨rfl, rfl⟩
      have hn : a ≠ b ∧ ¬ G.Adj a b := by
        simpa using hab'.2.2
      exact ⟨Or.inl ⟨hab'.1, mem_outsideVertices.mp hab'.2.1⟩,
        hn.2⟩
    · rcases hswap with ⟨rfl, rfl⟩
      have hn : a ≠ b ∧ ¬ G.Adj a b := by
        simpa using hab'.2.2
      exact ⟨Or.inr ⟨hab'.1, mem_outsideVertices.mp hab'.2.1⟩,
        (by simpa [SimpleGraph.adj_comm] using hn.2)⟩
  · rintro ⟨hroot, hnonedge⟩
    rw [missingCrossingEdges, crossingEdges]
    rcases hroot with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · apply Finset.mem_image.mpr
      refine ⟨(x, y), ?_, rfl⟩
      have hne : x ≠ y := by
        intro h
        exact hy (h ▸ hx)
      have hcomp : Gᶜ.Adj x y := by
        change x ≠ y ∧ ¬ G.Adj x y
        exact ⟨hne, hnonedge⟩
      exact mem_crossingIncidences.mpr
        ⟨hx, mem_outsideVertices.mpr hy, hcomp⟩
    · apply Finset.mem_image.mpr
      refine ⟨(y, x), ?_, Sym2.eq_swap⟩
      have hne : y ≠ x := by
        intro h
        exact hx (h ▸ hy)
      have hcomp : Gᶜ.Adj y x := by
        change y ≠ x ∧ ¬ G.Adj y x
        exact ⟨hne, by simpa [SimpleGraph.adj_comm] using hnonedge⟩
      exact mem_crossingIncidences.mpr
        ⟨hy, mem_outsideVertices.mpr hx, hcomp⟩

theorem mem_outsideEdges_mk {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} :
    s(x, y) ∈ outsideEdges G P ↔ x ∉ P ∧ y ∉ P ∧ G.Adj x y := by
  classical
  simp only [outsideEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq]
  constructor
  · rintro ⟨hxy, hsub⟩
    refine ⟨?_, ?_, hxy⟩
    · exact mem_outsideVertices.mp
        (hsub (Finset.mem_insert_self x {y}))
    · exact mem_outsideVertices.mp
        (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨hxy, ?_⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_outsideVertices.mpr hx
    · exact mem_outsideVertices.mpr hy

/-- For a clique root, the edits to its complete-split template are exactly
the outside edges and the missing root--outside edges. -/
theorem changedEdges_completeSplitGraph (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V)
    (hP : G.IsClique (P : Set V)) :
    changedEdges G (completeSplitGraph P) =
      outsideEdges G P ∪ missingCrossingEdges G P := by
  classical
  ext e
  refine Sym2.inductionOn e ?_
  intro x y
  simp only [mem_changedEdges, Set.mem_symmDiff, SimpleGraph.mem_edgeSet,
    completeSplitGraph_adj, Finset.mem_union, mem_outsideEdges_mk,
    mem_missingCrossingEdges_mk]
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hx : x ∈ P
  · by_cases hy : y ∈ P
    · have hadj : G.Adj x y := hP hx hy hxy
      simp [hxy, hx, hy, hadj]
    · simp [hxy, hx, hy]
  · by_cases hy : y ∈ P
    · simp [hxy, hx, hy]
    · simp [hxy, hx, hy]

theorem outsideEdges_disjoint_missingCrossingEdges (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    Disjoint (outsideEdges G P) (missingCrossingEdges G P) := by
  classical
  rw [Finset.disjoint_left]
  intro e hout hmissing
  revert hout hmissing
  refine Sym2.inductionOn e ?_
  intro x y hout hmissing
  exact (mem_missingCrossingEdges_mk.mp hmissing).2
    (mem_outsideEdges_mk.mp hout).2.2

/-- Exact defect interpretation as a labelled edit distance. -/
theorem edgeEditDistance_completeSplitGraph (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V)
    (hP : G.IsClique (P : Set V)) :
    edgeEditDistance G (completeSplitGraph P) =
      (outsideEdges G P).card + missingIncidences G P := by
  rw [edgeEditDistance, changedEdges_completeSplitGraph G P hP,
    Finset.card_union_of_disjoint
      (outsideEdges_disjoint_missingCrossingEdges G P),
    card_missingCrossingEdges]

/-- All unordered pairs incident with at least one vertex of `U`. -/
noncomputable def vertexEdgeSupport (U : Finset V) : Finset (Sym2 V) :=
  U.biUnion fun x ↦ (⊤ : SimpleGraph V).incidenceFinset x

theorem card_vertexEdgeSupport_le (U : Finset V) :
    (vertexEdgeSupport U).card ≤ U.card * Fintype.card V := by
  classical
  calc
    (vertexEdgeSupport U).card ≤
        ∑ x ∈ U, ((⊤ : SimpleGraph V).incidenceFinset x).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ U, Fintype.card V := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using
        Nat.le_of_lt ((⊤ : SimpleGraph V).degree_lt_card_verts x)
    _ = U.card * Fintype.card V := by simp

theorem changedEdges_nested_completeSplitGraph_subset {P A : Finset V}
    (hPA : P ⊆ A) :
    changedEdges (completeSplitGraph A) (completeSplitGraph P) ⊆
      vertexEdgeSupport (A \ P) := by
  classical
  intro e he
  revert he
  refine Sym2.inductionOn e ?_
  intro x y he
  simp only [mem_changedEdges, Set.mem_symmDiff, SimpleGraph.mem_edgeSet,
    completeSplitGraph_adj] at he
  have hne : x ≠ y := by tauto
  have hu : x ∈ A \ P ∨ y ∈ A \ P := by
    simp only [Finset.mem_sdiff]
    by_cases hxP : x ∈ P
    · have hxA : x ∈ A := hPA hxP
      by_cases hyP : y ∈ P
      · have hyA : y ∈ A := hPA hyP
        tauto
      · by_cases hyA : y ∈ A
        · exact Or.inr ⟨hyA, hyP⟩
        · tauto
    · by_cases hyP : y ∈ P
      · have hyA : y ∈ A := hPA hyP
        by_cases hxA : x ∈ A
        · exact Or.inl ⟨hxA, hxP⟩
        · tauto
      · by_cases hxA : x ∈ A
        · exact Or.inl ⟨hxA, hxP⟩
        · by_cases hyA : y ∈ A
          · exact Or.inr ⟨hyA, hyP⟩
          · tauto
  rw [vertexEdgeSupport]
  rcases hu with hxu | hyu
  · apply Finset.mem_biUnion.mpr
    refine ⟨x, hxu, ?_⟩
    simp [SimpleGraph.mem_incidenceFinset, hne]
  · apply Finset.mem_biUnion.mpr
    refine ⟨y, hyu, ?_⟩
    simp [SimpleGraph.mem_incidenceFinset,
      SimpleGraph.mk'_mem_incidenceSet_iff, hne]

/-- Moving from a root `A` to a nested root `P` changes at most
`|A \ P| |V|` template edges. -/
theorem edgeEditDistance_nested_completeSplitGraph_le {P A : Finset V}
    (hPA : P ⊆ A) :
    edgeEditDistance (completeSplitGraph A) (completeSplitGraph P) ≤
      (A.card - P.card) * Fintype.card V := by
  unfold edgeEditDistance
  calc
    (changedEdges (completeSplitGraph A) (completeSplitGraph P)).card ≤
        (vertexEdgeSupport (A \ P)).card :=
      Finset.card_le_card (changedEdges_nested_completeSplitGraph_subset hPA)
    _ ≤ (A \ P).card * Fintype.card V := card_vertexEdgeSupport_le _
    _ = (A.card - P.card) * Fintype.card V := by
      rw [Finset.card_sdiff_of_subset hPA]

/-- Every missing edge inside `A` is an edit against the complete-split
template with clique side `A`. -/
theorem induced_complement_edges_le_distance (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) :
    (G.induce (A : Set V))ᶜ.edgeFinset.card ≤
      edgeEditDistance G (completeSplitGraph A) := by
  classical
  let inclusion : A ↪ V := Function.Embedding.subtype _
  have hsubset :
      (G.induce (A : Set V))ᶜ.edgeFinset.map inclusion.sym2Map ⊆
        changedEdges G (completeSplitGraph A) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    revert he'
    refine Sym2.inductionOn e' ?_
    intro x y he'
    have hcomp : x ≠ y ∧ ¬ G.Adj x y := by
      simpa using
        (G.induce (A : Set V))ᶜ.mem_edgeSet.mp
          ((G.induce (A : Set V))ᶜ.mem_edgeFinset.mp he')
    have hne : (x : V) ≠ (y : V) := by
      intro hxy
      exact hcomp.1 (Subtype.ext hxy)
    change s((x : V), (y : V)) ∈ changedEdges G (completeSplitGraph A)
    rw [mem_changedEdges]
    simp only [Set.mem_symmDiff, SimpleGraph.mem_edgeSet,
      completeSplitGraph_adj]
    exact Or.inr ⟨⟨hne, Or.inl x.property⟩, hcomp.2⟩
  unfold edgeEditDistance
  calc
    (G.induce (A : Set V))ᶜ.edgeFinset.card =
        ((G.induce (A : Set V))ᶜ.edgeFinset.map inclusion.sym2Map).card := by
      rw [Finset.card_map]
    _ ≤ (changedEdges G (completeSplitGraph A)).card :=
      Finset.card_le_card hsubset

/-- Resize an arbitrary root to any feasible target cardinality, paying at
most one vertex-order of edits for each changed root role. -/
theorem exists_resized_completeSplitGraph (P : Finset V) {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = k ∧
      edgeEditDistance (completeSplitGraph P) (completeSplitGraph A) ≤
        Nat.dist P.card k * Fintype.card V := by
  classical
  by_cases hkp : k ≤ P.card
  · obtain ⟨A, hAP, hAcard⟩ := Finset.exists_subset_card_eq hkp
    refine ⟨A, hAcard, ?_⟩
    have hbound := edgeEditDistance_nested_completeSplitGraph_le hAP
    simpa [hAcard, Nat.dist_eq_sub_of_le_right hkp] using hbound
  · have hpk : P.card ≤ k := Nat.le_of_not_ge hkp
    obtain ⟨A, hPA, hAcard⟩ := Finset.exists_superset_card_eq hpk hk
    refine ⟨A, hAcard, ?_⟩
    rw [edgeEditDistance_comm]
    have hbound := edgeEditDistance_nested_completeSplitGraph_le hPA
    simpa [hAcard, Nat.dist_eq_sub_of_le hpk] using hbound

/-- A clique root gives an explicit upper bound for distance to the balanced
complete-split family: its two graph defects plus the cost of resizing its
role set to `floor(n/3)`. -/
theorem splitEditDistance_le_rootDefects_add_roles
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (hP : G.IsClique (P : Set V)) :
    splitEditDistance G ≤
      (outsideEdges G P).card + missingIncidences G P +
        Nat.dist P.card (Fintype.card V / 3) * Fintype.card V := by
  classical
  obtain ⟨A, hAcard, hroles⟩ :=
    exists_resized_completeSplitGraph P
      (k := Fintype.card V / 3) (by omega)
  have htemplate : completeSplitGraph A ∈ splitTemplates (V := V) :=
    mem_splitTemplates.mpr ⟨A, hAcard, rfl⟩
  calc
    splitEditDistance G ≤ edgeEditDistance G (completeSplitGraph A) :=
      distanceToFamily_le G (completeSplitGraph A) splitTemplates
        splitTemplates_nonempty htemplate
    _ ≤ edgeEditDistance G (completeSplitGraph P) +
        edgeEditDistance (completeSplitGraph P) (completeSplitGraph A) :=
      edgeEditDistance_triangle _ _ _
    _ ≤ ((outsideEdges G P).card + missingIncidences G P) +
        Nat.dist P.card (Fintype.card V / 3) * Fintype.card V := by
      rw [edgeEditDistance_completeSplitGraph G P hP]
      exact Nat.add_le_add_left hroles _

/-- For an arbitrary complete-split graph, only the root-role imbalance is
needed to reach the balanced complete-split family. -/
theorem splitEditDistance_completeSplitGraph_le_roles (P : Finset V) :
    splitEditDistance (completeSplitGraph P) ≤
      Nat.dist P.card (Fintype.card V / 3) * Fintype.card V := by
  classical
  obtain ⟨A, hAcard, hroles⟩ :=
    exists_resized_completeSplitGraph P
      (k := Fintype.card V / 3) (by omega)
  have htemplate : completeSplitGraph A ∈ splitTemplates (V := V) :=
    mem_splitTemplates.mpr ⟨A, hAcard, rfl⟩
  exact (distanceToFamily_le (completeSplitGraph P) (completeSplitGraph A)
    splitTemplates splitTemplates_nonempty htemplate).trans hroles

end RootDistance
end Erdos81
