import Erdos81.CliquePartitionCounting
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Tactic

/-!
# A graph viewed from a root clique

This file formalizes the bookkeeping used throughout the terminal and local
arguments.  For a chosen root finset `P`, graph edges split uniquely into
root edges, outside edges, and crossing edges.  When `P` is a clique this gives
the exact identity

`e(G) = choose(|P|, 2) + |P| |V \ P| - A + m`,

where `A` counts missing root--outside incidences and `m` counts outside
edges.
-/

namespace Erdos81
namespace RootedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices outside the selected root. -/
def outsideVertices (P : Finset V) : Finset V :=
  Finset.univ \ P

@[simp]
theorem mem_outsideVertices {P : Finset V} {v : V} :
    v ∈ outsideVertices P ↔ v ∉ P := by
  simp [outsideVertices]

theorem root_disjoint_outside (P : Finset V) :
    Disjoint P (outsideVertices P) := by
  rw [Finset.disjoint_left]
  simp [outsideVertices]

theorem root_union_outside (P : Finset V) :
    P ∪ outsideVertices P = Finset.univ := by
  simp [outsideVertices]

theorem card_outsideVertices (P : Finset V) :
    (outsideVertices P).card = Fintype.card V - P.card := by
  rw [outsideVertices,
    Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ]

/-- Graph edges with both endpoints in the root. -/
noncomputable def rootEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e ↦ e.toFinset ⊆ P

/-- Graph edges with both endpoints outside the root. -/
noncomputable def outsideEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e ↦ e.toFinset ⊆ outsideVertices P

/-- Ordered root--outside incidences which are graph edges. -/
noncomputable def crossingIncidences (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) : Finset (V × V) :=
  G.interedges P (outsideVertices P)

@[simp]
theorem mem_crossingIncidences {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} :
    (x, y) ∈ crossingIncidences G P ↔
      x ∈ P ∧ y ∈ outsideVertices P ∧ G.Adj x y :=
  Rel.mem_interedges_iff

/-- Unordered graph edges crossing between the root and its outside. -/
noncomputable def crossingEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) :=
  (crossingIncidences G P).image fun xy ↦ s(xy.1, xy.2)

theorem crossing_pair_injective (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Set.InjOn (fun xy : V × V ↦ s(xy.1, xy.2))
      (crossingIncidences G P : Set (V × V)) := by
  intro ⟨x, u⟩ hxu ⟨y, v⟩ hyv hEq
  have hxu' : x ∈ P ∧ u ∈ outsideVertices P ∧ G.Adj x u :=
    mem_crossingIncidences.mp hxu
  have hyv' : y ∈ P ∧ v ∈ outsideVertices P ∧ G.Adj y v :=
    mem_crossingIncidences.mp hyv
  change s(x, u) = s(y, v) at hEq
  rw [Sym2.eq, Sym2.rel_iff] at hEq
  rcases hEq with hDirect | hSwap
  · exact Prod.ext hDirect.1 hDirect.2
  · exfalso
    exact (mem_outsideVertices.mp hyv'.2.1) (hSwap.1 ▸ hxu'.1)

theorem card_crossingEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    (crossingEdges G P).card = (crossingIncidences G P).card := by
  classical
  exact Finset.card_image_of_injOn (crossing_pair_injective G P)

/-- Every graph edge belongs to exactly one of the three root-relative edge
types. -/
theorem edgeFinset_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    G.edgeFinset = rootEdges G P ∪ (outsideEdges G P ∪ crossingEdges G P) := by
  classical
  ext e
  constructor
  · intro he
    revert he
    refine Sym2.inductionOn e ?_
    intro x y hxy
    have hAdj : G.Adj x y :=
      G.mem_edgeSet.mp (G.mem_edgeFinset.mp hxy)
    by_cases hx : x ∈ P
    · by_cases hy : y ∈ P
      · apply Finset.mem_union.mpr (Or.inl ?_)
        apply Finset.mem_filter.mpr
        refine ⟨hxy, ?_⟩
        intro z hz
        simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
          Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      · apply Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr ?_)))
        apply Finset.mem_image.mpr
        refine ⟨(x, y), ?_, rfl⟩
        simp [crossingIncidences, SimpleGraph.mem_interedges_iff, hx, hy,
          hAdj]
    · by_cases hy : y ∈ P
      · apply Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr ?_)))
        apply Finset.mem_image.mpr
        refine ⟨(y, x), ?_, Sym2.eq_swap⟩
        simp [crossingIncidences, SimpleGraph.mem_interedges_iff, hx, hy,
          hAdj.symm]
      · apply Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl ?_)))
        apply Finset.mem_filter.mpr
        refine ⟨hxy, ?_⟩
        intro z hz
        simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
          Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_outsideVertices.mpr hx
        · exact mem_outsideVertices.mpr hy
  · intro he
    rcases Finset.mem_union.mp he with hroot | houtCross
    · exact (Finset.mem_filter.mp hroot).1
    · rcases Finset.mem_union.mp houtCross with hout | hcross
      · exact (Finset.mem_filter.mp hout).1
      · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hcross
        exact G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr
          (mem_crossingIncidences.mp hxy).2.2)

theorem rootEdges_disjoint_outsideEdges (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    Disjoint (rootEdges G P) (outsideEdges G P) := by
  classical
  rw [Finset.disjoint_left]
  intro e hroot hout
  obtain ⟨he, hsubsetRoot⟩ := Finset.mem_filter.mp hroot
  obtain ⟨_, hsubsetOut⟩ := Finset.mem_filter.mp hout
  revert he hsubsetRoot hsubsetOut
  refine Sym2.inductionOn e ?_
  intro x y hxy hxRoot hxOut
  have hx : x ∈ s(x, y).toFinset :=
    Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)
  exact (mem_outsideVertices.mp (hxOut hx)) (hxRoot hx)

theorem rootEdges_disjoint_crossingEdges (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    Disjoint (rootEdges G P) (crossingEdges G P) := by
  classical
  rw [Finset.disjoint_left]
  intro e hroot hcross
  obtain ⟨he, hsubset⟩ := Finset.mem_filter.mp hroot
  obtain ⟨⟨x, y⟩, hxy, hEq⟩ := Finset.mem_image.mp hcross
  have hyOut : y ∈ outsideVertices P :=
    (mem_crossingIncidences.mp hxy).2.1
  have hyPair : y ∈ s(x, y).toFinset :=
    Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y)
  have hyRoot : y ∈ P := hsubset (hEq ▸ hyPair)
  exact (mem_outsideVertices.mp hyOut) hyRoot

theorem outsideEdges_disjoint_crossingEdges (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    Disjoint (outsideEdges G P) (crossingEdges G P) := by
  classical
  rw [Finset.disjoint_left]
  intro e hout hcross
  obtain ⟨he, hsubset⟩ := Finset.mem_filter.mp hout
  obtain ⟨⟨x, y⟩, hxy, hEq⟩ := Finset.mem_image.mp hcross
  have hxRoot : x ∈ P := (mem_crossingIncidences.mp hxy).1
  have hxPair : x ∈ s(x, y).toFinset :=
    Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)
  have hxOut : x ∈ outsideVertices P := hsubset (hEq ▸ hxPair)
  exact (mem_outsideVertices.mp hxOut) hxRoot

/-- Cardinal form of the three-way edge partition. -/
theorem card_edgeFinset_eq_three_parts (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    G.edgeFinset.card = (rootEdges G P).card +
      (outsideEdges G P).card + (crossingEdges G P).card := by
  rw [edgeFinset_partition G P,
    Finset.card_union_of_disjoint
      (Finset.disjoint_union_right.mpr
        ⟨rootEdges_disjoint_outsideEdges G P,
          rootEdges_disjoint_crossingEdges G P⟩),
    Finset.card_union_of_disjoint (outsideEdges_disjoint_crossingEdges G P)]
  omega

/-- Missing root--outside incidences. -/
noncomputable def missingIncidences (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) : ℕ :=
  (Gᶜ.interedges P (outsideVertices P)).card

theorem crossing_add_missing (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    (crossingEdges G P).card + missingIncidences G P =
      P.card * (outsideVertices P).card := by
  rw [card_crossingEdges, missingIncidences, crossingIncidences]
  exact G.card_interedges_add_card_interedges_compl
    (root_disjoint_outside P)

/-- Outside vertices which fail to be adjacent to a fixed root vertex. -/
noncomputable def missingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (x : V) : Finset V :=
  (outsideVertices P).filter fun y ↦ ¬ G.Adj x y

@[simp]
theorem mem_missingColumn {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {x y : V} :
    y ∈ missingColumn G P x ↔ y ∈ outsideVertices P ∧ ¬ G.Adj x y := by
  simp [missingColumn]

/-- The total missing incidence count is the sum of the missing-column
sizes.  This fixes the orientation of the root--outside incidence count once
and for all. -/
theorem sum_card_missingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    ∑ x ∈ P, (missingColumn G P x).card = missingIncidences G P := by
  classical
  let S : Finset (V × V) := Gᶜ.interedges P (outsideVertices P)
  have hMaps : (S : Set (V × V)).MapsTo Prod.fst P := by
    intro xy hxy
    exact (Rel.mem_interedges_iff.mp hxy).1
  have hFibers : ∀ x ∈ P,
      (S.filter fun xy ↦ xy.1 = x).card = (missingColumn G P x).card := by
    intro x hx
    apply Finset.card_bij (fun xy _ ↦ xy.2)
    · intro xy hxy
      simp only [Finset.mem_filter] at hxy
      have hInter := Rel.mem_interedges_iff.mp hxy.1
      have hFirst : xy.1 = x := hxy.2
      exact mem_missingColumn.mpr
        ⟨hInter.2.1, by simpa [hFirst] using hInter.2.2.2⟩
    · intro xy₁ hxy₁ xy₂ hxy₂ hSecond
      simp only [Finset.mem_filter] at hxy₁ hxy₂
      exact Prod.ext (hxy₁.2.trans hxy₂.2.symm) hSecond
    · intro y hy
      have hy' := mem_missingColumn.mp hy
      refine ⟨(x, y), ?_, rfl⟩
      simp only [Finset.mem_filter]
      refine ⟨Rel.mem_interedges_iff.mpr ⟨hx, hy'.1, ?_⟩, trivial⟩
      refine ⟨?_, hy'.2⟩
      intro hxy
      have hxy' : x = y := by simpa using hxy
      exact (mem_outsideVertices.mp hy'.1) (hxy' ▸ hx)
  rw [missingIncidences]
  change ∑ x ∈ P, (missingColumn G P x).card = S.card
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  exact Finset.sum_congr rfl fun x hx ↦ (hFibers x hx).symm

/-- Maximum missing degree of a root vertex into the outside. -/
noncomputable def maxMissingColumn (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) : ℕ :=
  P.sup fun x ↦ (missingColumn G P x).card

theorem card_missingColumn_le_max (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) {x : V} (hx : x ∈ P) :
    (missingColumn G P x).card ≤ maxMissingColumn G P := by
  exact Finset.le_sup (f := fun x ↦ (missingColumn G P x).card) hx

theorem missingIncidences_le_card_mul_max (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    missingIncidences G P ≤ P.card * maxMissingColumn G P := by
  rw [← sum_card_missingColumn]
  calc
    ∑ x ∈ P, (missingColumn G P x).card
        ≤ ∑ _x ∈ P, maxMissingColumn G P := by
          exact Finset.sum_le_sum fun x hx ↦ card_missingColumn_le_max G P hx
    _ = P.card * maxMissingColumn G P := by simp

/-- Exact root-relative edge bookkeeping. -/
theorem edge_count_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (hClique : G.IsClique (P : Set V)) :
    G.edgeFinset.card = Nat.choose P.card 2 +
      P.card * (outsideVertices P).card - missingIncidences G P +
        (outsideEdges G P).card := by
  have hRoot : (rootEdges G P).card = Nat.choose P.card 2 := by
    exact CliquePartitionCounting.card_blockEdges P hClique
  have hParts := card_edgeFinset_eq_three_parts G P
  have hCross := crossing_add_missing G P
  rw [hRoot] at hParts
  omega

/-- The graph obtained by retaining exactly the outside edges.  Root vertices
remain in the ambient type as isolated vertices; this avoids coercions when
applying an edge colouring to the original graph. -/
def outsideGraph (G : SimpleGraph V) (P : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ P ∧ y ∉ P
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl x h := G.loopless.irrefl x h.1

instance outsideGraphDecidableAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : DecidableRel (outsideGraph G P).Adj :=
  fun x y ↦ inferInstanceAs (Decidable (G.Adj x y ∧ x ∉ P ∧ y ∉ P))

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem outsideGraph_adj (G : SimpleGraph V) (P : Finset V) (x y : V) :
    (outsideGraph G P).Adj x y ↔ G.Adj x y ∧ x ∉ P ∧ y ∉ P :=
  Iff.rfl

theorem outsideGraph_edgeFinset (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    (outsideGraph G P).edgeFinset = outsideEdges G P := by
  classical
  apply Finset.ext
  intro e
  refine Sym2.inductionOn e ?_
  intro x y
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    outsideGraph_adj, outsideEdges, Finset.mem_filter,
    Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
    mem_outsideVertices]

theorem card_outsideGraph_edges (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) :
    (outsideGraph G P).edgeFinset.card = (outsideEdges G P).card := by
  rw [outsideGraph_edgeFinset]

end RootedGraph
end Erdos81
