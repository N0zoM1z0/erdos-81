import Erdos81.Copying
import Erdos81.MixedModel

/-!
# Transporting the mixed dual through graph homomorphisms

A graph homomorphism is injective on each clique, even when it is not
injective on the full vertex set.  Consequently it maps the edges of every
triangle or four-clique bijectively to the edges of a clique of the same
order.  This module proves the finite-sum reindexing explicitly and uses it to
pull a feasible mixed fractional cover back along any graph homomorphism.

Applied to `Copying.collapseHom`, this is the feasibility part of the
manuscript's vertex-copy dual-cover construction.
-/

open scoped BigOperators

namespace Erdos81
namespace CopyCover

open MixedModel

variable {V W : Type*} [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]

/-- Map a triangle or four-clique through a graph homomorphism. -/
noncomputable def mapItem {H : SimpleGraph V} {J : SimpleGraph W}
    (f : H →g J) : Item H → Item J
  | Sum.inl T => Sum.inl ⟨T.1.image f,
      by simpa [T.2.1] using Copying.card_finset_image_of_isClique f T.1 T.2.2,
      Copying.finset_image_isClique_of_hom f T.1 T.2.2⟩
  | Sum.inr K => Sum.inr ⟨K.1.image f,
      by simpa [K.2.1] using Copying.card_finset_image_of_isClique f K.1 K.2.2,
      Copying.finset_image_isClique_of_hom f K.1 K.2.2⟩

omit [Fintype V] [Fintype W] [DecidableEq V] in
@[simp]
theorem vertices_mapItem {H : SimpleGraph V} {J : SimpleGraph W}
    (f : H →g J) (i : Item H) :
    vertices (mapItem f i) = (vertices i).image f := by
  cases i <;> rfl

omit [Fintype V] [Fintype W] [DecidableEq V] in
@[simp]
theorem gain_mapItem {H : SimpleGraph V} {J : SimpleGraph W}
    (f : H →g J) (i : Item H) :
    gain (mapItem f i) = gain i := by
  cases i <;> rfl

omit [Fintype V] in
theorem uses_iff_val_mem_sym2 {H : SimpleGraph V} (i : Item H)
    (e : Resource H) :
    Uses i e ↔ e.1 ∈ (vertices i).sym2 := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h a ha
    exact h (Sym2.mem_toFinset.mpr ha)
  · intro h a ha
    exact h a (Sym2.mem_toFinset.mp ha)

/-- The finite set of graph-edge resources occurring in an item. -/
noncomputable def itemEdges {H : SimpleGraph V} (i : Item H) :
    Finset (Resource H) := by
  classical
  exact Finset.univ.filter (Uses i)

/-- The incidence-matrix sum is exactly the sum over the item's edges. -/
theorem incidence_sum_eq_itemEdges {H : SimpleGraph V} (i : Item H)
    (price : Resource H → ℚ) :
    (∑ e, incidence i e * price e) = ∑ e ∈ itemEdges i, price e := by
  classical
  rw [itemEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases h : Uses i e <;> simp [incidence, h]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- An injective map on vertices of `K` is injective on unordered pairs from `K`. -/
theorem sym2_map_injectiveOn {f : V → W} {K : Finset V}
    (hf : Set.InjOn f K) :
    Set.InjOn (Sym2.map f) K.sym2 := by
  intro e he e' he' hmap
  revert he he' hmap
  refine Sym2.inductionOn₂ e e' ?_
  intro a b c d hab hcd hm
  have hab' := Finset.mk_mem_sym2_iff.mp hab
  have hcd' := Finset.mk_mem_sym2_iff.mp hcd
  simp only [Sym2.map_mk, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk] at hm ⊢
  rcases hm with hm | hm
  · left
    exact ⟨hf hab'.1 hcd'.1 hm.1, hf hab'.2 hcd'.2 hm.2⟩
  · right
    exact ⟨hf hab'.1 hcd'.2 hm.1, hf hab'.2 hcd'.1 hm.2⟩

omit [Fintype V] [Fintype W] in
/-- An edge used by an item maps to an edge used by the image item. -/
theorem uses_mapEdgeSet {H : SimpleGraph V} {J : SimpleGraph W}
    (f : H →g J) (i : Item H) (e : Resource H) (he : Uses i e) :
    Uses (mapItem f i) (f.mapEdgeSet e) := by
  rw [uses_iff_val_mem_sym2, vertices_mapItem, Finset.sym2_image]
  apply Finset.mem_image.mpr
  refine ⟨e.1, (uses_iff_val_mem_sym2 i e).mp he, ?_⟩
  rfl

omit [Fintype V] [Fintype W] in
/-- Every edge of the image item comes from an edge of the source item. -/
theorem exists_itemEdge_of_mapItem_edge {H : SimpleGraph V}
    {J : SimpleGraph W} (f : H →g J) (i : Item H)
    (e : Resource J) (he : Uses (mapItem f i) e) :
    ∃ d : Resource H, Uses i d ∧ f.mapEdgeSet d = e := by
  have he' := (uses_iff_val_mem_sym2 (mapItem f i) e).mp he
  rw [vertices_mapItem, Finset.sym2_image] at he'
  obtain ⟨z, hz, hmap⟩ := Finset.mem_image.mp he'
  have hzEdge : z ∈ H.edgeSet := by
    revert hz hmap
    refine Sym2.inductionOn z ?_
    intro a b hz hmap
    have hab := Finset.mk_mem_sym2_iff.mp hz
    have habJ : J.Adj (f a) (f b) := by
      have hedge := e.property
      rw [← hmap] at hedge
      exact hedge
    exact item_isClique i hab.1 hab.2 (fun h ↦ habJ.ne (congrArg f h))
  let d : Resource H := ⟨z, hzEdge⟩
  refine ⟨d, (uses_iff_val_mem_sym2 i d).mpr hz, ?_⟩
  apply Subtype.ext
  exact hmap

/-- The finite edge set of an image item is the image of its source edge set. -/
theorem itemEdges_mapItem {H : SimpleGraph V} {J : SimpleGraph W}
    (f : H →g J) (i : Item H) :
    itemEdges (mapItem f i) = (itemEdges i).image f.mapEdgeSet := by
  classical
  ext e
  constructor
  · intro he
    have huses := (Finset.mem_filter.mp he).2
    obtain ⟨d, hd, hde⟩ := exists_itemEdge_of_mapItem_edge f i e huses
    apply Finset.mem_image.mpr
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, hde⟩
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, uses_mapEdgeSet f i d (Finset.mem_filter.mp hd).2⟩

omit [Fintype W] [DecidableEq W] in
/-- The induced edge map is injective on the edges of one item. -/
theorem mapEdgeSet_injectiveOn_itemEdges {H : SimpleGraph V}
    {J : SimpleGraph W} (f : H →g J) (i : Item H) :
    Set.InjOn f.mapEdgeSet (itemEdges i) := by
  classical
  intro e he d hd hed
  apply Subtype.ext
  apply sym2_map_injectiveOn
    (Copying.hom_injectiveOn_of_isClique f (item_isClique i))
  · exact (uses_iff_val_mem_sym2 i e).mp (Finset.mem_filter.mp he).2
  · exact (uses_iff_val_mem_sym2 i d).mp (Finset.mem_filter.mp hd).2
  · exact congrArg Subtype.val hed

/-- Reindexing equality for the full incidence sums of one item and its image. -/
theorem pullback_incidence_sum {H : SimpleGraph V} {J : SimpleGraph W}
    (f : H →g J) (i : Item H) (price : Resource J → ℚ) :
    (∑ e, incidence i e * price (f.mapEdgeSet e)) =
      ∑ e, incidence (mapItem f i) e * price e := by
  classical
  rw [incidence_sum_eq_itemEdges, incidence_sum_eq_itemEdges,
    itemEdges_mapItem]
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact mapEdgeSet_injectiveOn_itemEdges f i ha hb hab

/-- Pull a feasible mixed cover back along a graph homomorphism. -/
noncomputable def pullbackCover {H : SimpleGraph V} {J : SimpleGraph W}
    (f : H →g J) (d : FractionalCover J) : FractionalCover H where
  price e := d.price (f.mapEdgeSet e)
  price_nonnegative e := d.price_nonnegative (f.mapEdgeSet e)
  demand i := by
    calc
      gain i = gain (mapItem f i) := (gain_mapItem f i).symm
      _ ≤ ∑ e, incidence (mapItem f i) e * d.price e := d.demand (mapItem f i)
      _ = ∑ e, incidence i e * d.price (f.mapEdgeSet e) :=
        (pullback_incidence_sum f i d.price).symm

end CopyCover
end Erdos81
