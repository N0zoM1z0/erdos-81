import Erdos81.Copying
import Erdos81.DiscreteConvexity
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

section OppositeCopies

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Extend an edge price by zero to all unordered vertex pairs. -/
noncomputable def extendPrice {G : SimpleGraph X}
    (price : Resource G → ℚ) (e : Sym2 X) : ℚ := by
  classical
  exact if h : e ∈ G.edgeSet then price ⟨e, h⟩ else 0

omit [Fintype X] [DecidableEq X] in
@[simp]
theorem extendPrice_of_mem {G : SimpleGraph X} (price : Resource G → ℚ)
    (e : Sym2 X) (he : e ∈ G.edgeSet) :
    extendPrice price e = price ⟨e, he⟩ := by
  simp [extendPrice, he]

omit [DecidableEq X] in
/-- Summing the zero extension over the edge finset recovers the subtype sum. -/
theorem sum_extendPrice_edgeFinset {G : SimpleGraph X}
    (price : Resource G → ℚ) :
    (∑ e ∈ G.edgeFinset, extendPrice price e) = ∑ e, price e := by
  classical
  rw [Finset.sum_subtype G.edgeFinset (fun e ↦ G.mem_edgeFinset)]
  apply Fintype.sum_congr
  intro e
  exact extendPrice_of_mem price e.1 e.2

omit [DecidableEq X] in
/-- Express a homomorphic edge-price pullback as a sum over the domain edge finset. -/
theorem mapped_edge_sum_eq_edgeFinset {H G : SimpleGraph X}
    (f : H →g G) (price : Resource G → ℚ) :
    (∑ e : Resource H, price (f.mapEdgeSet e)) =
      ∑ z ∈ H.edgeFinset, extendPrice price (Sym2.map f z) := by
  classical
  rw [Finset.sum_subtype H.edgeFinset (fun e ↦ H.mem_edgeFinset)]
  apply Fintype.sum_congr
  intro e
  symm
  apply extendPrice_of_mem

omit [Fintype X] in
/-- The collapse map fixes an unordered pair which does not contain its target. -/
theorem collapse_sym2_eq_self_of_not_mem (a b : X) (z : Sym2 X)
    (hb : b ∉ z) :
    Sym2.map (Copying.collapseVertex a b) z = z := by
  revert hb
  refine Sym2.inductionOn z ?_
  intro x y hb
  simp only [Sym2.mem_iff, not_or] at hb
  simp [Copying.collapseVertex, Ne.symm hb.1, Ne.symm hb.2]

/-- Incident edges are the image of the neighbor finset under `x ↦ {a,x}`. -/
theorem incidenceFinset_eq_neighbor_image (G : SimpleGraph X) (a : X)
    [DecidableRel G.Adj] :
    G.incidenceFinset a = (G.neighborFinset a).image (fun x ↦ s(a, x)) := by
  ext z
  refine Sym2.inductionOn z ?_
  intro x y
  simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mk'_mem_incidenceSet_iff, Finset.mem_image, Sym2.eq,
    Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  constructor
  · rintro ⟨hxy, hax | hay⟩
    · subst x
      exact ⟨y, hxy, Or.inl ⟨rfl, rfl⟩⟩
    · subst y
      exact ⟨x, hxy.symm, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨z, haz, (⟨hax, hzy⟩ | ⟨hay, hzx⟩)⟩
    · subst x
      subst y
      exact ⟨haz, Or.inl rfl⟩
    · subst y
      subst x
      exact ⟨haz.symm, Or.inr rfl⟩

/--
The weight of one collapsed cover is the weight away from the old target,
plus the weight incident with the copied source.
-/
theorem mapped_collapse_sum_eq_complement_add_incident
    (G : SimpleGraph X) [DecidableRel G.Adj] {a b : X}
    (hn : ¬G.Adj a b) (price : Resource G → ℚ) :
    (∑ e : Resource (G.replaceVertex a b),
        price ((Copying.collapseHom G).mapEdgeSet e)) =
      (∑ z ∈ G.edgeFinset \ G.incidenceFinset b, extendPrice price z) +
        ∑ z ∈ G.incidenceFinset a, extendPrice price z := by
  classical
  rw [mapped_edge_sum_eq_edgeFinset]
  have hedgeEq : (G.replaceVertex a b).edgeFinset =
      G.edgeFinset \ G.incidenceFinset b ∪
        (G.neighborFinset a).image (fun x ↦ s(x, b)) := by
    apply Finset.coe_injective
    push_cast
    exact G.edgeSet_replaceVertex_of_not_adj hn
  rw [hedgeEq]
  have hdis : Disjoint (G.edgeFinset \ G.incidenceFinset b)
      ((G.neighborFinset a).image (fun x ↦ s(x, b))) := by
    rw [Finset.disjoint_left]
    intro z hz hnew
    have hbnot : b ∉ z := by
      intro hbz
      exact (Finset.mem_sdiff.mp hz).2 <|
        (G.mem_incidenceFinset b z).mpr
          ⟨G.mem_edgeFinset.mp (Finset.mem_sdiff.mp hz).1, hbz⟩
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hnew
    exact hbnot (Sym2.mem_mk_right x b)
  rw [Finset.sum_union hdis]
  congr 1
  · apply Finset.sum_congr rfl
    intro z hz
    apply congrArg (extendPrice price)
    apply collapse_sym2_eq_self_of_not_mem
    intro hbz
    exact (Finset.mem_sdiff.mp hz).2 <|
      (G.mem_incidenceFinset b z).mpr
        ⟨G.mem_edgeFinset.mp (Finset.mem_sdiff.mp hz).1, hbz⟩
  · rw [incidenceFinset_eq_neighbor_image]
    have hinjB : Function.Injective (fun x : X ↦ s(x, b)) := by
      intro x y hxy
      apply (Sym2.mkEmbedding b).injective
      simpa [Sym2.eq_swap] using hxy
    have hinjA : Function.Injective (fun x : X ↦ s(a, x)) :=
      (Sym2.mkEmbedding a).injective
    rw [Finset.sum_image hinjB.injOn, Finset.sum_image hinjA.injOn]
    apply Finset.sum_congr rfl
    intro x hx
    have hxb : x ≠ b := by
      intro h
      subst x
      exact hn ((G.mem_neighborFinset a b).mp hx)
    congr 1
    simp [Copying.collapseHom, Copying.collapseVertex, hxb, Sym2.eq_swap]

/-- The two opposite collapse pullbacks have exactly twice the original weight. -/
theorem opposite_collapse_edge_sum
    (G : SimpleGraph X) [DecidableRel G.Adj] {a b : X}
    (hn : ¬G.Adj a b) (price : Resource G → ℚ) :
    (∑ e : Resource (G.replaceVertex a b),
        price ((Copying.collapseHom G).mapEdgeSet e)) +
      (∑ e : Resource (G.replaceVertex b a),
        price ((Copying.collapseHom G).mapEdgeSet e)) =
      2 * ∑ e : Resource G, price e := by
  classical
  have hnr : ¬G.Adj b a := by simpa [G.adj_comm] using hn
  rw [mapped_collapse_sum_eq_complement_add_incident G hn price]
  rw [mapped_collapse_sum_eq_complement_add_incident G hnr price]
  have hsubA : G.incidenceFinset a ⊆ G.edgeFinset := by
    intro z hz
    exact G.mem_edgeFinset.mpr
      (G.incidenceSet_subset a ((G.mem_incidenceFinset a z).mp hz))
  have hsubB : G.incidenceFinset b ⊆ G.edgeFinset := by
    intro z hz
    exact G.mem_edgeFinset.mpr
      (G.incidenceSet_subset b ((G.mem_incidenceFinset b z).mp hz))
  have hpartA := Finset.sum_sdiff (f := extendPrice price) hsubA
  have hpartB := Finset.sum_sdiff (f := extendPrice price) hsubB
  have htotal := sum_extendPrice_edgeFinset price
  calc
    ((∑ z ∈ G.edgeFinset \ G.incidenceFinset b, extendPrice price z) +
          ∑ z ∈ G.incidenceFinset a, extendPrice price z) +
        ((∑ z ∈ G.edgeFinset \ G.incidenceFinset a, extendPrice price z) +
          ∑ z ∈ G.incidenceFinset b, extendPrice price z) =
      ((∑ z ∈ G.edgeFinset \ G.incidenceFinset b, extendPrice price z) +
          ∑ z ∈ G.incidenceFinset b, extendPrice price z) +
        ((∑ z ∈ G.edgeFinset \ G.incidenceFinset a, extendPrice price z) +
          ∑ z ∈ G.incidenceFinset a, extendPrice price z) := by ring
    _ = (∑ z ∈ G.edgeFinset, extendPrice price z) +
        ∑ z ∈ G.edgeFinset, extendPrice price z := by rw [hpartB, hpartA]
    _ = 2 * ∑ e : Resource G, price e := by rw [htotal]; ring

/-- The objective identity for the two feasible covers used in the copy argument. -/
theorem coverValue_opposite_pullbacks
    (G : SimpleGraph X) [DecidableRel G.Adj] {a b : X}
    (hn : ¬G.Adj a b) (d : FractionalCover G) :
    coverValue (pullbackCover (Copying.collapseHom (G := G) (s := a) (t := b)) d) +
        coverValue (pullbackCover (Copying.collapseHom (G := G) (s := b) (t := a)) d) =
      2 * coverValue d := by
  change
    (∑ e : Resource (G.replaceVertex a b),
        d.price ((Copying.collapseHom G).mapEdgeSet e)) +
      (∑ e : Resource (G.replaceVertex b a),
        d.price ((Copying.collapseHom G).mapEdgeSet e)) =
      2 * ∑ e : Resource G, d.price e
  exact opposite_collapse_edge_sum G hn d.price

/-- Opposite copied graphs' certified dual optima sum to at most twice the source optimum. -/
theorem cover_optima_opposite_copy
    (G : SimpleGraph X) [DecidableRel G.Adj] {a b : X}
    (hn : ¬G.Adj a b) {w wAB wBA : ℚ}
    (hG : IsCoverOptimum (G := G) w)
    (hAB : IsCoverOptimum (G := G.replaceVertex a b) wAB)
    (hBA : IsCoverOptimum (G := G.replaceVertex b a) wBA) :
    wAB + wBA ≤ 2 * w := by
  obtain ⟨d, hd⟩ := hG.1
  calc
    wAB + wBA ≤
        coverValue (pullbackCover
          (Copying.collapseHom (G := G) (s := a) (t := b)) d) +
        coverValue (pullbackCover
          (Copying.collapseHom (G := G) (s := b) (t := a)) d) :=
      add_le_add (hAB.2 _) (hBA.2 _)
    _ = 2 * coverValue d := coverValue_opposite_pullbacks G hn d
    _ = 2 * w := by rw [hd]

/--
The manuscript's mixed-potential copy inequality, stated for certified dual
optima.  General existence of those optima is kept as the separate finite-LP
formalization boundary.
-/
theorem potential_opposite_copy_inequality
    (G : SimpleGraph X) [DecidableRel G.Adj] {a b : X}
    (hn : ¬G.Adj a b) {w wAB wBA : ℚ}
    (hG : IsCoverOptimum (G := G) w)
    (hAB : IsCoverOptimum (G := G.replaceVertex a b) wAB)
    (hBA : IsCoverOptimum (G := G.replaceVertex b a) wBA) :
    2 * potential G w ≤
      potential (G.replaceVertex a b) wAB +
        potential (G.replaceVertex b a) wBA := by
  have hcover : wAB + wBA ≤ 2 * w :=
    cover_optima_opposite_copy G hn hG hAB hBA
  have hedge :
      ((G.replaceVertex a b).edgeFinset.card : ℚ) +
          ((G.replaceVertex b a).edgeFinset.card : ℚ) =
        2 * (G.edgeFinset.card : ℚ) := by
    have hsum := opposite_collapse_edge_sum G hn (fun _ ↦ (1 : ℚ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
    simpa only [SimpleGraph.edgeFinset_card] using hsum
  unfold potential
  exact DiscreteConvexity.potential_copy_inequality hedge hcover

end OppositeCopies

end CopyCover
end Erdos81
