import Erdos81.CliquePartitionCounting
import Erdos81.MixedModel
import Mathlib.Tactic

/-!
# Integral mixed triangle--four-clique packings

An integral packing is a finite collection of triangle and four-clique items
such that each graph edge belongs to at most one selected item.  This module
develops the exact used-edge and gain accounting needed to compare integral
packings with clique partitions of order at most four.
-/

namespace Erdos81
namespace IntegralPacking

open scoped BigOperators
open MixedModel

-- Prefer the adjacency-derived edge-set fintype here.  `MixedModel` also
-- exposes a noncomputable fintype for LP resources; disabling it locally keeps
-- `edgeFinset` terms definitionally uniform across the counting modules.
attribute [-instance] MixedModel.resourceFintype

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A mixed integral packing, with edge-disjointness stated resource by
resource. -/
structure Packing (G : SimpleGraph V) where
  items : Finset (Item G)
  exclusive : ∀ ⦃i j : Item G⦄, i ∈ items → j ∈ items →
    ∀ e : Resource G, Uses i e → Uses j e → i = j

/-- Integral gain: `2` for a triangle and `5` for a four-clique. -/
def itemGain {G : SimpleGraph V} : Item G → ℕ
  | Sum.inl _ => 2
  | Sum.inr _ => 5

/-- Total gain of an integral packing. -/
noncomputable def gain {G : SimpleGraph V} (p : Packing G) : ℕ :=
  ∑ i ∈ p.items, itemGain i

omit [Fintype V] [DecidableEq V] in
/-- The vertex-set projection is injective on mixed items. -/
theorem vertices_injective {G : SimpleGraph V} :
    Function.Injective (vertices : Item G → Finset V) := by
  intro i j hij
  cases i with
  | inl T =>
      cases j with
      | inl U =>
          congr 1
          exact Subtype.ext hij
      | inr K =>
          have hcard := congrArg Finset.card hij
          simp only [vertices] at hcard
          rw [T.2.1, K.2.1] at hcard
          omega
  | inr K =>
      cases j with
      | inl T =>
          have hcard := congrArg Finset.card hij
          simp only [vertices] at hcard
          rw [K.2.1, T.2.1] at hcard
          omega
      | inr L =>
          congr 1
          exact Subtype.ext hij

omit [Fintype V] [DecidableEq V] in
/-- An item uses exactly one more edge than its saving. -/
theorem choose_vertices_card {G : SimpleGraph V} (i : Item G) :
    Nat.choose (vertices i).card 2 = itemGain i + 1 := by
  cases i with
  | inl T => simp only [vertices, itemGain, T.2.1]; decide
  | inr K => simp only [vertices, itemGain, K.2.1]; decide

/-- Vertex sets of the selected nontrivial items. -/
noncomputable def largeBlocks {G : SimpleGraph V} (p : Packing G) :
    Finset (Finset V) :=
  p.items.image vertices

omit [Fintype V] in
theorem card_largeBlocks {G : SimpleGraph V} (p : Packing G) :
    (largeBlocks p).card = p.items.card := by
  classical
  exact Finset.card_image_of_injective p.items vertices_injective

/-- Graph edges covered by at least one selected item. -/
noncomputable def usedEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e ↦
    ∃ i ∈ p.items, e.toFinset ⊆ vertices i

/-- Selected items which contain a given unordered vertex pair. -/
noncomputable def itemsUsing {G : SimpleGraph V} (p : Packing G)
    (e : Sym2 V) : Finset (Item G) := by
  classical
  exact p.items.filter fun i ↦ e.toFinset ⊆ vertices i

/-- A used graph edge lies in exactly one selected item. -/
theorem card_itemsUsing_eq_one {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (hused : ∃ i ∈ p.items, e.toFinset ⊆ vertices i) :
    (itemsUsing p e).card = 1 := by
  classical
  obtain ⟨i, hi, hei⟩ := hused
  have hEq : itemsUsing p e = {i} := by
    ext j
    simp only [itemsUsing, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hj
      let edge : Resource G := ⟨e, G.mem_edgeFinset.mp he⟩
      exact p.exclusive hj.1 hi edge hj.2 hei
    · rintro rfl
      exact ⟨hi, hei⟩
  rw [hEq, Finset.card_singleton]

/-- Double count incidences between selected items and their used edges. -/
theorem sum_item_edge_counts {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) :
    (∑ i ∈ p.items,
      (CliquePartitionCounting.blockEdges G (vertices i)).card) =
      (usedEdges p).card := by
  classical
  calc
    (∑ i ∈ p.items,
        (CliquePartitionCounting.blockEdges G (vertices i)).card) =
        ∑ i ∈ p.items, ∑ e ∈ G.edgeFinset,
          if e.toFinset ⊆ vertices i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold CliquePartitionCounting.blockEdges
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset, ∑ i ∈ p.items,
          if e.toFinset ⊆ vertices i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, (itemsUsing p e).card := by
      apply Finset.sum_congr rfl
      intro e he
      change (∑ i ∈ p.items,
        if e.toFinset ⊆ vertices i then 1 else 0) =
        (p.items.filter fun i ↦ e.toFinset ⊆ vertices i).card
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset,
          if ∃ i ∈ p.items, e.toFinset ⊆ vertices i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hused : ∃ i ∈ p.items, e.toFinset ⊆ vertices i
      · rw [if_pos hused, card_itemsUsing_eq_one p he hused]
      · rw [if_neg hused]
        have hEmpty : itemsUsing p e = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact hused ⟨i, (Finset.mem_filter.mp hi).1,
            (Finset.mem_filter.mp hi).2⟩
        rw [hEmpty, Finset.card_empty]
    _ = (usedEdges p).card := by
      change _ = (G.edgeFinset.filter fun e ↦
        ∃ i ∈ p.items, e.toFinset ⊆ vertices i).card
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The number of used graph edges is the sum of `(gain + 1)` over selected
items. -/
theorem card_usedEdges_eq_sum_gain_add_one {G : SimpleGraph V}
    [DecidableRel G.Adj] (p : Packing G) :
    (usedEdges p).card = ∑ i ∈ p.items, (itemGain i + 1) := by
  rw [← sum_item_edge_counts p]
  apply Finset.sum_congr rfl
  intro i hi
  rw [CliquePartitionCounting.card_blockEdges
    (vertices i) (item_isClique i), choose_vertices_card]

/-- In particular, total integral gain never exceeds the graph's edge count. -/
theorem gain_le_card_edges {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) : gain p ≤ G.edgeFinset.card := by
  have husedSubset : usedEdges p ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hused := card_usedEdges_eq_sum_gain_add_one p
  have hcard := Finset.card_le_card husedSubset
  unfold gain
  calc
    (∑ i ∈ p.items, itemGain i) ≤
        ∑ i ∈ p.items, (itemGain i + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      omega
    _ = (usedEdges p).card := hused.symm
    _ ≤ G.edgeFinset.card := hcard

omit [Fintype V] in
/-- Taking the underlying finset is injective for unordered pairs. -/
theorem sym2_toFinset_injective :
    Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f hef
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]

/-- Graph edges not covered by a selected triangle or four-clique. -/
noncomputable def unusedEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) : Finset (Sym2 V) :=
  G.edgeFinset \ usedEdges p

/-- Two-vertex blocks used to complete a packing to an edge partition. -/
noncomputable def pairBlocks {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) : Finset (Finset V) :=
  (unusedEdges p).image Sym2.toFinset

/-- All selected large blocks together with the uncovered two-vertex blocks. -/
noncomputable def completedBlocks {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) : Finset (Finset V) :=
  largeBlocks p ∪ pairBlocks p

theorem card_pairBlocks {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) :
    (pairBlocks p).card = (unusedEdges p).card := by
  classical
  exact Finset.card_image_of_injective _ sym2_toFinset_injective

/-- Large item blocks and residual pair blocks cannot coincide because their
orders are respectively three or four, and two. -/
theorem largeBlocks_disjoint_pairBlocks {G : SimpleGraph V}
    [DecidableRel G.Adj] (p : Packing G) :
    Disjoint (largeBlocks p) (pairBlocks p) := by
  classical
  rw [Finset.disjoint_left]
  intro K hlarge hpair
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hlarge
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hpair
  have heGraph : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp he).1
  have hedgeCard : e.toFinset.card = 2 :=
    G.card_toFinset_mem_edgeFinset ⟨e, heGraph⟩
  have hitemCard := vertices_card_three_or_four i
  rw [← heq] at hitemCard
  omega

/-- Completing an integral packing with its unused edges gives a genuine
clique partition with all blocks of order at most four. -/
noncomputable def toCliquePartition {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) : CliquePartition G := by
  classical
  refine
    { blocks := completedBlocks p
      nontrivial := ?_
      isClique := ?_
      coversOnce := ?_ }
  · intro K hK
    rcases Finset.mem_union.mp hK with hlarge | hpair
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hlarge
      rcases vertices_card_three_or_four i with h | h <;> omega
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hpair
      exact (G.card_toFinset_mem_edgeFinset
        ⟨e, (Finset.mem_sdiff.mp he).1⟩).ge
  · intro K hK
    rcases Finset.mem_union.mp hK with hlarge | hpair
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hlarge
      exact item_isClique i
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hpair
      revert he
      refine Sym2.inductionOn e ?_
      intro u v he
      have huv : G.Adj u v := G.mem_edgeSet.mp
        (G.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
      simpa [Sym2.toFinset_mk_eq] using
        (SimpleGraph.isClique_pair.mpr fun _ ↦ huv)
  · intro u v huv
    let e : Sym2 V := s(u, v)
    have he : e ∈ G.edgeFinset :=
      G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr huv)
    by_cases hused : e ∈ usedEdges p
    · obtain ⟨heGraph, i, hi, hei⟩ := Finset.mem_filter.mp hused
      refine ⟨vertices i, ?_, ?_⟩
      · refine ⟨Finset.mem_union.mpr (Or.inl ?_), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
        · exact hei (by simp [e, Sym2.toFinset_mk_eq])
        · exact hei (by simp [e, Sym2.toFinset_mk_eq])
      · intro L hL
        rcases Finset.mem_union.mp hL.1 with hlarge | hpair
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hlarge
          let edge : Resource G := ⟨e, G.mem_edgeFinset.mp he⟩
          have hej : Uses j edge := by
            change e.toFinset ⊆ vertices j
            intro x hx
            simp only [e, Sym2.toFinset_mk_eq,
              Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hL.2.1
            · exact hL.2.2
          exact congrArg vertices (p.exclusive hj hi edge hej hei)
        · obtain ⟨d, hd, hdL⟩ := Finset.mem_image.mp hpair
          have hdGraph : d ∈ G.edgeFinset := (Finset.mem_sdiff.mp hd).1
          have hdCard : d.toFinset.card = 2 :=
            G.card_toFinset_mem_edgeFinset ⟨d, hdGraph⟩
          have hsubset : e.toFinset ⊆ d.toFinset := by
            intro x hx
            rw [hdL]
            simp only [e, Sym2.toFinset_mk_eq,
              Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hL.2.1
            · exact hL.2.2
          have heCard : e.toFinset.card = 2 :=
            G.card_toFinset_mem_edgeFinset ⟨e, heGraph⟩
          have hed : e = d := sym2_toFinset_injective
            (Finset.eq_of_subset_of_card_le hsubset (by omega))
          subst d
          exact ((Finset.mem_sdiff.mp hd).2 hused).elim
    · have heUnused : e ∈ unusedEdges p :=
        Finset.mem_sdiff.mpr ⟨he, hused⟩
      refine ⟨e.toFinset, ?_, ?_⟩
      · refine ⟨Finset.mem_union.mpr (Or.inr ?_), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨e, heUnused, rfl⟩
        · simp [e, Sym2.toFinset_mk_eq]
        · simp [e, Sym2.toFinset_mk_eq]
      · intro L hL
        rcases Finset.mem_union.mp hL.1 with hlarge | hpair
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hlarge
          apply (hused ?_).elim
          apply Finset.mem_filter.mpr
          refine ⟨he, i, hi, ?_⟩
          intro x hx
          simp only [e, Sym2.toFinset_mk_eq,
            Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hL.2.1
          · exact hL.2.2
        · obtain ⟨d, hd, hdL⟩ := Finset.mem_image.mp hpair
          have hdGraph : d ∈ G.edgeFinset := (Finset.mem_sdiff.mp hd).1
          have hdCard : d.toFinset.card = 2 :=
            G.card_toFinset_mem_edgeFinset ⟨d, hdGraph⟩
          have huvNe : u ≠ v := huv.ne
          have hsubset : e.toFinset ⊆ d.toFinset := by
            intro x hx
            rw [hdL]
            simp only [e, Sym2.toFinset_mk_eq,
              Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hL.2.1
            · exact hL.2.2
          have heCard : e.toFinset.card = 2 := by
            simp [e, Sym2.toFinset_mk_eq, huvNe]
          have hEq : e.toFinset = d.toFinset :=
            Finset.eq_of_subset_of_card_le hsubset (by omega)
          exact hdL.symm.trans hEq.symm

/-- The completed partition has exactly `e(G) - gain` blocks. -/
theorem size_toCliquePartition {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) :
    (toCliquePartition p).size = G.edgeFinset.card - gain p := by
  classical
  have husedSubset : usedEdges p ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hunusedCard : (unusedEdges p).card =
      G.edgeFinset.card - (usedEdges p).card := by
    exact Finset.card_sdiff_of_subset husedSubset
  have husedCard := card_usedEdges_eq_sum_gain_add_one p
  have hsum : (∑ i ∈ p.items, (itemGain i + 1)) =
      gain p + p.items.card := by
    unfold gain
    rw [Finset.sum_add_distrib]
    simp
  have hdisjoint := largeBlocks_disjoint_pairBlocks p
  change (completedBlocks p).card = G.edgeFinset.card - gain p
  rw [completedBlocks, Finset.card_union_of_disjoint hdisjoint,
    card_largeBlocks, card_pairBlocks, hunusedCard, husedCard, hsum]
  have hgain := gain_le_card_edges p
  have husedLe := Finset.card_le_card husedSubset
  have hbudget : gain p + p.items.card ≤ G.edgeFinset.card := by
    rw [← hsum, ← husedCard]
    exact husedLe
  omega

/-- The completed partition uses only blocks of order at most four. -/
theorem orderAtMost_toCliquePartition {G : SimpleGraph V}
    [DecidableRel G.Adj] (p : Packing G) :
    (toCliquePartition p).OrderAtMost 4 := by
  classical
  intro K hK
  rcases Finset.mem_union.mp hK with hlarge | hpair
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hlarge
    rcases vertices_card_three_or_four i with h | h <;> omega
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hpair
    calc
      e.toFinset.card = 2 := G.card_toFinset_mem_edgeFinset
        ⟨e, (Finset.mem_sdiff.mp he).1⟩
      _ ≤ 4 := by omega

/-- Blocks of order three or four in a clique partition. -/
noncomputable def eligibleBlocks {G : SimpleGraph V} (P : CliquePartition G) :
    Finset (Finset V) := by
  classical
  exact P.blocks.filter fun K ↦ K.card = 3 ∨ K.card = 4

/-- Turn an eligible partition block into the corresponding mixed item. -/
noncomputable def blockItem {G : SimpleGraph V} (P : CliquePartition G)
    (K : ↥(eligibleBlocks P : Finset (Finset V))) : Item G := by
  classical
  have hBlock : K.val ∈ P.blocks := (Finset.mem_filter.mp K.2).1
  have hOrder := (Finset.mem_filter.mp K.2).2
  by_cases hThree : K.val.card = 3
  · exact Sum.inl ⟨K.val, hThree, P.isClique K.val hBlock⟩
  · exact Sum.inr ⟨K.val, hOrder.resolve_left hThree,
      P.isClique K.val hBlock⟩

omit [Fintype V] in
@[simp]
theorem vertices_blockItem {G : SimpleGraph V} (P : CliquePartition G)
    (K : ↥(eligibleBlocks P : Finset (Finset V))) :
    vertices (blockItem P K) = K.val := by
  classical
  unfold blockItem
  split <;> rfl

/-- Eligible blocks embed injectively into the item type. -/
noncomputable def blockItemEmbedding {G : SimpleGraph V}
    (P : CliquePartition G) :
    ↥(eligibleBlocks P : Finset (Finset V)) ↪ Item G where
  toFun := blockItem P
  inj' := by
    intro K L hKL
    apply Subtype.ext
    rw [← vertices_blockItem P K, ← vertices_blockItem P L, hKL]

/-- Extract the triangle and four-clique blocks of a clique partition as an
integral packing. -/
noncomputable def ofCliquePartition {G : SimpleGraph V}
    (P : CliquePartition G) : Packing G := by
  classical
  refine
    { items := Finset.univ.map (blockItemEmbedding P)
      exclusive := ?_ }
  intro i j hi hj e hei hej
  obtain ⟨K, _, hKi⟩ := Finset.mem_map.mp hi
  obtain ⟨L, _, hLj⟩ := Finset.mem_map.mp hj
  subst i
  subst j
  apply congrArg (blockItem P)
  apply Subtype.ext
  have huv : G.Adj e.val.out.1 e.val.out.2 := by
    rw [← G.mem_edgeSet]
    simpa only [Sym2.mk, e.val.out_eq] using e.property
  have hKBlock : K.val ∈ P.blocks :=
    (Finset.mem_filter.mp K.2).1
  have hLBlock : L.val ∈ P.blocks :=
    (Finset.mem_filter.mp L.2).1
  have hKu' : e.val.out.1 ∈ K.val := by
    rw [← vertices_blockItem P K]
    exact hei (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e.val))
  have hKv' : e.val.out.2 ∈ K.val := by
    rw [← vertices_blockItem P K]
    exact hei (Sym2.mem_toFinset.mpr (Sym2.out_snd_mem e.val))
  have hLu' : e.val.out.1 ∈ L.val := by
    rw [← vertices_blockItem P L]
    exact hej (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e.val))
  have hLv' : e.val.out.2 ∈ L.val := by
    rw [← vertices_blockItem P L]
    exact hej (Sym2.mem_toFinset.mpr (Sym2.out_snd_mem e.val))
  obtain ⟨B, hB, hunique⟩ := P.coversOnce huv
  exact (hunique K.val ⟨hKBlock, hKu', hKv'⟩).trans
    (hunique L.val ⟨hLBlock, hLu', hLv'⟩).symm

/-- The saving contributed by a block of order at most four.  Pair blocks
contribute zero, triangles contribute two, and four-cliques contribute five. -/
def blockGain (K : Finset V) : ℕ :=
  if K.card = 3 then 2 else if K.card = 4 then 5 else 0

omit [Fintype V] in
/-- On an eligible block, extracting the corresponding item preserves its
gain. -/
@[simp]
theorem itemGain_blockItem {G : SimpleGraph V} (P : CliquePartition G)
    (K : ↥(eligibleBlocks P : Finset (Finset V))) :
    itemGain (blockItem P K) = blockGain K.val := by
  classical
  have hEligible : K.val.card = 3 ∨ K.val.card = 4 :=
    (Finset.mem_filter.mp K.2).2
  by_cases hThree : K.val.card = 3
  · simp [blockItem, blockGain, itemGain, hThree]
  · have hFour : K.val.card = 4 := hEligible.resolve_left hThree
    simp [blockItem, blockGain, itemGain, hFour]

omit [Fintype V] [DecidableEq V] in
/-- For a block whose order lies between two and four, its edge count is one
plus its packing gain. -/
theorem choose_eq_blockGain_add_one (K : Finset V)
    (hTwo : 2 ≤ K.card) (hFour : K.card ≤ 4) :
    Nat.choose K.card 2 = blockGain K + 1 := by
  interval_cases hCard : K.card <;>
    norm_num [blockGain, hCard, Nat.choose]

omit [Fintype V] in
/-- The gain of the packing extracted from a restricted clique partition is
the sum of the block gains over all of its blocks. -/
theorem gain_ofCliquePartition_eq_sum {G : SimpleGraph V}
    (P : CliquePartition G) :
    gain (ofCliquePartition P) = ∑ K ∈ P.blocks, blockGain K := by
  classical
  calc
    gain (ofCliquePartition P) =
        ∑ K : ↥(eligibleBlocks P : Finset (Finset V)),
          itemGain (blockItem P K) := by
      unfold gain ofCliquePartition
      rw [Finset.sum_map]
      simp only [blockItemEmbedding]
      rfl
    _ = ∑ K : ↥(eligibleBlocks P : Finset (Finset V)),
          blockGain K.val := by
      apply Fintype.sum_congr
      intro K
      exact itemGain_blockItem P K
    _ = ∑ K ∈ eligibleBlocks P, blockGain K := by
      rw [Finset.sum_subtype (eligibleBlocks P)
        (fun _ ↦ Iff.rfl)]
    _ = ∑ K ∈ P.blocks, blockGain K := by
      unfold eligibleBlocks
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro K hK
      by_cases hEligible : K.card = 3 ∨ K.card = 4
      · simp [hEligible]
      · have hNotThree : K.card ≠ 3 := fun h ↦ hEligible (Or.inl h)
        have hNotFour : K.card ≠ 4 := fun h ↦ hEligible (Or.inr h)
        simp [blockGain, hNotThree, hNotFour]

/-- Exact reverse accounting: a clique partition using blocks of order at
most four yields integral gain `e(G) - |P|`. -/
theorem gain_ofCliquePartition {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : CliquePartition G) (hOrder : P.OrderAtMost 4) :
    gain (ofCliquePartition P) = G.edgeFinset.card - P.size := by
  classical
  have hEdgeAccounting : G.edgeFinset.card =
      (∑ K ∈ P.blocks, blockGain K) + P.size := by
    calc
      G.edgeFinset.card =
          ∑ K ∈ P.blocks, Nat.choose K.card 2 :=
        (CliquePartitionCounting.sum_choose_eq_card_edges P).symm
      _ = ∑ K ∈ P.blocks, (blockGain K + 1) := by
        apply Finset.sum_congr rfl
        intro K hK
        exact choose_eq_blockGain_add_one K
          (P.nontrivial K hK) (hOrder K hK)
      _ = (∑ K ∈ P.blocks, blockGain K) + P.blocks.card := by
        rw [Finset.sum_add_distrib]
        simp
      _ = (∑ K ∈ P.blocks, blockGain K) + P.size := rfl
  rw [gain_ofCliquePartition_eq_sum]
  omega

/-- An attained maximum among integral triangle--four-clique packings. -/
def IsIntegralOptimum (G : SimpleGraph V) (w : ℕ) : Prop :=
  (∃ p : Packing G, gain p = w) ∧ ∀ p : Packing G, gain p ≤ w

/-- An attained minimum among clique partitions with blocks of order at most
four. -/
def IsRestrictedPartitionMinimum (G : SimpleGraph V) (c : ℕ) : Prop :=
  (∃ P : CliquePartition G, P.OrderAtMost 4 ∧ P.size = c) ∧
    ∀ P : CliquePartition G, P.OrderAtMost 4 → c ≤ P.size

/-- Exact optimization identity
`cp_{≤4}(G) = e(G) - (maximum integral mixed gain)`.

The explicit hypothesis `w ≤ e(G)` makes subtraction cancellation valid
without hiding a boundary case in truncated natural-number arithmetic.  It is
automatic whenever `w` is an attained packing gain. -/
theorem isIntegralOptimum_iff_isRestrictedPartitionMinimum
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : ℕ)
    (hw : w ≤ G.edgeFinset.card) :
    IsIntegralOptimum G w ↔
      IsRestrictedPartitionMinimum G (G.edgeFinset.card - w) := by
  constructor
  · rintro ⟨⟨p, hpGain⟩, hpMax⟩
    constructor
    · refine ⟨toCliquePartition p, orderAtMost_toCliquePartition p, ?_⟩
      rw [size_toCliquePartition, hpGain]
    · intro P hOrder
      have hGain := hpMax (ofCliquePartition P)
      rw [gain_ofCliquePartition P hOrder] at hGain
      omega
  · rintro ⟨⟨P, hOrder, hPSize⟩, hPMin⟩
    constructor
    · refine ⟨ofCliquePartition P, ?_⟩
      rw [gain_ofCliquePartition P hOrder, hPSize]
      omega
    · intro p
      have hMin := hPMin (toCliquePartition p)
        (orderAtMost_toCliquePartition p)
      rw [size_toCliquePartition] at hMin
      have hGainBound := gain_le_card_edges p
      omega

end IntegralPacking
end Erdos81
