import Erdos81.Statement
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Counting edges in clique partitions

This module proves the exact double-counting identity saying that the sum of
the edge counts of the blocks of a clique partition is the edge count of the
graph.  It is the accounting kernel behind the integral mixed-packing
identity.
-/

namespace Erdos81
namespace CliquePartitionCounting

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges of `G` whose two endpoints lie in `K`. -/
noncomputable def blockEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset V) :
    Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e ↦ e.toFinset ⊆ K

/-- The edges inside a clique have cardinality `choose(card K, 2)`. -/
theorem card_blockEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    (K : Finset V) (hK : G.IsClique (K : Set V)) :
    (blockEdges G K).card = Nat.choose K.card 2 := by
  classical
  have hinjective : Set.InjOn Sym2.toFinset
      (blockEdges G K : Set (Sym2 V)) := by
    intro e _ f _ hef
    apply Sym2.ext
    intro x
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]
  have himage : (blockEdges G K).image Sym2.toFinset =
      K.powersetCard 2 := by
    ext L
    constructor
    · intro hL
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hL
      have he' := Finset.mem_filter.mp he
      apply Finset.mem_powersetCard.mpr
      exact ⟨he'.2, G.card_toFinset_mem_edgeFinset ⟨e, he'.1⟩⟩
    · intro hL
      obtain ⟨hLK, hLcard⟩ := Finset.mem_powersetCard.mp hL
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hLcard
      have hxK : x ∈ K := hLK (by simp)
      have hyK : y ∈ K := hLK (by simp)
      have hxyG : G.Adj x y := hK hxK hyK hxy
      apply Finset.mem_image.mpr
      refine ⟨s(x, y), ?_, Sym2.toFinset_mk_eq⟩
      apply Finset.mem_filter.mpr
      refine ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hxyG), ?_⟩
      simpa only [Sym2.toFinset_mk_eq] using hLK
  calc
    (blockEdges G K).card =
        ((blockEdges G K).image Sym2.toFinset).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ = (K.powersetCard 2).card := by rw [himage]
    _ = Nat.choose K.card 2 := Finset.card_powersetCard 2 K

/-- Blocks of a partition which contain a specified graph edge. -/
noncomputable def containingBlocks {G : SimpleGraph V}
    (P : CliquePartition G) (e : Sym2 V) : Finset (Finset V) := by
  classical
  exact P.blocks.filter fun K ↦ e.toFinset ⊆ K

/-- Unique edge coverage says that the finset of blocks containing an edge is
a singleton. -/
theorem card_containingBlocks_eq_one {G : SimpleGraph V}
    [DecidableRel G.Adj] (P : CliquePartition G)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (containingBlocks P e).card = 1 := by
  classical
  revert he
  refine Sym2.inductionOn e ?_
  intro u v huvEdge
  have huv : G.Adj u v := G.mem_edgeSet.mp (G.mem_edgeFinset.mp huvEdge)
  obtain ⟨K, hK, hunique⟩ := P.coversOnce huv
  have hEq : containingBlocks P s(u, v) = {K} := by
    ext L
    simp only [containingBlocks, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hL
      have huL : u ∈ L := hL.2 (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left u v))
      have hvL : v ∈ L := hL.2 (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right u v))
      exact hunique L ⟨hL.1, huL, hvL⟩
    · rintro rfl
      refine ⟨hK.1, ?_⟩
      intro x hx
      simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hK.2.1
      · exact hK.2.2
  rw [hEq, Finset.card_singleton]

/-- Double-counting block-edge incidences in a clique partition. -/
theorem sum_card_blockEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : CliquePartition G) :
    (∑ K ∈ P.blocks, (blockEdges G K).card) = G.edgeFinset.card := by
  classical
  calc
    (∑ K ∈ P.blocks, (blockEdges G K).card) =
        ∑ K ∈ P.blocks, ∑ e ∈ G.edgeFinset,
          if e.toFinset ⊆ K then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro K hK
      change (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ K).card = _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset, ∑ K ∈ P.blocks,
          if e.toFinset ⊆ K then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, (containingBlocks P e).card := by
      apply Finset.sum_congr rfl
      intro e he
      change (∑ K ∈ P.blocks, if e.toFinset ⊆ K then 1 else 0) =
        (P.blocks.filter fun K ↦ e.toFinset ⊆ K).card
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ _e ∈ G.edgeFinset, 1 := by
      apply Finset.sum_congr rfl
      intro e he
      exact card_containingBlocks_eq_one P he
    _ = G.edgeFinset.card := by simp

/-- Weighted form of the partition incidence count: after restricting graph
edges by any decidable predicate, summing the restricted block-edge counts
still counts every selected edge exactly once. -/
theorem sum_card_filtered_blockEdges {G : SimpleGraph V}
    [DecidableRel G.Adj] (P : CliquePartition G)
    (q : Sym2 V → Prop) [DecidablePred q] :
    (∑ K ∈ P.blocks, ((blockEdges G K).filter q).card) =
      (G.edgeFinset.filter q).card := by
  classical
  calc
    (∑ K ∈ P.blocks, ((blockEdges G K).filter q).card) =
        ∑ K ∈ P.blocks, ∑ e ∈ G.edgeFinset,
          if e.toFinset ⊆ K ∧ q e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro K hK
      change ((G.edgeFinset.filter fun e ↦ e.toFinset ⊆ K).filter q).card = _
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hsubset : e.toFinset ⊆ K <;> by_cases hq : q e <;>
        simp [hsubset, hq]
    _ = ∑ e ∈ G.edgeFinset, ∑ K ∈ P.blocks,
          if e.toFinset ⊆ K ∧ q e then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, if q e then (containingBlocks P e).card else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hq : q e
      · simp only [hq, and_true, if_true]
        change (∑ K ∈ P.blocks, if e.toFinset ⊆ K then 1 else 0) =
          (P.blocks.filter fun K ↦ e.toFinset ⊆ K).card
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      · simp [hq]
    _ = ∑ e ∈ G.edgeFinset, if q e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [card_containingBlocks_eq_one P he]
    _ = (G.edgeFinset.filter q).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The standard exact edge-count identity for a clique partition. -/
theorem sum_choose_eq_card_edges {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : CliquePartition G) :
    (∑ K ∈ P.blocks, Nat.choose K.card 2) = G.edgeFinset.card := by
  rw [← sum_card_blockEdges P]
  apply Finset.sum_congr rfl
  intro K hK
  exact (card_blockEdges K (P.isClique K hK)).symm

/-- Every nontrivial partition block contains an edge, so a clique partition
has no more blocks than the graph has edges. -/
theorem size_le_card_edges {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : CliquePartition G) : P.size ≤ G.edgeFinset.card := by
  rw [← sum_choose_eq_card_edges P]
  change P.blocks.card ≤ ∑ K ∈ P.blocks, Nat.choose K.card 2
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro K hK
  have hTwo := P.nontrivial K hK
  exact Nat.choose_pos hTwo

end CliquePartitionCounting
end Erdos81
