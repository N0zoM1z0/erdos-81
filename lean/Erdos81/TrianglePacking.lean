import Erdos81.IntegralPacking
import Mathlib.Tactic

/-!
# Edge-disjoint triangle packings

The terminal construction naturally produces a family of edge-disjoint
triangles.  This module packages such a family, embeds it in the mixed
triangle--four-clique packing model, and obtains the exact clique-partition
count by adding every unused edge as a two-vertex block.
-/

namespace Erdos81
namespace TrianglePacking

open MixedModel IntegralPacking

attribute [-instance] MixedModel.resourceFintype

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite family of pairwise edge-disjoint triangles. -/
structure Packing (G : SimpleGraph V) where
  triangles : Finset (CliqueOfOrder G 3)
  exclusive : ∀ ⦃T U : CliqueOfOrder G 3⦄,
    T ∈ triangles → U ∈ triangles → ∀ e : Resource G,
      Uses (Sum.inl T) e → Uses (Sum.inl U) e → T = U

/-- The empty triangle packing. -/
def empty (G : SimpleGraph V) : Packing G where
  triangles := ∅
  exclusive := by simp

/-- The canonical injection of triangles into mixed items. -/
def triangleEmbedding (G : SimpleGraph V) :
    CliqueOfOrder G 3 ↪ Item G :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Regard a triangle packing as a mixed integral packing. -/
noncomputable def toMixed {G : SimpleGraph V} (p : Packing G) :
    IntegralPacking.Packing G := by
  classical
  refine
    { items := p.triangles.map (triangleEmbedding G)
      exclusive := ?_ }
  intro i j hi hj e hei hej
  obtain ⟨T, hT, rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨U, hU, rfl⟩ := Finset.mem_map.mp hj
  exact congrArg Sum.inl (p.exclusive hT hU e hei hej)

omit [Fintype V] in
/-- The mixed gain of `f` edge-disjoint triangles is exactly `2f`. -/
theorem gain_toMixed {G : SimpleGraph V} (p : Packing G) :
    IntegralPacking.gain (toMixed p) = 2 * p.triangles.card := by
  classical
  unfold IntegralPacking.gain toMixed
  rw [Finset.sum_map]
  simp [triangleEmbedding, IntegralPacking.itemGain, Nat.mul_comm]

/-- Completing a triangle packing uses only pairs and triangles. -/
theorem orderAtMost_three {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) :
    (IntegralPacking.toCliquePartition (toMixed p)).OrderAtMost 3 := by
  classical
  intro K hK
  rcases Finset.mem_union.mp hK with hlarge | hpair
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hlarge
    obtain ⟨T, hT, rfl⟩ := Finset.mem_map.mp hi
    exact T.2.1.le
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hpair
    calc
      e.toFinset.card = 2 := G.card_toFinset_mem_edgeFinset
        ⟨e, (Finset.mem_sdiff.mp he).1⟩
      _ ≤ 3 := by omega

/-- Exact part count obtained by completing a triangle packing with unused
edges. -/
theorem size_completedPartition {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) :
    (IntegralPacking.toCliquePartition (toMixed p)).size =
      G.edgeFinset.card - 2 * p.triangles.card := by
  rw [IntegralPacking.size_toCliquePartition, gain_toMixed]

/-- A family of `f` edge-disjoint triangles therefore supplies an explicit
order-at-most-three clique partition with `e(G)-2f` parts. -/
theorem exists_partition {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : Packing G) :
    ∃ P : CliquePartition G,
      P.OrderAtMost 3 ∧
      P.size = G.edgeFinset.card - 2 * p.triangles.card :=
  ⟨IntegralPacking.toCliquePartition (toMixed p), orderAtMost_three p,
    size_completedPartition p⟩

end TrianglePacking
end Erdos81
