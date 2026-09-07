import Erdos81.Statement
import Mathlib.Tactic

/-!
# Structural facts about chordal graphs

This module derives small structural consequences directly from the project's
forbidden-induced-cycle definition of chordality.  In particular, it does not
import a perfect-elimination-order characterization as an additional
hypothesis.
-/

namespace Erdos81
namespace Chordal

open scoped SimpleGraph

variable {V : Type*}
variable (G : SimpleGraph V) {u x : V}

/-- Every induced subgraph of a chordal graph is chordal. -/
theorem induce_isChordal (hG : Erdos81.IsChordal G) (S : Set V) :
    Erdos81.IsChordal (G.induce S) := by
  intro k hk hcycle
  apply hG k hk
  exact hcycle.trans ⟨SimpleGraph.Embedding.induce S⟩

/--
The common neighborhood of two distinct nonadjacent vertices in a chordal
graph is a clique.

Distinctness is stated separately because, for a loopless simple graph,
`¬ G.Adj u x` alone is also true when `u = x`.  If two common neighbors were
nonadjacent, the ordered vertices `u, a, x, b` would induce a four-cycle.
-/
theorem commonNeighbors_isClique_of_chordal
    (hG : Erdos81.IsChordal G) (hux : u ≠ x) (hnux : ¬G.Adj u x) :
    G.IsClique (G.commonNeighbors u x) := by
  rw [G.isClique_iff]
  intro a ha b hb hab
  have hua : G.Adj u a := (G.mem_commonNeighbors.mp ha).1
  have hxa : G.Adj x a := (G.mem_commonNeighbors.mp ha).2
  have hub : G.Adj u b := (G.mem_commonNeighbors.mp hb).1
  have hxb : G.Adj x b := (G.mem_commonNeighbors.mp hb).2
  by_contra hnab
  apply hG 4 (by omega)
  refine ⟨{
    toFun := ![u, a, x, b]
    inj' := ?_
    map_rel_iff' := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [G.adj_comm]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [SimpleGraph.cycleGraph_adj', G.adj_comm] <;> decide

/--
The cardinal form of the manuscript's nonadjacency degree bound.

Here `U` is the outside vertex set, `w` bounds the order of every clique
contained in `U`, and `D` bounds the missing column of `x` inside `U`.  The
neighbors of `u` in `U` split into common neighbors of `u,x` and neighbors
missed by `x`.  The first class has size at most `w - 1`, while the second has
size at most `D - 1`, because the missing column also contains `u`.
-/
theorem root_nonadjacency_degree_bound [DecidableEq V] [DecidableRel G.Adj]
    (hG : Erdos81.IsChordal G) (U : Finset V) (w D : ℕ)
    (hu : u ∈ U) (hux : u ≠ x) (hnux : ¬G.Adj u x)
    (hcliqueBound : ∀ K : Finset V, K ⊆ U →
      G.IsClique (K : Set V) → K.card ≤ w)
    (hcolumnBound : (U.filter fun v ↦ ¬G.Adj x v).card ≤ D) :
    (U.filter fun v ↦ G.Adj u v).card ≤ D + w - 2 := by
  classical
  let N := U.filter fun v ↦ G.Adj u v
  let C := U.filter fun v ↦ G.Adj u v ∧ G.Adj x v
  let B := U.filter fun v ↦ G.Adj u v ∧ ¬G.Adj x v
  let X := U.filter fun v ↦ ¬G.Adj x v
  have hNCB : N = C ∪ B := by
    ext v
    simp only [N, C, B, Finset.mem_filter, Finset.mem_union]
    tauto
  have hCB : Disjoint C B := by
    rw [Finset.disjoint_left]
    intro v hvC hvB
    exact (Finset.mem_filter.mp hvB).2.2 (Finset.mem_filter.mp hvC).2.2
  have hNcard : N.card = C.card + B.card := by
    rw [hNCB, Finset.card_union_of_disjoint hCB]
  have hCsub : (C : Set V) ⊆ G.commonNeighbors u x := by
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    exact G.mem_commonNeighbors.mpr hv'
  have hCclique : G.IsClique (C : Set V) :=
    (commonNeighbors_isClique_of_chordal G hG hux hnux).subset hCsub
  have huC : u ∉ C := by
    intro huC
    exact G.irrefl (Finset.mem_filter.mp huC).2.1
  have hrootClique : G.IsClique ((insert u C : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    apply hCclique.insert
    intro v hv _hne
    exact (Finset.mem_filter.mp hv).2.1
  have hrootSub : insert u C ⊆ U := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hu
    · exact (Finset.mem_filter.mp hv).1
  have hCcard : C.card + 1 ≤ w := by
    have h := hcliqueBound (insert u C) hrootSub hrootClique
    simpa [Finset.card_insert_of_notMem huC] using h
  have huB : u ∉ B := by
    intro huB
    exact G.irrefl (Finset.mem_filter.mp huB).2.1
  have hBX : insert u B ⊆ X := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_filter.mpr ⟨hu, by simpa [G.adj_comm] using hnux⟩
    · have hv' := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨hv'.1, hv'.2.2⟩
  have hBcard : B.card + 1 ≤ D := by
    calc
      B.card + 1 = (insert u B).card := by
        symm
        exact Finset.card_insert_of_notMem huB
      _ ≤ X.card := Finset.card_le_card hBX
      _ ≤ D := by simpa [X] using hcolumnBound
  change N.card ≤ D + w - 2
  omega

end Chordal
end Erdos81
