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

end Chordal
end Erdos81
