import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

/-!
# Vertex copying

Mathlib's `G.replaceVertex s t` forgets the neighborhood of `t` and replaces
it by the neighborhood of `s`, with `s` and `t` nonadjacent afterward.  Thus
the manuscript's notation `G_{u→v}` is represented by
`G.replaceVertex v u`.
-/

namespace Erdos81
namespace Copying

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) {s t u v : V}

/-- A vertex is simplicial when its open neighborhood is a clique. -/
def IsSimplicial (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

/-- Two distinct nonadjacent vertices with the same open neighborhood. -/
def AreFalseTwins (u v : V) : Prop :=
  u ≠ v ∧ ¬G.Adj u v ∧ G.neighborSet u = G.neighborSet v

omit [Fintype V] in
/-- Copying along a nonedge gives the target exactly the source neighborhood. -/
theorem neighborSet_replaceVertex_target (hn : ¬G.Adj s t) :
    (G.replaceVertex s t).neighborSet t = G.neighborSet s := by
  ext w
  simp only [SimpleGraph.mem_neighborSet]
  by_cases hwt : w = t
  · subst w
    simp [SimpleGraph.replaceVertex, hn]
  · simp [SimpleGraph.replaceVertex, hwt]

omit [Fintype V] in
/-- A copy of a simplicial source is simplicial in the copied graph. -/
theorem simplicial_target_of_simplicial_source (hn : ¬G.Adj s t)
    (hs : IsSimplicial G s) :
    IsSimplicial (G.replaceVertex s t) t := by
  rw [IsSimplicial, neighborSet_replaceVertex_target G hn]
  intro a ha b hb hab
  have hat : a ≠ t := by
    intro hat
    subst a
    exact hn ((G.mem_neighborSet s t).mp ha)
  have hbt : b ≠ t := by
    intro hbt
    subst b
    exact hn ((G.mem_neighborSet s t).mp hb)
  exact (G.adj_replaceVertex_iff_of_ne s hat hbt).mpr (hs ha hb hab)

/--
The exact edge-count identity for the two opposite copies of a nonadjacent
pair.  It is stated over naturals; the proof checks that the subtractions in
Mathlib's individual cardinality formula cannot truncate incorrectly.
-/
theorem opposite_copy_edge_count [DecidableRel G.Adj] (hn : ¬G.Adj u v) :
    (G.replaceVertex v u).edgeFinset.card +
        (G.replaceVertex u v).edgeFinset.card =
      2 * G.edgeFinset.card := by
  have hnv : ¬G.Adj v u := by
    simpa [G.adj_comm] using hn
  rw [G.card_edgeFinset_replaceVertex_of_not_adj hnv,
    G.card_edgeFinset_replaceVertex_of_not_adj hn]
  have hu := G.degree_le_card_edgeFinset u
  have hv := G.degree_le_card_edgeFinset v
  omega

end Copying
end Erdos81
