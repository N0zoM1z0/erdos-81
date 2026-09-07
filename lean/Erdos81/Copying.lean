import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic
import Erdos81.Statement

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

def cycleStep {k : ℕ} (hk : 4 ≤ k) : Fin k :=
  ⟨1, by omega⟩

/-- The predecessor and successor of a vertex on a cycle of order at least four are distinct. -/
theorem cycle_predecessor_successor_ne {k : ℕ} (hk : 4 ≤ k) (i : Fin k) :
    i - cycleStep hk ≠ i + cycleStep hk := by
  letI : NeZero k := ⟨by omega⟩
  let one : Fin k := cycleStep hk
  let two : Fin k := ⟨2, by omega⟩
  change i - one ≠ i + one
  have htwo_ne : two ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [two] at hv
  have hsum_two : one + one = two := by
    apply Fin.ext
    simp only [Fin.val_add]
    simp [one, two, cycleStep, Nat.mod_eq_of_lt (show 2 < k by omega)]
  intro heq
  have hz : one + one = 0 := by
    calc
      one + one = (i + one) - (i - one) := by abel
      _ = 0 := sub_eq_zero.mpr heq.symm
  exact htwo_ne (hsum_two ▸ hz)

/-- The predecessor and successor are nonadjacent on every cycle of order at least four. -/
theorem cycle_predecessor_successor_not_adj {k : ℕ} (hk : 4 ≤ k) (i : Fin k) :
    ¬(SimpleGraph.cycleGraph k).Adj (i - cycleStep hk) (i + cycleStep hk) := by
  letI : NeZero k := ⟨by omega⟩
  let one : Fin k := cycleStep hk
  let three : Fin k := ⟨3, by omega⟩
  change ¬(SimpleGraph.cycleGraph k).Adj (i - one) (i + one)
  have hone_ne : one ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [one, cycleStep] at hv
  have hthree_ne : three ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [three] at hv
  have hsum_three : one + one + one = three := by
    apply Fin.ext
    simp only [Fin.val_add]
    simp [one, three, cycleStep, Nat.mod_eq_of_lt (show 2 < k by omega),
      Nat.mod_eq_of_lt (show 3 < k by omega)]
  rw [SimpleGraph.cycleGraph_adj']
  simp only [not_or]
  constructor
  · intro hval
    have h : (i - one) - (i + one) = one := by
      apply Fin.ext
      simpa [one, cycleStep] using hval
    have hz : -one - one - one = 0 := by
      calc
        -one - one - one = (i - one) - (i + one) - one := by abel
        _ = 0 := sub_eq_zero.mpr h
    have hsum_zero : one + one + one = 0 := by
      rw [← neg_eq_zero]
      calc
        -(one + one + one) = -one - one - one := by abel
        _ = 0 := hz
    exact hthree_ne (hsum_three ▸ hsum_zero)
  · intro hval
    have h : (i + one) - (i - one) = one := by
      apply Fin.ext
      simpa [one, cycleStep] using hval
    have hz : one = 0 := by
      calc
        one = (i + one) - (i - one) - one := by abel
        _ = 0 := sub_eq_zero.mpr h
    exact hone_ne hz

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

omit [Fintype V] in
/-- Replacing any vertex by a copy of a simplicial vertex preserves chordality. -/
theorem chordal_replaceVertex_of_simplicial_source
    (hG : Erdos81.IsChordal G) (hs : IsSimplicial G s) :
    Erdos81.IsChordal (G.replaceVertex s t) := by
  intro k hk hcycle
  rcases hcycle with ⟨f⟩
  by_cases ht : ∃ i : Fin k, f i = t
  · obtain ⟨i, hi⟩ := ht
    letI : NeZero k := ⟨by omega⟩
    let one : Fin k := cycleStep hk
    let left : Fin k := i - one
    let right : Fin k := i + one
    have hcycleLeft : (SimpleGraph.cycleGraph k).Adj i left := by
      rw [SimpleGraph.cycleGraph_adj']
      left
      have heq : i - left = one := by
        dsimp only [left]
        abel
      rw [heq]
      rfl
    have hcycleRight : (SimpleGraph.cycleGraph k).Adj i right := by
      rw [SimpleGraph.cycleGraph_adj']
      right
      have heq : right - i = one := by
        dsimp only [right]
        abel
      rw [heq]
      rfl
    have hHleft : (G.replaceVertex s t).Adj t (f left) := by
      simpa [hi] using (f.map_adj_iff.mpr hcycleLeft)
    have hHright : (G.replaceVertex s t).Adj t (f right) := by
      simpa [hi] using (f.map_adj_iff.mpr hcycleRight)
    have hleftt : f left ≠ t := hHleft.ne.symm
    have hrightt : f right ≠ t := hHright.ne.symm
    have hGsleft : G.Adj s (f left) :=
      (G.adj_replaceVertex_iff_of_ne_right s hleftt).mp hHleft
    have hGsright : G.Adj s (f right) :=
      (G.adj_replaceVertex_iff_of_ne_right s hrightt).mp hHright
    have hleftright : f left ≠ f right := by
      intro heq
      have hindices : left = right := f.injective heq
      exact (cycle_predecessor_successor_ne hk i) hindices
    have hGold : G.Adj (f left) (f right) := by
      exact hs ((G.mem_neighborSet s (f left)).mpr hGsleft)
        ((G.mem_neighborSet s (f right)).mpr hGsright) hleftright
    have hHnew : (G.replaceVertex s t).Adj (f left) (f right) :=
      (G.adj_replaceVertex_iff_of_ne s hleftt hrightt).mpr hGold
    have hcycleChord : (SimpleGraph.cycleGraph k).Adj left right :=
      f.map_adj_iff.mp hHnew
    exact (cycle_predecessor_successor_not_adj hk i) hcycleChord
  · apply hG k hk
    refine ⟨{
      toFun := f
      inj' := f.injective
      map_rel_iff' := ?_ }⟩
    intro a b
    have hfa : f a ≠ t := by
      intro h
      exact ht ⟨a, h⟩
    have hfb : f b ≠ t := by
      intro h
      exact ht ⟨b, h⟩
    exact (G.adj_replaceVertex_iff_of_ne s hfa hfb).symm.trans f.map_adj_iff

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
