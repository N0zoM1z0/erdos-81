import Erdos81.Dirac
import Erdos81.EditDistance
import Mathlib.Tactic

/-!
# Terminal chordal graphs

This module proves the structural stopping criterion used by the copying
argument.  If every two nonadjacent simplicial vertices have the same open
neighbourhood, then the graph is a complete-split graph.

The proof avoids any unformalized clique-tree theory.  Starting from one
simplicial vertex `u`, its open neighbourhood `K` is a clique.  In every
component of `G - K`, Dirac's theorem supplies a vertex which is simplicial in
the ambient graph.  The terminal hypothesis forces that vertex to have open
neighbourhood `K`, so no component of `G - K` can contain an edge.  The same
hypothesis then makes every vertex outside `K` adjacent to every vertex of
`K`.
-/

namespace Erdos81
namespace TerminalCharacterization

open SimpleGraph Copying EditDistance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The stopping condition for simplicial copying. -/
def IsTerminal (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v → ¬G.Adj u v →
    IsSimplicial G u → IsSimplicial G v →
      G.neighborSet u = G.neighborSet v

/-- A graph is (labelled) complete-split if it is one of the templates with
an arbitrary clique-side cardinality. -/
def IsCompleteSplit (G : SimpleGraph V) : Prop :=
  ∃ K : Finset V, G = completeSplitGraph K

/-- A simplicial vertex has a clique open neighbourhood. -/
theorem neighborFinset_isClique_of_simplicial
    {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}
    (hu : IsSimplicial G u) :
    G.IsClique (G.neighborFinset u : Set V) := by
  simpa [IsSimplicial] using hu

/-- There is no edge between two vertices outside the neighbourhood of a
fixed simplicial vertex in a terminal chordal graph. -/
theorem outside_neighborFinset_independent
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hchordal : IsChordal G) (hterminal : IsTerminal G)
    {u : V} (hu : IsSimplicial G u) :
    ∀ ⦃x y : V⦄, x ∉ G.neighborFinset u → y ∉ G.neighborFinset u →
      ¬G.Adj x y := by
  classical
  let K : Finset V := G.neighborFinset u
  have hK : G.IsClique (K : Set V) := by
    simpa [K] using neighborFinset_isClique_of_simplicial hu
  intro x y hxK hyK hxy
  have hxu : x ≠ u := by
    intro h
    subst x
    exact hyK (by simpa using hxy)
  let J : SimpleGraph ↥((K : Set V)ᶜ) := G.induce ((K : Set V)ᶜ)
  let xout : ↥((K : Set V)ᶜ) := ⟨x, hxK⟩
  let A : Set V := {z | ∃ (hz : z ∉ K),
    J.connectedComponentMk ⟨z, hz⟩ = J.connectedComponentMk xout}
  let T : Set V := (K : Set V) ∪ A
  have hA : A.Nonempty := ⟨x, hxK, rfl⟩
  have hAT : A ⊆ T := Set.subset_union_right
  have hneighbors : ∀ z ∈ A, G.neighborSet z ⊆ T := by
    intro z hz w hzw
    by_cases hwK : w ∈ K
    · exact Or.inl hwK
    · right
      obtain ⟨hzK, hzcomp⟩ := hz
      refine ⟨hwK, ?_⟩
      have hcomp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (G := J) (show J.Adj ⟨z, hzK⟩ ⟨w, hwK⟩ from hzw)
      exact hcomp.symm.trans hzcomp
  have hboundary : G.IsClique (T \ A) :=
    hK.subset (by
      intro z hz
      rcases hz.1 with hzK | hzA
      · exact hzK
      · exact (hz.2 hzA).elim)
  have hTchordal : IsChordal (G.induce T) :=
    Chordal.induce_isChordal G hchordal T
  have hTcard : Fintype.card T ≤ Fintype.card V := by
    exact Fintype.card_le_of_injective (fun z : T ↦ z.val)
      Subtype.val_injective
  have hTalternative : G.induce T = ⊤ ∨
      ∃ a b : T, a ≠ b ∧ ¬(G.induce T).Adj a b ∧
        IsSimplicial (G.induce T) a ∧ IsSimplicial (G.induce T) b :=
    Dirac.complete_or_two_simplicial (Fintype.card V) T (G.induce T)
      hTcard hTchordal
  obtain ⟨z, hzA, hzSimplicial⟩ :=
    Dirac.choose_simplicial_in hAT hA hneighbors hboundary hTalternative
  obtain ⟨hzK, hzcomp⟩ := hzA
  have huK : u ∉ K := by
    simp [K]
  have huxNotReachable : ¬J.Reachable ⟨u, huK⟩ xout := by
    apply SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
      (G := J) (show (⟨u, huK⟩ : ↥((K : Set V)ᶜ)) ≠ xout by
        intro h
        exact hxu.symm (congrArg Subtype.val h))
    ext w
    constructor
    · intro huw
      have huwG : G.Adj u w.val := huw
      exact (w.2 (by simpa [K] using huwG)).elim
    · simp
  have huz : u ≠ z := by
    intro huz
    subst z
    apply huxNotReachable
    exact SimpleGraph.ConnectedComponent.eq.mp hzcomp
  have hnuz : ¬G.Adj u z := by
    intro huzAdj
    exact hzK (by simpa [K] using huzAdj)
  have hneighborhood := hterminal huz hnuz hu hzSimplicial
  have hzxReachable : J.Reachable ⟨z, hzK⟩ xout :=
    SimpleGraph.ConnectedComponent.eq.mp hzcomp
  have hzHasOutsideNeighbor : ∃ w : V, w ∉ K ∧ G.Adj z w := by
    by_cases hzx : z = x
    · exact ⟨y, hyK, by simpa [hzx] using hxy⟩
    · obtain ⟨w, hzw⟩ :=
        hzxReachable.nonempty_neighborSet_left
          (show (⟨z, hzK⟩ : ↥((K : Set V)ᶜ)) ≠ xout by
            intro h
            exact hzx (congrArg Subtype.val h))
      exact ⟨w.val, w.2, hzw⟩
  obtain ⟨w, hwK, hzw⟩ := hzHasOutsideNeighbor
  have hwz : w ∈ G.neighborSet z := hzw
  have hwu : w ∈ G.neighborSet u := hneighborhood.symm ▸ hwz
  exact hwK (by simpa [K] using hwu)

/-- The terminal condition characterizes complete-split chordal graphs. -/
theorem isCompleteSplit_of_terminal
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nonempty V]
    (hchordal : IsChordal G) (hterminal : IsTerminal G) :
    IsCompleteSplit G := by
  classical
  obtain ⟨u, hu⟩ := Dirac.exists_simplicial (G := G) hchordal
  let K : Finset V := G.neighborFinset u
  have hK : G.IsClique (K : Set V) := by
    simpa [K] using neighborFinset_isClique_of_simplicial hu
  have hindependent : ∀ ⦃x y : V⦄, x ∉ K → y ∉ K → ¬G.Adj x y := by
    simpa [K] using outside_neighborFinset_independent hchordal hterminal hu
  have hsimpOutside : ∀ ⦃v : V⦄, v ∉ K → IsSimplicial G v := by
    intro v hvK
    rw [IsSimplicial]
    intro x hx y hy hxy
    have hxK : x ∈ K := by
      by_contra hxK
      exact hindependent hvK hxK (by simpa using hx)
    have hyK : y ∈ K := by
      by_contra hyK
      exact hindependent hvK hyK (by simpa using hy)
    exact hK hxK hyK hxy
  have hrootOutside : ∀ ⦃x y : V⦄, x ∈ K → y ∉ K → G.Adj x y := by
    intro x y hxK hyK
    by_cases hyu : y = u
    · subst y
      exact (show G.Adj u x by simpa [K] using hxK).symm
    · have huK : u ∉ K := by simp [K]
      have hnuy : ¬G.Adj u y := by
        intro huy
        exact hyK (by simpa [K] using huy)
      have hNy := hterminal (u := u) (v := y) (Ne.symm hyu) hnuy hu
        (hsimpOutside hyK)
      have hxNu : x ∈ G.neighborSet u := by simpa [K] using hxK
      have hxNy : x ∈ G.neighborSet y := hNy ▸ hxNu
      exact hxNy.symm
  refine ⟨K, ?_⟩
  ext x y
  constructor
  · intro hxy
    refine ⟨hxy.ne, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hindependent hnone.1 hnone.2 hxy
  · rintro ⟨hxy, hxK | hyK⟩
    · by_cases hyK : y ∈ K
      · exact hK hxK hyK hxy
      · exact hrootOutside hxK hyK
    · by_cases hxK : x ∈ K
      · exact hK hxK hyK hxy
      · exact (hrootOutside hyK hxK).symm

end TerminalCharacterization
end Erdos81
