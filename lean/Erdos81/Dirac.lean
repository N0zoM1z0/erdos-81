import Erdos81.ChordalSeparator
import Erdos81.Copying
import Mathlib.Tactic

/-!
# Dirac's simplicial-vertex theorem

We prove the strong finite form: a chordal graph is complete or contains two
distinct nonadjacent simplicial vertices.  The proof uses the clique minimal
separator from `ChordalSeparator` and strong induction on the number of
vertices.
-/

namespace Erdos81
namespace Dirac

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Simpliciality in an induced subgraph transfers to the ambient graph when
all ambient neighbors remain in the induced carrier. -/
theorem simplicial_of_induce {T : Set V} {v : V} (hv : v ∈ T)
    (hneighbors : G.neighborSet v ⊆ T)
    (hsimplicial : Copying.IsSimplicial (G.induce T) ⟨v, hv⟩) :
    Copying.IsSimplicial G v := by
  rw [Copying.IsSimplicial] at hsimplicial ⊢
  intro p hp q hq hpq
  have hp' : (⟨p, hneighbors hp⟩ : T) ∈
      (G.induce T).neighborSet ⟨v, hv⟩ := hp
  have hq' : (⟨q, hneighbors hq⟩ : T) ∈
      (G.induce T).neighborSet ⟨v, hv⟩ := hq
  exact hsimplicial hp' hq' (fun h ↦ hpq (congrArg Subtype.val h))

/-- Every vertex of a complete graph is simplicial. -/
theorem simplicial_top (v : V) :
    Copying.IsSimplicial (⊤ : SimpleGraph V) v := by
  rw [Copying.IsSimplicial]
  intro p _ q _ hpq
  exact (SimpleGraph.top_adj p q).mpr hpq

/-- If an induced graph is complete or has two nonadjacent simplicial
vertices, and the part outside `A` is a clique, then a simplicial vertex can be
chosen in the nonempty set `A`. -/
theorem choose_simplicial_in {T A : Set V} (hAT : A ⊆ T)
    (hA : A.Nonempty)
    (hneighbors : ∀ v ∈ A, G.neighborSet v ⊆ T)
    (hboundary : G.IsClique (T \ A))
    (halternative : G.induce T = ⊤ ∨
      ∃ a b : T, a ≠ b ∧ ¬(G.induce T).Adj a b ∧
        Copying.IsSimplicial (G.induce T) a ∧
        Copying.IsSimplicial (G.induce T) b) :
    ∃ v ∈ A, Copying.IsSimplicial G v := by
  rcases halternative with hcomplete |
      ⟨a, b, hab, hnab, haSimplicial, hbSimplicial⟩
  · obtain ⟨v, hvA⟩ := hA
    refine ⟨v, hvA, simplicial_of_induce (hAT hvA)
      (hneighbors v hvA) ?_⟩
    rw [hcomplete]
    exact simplicial_top _
  · by_cases haA : a.val ∈ A
    · exact ⟨a.val, haA,
        simplicial_of_induce a.2 (hneighbors a.val haA) haSimplicial⟩
    · by_cases hbA : b.val ∈ A
      · exact ⟨b.val, hbA,
          simplicial_of_induce b.2 (hneighbors b.val hbA) hbSimplicial⟩
      · have habG : G.Adj a.val b.val := hboundary
          ⟨a.2, haA⟩ ⟨b.2, hbA⟩
          (fun h ↦ hab (Subtype.ext h))
        exact (hnab habG).elim

universe u

/-- Strong finite Dirac theorem, stated with a cardinality bound so that the
induction applies uniformly to induced subtype graphs. -/
theorem complete_or_two_simplicial :
    ∀ (bound : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
      Fintype.card W ≤ bound → Erdos81.IsChordal H →
        H = ⊤ ∨ ∃ a b : W, a ≠ b ∧ ¬H.Adj a b ∧
          Copying.IsSimplicial H a ∧ Copying.IsSimplicial H b := by
  classical
  intro bound
  induction bound with
  | zero =>
      intro W _ H hcard _
      left
      have hEmpty : IsEmpty W :=
        Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      ext a b
      exact (hEmpty.false a).elim
  | succ bound ih =>
      intro W _ H hcard hchordal
      by_cases hcomplete : H = ⊤
      · exact Or.inl hcomplete
      · right
        have recurse : ∀ (T A : Set W), A ⊆ T → A.Nonempty →
            (∃ outside : W, outside ∉ T) →
            (∀ v ∈ A, H.neighborSet v ⊆ T) →
            H.IsClique (T \ A) →
            ∃ v ∈ A, Copying.IsSimplicial H v := by
          intro T A hAT hA hout hneighbors hboundary
          obtain ⟨outside, houtside⟩ := hout
          have hsmaller : Fintype.card T < Fintype.card W :=
            Fintype.card_subtype_lt houtside
          have hTchordal : Erdos81.IsChordal (H.induce T) :=
            Chordal.induce_isChordal H hchordal T
          exact choose_simplicial_in hAT hA hneighbors hboundary
            (ih T (H.induce T) (by omega) hTchordal)
        by_cases hconnected : H.Connected
        · obtain ⟨S, hseparator, hminimal⟩ :=
            Separator.exists_minimal_separator hconnected hcomplete
          have hSclique : H.IsClique S :=
            ChordalSeparator.minimal_separator_isClique
              hchordal hseparator hminimal
          obtain ⟨_, u, v, hu, hv, huv⟩ := hseparator
          have hcomponentNe :
              (H.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ≠
                (H.induce Sᶜ).connectedComponentMk ⟨v, hv⟩ :=
            fun h ↦ huv (SimpleGraph.ConnectedComponent.eq.mp h)
          have find_on_side : ∀ x y : ↥Sᶜ,
              (H.induce Sᶜ).connectedComponentMk x ≠
                (H.induce Sᶜ).connectedComponentMk y →
              ∃ z : W, ∃ (hz : z ∉ S),
                (H.induce Sᶜ).connectedComponentMk ⟨z, hz⟩ =
                    (H.induce Sᶜ).connectedComponentMk x ∧
                  Copying.IsSimplicial H z := by
            intro x y hxy
            let A : Set W := {z | ∃ (hz : z ∉ S),
              (H.induce Sᶜ).connectedComponentMk ⟨z, hz⟩ =
                (H.induce Sᶜ).connectedComponentMk x}
            have hA : A.Nonempty := ⟨x.val, x.2, rfl⟩
            have hyOutside : y.val ∉ S ∪ A := by
              intro hy
              rcases hy with hyS | ⟨hyS, hyComponent⟩
              · exact y.2 hyS
              · exact hxy hyComponent.symm
            have hneighbors : ∀ z ∈ A,
                H.neighborSet z ⊆ S ∪ A := by
              intro z hz p hzp
              obtain ⟨hzS, hzComponent⟩ := hz
              by_cases hpS : p ∈ S
              · exact Or.inl hpS
              · exact Or.inr ⟨hpS,
                  (Separator.component_eq_of_adj hzS hpS hzp).symm.trans
                    hzComponent⟩
            have hboundary : H.IsClique ((S ∪ A) \ A) :=
              hSclique.subset (by
                intro z hz
                rcases hz.1 with hzS | hzA
                · exact hzS
                · exact (hz.2 hzA).elim)
            obtain ⟨z, hzA, hzSimplicial⟩ := recurse (S ∪ A) A
              Set.subset_union_right hA ⟨y.val, hyOutside⟩
              hneighbors hboundary
            obtain ⟨hzS, hzComponent⟩ := hzA
            exact ⟨z, hzS, hzComponent, hzSimplicial⟩
          obtain ⟨left, hleftS, hleftComponent, hleftSimplicial⟩ :=
            find_on_side ⟨u, hu⟩ ⟨v, hv⟩ hcomponentNe
          obtain ⟨right, hrightS, hrightComponent, hrightSimplicial⟩ :=
            find_on_side ⟨v, hv⟩ ⟨u, hu⟩ hcomponentNe.symm
          refine ⟨left, right, ?_, ?_, hleftSimplicial, hrightSimplicial⟩
          · intro hlr
            subst right
            exact hcomponentNe (hleftComponent.symm.trans hrightComponent)
          · intro hlr
            have hsame := Separator.component_eq_of_adj
              hleftS hrightS hlr
            exact hcomponentNe
              (hleftComponent.symm.trans (hsame.trans hrightComponent))
        · haveI : Nonempty W := by
            rw [← not_isEmpty_iff]
            intro hEmpty
            apply hcomplete
            ext a b
            exact (hEmpty.false a).elim
          obtain ⟨u, v, huv⟩ : ∃ u v : W, ¬H.Reachable u v := by
            by_contra h
            push Not at h
            exact hconnected ⟨h⟩
          have hcomponentNe : H.connectedComponentMk u ≠
              H.connectedComponentMk v :=
            fun h ↦ huv (SimpleGraph.ConnectedComponent.eq.mp h)
          have find_in_component : ∀ x y : W,
              H.connectedComponentMk x ≠ H.connectedComponentMk y →
              ∃ z : W, H.connectedComponentMk z =
                  H.connectedComponentMk x ∧ Copying.IsSimplicial H z := by
            intro x y hxy
            let A : Set W := {z | H.connectedComponentMk z =
              H.connectedComponentMk x}
            have hA : A.Nonempty := ⟨x, rfl⟩
            have hyOutside : y ∉ A := fun hy ↦ hxy hy.symm
            have hneighbors : ∀ z ∈ A, H.neighborSet z ⊆ A := by
              intro z hz p hzp
              exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hzp).symm.trans hz
            have hboundary : H.IsClique (A \ A) := by
              rw [H.isClique_iff]
              intro z hz
              exact (hz.2 hz.1).elim
            obtain ⟨z, hzA, hzSimplicial⟩ := recurse A A subset_rfl hA
              ⟨y, hyOutside⟩ hneighbors hboundary
            exact ⟨z, hzA, hzSimplicial⟩
          obtain ⟨left, hleftComponent, hleftSimplicial⟩ :=
            find_in_component u v hcomponentNe
          obtain ⟨right, hrightComponent, hrightSimplicial⟩ :=
            find_in_component v u hcomponentNe.symm
          refine ⟨left, right, ?_, ?_, hleftSimplicial, hrightSimplicial⟩
          · intro hlr
            subst right
            exact hcomponentNe (hleftComponent.symm.trans hrightComponent)
          · intro hlr
            have hsame :=
              SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hlr
            exact hcomponentNe
              (hleftComponent.symm.trans (hsame.trans hrightComponent))

/-- Every nonempty finite chordal graph has a simplicial vertex. -/
theorem exists_simplicial [Fintype V] [Nonempty V]
    (hchordal : Erdos81.IsChordal G) :
    ∃ v : V, Copying.IsSimplicial G v := by
  rcases complete_or_two_simplicial (Fintype.card V) V G le_rfl hchordal with
    hcomplete | ⟨a, _, _, _, haSimplicial, _⟩
  · obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨v, by rw [hcomplete]; exact simplicial_top v⟩
  · exact ⟨a, haSimplicial⟩

end Dirac
end Erdos81
