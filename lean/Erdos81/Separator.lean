import Erdos81.Chordal
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Vertex separators in finite graphs

This module supplies the separator facts needed for the Dirac theorem.  A
separator is recorded together with two vertices that become unreachable after
the separator is deleted.  The formulation keeps all connectivity witnesses
explicit and is convenient for subsequent component arguments.
-/

namespace Erdos81
namespace Separator

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Deleting `S` from a connected graph leaves two vertices unreachable from
one another. -/
def IsSeparator (G : SimpleGraph V) (S : Set V) : Prop :=
  G.Connected ∧
    ∃ u v : V, ∃ (hu : u ∉ S) (hv : v ∉ S),
      ¬(G.induce Sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩

/-- Adjacent vertices outside a deleted set belong to the same component. -/
theorem component_eq_of_adj {S : Set V} {u v : V} (hu : u ∉ S) (hv : v ∉ S)
    (huv : G.Adj u v) :
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ =
      (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩ := by
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  exact huv

/-- A connected, non-complete finite graph has an inclusion-minimal vertex
separator. -/
theorem exists_minimal_separator [Finite V] (hconnected : G.Connected)
    (hproper : G ≠ ⊤) :
    ∃ S : Set V, IsSeparator G S ∧
      ∀ T : Set V, T ⊂ S → ¬IsSeparator G T := by
  classical
  obtain ⟨a, b, hab, hnab⟩ : ∃ a b : V, a ≠ b ∧ ¬G.Adj a b := by
    by_contra h
    push Not at h
    apply hproper
    ext u v
    rw [SimpleGraph.top_adj]
    exact ⟨SimpleGraph.Adj.ne, h u v⟩
  have hinduce : G.induce (({a, b}ᶜ)ᶜ : Set V) = ⊥ := by
    ext u v
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    simp only [Set.mem_compl_iff, not_not] at hu hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.irrefl
    · exact hnab
    · exact fun h ↦ hnab h.symm
    · exact G.irrefl
  have hstarting : IsSeparator G ({a, b}ᶜ) := by
    refine ⟨hconnected, a, b, ?_, ?_, ?_⟩
    · simp
    · simp
    · rw [hinduce]
      intro hreach
      have heq := SimpleGraph.reachable_bot.mp hreach
      exact hab (congrArg Subtype.val heq)
  obtain ⟨S, hS, hminimal⟩ :=
    (Set.toFinite {T : Set V | IsSeparator G T}).exists_minimal
      ⟨{a, b}ᶜ, hstarting⟩
  refine ⟨S, hS, ?_⟩
  intro T hTS hT
  exact hTS.2 (hminimal hT hTS.1)

/-- Every vertex of an inclusion-minimal separator has a neighbor in either
component singled out by a separated pair. -/
theorem exists_neighbor_in_component {S : Set V}
    (hconnected : G.Connected)
    (hminimal : ∀ T : Set V, T ⊂ S → ¬IsSeparator G T)
    {s u v : V} (hs : s ∈ S) (hu : u ∉ S) (hv : v ∉ S)
    (huv : ¬(G.induce Sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    ∃ a : V, ∃ (ha : a ∉ S),
      (G.induce Sᶜ).connectedComponentMk ⟨a, ha⟩ =
          (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ∧
        G.Adj s a := by
  classical
  by_contra hnone
  push Not at hnone
  have hu' : u ∉ S \ {s} := fun h ↦ hu h.1
  have hv' : v ∉ S \ {s} := fun h ↦ hv h.1
  have hstill : ¬(G.induce (S \ {s})ᶜ).Reachable ⟨u, hu'⟩ ⟨v, hv'⟩ := by
    intro hreach
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    have invariant : ∀ z : ↥(S \ {s})ᶜ,
        Relation.ReflTransGen (G.induce (S \ {s})ᶜ).Adj ⟨u, hu'⟩ z →
          ∃ (hz : z.val ∉ S),
            (G.induce Sᶜ).connectedComponentMk ⟨z.val, hz⟩ =
              (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ := by
      intro z hz
      induction hz with
      | refl => exact ⟨hu, rfl⟩
      | @tail b c _ hbc hb =>
          obtain ⟨hbS, hbcomponent⟩ := hb
          have hbcG : G.Adj b.val c.val := hbc
          have hc_cases : c.val ∉ S ∨ c.val = s := by
            have hc := c.2
            simp only [Set.mem_compl_iff, Set.mem_sdiff,
              Set.mem_singleton_iff, not_and, not_not] at hc
            tauto
          rcases hc_cases with hcS | hcs
          · refine ⟨hcS, ?_⟩
            exact (component_eq_of_adj hbS hcS hbcG).symm.trans hbcomponent
          · have hbs : G.Adj b.val s := by simpa only [hcs] using hbcG
            exact (hnone b.val hbS hbcomponent hbs.symm).elim
    obtain ⟨hvS, hvcomponent⟩ := invariant ⟨v, hv'⟩ hreach
    exact huv (SimpleGraph.ConnectedComponent.eq.mp hvcomponent.symm)
  exact hminimal (S \ {s}) (Set.sdiff_singleton_ssubset.mpr hs)
    ⟨hconnected, u, v, hu', hv', hstill⟩

end Separator
end Erdos81
