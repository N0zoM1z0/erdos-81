import Erdos81.HostedTriangles
import Mathlib.Tactic

/-!
# Host lists for root edges

After the outside-edge triangles have been chosen, a root edge may use any
outside vertex adjacent to both endpoints whose two spokes remain unused.
The forbidden set is the union of two missing columns and two used-spoke
sets.  This file proves the exact finite union bound required before applying
the Häggkvist--Janssen list-edge-colouring theorem.
-/

namespace Erdos81
namespace RootHostLists

open MixedModel ExternalInputs EdgeColoring RootedGraph RootedPEO
  TerminalAssignment HostedTriangles

attribute [-instance] MixedModel.resourceFintype

variable {V Color : Type} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- Vertices forbidden as hosts for a root edge. -/
noncomputable def forbidden {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (e : Resource (⊤ : SimpleGraph ↑P)) : Finset V := by
  classical
  exact e.1.toFinset.biUnion fun x ↦
    missingColumn G P x.1 ∪ usedOutsideVertices O C S assign x.1

/-- The actual list of available outside hosts for a root edge. -/
noncomputable def hostList {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (e : Resource (⊤ : SimpleGraph ↑P)) : Finset V :=
  outsideVertices P \ forbidden P O C S assign e

theorem usedOutsideVertices_subset {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P) (x : V) :
    usedOutsideVertices O C S assign x ⊆ outsideVertices P := by
  classical
  intro z hz
  obtain ⟨e, he, hzEdge⟩ := Finset.mem_biUnion.mp hz
  exact resource_endpoint_mem_outside O e.1.1 hzEdge

theorem forbidden_subset_outside {G : SimpleGraph V}
    [DecidableRel G.Adj] (P : Finset V)
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    forbidden P O C S assign e ⊆ outsideVertices P := by
  classical
  intro z hz
  obtain ⟨x, _hxEdge, hzBad⟩ :=
    Finset.mem_biUnion.mp (show z ∈ e.1.toFinset.biUnion (fun x ↦
      missingColumn G P x.1 ∪ usedOutsideVertices O C S assign x.1) from hz)
  rcases Finset.mem_union.mp hzBad with hzMissing | hzUsed
  · exact (mem_missingColumn.mp hzMissing).1
  · exact usedOutsideVertices_subset O C S assign x hzUsed

/-- The four forbidden sets have total size at most `2D+4t`. -/
theorem card_forbidden_le {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) (O : RootedPEO.Order G P)
    (C : BoundedColoring (outsideGraph G P) Color t)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    (forbidden P O C.toProper S assign e).card ≤
      2 * maxMissingColumn G P + 4 * t := by
  classical
  have hedgeCard : e.1.toFinset.card = 2 := by
    let ef : ↑(⊤ : SimpleGraph ↑P).edgeFinset :=
      ⟨e.1, (⊤ : SimpleGraph ↑P).mem_edgeFinset.mpr e.2⟩
    exact (⊤ : SimpleGraph ↑P).card_toFinset_mem_edgeFinset ef
  calc
    (forbidden P O C.toProper S assign e).card ≤
        ∑ x ∈ e.1.toFinset,
          (missingColumn G P x.1 ∪
            usedOutsideVertices O C.toProper S assign x.1).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ e.1.toFinset,
        (maxMissingColumn G P + 2 * t) := by
      exact Finset.sum_le_sum fun x _hx ↦
        (Finset.card_union_le (missingColumn G P x.1)
          (usedOutsideVertices O C.toProper S assign x.1)).trans (Nat.add_le_add
          (card_missingColumn_le_max G P x.2)
          (card_usedOutsideVertices_le O C S assign x.2))
    _ = 2 * maxMissingColumn G P + 4 * t := by
      simp [hedgeCard]
      ring

/-- The manuscript host condition guarantees at least `|P|` actual hosts on
every root edge. -/
theorem card_hostList_ge_root {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) (O : RootedPEO.Order G P)
    (C : BoundedColoring (outsideGraph G P) Color t)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (hhost : P.card + 2 * maxMissingColumn G P + 4 * t ≤
      (outsideVertices P).card)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    P.card ≤ (hostList P O C.toProper S assign e).card := by
  have hsub := forbidden_subset_outside P O C.toProper S assign e
  have hcard := card_forbidden_le P O C S assign e
  rw [hostList, Finset.card_sdiff_of_subset hsub]
  omega

theorem mem_hostList_outside {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {e : Resource (⊤ : SimpleGraph ↑P)} {z : V}
    (hz : z ∈ hostList P O C S assign e) : z ∈ outsideVertices P :=
  (Finset.mem_sdiff.mp hz).1

/-- A listed host is adjacent to every endpoint of its root edge. -/
theorem mem_hostList_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {e : Resource (⊤ : SimpleGraph ↑P)} {z : V}
    (hz : z ∈ hostList P O C S assign e) :
    ∀ x ∈ e.1.toFinset, G.Adj x.1 z := by
  classical
  intro x hx
  have hzOut := mem_hostList_outside hz
  have hzNotForbidden := (Finset.mem_sdiff.mp hz).2
  have hzNotMissing : z ∉ missingColumn G P x.1 := by
    intro hzMissing
    apply hzNotForbidden
    apply Finset.mem_biUnion.mpr
    exact ⟨x, hx, Finset.mem_union.mpr (Or.inl hzMissing)⟩
  by_contra hAdj
  exact hzNotMissing (mem_missingColumn.mpr ⟨hzOut, hAdj⟩)

/-- A listed host has not had the relevant spoke consumed by an outside-edge
triangle. -/
theorem mem_hostList_not_used {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {e : Resource (⊤ : SimpleGraph ↑P)} {z : V}
    (hz : z ∈ hostList P O C S assign e) :
    ∀ x ∈ e.1.toFinset,
      z ∉ usedOutsideVertices O C S assign x.1 := by
  classical
  intro x hx hzUsed
  exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_biUnion.mpr
    ⟨x, hx, Finset.mem_union.mpr (Or.inr hzUsed)⟩)

/-- Häggkvist--Janssen assigns an actual available outside host to every
root edge. -/
theorem exists_root_host_coloring {G : SimpleGraph V}
    [DecidableRel G.Adj] (hHJ : HaggkvistJanssenInput)
    (P : Finset V) (O : RootedPEO.Order G P)
    (C : BoundedColoring (outsideGraph G P) Color t)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (hhost : P.card + 2 * maxMissingColumn G P + 4 * t ≤
      (outsideVertices P).card) :
    ∃ R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V,
      ∀ e, R.color e ∈ hostList P O C.toProper S assign e := by
  apply hHJ (hostList P O C.toProper S assign)
  intro e
  simpa only [Fintype.card_coe] using
    card_hostList_ge_root P O C S assign hhost e

end RootHostLists
end Erdos81
