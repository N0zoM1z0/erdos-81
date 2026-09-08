import Erdos81.RootHostedTriangles
import Mathlib.Tactic

/-!
# The combined terminal triangle packing

This module combines the outside-edge triangles with the root-edge triangles.
The actual host lists exclude every spoke consumed by the first family, so
the two certified packings are cross-disjoint.
-/

namespace Erdos81
namespace TerminalPacking

open MixedModel ExternalInputs RootedGraph RootedPEO TerminalAssignment
  RootHostLists

attribute [-instance] MixedModel.resourceFintype

variable {V Color : Type} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- An outside-edge triangle and a root-edge triangle cannot share a graph
edge. -/
theorem no_cross_shared_edge {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e : ↑(retainedAssignedEdges O C S assign))
    (f : Resource (⊤ : SimpleGraph ↑P)) (r : Resource G)
    (her : Uses (Sum.inl (HostedTriangles.triangle O C S assign e)) r)
    (hfr : Uses (Sum.inl (RootHostedTriangles.triangle hP hR f)) r) : False := by
  classical
  change r.1.toFinset ⊆ HostedTriangles.vertices O C S assign e at her
  change r.1.toFinset ⊆
    RootHostedTriangles.vertices O C S assign R f at hfr
  have hrCard : r.1.toFinset.card = 2 := by
    let rf : ↑G.edgeFinset := ⟨r.1, G.mem_edgeFinset.mpr r.2⟩
    exact G.card_toFinset_mem_edgeFinset rf
  have hroot : ∃ a ∈ r.1.toFinset, a ∈ P := by
    by_contra hnone
    push Not at hnone
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
      1 < r.1.toFinset.card)
    have haTri := hfr ha
    have hbTri := hfr hb
    simp only [RootHostedTriangles.vertices, Finset.mem_insert] at haTri hbTri
    have haHost : a = R.color f := by
      rcases haTri with haHost | haRoot
      · exact haHost
      · exact (hnone a ha (RootHostedTriangles.mem_rootEndpoints_mem_root haRoot)).elim
    have hbHost : b = R.color f := by
      rcases hbTri with hbHost | hbRoot
      · exact hbHost
      · exact (hnone b hb (RootHostedTriangles.mem_rootEndpoints_mem_root hbRoot)).elim
    exact hab (haHost.trans hbHost.symm)
  obtain ⟨a, haR, haP⟩ := hroot
  obtain ⟨b, hbR, hba⟩ := Finset.exists_mem_ne (by omega :
    1 < r.1.toFinset.card) a
  have haOutTri := her haR
  have haRootTri := hfr haR
  simp only [HostedTriangles.vertices, Finset.mem_insert] at haOutTri
  simp only [RootHostedTriangles.vertices, Finset.mem_insert] at haRootTri
  have haHost : a = assignedHost C S assign e.1 := by
    rcases haOutTri with haHost | haOutside
    · exact haHost
    · exact ((mem_outsideVertices.mp
        (resource_endpoint_mem_outside O e.1.1 haOutside)) haP).elim
  have haRootEndpoint : a ∈ RootHostedTriangles.rootEndpoints f := by
    rcases haRootTri with haOutsideHost | haRootEndpoint
    · exact ((mem_outsideVertices.mp
        (RootHostedTriangles.host_outside hR f))
          (haOutsideHost ▸ haP)).elim
    · exact haRootEndpoint
  have hbOutTri := her hbR
  simp only [HostedTriangles.vertices, Finset.mem_insert] at hbOutTri
  have hbNotRoot : b ∉ P := by
    intro hbP
    rcases hbOutTri with hbHost | hbOutside
    · exact hba (hbHost.trans haHost.symm)
    · exact (mem_outsideVertices.mp
        (resource_endpoint_mem_outside O e.1.1 hbOutside)) hbP
  have hbOutside : b ∈ outsideVertices P := mem_outsideVertices.mpr hbNotRoot
  have hbEdge : b ∈ e.1.1.1.toFinset := by
    rcases hbOutTri with hbHost | hbEdge
    case inl =>
      have hbP : b ∈ P := hbHost.symm ▸
        HostedTriangles.host_mem_root O C S assign e
      exact (hbNotRoot hbP).elim
    case inr => exact hbEdge
  have hbRootTri := hfr hbR
  simp only [RootHostedTriangles.vertices, Finset.mem_insert] at hbRootTri
  have hbRootHost : b = R.color f := by
    rcases hbRootTri with hbHost | hbEndpoint
    · exact hbHost
    · exact (hbNotRoot
        (RootHostedTriangles.mem_rootEndpoints_mem_root hbEndpoint)).elim
  obtain ⟨aRoot, haEdge, haVal⟩ := Finset.mem_image.mp haRootEndpoint
  have hbUsed : b ∈ HostedTriangles.usedOutsideVertices O C S assign a := by
    apply Finset.mem_biUnion.mpr
    refine ⟨e, ?_, hbEdge⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, haHost.symm⟩
  have hnotUsed := mem_hostList_not_used (hR f) aRoot haEdge
  have haRootEq : (aRoot : V) = a := haVal
  have hbUsedAtRoot : b ∈
      HostedTriangles.usedOutsideVertices O C S assign aRoot.1 := by
    simpa [haRootEq] using hbUsed
  exact hnotUsed (hbRootHost ▸ hbUsedAtRoot)

/-- The triangle finsets of the outside and root packings are disjoint. -/
theorem packing_triangle_disjoint {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e) :
    Disjoint (HostedTriangles.packing O C S assign).triangles
      (RootHostedTriangles.packing hP hR).triangles := by
  classical
  rw [Finset.disjoint_left]
  intro T hTout hTroot
  obtain ⟨e, _he, rfl⟩ := Finset.mem_map.mp hTout
  obtain ⟨f, _hf, heq⟩ := Finset.mem_map.mp hTroot
  have hsets := congrArg Subtype.val heq.symm
  change HostedTriangles.vertices O C S assign e =
    RootHostedTriangles.vertices O C S assign R f at hsets
  have hinter := congrArg (fun K : Finset V ↦ (K ∩ P).card) hsets
  rw [HostedTriangles.vertices_inter_root,
    RootHostedTriangles.vertices_inter_root hR,
    Finset.card_singleton, RootHostedTriangles.rootEndpoints_card] at hinter
  omega

/-- Union of the two triangle packings. -/
noncomputable def packing {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e) :
    TrianglePacking.Packing G := by
  classical
  let out := HostedTriangles.packing O C S assign
  let root := RootHostedTriangles.packing hP hR
  refine
    { triangles := out.triangles ∪ root.triangles
      exclusive := ?_ }
  intro T U hT hU r hTr hUr
  rcases Finset.mem_union.mp hT with hTout | hTroot <;>
    rcases Finset.mem_union.mp hU with hUout | hUroot
  · exact out.exclusive hTout hUout r hTr hUr
  · obtain ⟨e, _he, rfl⟩ := Finset.mem_map.mp hTout
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_map.mp hUroot
    exact (no_cross_shared_edge hP hR e f r hTr hUr).elim
  · obtain ⟨f, _hf, rfl⟩ := Finset.mem_map.mp hUout
    obtain ⟨e, _he, rfl⟩ := Finset.mem_map.mp hTroot
    exact (no_cross_shared_edge hP hR f e r hUr hTr).elim
  · exact root.exclusive hTroot hUroot r hTr hUr

theorem card_packing {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e) :
    (packing hP hR).triangles.card =
      (retainedAssignedEdges O C S assign).card + Nat.choose P.card 2 := by
  classical
  rw [packing, Finset.card_union_of_disjoint
    (packing_triangle_disjoint hP hR),
    HostedTriangles.card_packing, RootHostedTriangles.card_packing]

end TerminalPacking
end Erdos81
