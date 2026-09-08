import Erdos81.RootHostLists
import Mathlib.Tactic

/-!
# Root-edge triangles from an actual host-list colouring

The Häggkvist--Janssen colouring assigns an available outside vertex to each
edge of the complete graph on the root.  This file turns every such assignment
into a certified triangle of the original graph.
-/

namespace Erdos81
namespace RootHostedTriangles

open MixedModel ExternalInputs RootedGraph RootedPEO TerminalAssignment
  HostedTriangles RootHostLists

attribute [-instance] MixedModel.resourceFintype

variable {V Color : Type} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- The original-vertex image of the two endpoints of a root edge. -/
noncomputable def rootEndpoints {P : Finset V}
    (e : Resource (⊤ : SimpleGraph ↑P)) : Finset V := by
  classical
  exact e.1.toFinset.image Subtype.val

/-- Vertex set of the root-edge triangle. -/
noncomputable def vertices {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V)
    (e : Resource (⊤ : SimpleGraph ↑P)) : Finset V :=
  insert (R.color e) (rootEndpoints e)

theorem rootEndpoints_card {P : Finset V}
    (e : Resource (⊤ : SimpleGraph ↑P)) : (rootEndpoints e).card = 2 := by
  classical
  rw [rootEndpoints, Finset.card_image_of_injective _ Subtype.val_injective]
  let ef : ↑(⊤ : SimpleGraph ↑P).edgeFinset :=
    ⟨e.1, (⊤ : SimpleGraph ↑P).mem_edgeFinset.mpr e.2⟩
  exact (⊤ : SimpleGraph ↑P).card_toFinset_mem_edgeFinset ef

theorem mem_rootEndpoints_mem_root {P : Finset V}
    {e : Resource (⊤ : SimpleGraph ↑P)} {x : V}
    (hx : x ∈ rootEndpoints e) : x ∈ P := by
  classical
  obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
  exact y.2

@[simp]
theorem mem_rootEndpoints_iff {P : Finset V}
    {e : Resource (⊤ : SimpleGraph ↑P)} {x : ↑P} :
    (x : V) ∈ rootEndpoints e ↔ x ∈ e.1.toFinset := by
  classical
  simp [rootEndpoints]

theorem host_outside {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    R.color e ∈ outsideVertices P :=
  mem_hostList_outside (hR e)

theorem host_not_rootEndpoints {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    R.color e ∉ rootEndpoints e := by
  intro h
  exact (mem_outsideVertices.mp (host_outside hR e))
    (mem_rootEndpoints_mem_root h)

theorem vertices_card {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    (vertices O C S assign R e).card = 3 := by
  rw [vertices, Finset.card_insert_of_notMem
    (host_not_rootEndpoints hR e), rootEndpoints_card]

theorem vertices_isClique {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    G.IsClique (vertices O C S assign R e : Set V) := by
  classical
  intro x hx y hy hxy
  simp only [vertices, Finset.coe_insert, Set.mem_insert_iff] at hx hy
  rcases hx with hx | hx
  · subst x
    rcases hy with hy | hy
    · exact (hxy hy.symm).elim
    · obtain ⟨yRoot, hyEdge, rfl⟩ := Finset.mem_image.mp hy
      exact (mem_hostList_adj (hR e) yRoot hyEdge).symm
  · rcases hy with hy | hy
    · subst y
      obtain ⟨xRoot, hxEdge, rfl⟩ := Finset.mem_image.mp hx
      exact mem_hostList_adj (hR e) xRoot hxEdge
    · exact hP (mem_rootEndpoints_mem_root hx)
        (mem_rootEndpoints_mem_root hy) hxy

/-- A root-edge triangle contains exactly its two root endpoints in `P`. -/
theorem vertices_inter_root {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e : Resource (⊤ : SimpleGraph ↑P)) :
    vertices O C S assign R e ∩ P = rootEndpoints e := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hx' := Finset.mem_inter.mp hx
    simp only [vertices, Finset.mem_insert] at hx'
    rcases hx'.1 with hxHost | hxRoot
    · exact ((mem_outsideVertices.mp (host_outside hR e))
        (hxHost ▸ hx'.2)).elim
    · exact hxRoot
  · intro hx
    exact Finset.mem_inter.mpr
      ⟨by exact Finset.mem_insert_of_mem hx, mem_rootEndpoints_mem_root hx⟩

/-- Certified root-edge triangle. -/
noncomputable def triangle {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e : Resource (⊤ : SimpleGraph ↑P)) : CliqueOfOrder G 3 :=
  ⟨vertices O C S assign R e, vertices_card hR e,
    vertices_isClique hP hR e⟩

/-- The root edge can be recovered from its hosted triangle. -/
theorem triangle_injective {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e) :
    Function.Injective (triangle hP hR) := by
  intro e f hef
  apply Subtype.ext
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset]
  have hvertices := congrArg Subtype.val hef
  change vertices O C S assign R e = vertices O C S assign R f at hvertices
  have hroot : (x : V) ∈ P := x.2
  constructor
  · intro hx
    have hxTri : (x : V) ∈ vertices O C S assign R e := by
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hxTriF : (x : V) ∈ vertices O C S assign R f := by
      rw [← hvertices]
      exact hxTri
    have hxNeHost : (x : V) ≠ R.color f := by
      intro h
      exact (mem_outsideVertices.mp (host_outside hR f)) (h.symm ▸ hroot)
    have hxEndpoints : (x : V) ∈ rootEndpoints f := by
      simpa [vertices, hxNeHost] using hxTriF
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxEndpoints
    have : y = x := Subtype.ext hyx
    simpa [this] using hy
  · intro hx
    have hxTri : (x : V) ∈ vertices O C S assign R f := by
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hxTriE : (x : V) ∈ vertices O C S assign R e := by
      rw [hvertices]
      exact hxTri
    have hxNeHost : (x : V) ≠ R.color e := by
      intro h
      exact (mem_outsideVertices.mp (host_outside hR e)) (h.symm ▸ hroot)
    have hxEndpoints : (x : V) ∈ rootEndpoints e := by
      simpa [vertices, hxNeHost] using hxTriE
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxEndpoints
    have : y = x := Subtype.ext hyx
    simpa [this] using hy

/-- Two root-hosted triangles sharing an edge arise from the same root edge. -/
theorem eq_of_shared_edge {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e)
    (e f : Resource (⊤ : SimpleGraph ↑P)) (r : Resource G)
    (her : Uses (Sum.inl (triangle hP hR e)) r)
    (hfr : Uses (Sum.inl (triangle hP hR f)) r) : e = f := by
  classical
  change r.1.toFinset ⊆ vertices O C S assign R e at her
  change r.1.toFinset ⊆ vertices O C S assign R f at hfr
  by_cases hout : ∃ z ∈ r.1.toFinset, z ∈ outsideVertices P
  · obtain ⟨z, hzR, hzOut⟩ := hout
    have hzE := her hzR
    have hzF := hfr hzR
    simp only [vertices, Finset.mem_insert] at hzE hzF
    have hzHostE : z = R.color e := by
      rcases hzE with hzHost | hzRoot
      · exact hzHost
      · exact ((mem_outsideVertices.mp hzOut)
          (mem_rootEndpoints_mem_root hzRoot)).elim
    have hzHostF : z = R.color f := by
      rcases hzF with hzHost | hzRoot
      · exact hzHost
      · exact ((mem_outsideVertices.mp hzOut)
          (mem_rootEndpoints_mem_root hzRoot)).elim
    have hcolor : R.color e = R.color f := hzHostE.symm.trans hzHostF
    obtain ⟨y, hyR, hyz⟩ := Finset.exists_mem_ne
      (show 1 < r.1.toFinset.card from by
        let rf : ↑G.edgeFinset := ⟨r.1, G.mem_edgeFinset.mpr r.2⟩
        have hcard := G.card_toFinset_mem_edgeFinset rf
        change r.1.toFinset.card = 2 at hcard
        omega) z
    have hyE := her hyR
    have hyF := hfr hyR
    simp only [vertices, Finset.mem_insert] at hyE hyF
    have hyRootE : y ∈ rootEndpoints e := by
      rcases hyE with hyHost | hyRoot
      · exact (hyz (hyHost.trans hzHostE.symm)).elim
      · exact hyRoot
    have hyRootF : y ∈ rootEndpoints f := by
      rcases hyF with hyHost | hyRoot
      · exact (hyz (hyHost.trans hzHostF.symm)).elim
      · exact hyRoot
    obtain ⟨ye, hye, hyeVal⟩ := Finset.mem_image.mp hyRootE
    obtain ⟨yf, hyf, hyfVal⟩ := Finset.mem_image.mp hyRootF
    have heyf : ye = yf := Subtype.ext (hyeVal.trans hyfVal.symm)
    have hmeet : EdgesMeet e f :=
      ⟨ye, Sym2.mem_toFinset.mp hye,
        Sym2.mem_toFinset.mp (heyf ▸ hyf)⟩
    by_contra hne
    exact R.proper hne hmeet hcolor
  · have hroot : ∀ z ∈ r.1.toFinset, z ∈ P := by
      intro z hz
      by_contra hzP
      exact hout ⟨z, hz, mem_outsideVertices.mpr hzP⟩
    have hsubE : r.1.toFinset ⊆ rootEndpoints e := by
      intro z hz
      have hzTri := her hz
      simp only [vertices, Finset.mem_insert] at hzTri
      rcases hzTri with hzHost | hzRoot
      · exact ((mem_outsideVertices.mp (host_outside hR e))
          (hzHost ▸ hroot z hz)).elim
      · exact hzRoot
    have hsubF : r.1.toFinset ⊆ rootEndpoints f := by
      intro z hz
      have hzTri := hfr hz
      simp only [vertices, Finset.mem_insert] at hzTri
      rcases hzTri with hzHost | hzRoot
      · exact ((mem_outsideVertices.mp (host_outside hR f))
          (hzHost ▸ hroot z hz)).elim
      · exact hzRoot
    have hrCard : r.1.toFinset.card = 2 := by
      let rf : ↑G.edgeFinset := ⟨r.1, G.mem_edgeFinset.mpr r.2⟩
      exact G.card_toFinset_mem_edgeFinset rf
    have hEqE : r.1.toFinset = rootEndpoints e :=
      Finset.eq_of_subset_of_card_le hsubE (by rw [rootEndpoints_card, hrCard])
    have hEqF : r.1.toFinset = rootEndpoints f :=
      Finset.eq_of_subset_of_card_le hsubF (by rw [rootEndpoints_card, hrCard])
    apply Subtype.ext
    apply Sym2.ext
    intro x
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset,
      ← mem_rootEndpoints_iff, ← mem_rootEndpoints_iff,
      ← hEqE, ← hEqF]

/-- All root edges form an edge-disjoint triangle packing. -/
noncomputable def packing {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e) :
    TrianglePacking.Packing G := by
  classical
  let emb : Resource (⊤ : SimpleGraph ↑P) ↪ CliqueOfOrder G 3 :=
    ⟨triangle hP hR, triangle_injective hP hR⟩
  refine
    { triangles := Finset.univ.map emb
      exclusive := ?_ }
  intro T U hT hU r hTr hUr
  obtain ⟨e, _he, rfl⟩ := Finset.mem_map.mp hT
  obtain ⟨f, _hf, rfl⟩ := Finset.mem_map.mp hU
  exact congrArg (triangle hP hR)
    (eq_of_shared_edge hP hR e f r hTr hUr)

theorem card_packing {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (hP : G.IsClique (P : Set V))
    {O : RootedPEO.Order G P}
    {C : ProperEdgeColoring (outsideGraph G P) Color}
    {S : Finset Color} {assign : ↑S ≃ ↑P}
    {R : ProperEdgeColoring (⊤ : SimpleGraph ↑P) V}
    (hR : ∀ e, R.color e ∈ hostList P O C S assign e) :
    (packing hP hR).triangles.card = Nat.choose P.card 2 := by
  classical
  rw [packing, Finset.card_map, Finset.card_univ,
    ← (⊤ : SimpleGraph ↑P).edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_coe]

end RootHostedTriangles
end Erdos81
