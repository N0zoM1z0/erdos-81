import Erdos81.ChordalWalk
import Erdos81.Separator
import Mathlib.Tactic

/-!
# Minimal separators in chordal graphs

The main construction in this module finds a geodesic arc whose internal
vertices lie in one prescribed component after a separator is deleted.  Two
such arcs, through different components, will force an induced cycle whenever
two separator vertices fail to be adjacent.
-/

namespace Erdos81
namespace ChordalSeparator

open SimpleGraph
open SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- A shortest `x`--`y` arc can be confined to a chosen component of `G - S`
when both endpoints have a neighbor in that component. -/
theorem exists_component_arc {S : Set V} {x y u : V}
    (hxy : x ≠ y) (hnxy : ¬G.Adj x y) (hu : u ∉ S)
    (hx : ∃ a : V, ∃ (ha : a ∉ S),
      (G.induce Sᶜ).connectedComponentMk ⟨a, ha⟩ =
          (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ∧ G.Adj x a)
    (hy : ∃ b : V, ∃ (hb : b ∉ S),
      (G.induce Sᶜ).connectedComponentMk ⟨b, hb⟩ =
          (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ∧ G.Adj y b) :
    ∃ P : G.Walk x y,
      P.IsPath ∧ 2 ≤ P.length ∧
      (∀ i j, i + 1 < j → j ≤ P.length →
        ¬G.Adj (P.getVert i) (P.getVert j)) ∧
      (∀ i, 0 < i → i < P.length →
        ∃ (hi : P.getVert i ∉ S),
          (G.induce Sᶜ).connectedComponentMk ⟨P.getVert i, hi⟩ =
            (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩) := by
  classical
  obtain ⟨a, haS, haComponent, hxa⟩ := hx
  obtain ⟨b, hbS, hbComponent, hyb⟩ := hy
  let component : Set V := {v | ∃ (hv : v ∉ S),
    (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩ =
      (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩}
  let carrier : Set V := insert x (insert y component)
  have hxCarrier : x ∈ carrier := Set.mem_insert _ _
  have hyCarrier : y ∈ carrier := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have component_mem_carrier {z : V} (hz : z ∈ component) : z ∈ carrier :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hz)
  have haCarrier : a ∈ carrier :=
    component_mem_carrier ⟨haS, haComponent⟩
  have hbCarrier : b ∈ carrier :=
    component_mem_carrier ⟨hbS, hbComponent⟩
  obtain ⟨middle⟩ : (G.induce Sᶜ).Reachable ⟨a, haS⟩ ⟨b, hbS⟩ :=
    SimpleGraph.ConnectedComponent.eq.mp (haComponent.trans hbComponent.symm)
  have middle_mem : ∀ z ∈
      (middle.map (SimpleGraph.Embedding.induce Sᶜ).toHom).support,
      z ∈ carrier := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    apply component_mem_carrier
    refine ⟨z'.2, ?_⟩
    have haz : (G.induce Sᶜ).Reachable ⟨a, haS⟩ z' :=
      ⟨middle.takeUntil z' hz'⟩
    exact (SimpleGraph.ConnectedComponent.eq.mpr haz).symm.trans haComponent
  let full : G.Walk x y :=
    cons hxa ((middle.map (SimpleGraph.Embedding.induce Sᶜ).toHom).append
      (cons hyb.symm nil))
  have full_mem : ∀ z ∈ full.support, z ∈ carrier := by
    intro z hz
    change z ∈ (cons hxa
      ((middle.map (SimpleGraph.Embedding.induce Sᶜ).toHom).append
        (cons hyb.symm nil))).support at hz
    rw [support_cons] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hxCarrier
    · rcases (mem_support_append_iff _ _).mp hz with hz | hz
      · exact middle_mem _ hz
      · rw [support_cons] at hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hbCarrier
        · simp only [support_nil, List.mem_singleton] at hz
          simpa only [hz] using hyCarrier
  have hreachable : (G.induce carrier).Reachable
      ⟨x, hxCarrier⟩ ⟨y, hyCarrier⟩ :=
    ⟨full.induce carrier full_mem⟩
  obtain ⟨P', hgeodesic⟩ := hreachable.exists_walk_length_eq_dist
  have hP'path : P'.IsPath := P'.isPath_of_length_eq_dist hgeodesic
  let embedding := SimpleGraph.Embedding.induce (G := G) carrier
  let P : G.Walk x y := P'.map embedding.toHom
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact map_isPath_of_injective embedding.injective hP'path
  · change 2 ≤ (P'.map embedding.toHom).length
    rw [length_map, hgeodesic]
    have hne : (⟨x, hxCarrier⟩ : carrier) ≠ ⟨y, hyCarrier⟩ :=
      fun h ↦ hxy (congrArg Subtype.val h)
    have hnotAdjacent : ¬(G.induce carrier).Adj
        ⟨x, hxCarrier⟩ ⟨y, hyCarrier⟩ := fun h ↦ hnxy h
    exact hreachable.one_lt_dist_of_ne_of_not_adj hne hnotAdjacent
  · intro i j hij hj
    change j ≤ (P'.map embedding.toHom).length at hj
    rw [length_map] at hj
    intro hadj
    change G.Adj ((P'.map embedding.toHom).getVert i)
      ((P'.map embedding.toHom).getVert j) at hadj
    rw [getVert_map, getVert_map] at hadj
    have hadj' : (G.induce carrier).Adj (P'.getVert i) (P'.getVert j) := by
      exact embedding.map_adj_iff.mp hadj
    exact ChordalWalk.geodesic_not_adj_of_gap P' hgeodesic hij hj hadj'
  · intro i hi hlt
    change i < (P'.map embedding.toHom).length at hlt
    rw [length_map] at hlt
    have hnotX : P'.getVert i ≠ ⟨x, hxCarrier⟩ := by
      intro heq
      have hi0 := hP'path.getVert_injOn hlt.le (Nat.zero_le _)
        (heq.trans P'.getVert_zero.symm)
      omega
    have hnotY : P'.getVert i ≠ ⟨y, hyCarrier⟩ := by
      intro heq
      have hiLength := hP'path.getVert_injOn hlt.le
        (show P'.length ≤ P'.length from le_rfl)
        (heq.trans P'.getVert_length.symm)
      omega
    have hz := (P'.getVert i).2
    change (P'.getVert i).val ∈ insert x (insert y component) at hz
    rcases hz with hz | hz | hz
    · exact (hnotX (Subtype.ext hz)).elim
    · exact (hnotY (Subtype.ext hz)).elim
    · obtain ⟨hzS, hzComponent⟩ := hz
      have hmap : (P'.map embedding.toHom).getVert i = (P'.getVert i).val := by
        rw [getVert_map]
        rfl
      have hmappedS : (P'.map embedding.toHom).getVert i ∉ S := by
        simpa only [hmap] using hzS
      refine ⟨hmappedS, ?_⟩
      change (G.induce Sᶜ).connectedComponentMk
          ⟨(P'.map embedding.toHom).getVert i, hmappedS⟩ =
        (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩
      simpa only [hmap] using hzComponent

/-- An inclusion-minimal separator of a chordal graph is a clique. -/
theorem minimal_separator_isClique {S : Set V}
    (hchordal : Erdos81.IsChordal G)
    (hseparator : Separator.IsSeparator G S)
    (hminimal : ∀ T : Set V, T ⊂ S → ¬Separator.IsSeparator G T) :
    G.IsClique S := by
  rw [G.isClique_iff]
  intro x hx y hy hxy
  by_contra hnxy
  obtain ⟨hconnected, u, v, hu, hv, huv⟩ := hseparator
  have hvu : ¬(G.induce Sᶜ).Reachable ⟨v, hv⟩ ⟨u, hu⟩ :=
    fun h ↦ huv h.symm
  have hcomponents :
      (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ≠
        (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩ :=
    fun h ↦ huv (SimpleGraph.ConnectedComponent.eq.mp h)
  obtain ⟨P, hPpath, hPlength, hPchordless, hPinside⟩ :=
    exists_component_arc hxy hnxy hu
      (Separator.exists_neighbor_in_component hconnected hminimal hx hu hv huv)
      (Separator.exists_neighbor_in_component hconnected hminimal hy hu hv huv)
  obtain ⟨Q, hQpath, hQlength, hQchordless, hQinside⟩ :=
    exists_component_arc hxy hnxy hv
      (Separator.exists_neighbor_in_component hconnected hminimal hx hv hu hvu)
      (Separator.exists_neighbor_in_component hconnected hminimal hy hv hu hvu)
  have hPclassify : ∀ z ∈ P.support,
      z = x ∨ z = y ∨
        ∃ (hz : z ∉ S),
          (G.induce Sᶜ).connectedComponentMk ⟨z, hz⟩ =
            (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨i, hiz, hi⟩ := hz
    rcases Nat.eq_zero_or_pos i with rfl | hiPos
    · exact Or.inl (by simpa only [P.getVert_zero] using hiz.symm)
    · rcases eq_or_lt_of_le hi with hiEnd | hiInterior
      · exact Or.inr (Or.inl (by
          rw [hiEnd, P.getVert_length] at hiz
          exact hiz.symm))
      · exact Or.inr (Or.inr (by
          rw [← hiz]
          exact hPinside i hiPos hiInterior))
  have hQclassify : ∀ z ∈ Q.support,
      z = x ∨ z = y ∨
        ∃ (hz : z ∉ S),
          (G.induce Sᶜ).connectedComponentMk ⟨z, hz⟩ =
            (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩ := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨i, hiz, hi⟩ := hz
    rcases Nat.eq_zero_or_pos i with rfl | hiPos
    · exact Or.inl (by simpa only [Q.getVert_zero] using hiz.symm)
    · rcases eq_or_lt_of_le hi with hiEnd | hiInterior
      · exact Or.inr (Or.inl (by
          rw [hiEnd, Q.getVert_length] at hiz
          exact hiz.symm))
      · exact Or.inr (Or.inr (by
          rw [← hiz]
          exact hQinside i hiPos hiInterior))
  have hcommon_support : ∀ z ∈ P.support, z ∈ Q.support → z = x ∨ z = y := by
    intro z hzP hzQ
    rcases hPclassify z hzP with hzx | hzy | ⟨hzS, hzPcomponent⟩
    · exact Or.inl hzx
    · exact Or.inr hzy
    · rcases hQclassify z hzQ with hzx | hzy | ⟨_, hzQcomponent⟩
      · exact Or.inl hzx
      · exact Or.inr hzy
      · exact (hcomponents (hzPcomponent.symm.trans hzQcomponent)).elim
  have hcross : ∀ i j, 0 < i → i < P.length →
      0 < j → j < Q.length →
      ¬G.Adj (P.getVert i) (Q.getVert j) := by
    intro i j hiPos hiLt hjPos hjLt hij
    obtain ⟨hiS, hiComponent⟩ := hPinside i hiPos hiLt
    obtain ⟨hjS, hjComponent⟩ := hQinside j hjPos hjLt
    have hsame := Separator.component_eq_of_adj hiS hjS hij
    exact hcomponents (hiComponent.symm.trans (hsame.trans hjComponent))
  have hxNotPTail : x ∉ P.support.tail := by
    have hnodup := hPpath.support_nodup
    rw [← P.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hyNotQReverseTail : y ∉ Q.reverse.support.tail := by
    have hnodup := hQpath.reverse.support_nodup
    rw [← Q.reverse.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hedges : List.Disjoint P.edges Q.edges := by
    intro edge
    induction edge using Sym2.ind with
    | _ a b =>
        intro habP habQ
        have hab : G.Adj a b := P.adj_of_mem_edges habP
        have ha := hcommon_support a
          (P.fst_mem_support_of_mem_edges habP)
          (Q.fst_mem_support_of_mem_edges habQ)
        have hb := hcommon_support b
          (P.snd_mem_support_of_mem_edges habP)
          (Q.snd_mem_support_of_mem_edges habQ)
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hab.ne rfl
        · exact hnxy hab
        · exact hnxy hab.symm
        · exact hab.ne rfl
  have hinteriors : List.Disjoint P.support.tail Q.reverse.support.tail := by
    intro z hzP hzQ
    have hzP' : z ∈ P.support := List.mem_of_mem_tail hzP
    have hzQ' : z ∈ Q.support := by
      have h : z ∈ Q.reverse.support := List.mem_of_mem_tail hzQ
      rwa [support_reverse, List.mem_reverse] at h
    rcases hcommon_support z hzP' hzQ' with rfl | rfl
    · exact hxNotPTail hzP
    · exact hyNotQReverseTail hzQ
  have hcycle := ChordalWalk.inducedCycleEmbedding_of_two_arcs
    hxy P Q hPpath hQpath hPlength hQlength hPchordless hQchordless
      hcross hedges hinteriors
  exact hchordal (P.length + Q.length) (by omega) hcycle

end ChordalSeparator
end Erdos81
