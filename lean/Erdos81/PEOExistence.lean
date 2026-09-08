import Erdos81.Dirac
import Erdos81.PerfectElimination
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic

/-!
# Constructing perfect-elimination orders

Repeatedly removing a simplicial vertex produces an elimination list.  For a
graph on `Fin n`, the list is then converted to an equivalence `Fin n ≃ Fin n`
whose pullback order is the fixed natural-order PEO used by
`PerfectElimination`.
-/

namespace Erdos81
namespace PEOExistence

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Suffix condition carried by a perfect-elimination list. -/
def HasCliqueSuffixes (G : SimpleGraph V) (l : List V) : Prop :=
  ∀ v rest, v :: rest <:+ l →
    G.IsClique {w | w ∈ rest ∧ G.Adj v w}

/-- A finite chordal graph has a simplicial vertex outside any proper clique. -/
theorem exists_simplicial_outside_clique [Fintype V]
    (hchordal : Erdos81.IsChordal G) {K : Set V} (hK : G.IsClique K)
    (houtside : ∃ v : V, v ∉ K) :
    ∃ v : V, v ∉ K ∧ Copying.IsSimplicial G v := by
  classical
  rcases Dirac.complete_or_two_simplicial
      (Fintype.card V) V G le_rfl hchordal with
    hcomplete | ⟨a, b, hab, hnab, haSimplicial, hbSimplicial⟩
  · obtain ⟨v, hvK⟩ := houtside
    refine ⟨v, hvK, ?_⟩
    rw [hcomplete]
    exact Dirac.simplicial_top v
  · by_cases haK : a ∈ K
    · have hbK : b ∉ K := by
        intro hbK
        exact hnab (hK haK hbK hab)
      exact ⟨b, hbK, hbSimplicial⟩
    · exact ⟨a, haK, haSimplicial⟩

/-- An arbitrary ordering of a clique already satisfies every PEO suffix
condition. -/
theorem clique_toList_hasCliqueSuffixes [DecidableEq V]
    {K : Finset V} (hK : G.IsClique (K : Set V)) :
    HasCliqueSuffixes G K.toList := by
  intro v rest hsuffix a ha b hb hab
  obtain ⟨pre, heq⟩ := hsuffix
  apply hK
  · have hlist : a ∈ K.toList := by
      rw [← heq]
      exact List.mem_append_right pre (List.mem_cons_of_mem v ha.1)
    exact Finset.mem_toList.mp hlist
  · have hlist : b ∈ K.toList := by
      rw [← heq]
      exact List.mem_append_right pre (List.mem_cons_of_mem v hb.1)
    exact Finset.mem_toList.mp hlist
  · exact hab

/-- Simpliciality inside `G[s]` gives the ambient clique needed for the first
suffix after a vertex is peeled. -/
theorem clique_of_simplicial_induce {s : Set V} {v : V} (hv : v ∈ s)
    (hsimplicial : Copying.IsSimplicial (G.induce s) ⟨v, hv⟩) :
    G.IsClique {w | w ∈ s ∧ G.Adj v w} := by
  rw [Copying.IsSimplicial] at hsimplicial
  intro p hp q hq hpq
  have hp' : (⟨p, hp.1⟩ : s) ∈
      (G.induce s).neighborSet ⟨v, hv⟩ := hp.2
  have hq' : (⟨q, hq.1⟩ : s) ∈
      (G.induce s).neighborSet ⟨v, hv⟩ := hq.2
  exact hsimplicial hp' hq' (fun h ↦ hpq (congrArg Subtype.val h))

/-- Eliminate all vertices outside `K` first.  The resulting list covers `s`
and has `K.toList` as a suffix. -/
theorem elimination_list_ending_clique_aux (hchordal : Erdos81.IsChordal G)
    (K : Finset V) (hK : G.IsClique (K : Set V)) :
    ∀ (bound : ℕ) (s : Finset V), s.card ≤ bound → K ⊆ s →
      ∃ l : List V, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ s) ∧
        HasCliqueSuffixes G l ∧ K.toList <:+ l := by
  classical
  intro bound
  induction bound with
  | zero =>
      intro s hs hKs
      have hcardKs : K.card ≤ s.card := Finset.card_le_card hKs
      have hEq : K = s := Finset.eq_of_subset_of_card_le hKs (by omega)
      subst s
      exact ⟨K.toList, K.nodup_toList, by simp,
        clique_toList_hasCliqueSuffixes hK, List.suffix_rfl⟩
  | succ bound ih =>
      intro s hs hKs
      by_cases hsK : s = K
      · subst s
        exact ⟨K.toList, K.nodup_toList, by simp,
          clique_toList_hasCliqueSuffixes hK, List.suffix_rfl⟩
      · have hnotSubset : ¬s ⊆ K := by
          intro hsSubset
          exact hsK (Finset.Subset.antisymm hsSubset hKs)
        obtain ⟨v, hvS, hvK⟩ := Finset.not_subset.mp hnotSubset
        let Ksub : Set ↥(s : Set V) := {z | z.val ∈ K}
        have hKsub : (G.induce (s : Set V)).IsClique Ksub := by
          intro a ha b hb hab
          exact hK ha hb (fun h ↦ hab (Subtype.ext h))
        have houtside : ∃ z : ↥(s : Set V), z ∉ Ksub :=
          ⟨⟨v, hvS⟩, hvK⟩
        obtain ⟨w, hwKsub, hwSimplicial⟩ :=
          exists_simplicial_outside_clique
            (G := G.induce (s : Set V))
            (Chordal.induce_isChordal G hchordal (s : Set V))
            hKsub houtside
        have hwK : w.val ∉ K := hwKsub
        have hKerased : K ⊆ s.erase w.val := by
          intro z hzK
          apply Finset.mem_erase.mpr
          refine ⟨?_, hKs hzK⟩
          intro hzw
          exact hwK (hzw ▸ hzK)
        have heraseCard := Finset.card_erase_of_mem w.2
        obtain ⟨tail, htailNodup, htailMem, htailSuffix, htailEnds⟩ :=
          ih (s.erase w.val) (by omega) hKerased
        have hwNotTail : w.val ∉ tail := by
          intro hwtail
          exact (Finset.mem_erase.mp ((htailMem w.val).mp hwtail)).1 rfl
        have hwClique : G.IsClique
            {z | z ∈ (s : Set V) ∧ G.Adj w.val z} :=
          clique_of_simplicial_induce w.2 hwSimplicial
        refine ⟨w.val :: tail,
          List.nodup_cons.mpr ⟨hwNotTail, htailNodup⟩, ?_, ?_, ?_⟩
        · intro z
          rw [List.mem_cons, htailMem, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨_, hz⟩)
            · exact w.2
            · exact hz
          · intro hz
            by_cases hzw : z = w.val
            · exact Or.inl hzw
            · exact Or.inr ⟨hzw, hz⟩
        · intro z rest hsuffix
          rw [List.suffix_cons_iff] at hsuffix
          rcases hsuffix with hfirst | hlater
          · obtain ⟨rfl, rfl⟩ := List.cons.inj hfirst
            intro a ha b hb hab
            exact hwClique
              ⟨(Finset.mem_erase.mp ((htailMem a).mp ha.1)).2, ha.2⟩
              ⟨(Finset.mem_erase.mp ((htailMem b).mp hb.1)).2, hb.2⟩
              hab
          · exact htailSuffix z rest hlater
        · exact htailEnds.trans (List.suffix_cons w.val tail)

/-- A PEO list can be chosen to end in any prescribed clique. -/
theorem exists_elimination_list_ending_clique [Fintype V]
    (hchordal : Erdos81.IsChordal G) (K : Finset V)
    (hK : G.IsClique (K : Set V)) :
    ∃ l : List V, l.Nodup ∧ (∀ x : V, x ∈ l) ∧
      HasCliqueSuffixes G l ∧ K.toList <:+ l := by
  classical
  obtain ⟨l, hnodup, hmem, hsuffix, hends⟩ :=
    elimination_list_ending_clique_aux hchordal K hK
      (Fintype.card V) Finset.univ Finset.card_univ.le (Finset.subset_univ K)
  exact ⟨l, hnodup, fun x ↦ (hmem x).mpr (Finset.mem_univ x), hsuffix, hends⟩

/-- The recursive elimination-list construction on an arbitrary finite vertex
set. -/
theorem elimination_list_aux (hchordal : Erdos81.IsChordal G) :
    ∀ (bound : ℕ) (s : Finset V), s.card ≤ bound →
      ∃ l : List V, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ s) ∧
        HasCliqueSuffixes G l := by
  classical
  intro bound
  induction bound with
  | zero =>
      intro s hs
      have hsEmpty : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
      subst s
      exact ⟨[], List.nodup_nil, by simp, by
        intro v rest hsuffix
        simp at hsuffix⟩
  | succ bound ih =>
      intro s hs
      rcases s.eq_empty_or_nonempty with rfl | hsNonempty
      · exact ⟨[], List.nodup_nil, by simp, by
          intro v rest hsuffix
          simp at hsuffix⟩
      · haveI : Nonempty ↥(s : Set V) :=
          (Finset.coe_nonempty.mpr hsNonempty).to_subtype
        obtain ⟨⟨v, hv⟩, hvSimplicial⟩ :=
          Dirac.exists_simplicial
            (G := G.induce (s : Set V))
            (Chordal.induce_isChordal G hchordal (s : Set V))
        have hvClique : G.IsClique
            {w | w ∈ (s : Set V) ∧ G.Adj v w} :=
          clique_of_simplicial_induce hv hvSimplicial
        obtain ⟨tail, htailNodup, htailMem, htailSuffix⟩ :=
          ih (s.erase v) (by
            have herase := Finset.card_erase_of_mem hv
            omega)
        have hvNotTail : v ∉ tail := by
          intro hvtail
          exact (Finset.mem_erase.mp ((htailMem v).mp hvtail)).1 rfl
        refine ⟨v :: tail, List.nodup_cons.mpr ⟨hvNotTail, htailNodup⟩,
          ?_, ?_⟩
        · intro x
          rw [List.mem_cons, htailMem, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨_, hx⟩)
            · exact hv
            · exact hx
          · intro hx
            by_cases hxv : x = v
            · exact Or.inl hxv
            · exact Or.inr ⟨hxv, hx⟩
        · intro x rest hsuffix
          rw [List.suffix_cons_iff] at hsuffix
          rcases hsuffix with hfirst | hlater
          · obtain ⟨rfl, rfl⟩ := List.cons.inj hfirst
            intro p hp q hq hpq
            exact hvClique
              ⟨(Finset.mem_erase.mp ((htailMem p).mp hp.1)).2, hp.2⟩
              ⟨(Finset.mem_erase.mp ((htailMem q).mp hq.1)).2, hq.2⟩
              hpq
          · exact htailSuffix x rest hlater

/-- Every finite chordal graph has a duplicate-free elimination list covering
all vertices. -/
theorem exists_elimination_list [Fintype V]
    (hchordal : Erdos81.IsChordal G) :
    ∃ l : List V, l.Nodup ∧ (∀ x : V, x ∈ l) ∧
      HasCliqueSuffixes G l := by
  classical
  obtain ⟨l, hnodup, hmem, hsuffix⟩ := elimination_list_aux hchordal
    (Fintype.card V) Finset.univ Finset.card_univ.le
  exact ⟨l, hnodup, fun x ↦ (hmem x).mpr (Finset.mem_univ x), hsuffix⟩

/-- An entry strictly after index `i` belongs to the tail obtained by dropping
the first `i+1` entries. -/
theorem get_mem_drop_succ {l : List V} (i j : Fin l.length) (hij : i < j) :
    l.get j ∈ l.drop (i.val + 1) := by
  apply List.mem_iff_getElem.mpr
  refine ⟨j.val - (i.val + 1), ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · simp only [List.getElem_drop]
    congr 1
    omega

/-- A duplicate-free list covering a finite type has the expected length. -/
theorem length_eq_card [Fintype V] [DecidableEq V] {l : List V}
    (hnodup : l.Nodup) (hcover : ∀ v : V, v ∈ l) :
    l.length = Fintype.card V := by
  have hfinset : l.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall (fun v ↦ by simpa using hcover v)
  calc
    l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = Fintype.card V := by rw [hfinset, Finset.card_univ]

/-- The elimination list supplies the relabelling required by
`PerfectElimination.HasPEO`. -/
theorem hasPEO_of_chordal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hchordal : Erdos81.IsChordal G) :
    PerfectElimination.HasPEO G := by
  classical
  obtain ⟨l, hnodup, hcover, hsuffix⟩ :=
    exists_elimination_list (G := G) hchordal
  have hlength : l.length = n := by
    simpa using length_eq_card hnodup hcover
  let toVertex : Fin l.length ≃ Fin n :=
    hnodup.getEquivOfForallMemList l hcover
  let toIndex : Fin n ≃ Fin l.length := finCongr hlength.symm
  let relabel : Fin n ≃ Fin n := toIndex.trans toVertex
  refine ⟨relabel, ?_⟩
  intro i
  rw [(G.comap relabel).isClique_iff]
  intro a ha b hb hab
  have ha' : a ∈ Finset.Ioi i ∧ (G.comap relabel).Adj i a := by
    simpa [PerfectElimination.laterNeighbors] using ha
  have hb' : b ∈ Finset.Ioi i ∧ (G.comap relabel).Adj i b := by
    simpa [PerfectElimination.laterNeighbors] using hb
  have hia : i < a := Finset.mem_Ioi.mp ha'.1
  have hib : i < b := Finset.mem_Ioi.mp hb'.1
  let ii : Fin l.length := toIndex i
  let ia : Fin l.length := toIndex a
  let ib : Fin l.length := toIndex b
  have hiia : ii < ia := by
    change i.val < a.val
    exact hia
  have hiib : ii < ib := by
    change i.val < b.val
    exact hib
  have haTail : l.get ia ∈ l.drop (ii.val + 1) :=
    get_mem_drop_succ ii ia hiia
  have hbTail : l.get ib ∈ l.drop (ii.val + 1) :=
    get_mem_drop_succ ii ib hiib
  have hsuffixAt : l.get ii :: l.drop (ii.val + 1) <:+ l := by
    rw [List.cons_get_drop_succ]
    exact List.drop_suffix _ _
  have hiaAdj : G.Adj (l.get ii) (l.get ia) := by
    have h := ha'.2
    change G.Adj (relabel i) (relabel a) at h
    change G.Adj (l.get ii) (l.get ia) at h
    exact h
  have hibAdj : G.Adj (l.get ii) (l.get ib) := by
    have h := hb'.2
    change G.Adj (relabel i) (relabel b) at h
    change G.Adj (l.get ii) (l.get ib) at h
    exact h
  have hiab : l.get ia ≠ l.get ib := by
    intro h
    exact hab (toIndex.injective (toVertex.injective h))
  have habAdj := hsuffix (l.get ii) (l.drop (ii.val + 1)) hsuffixAt
    ⟨haTail, hiaAdj⟩ ⟨hbTail, hibAdj⟩ hiab
  change G.Adj (relabel a) (relabel b)
  change G.Adj (l.get ia) (l.get ib)
  exact habAdj

/-- For finite labelled graphs, forbidden induced cycles and perfect
elimination orders are equivalent. -/
theorem isChordal_iff_hasPEO {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    Erdos81.IsChordal G ↔ PerfectElimination.HasPEO G :=
  ⟨hasPEO_of_chordal G, PerfectElimination.isChordal_of_hasPEO⟩

/-- The PEO edge bound, now discharged directly from chordality. -/
theorem edge_bound_of_chordal {n p : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hpn : p ≤ n) (hchordal : Erdos81.IsChordal G)
    (hclique : PerfectElimination.CliqueOrderAtMost G p) :
    G.edgeFinset.card + Nat.choose p 2 ≤ (p - 1) * n :=
  PerfectElimination.edge_bound_of_hasPEO hpn
    (hasPEO_of_chordal G hchordal) hclique

/-- The manuscript's missing-pair consequence for every finite chordal graph. -/
theorem complement_edge_bound_of_chordal {n p : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hp : 1 ≤ p) (hpn : p ≤ n) (hchordal : Erdos81.IsChordal G)
    (hclique : PerfectElimination.CliqueOrderAtMost G p) :
    Nat.choose (n - p + 1) 2 ≤ Gᶜ.edgeFinset.card :=
  PerfectElimination.complement_edge_bound_of_hasPEO hp hpn
    (hasPEO_of_chordal G hchordal) hclique

/-- Label-independent form of the chordal missing-pair bound.  This is the
version used on an induced graph whose vertex type is a finite subtype. -/
theorem complement_edge_bound_of_chordal_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p : ℕ}
    (hp : 1 ≤ p) (hpn : p ≤ Fintype.card V)
    (hchordal : Erdos81.IsChordal G)
    (hclique : ∀ K : Finset V, G.IsClique (K : Set V) → K.card ≤ p) :
    Nat.choose (Fintype.card V - p + 1) 2 ≤ Gᶜ.edgeFinset.card := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e
  have hHchordal : Erdos81.IsChordal H := by
    intro k hk hcycle
    apply hchordal k hk
    obtain ⟨f⟩ := hcycle
    exact ⟨(SimpleGraph.Embedding.comap e.toEmbedding G).comp f⟩
  have hHclique : PerfectElimination.CliqueOrderAtMost H p := by
    intro K hK
    have hmap : G.IsClique ((K.map e.toEmbedding : Finset V) : Set V) := by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
      have hab : a ≠ b := fun hab ↦ hxy (congrArg e hab)
      exact (SimpleGraph.Iso.comap e G).map_adj_iff.mp (hK ha hb hab)
    simpa using hclique (K.map e.toEmbedding) hmap
  have hbound := complement_edge_bound_of_chordal hp hpn hHchordal hHclique
  let ec : Hᶜ ≃g Gᶜ :=
    { __ := e
      map_rel_iff' := by simp [H] }
  rw [ec.card_edgeFinset_eq] at hbound
  exact hbound

end PEOExistence
end Erdos81
