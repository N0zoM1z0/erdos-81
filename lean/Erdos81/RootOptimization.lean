import Erdos81.Chordal
import Erdos81.RootedGraph
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-!
# Finite optimization form of root promotion

Instead of making arbitrary sequential choices, root promotion is encoded by
minimizing

`8 * outsideEdges + 7 * p * (p - 1)`

over clique roots containing a fixed initial root, and then maximizing root
cardinality among minimizers.  Adding a complete outside vertex of degree at
least `7p/4` cannot increase this energy, so the tie-breaker rules it out.
Removing any newly added root vertex gives the complementary lower-degree
estimate needed to bound its missing column.  This finite optimization is
equivalent to the promotion argument but substantially cleaner to certify.
-/

namespace Erdos81
namespace RootOptimization

open SimpleGraph RootedGraph Chordal

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem outsideVertices_mono {P Q : Finset V} (hPQ : P ⊆ Q) :
    outsideVertices Q ⊆ outsideVertices P := by
  intro x hx
  rw [mem_outsideVertices] at hx ⊢
  exact fun hxP ↦ hx (hPQ hxP)

theorem outsideGraph_mono (G : SimpleGraph V) {P Q : Finset V}
    (hPQ : P ⊆ Q) : outsideGraph G Q ≤ outsideGraph G P := by
  intro x y hxy
  rw [outsideGraph_adj] at hxy ⊢
  exact ⟨hxy.1, fun hxP ↦ hxy.2.1 (hPQ hxP),
    fun hyP ↦ hxy.2.2 (hPQ hyP)⟩

theorem cliqueNum_outsideGraph_mono (G : SimpleGraph V) {P Q : Finset V}
    (hPQ : P ⊆ Q) :
    (outsideGraph G Q).cliqueNum ≤ (outsideGraph G P).cliqueNum := by
  obtain ⟨S, hS⟩ := (outsideGraph G Q).exists_isNClique_cliqueNum
  exact hS.card_eq ▸
    ((hS.isClique.mono (outsideGraph_mono G hPQ)).card_le_cliqueNum)

theorem outsideGraph_insert (G : SimpleGraph V) (P : Finset V) (u : V) :
    outsideGraph G (insert u P) = (outsideGraph G P).deleteIncidenceSet u := by
  ext x y
  simp only [outsideGraph_adj, deleteIncidenceSet_adj, Finset.mem_insert,
    not_or]
  tauto

theorem outsideEdgeCard_insert_add_degree (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset V) (u : V) :
    (outsideEdges G (insert u P)).card + (outsideGraph G P).degree u =
      (outsideEdges G P).card := by
  have hgraphs : outsideGraph G (insert u P) =
      (outsideGraph G P).deleteIncidenceSet u := outsideGraph_insert G P u
  have hfinsets : (outsideGraph G (insert u P)).edgeFinset =
      ((outsideGraph G P).deleteIncidenceSet u).edgeFinset := by
    apply Finset.ext
    intro e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [hgraphs]
  have hcard : (outsideGraph G (insert u P)).edgeFinset.card =
      (outsideGraph G P).edgeFinset.card - (outsideGraph G P).degree u := by
    rw [hfinsets]
    exact SimpleGraph.card_edgeFinset_deleteIncidenceSet
      (outsideGraph G P) u
  rw [card_outsideGraph_edges, card_outsideGraph_edges] at hcard
  have hdegree := (outsideGraph G P).degree_le_card_edgeFinset u
  rw [card_outsideGraph_edges] at hdegree
  omega

theorem degree_outsideGraph_erase_add_missingColumn
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) {x : V} (hx : x ∈ P) :
    (outsideGraph G (P.erase x)).degree x +
        (missingColumn G P x).card = (outsideVertices P).card := by
  have hneighbors : (outsideGraph G (P.erase x)).neighborFinset x =
      (outsideVertices P).filter fun y ↦ G.Adj x y := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, outsideGraph_adj,
      Finset.mem_erase, mem_outsideVertices, Finset.mem_filter]
    constructor
    · rintro ⟨hxy, _hxErase, hyErase⟩
      have hyP : y ∉ P := by
        intro hy
        exact hyErase ⟨(G.ne_of_adj hxy).symm, hy⟩
      exact ⟨hyP, hxy⟩
    · rintro ⟨hyP, hxy⟩
      exact ⟨hxy, by simp, by simp [hyP]⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors]
  unfold missingColumn
  simpa [add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := outsideVertices P) (fun y ↦ G.Adj x y))

/-- Finite candidate roots containing the initial root. -/
noncomputable def candidates (G : SimpleGraph V) (P₀ : Finset V) :
    Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun P ↦ P₀ ⊆ P ∧ G.IsClique (P : Set V)

theorem mem_candidates {G : SimpleGraph V} {P₀ P : Finset V} :
    P ∈ candidates G P₀ ↔ P₀ ⊆ P ∧ G.IsClique (P : Set V) := by
  classical
  simp [candidates]

/-- Energy whose local optimality is exactly the `7p/4` promotion rule. -/
noncomputable def rootEnergy (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : ℕ :=
  8 * (outsideEdges G P).card + 7 * P.card * (P.card - 1)

/-- A root minimizing the promotion energy and, among minimizers, maximizing
cardinality. -/
structure OptimizedRoot (G : SimpleGraph V) [DecidableRel G.Adj]
    (P₀ : Finset V) where
  root : Finset V
  base_subset : P₀ ⊆ root
  isClique : G.IsClique (root : Set V)
  energy_min : ∀ Q : Finset V, P₀ ⊆ Q → G.IsClique (Q : Set V) →
    rootEnergy G root ≤ rootEnergy G Q
  card_max : ∀ Q : Finset V, P₀ ⊆ Q → G.IsClique (Q : Set V) →
    rootEnergy G Q = rootEnergy G root → Q.card ≤ root.card

theorem exists_optimizedRoot {G : SimpleGraph V} [DecidableRel G.Adj]
    (P₀ : Finset V) (hP₀ : G.IsClique (P₀ : Set V)) :
    Nonempty (OptimizedRoot G P₀) := by
  classical
  have hfamily : (candidates G P₀).Nonempty :=
    ⟨P₀, mem_candidates.mpr ⟨Finset.Subset.rfl, hP₀⟩⟩
  obtain ⟨Pmin, hPminMem, hPmin⟩ :=
    Finset.exists_min_image (candidates G P₀) (rootEnergy G) hfamily
  let minimizers := (candidates G P₀).filter fun P ↦
    rootEnergy G P = rootEnergy G Pmin
  have hminimizers : minimizers.Nonempty := by
    refine ⟨Pmin, Finset.mem_filter.mpr ⟨hPminMem, rfl⟩⟩
  obtain ⟨P, hPmem, hPmax⟩ :=
    Finset.exists_max_image minimizers Finset.card hminimizers
  have hPdata := Finset.mem_filter.mp hPmem
  have hPcand := mem_candidates.mp hPdata.1
  refine ⟨⟨P, hPcand.1, hPcand.2, ?_, ?_⟩⟩
  · intro Q hbase hclique
    have hQmem := mem_candidates.mpr ⟨hbase, hclique⟩
    rw [hPdata.2]
    exact hPmin Q hQmem
  · intro Q hbase hclique henergy
    apply hPmax Q
    apply Finset.mem_filter.mpr
    refine ⟨mem_candidates.mpr ⟨hbase, hclique⟩, ?_⟩
    rw [henergy, hPdata.2]

theorem energy_insert_identity {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) {u : V} (hu : u ∉ P) :
    rootEnergy G (insert u P) + 8 * (outsideGraph G P).degree u =
      rootEnergy G P + 14 * P.card := by
  have hcount := outsideEdgeCard_insert_add_degree G P u
  have hsub : P.card + 1 - 1 = P.card := by omega
  unfold rootEnergy
  rw [Finset.card_insert_of_notMem hu, hsub]
  calc
    8 * (outsideEdges G (insert u P)).card + 7 * (P.card + 1) * P.card +
          8 * (outsideGraph G P).degree u =
        8 * ((outsideEdges G (insert u P)).card +
          (outsideGraph G P).degree u) + 7 * (P.card + 1) * P.card := by ring
    _ = 8 * (outsideEdges G P).card + 7 * (P.card + 1) * P.card := by
      rw [hcount]
    _ = 8 * (outsideEdges G P).card + 7 * P.card * (P.card - 1) +
        14 * P.card := by
      have hp : P.card = 0 ∨ 0 < P.card := Nat.eq_zero_or_pos P.card
      rcases hp with hp | hp
      · simp [hp]
      · have hpred : P.card = (P.card - 1) + 1 := by omega
        nth_rewrite 1 [hpred]
        ring

theorem complete_outside_degree_lt {G : SimpleGraph V} [DecidableRel G.Adj]
    {P₀ : Finset V} (R : OptimizedRoot G P₀)
    {u : V} (hu : u ∈ outsideVertices R.root)
    (hcomplete : ∀ x ∈ R.root, G.Adj u x) :
    4 * (outsideGraph G R.root).degree u < 7 * R.root.card := by
  have huRoot : u ∉ R.root := mem_outsideVertices.mp hu
  have hinsertClique : G.IsClique ((insert u R.root : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact R.isClique.insert (fun x hx _ ↦ hcomplete x hx)
  have hmin := R.energy_min (insert u R.root)
    (R.base_subset.trans (Finset.subset_insert u R.root)) hinsertClique
  by_contra hnot
  have hdegree : 7 * R.root.card ≤
      4 * (outsideGraph G R.root).degree u := by omega
  have hidentity := energy_insert_identity (G := G) R.root huRoot
  have hreverse : rootEnergy G (insert u R.root) ≤ rootEnergy G R.root := by
    omega
  have heq : rootEnergy G (insert u R.root) = rootEnergy G R.root := by omega
  have hcard := R.card_max (insert u R.root)
    (R.base_subset.trans (Finset.subset_insert u R.root)) hinsertClique heq
  rw [Finset.card_insert_of_notMem huRoot] at hcard
  omega

theorem new_root_degree_lower {G : SimpleGraph V} [DecidableRel G.Adj]
    {P₀ : Finset V} (R : OptimizedRoot G P₀)
    (hP₀pos : 0 < P₀.card) {x : V}
    (hx : x ∈ R.root) (hxNew : x ∉ P₀) :
    7 * (R.root.card - 1) ≤
      4 * (outsideGraph G (R.root.erase x)).degree x := by
  have hbaseErase : P₀ ⊆ R.root.erase x := by
    intro y hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, R.base_subset hy⟩
    intro hyx
    subst y
    exact hxNew hy
  have hcliqueErase : G.IsClique ((R.root.erase x : Finset V) : Set V) :=
    R.isClique.subset (Finset.erase_subset x R.root)
  have hmin := R.energy_min (R.root.erase x) hbaseErase hcliqueErase
  have hxNotErase : x ∉ R.root.erase x := Finset.notMem_erase x R.root
  have hrecover : insert x (R.root.erase x) = R.root := Finset.insert_erase hx
  have hidentity := energy_insert_identity (G := G) (R.root.erase x) hxNotErase
  rw [hrecover, Finset.card_erase_of_mem hx] at hidentity
  have hrootPos : 0 < R.root.card :=
    lt_of_lt_of_le hP₀pos (Finset.card_le_card R.base_subset)
  omega

/-- Quantitative output of energy-minimizing promotion. -/
structure PromotionBounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (P₀ : Finset V) (D w₀ : ℕ) where
  root : Finset V
  base_subset : P₀ ⊆ root
  isClique : G.IsClique (root : Set V)
  maxMissing_le : maxMissingColumn G root ≤ D
  outsideCliqueNum_le : (outsideGraph G root).cliqueNum ≤ w₀
  promoted_mul_le : 7 * P₀.card * (root.card - P₀.card) ≤
    4 * (outsideEdges G P₀).card
  maxDegree_threshold : 4 * (outsideGraph G root).maxDegree < 7 * root.card

theorem optimizedRoot_bounds {G : SimpleGraph V} [DecidableRel G.Adj]
    (hchordal : IsChordal G) (P₀ : Finset V)
    (hP₀ : G.IsClique (P₀ : Set V)) (hP₀pos : 0 < P₀.card)
    (D w₀ : ℕ)
    (hD₀ : ∀ x ∈ P₀, (missingColumn G P₀ x).card ≤ D)
    (hw₀ : (outsideGraph G P₀).cliqueNum ≤ w₀)
    (hbalance : 4 * (outsideVertices P₀).card ≤ 7 * P₀.card + 4 * D)
    (hseparation : 4 * (D + w₀) < 7 * P₀.card) :
    Nonempty (PromotionBounds G P₀ D w₀) := by
  classical
  obtain ⟨R⟩ := exists_optimizedRoot P₀ hP₀
  let P := R.root
  have hP₀P : P₀ ⊆ P := R.base_subset
  have hPpos : 0 < P.card :=
    lt_of_lt_of_le hP₀pos (Finset.card_le_card hP₀P)
  have houtMono := outsideVertices_mono hP₀P
  have hmissingEach : ∀ x ∈ P, (missingColumn G P x).card ≤ D := by
    intro x hx
    by_cases hxOld : x ∈ P₀
    · exact (Finset.card_le_card (by
        intro y hy
        have hy' := mem_missingColumn.mp hy
        exact mem_missingColumn.mpr ⟨houtMono hy'.1, hy'.2⟩)).trans
          (hD₀ x hxOld)
    · have hdegree := new_root_degree_lower R hP₀pos hx hxOld
      have hpartition := degree_outsideGraph_erase_add_missingColumn G P hx
      have hcardP := Finset.card_le_card hP₀P
      have houtCards₀ := card_outsideVertices P₀
      have houtCards := card_outsideVertices P
      have hstrict : P₀ ⊂ P :=
        (Finset.ssubset_iff_of_subset hP₀P).mpr ⟨x, hx, hxOld⟩
      have hcardStrict : P₀.card < P.card := Finset.card_lt_card hstrict
      have hnew : 1 ≤ P.card - P₀.card := by omega
      have hcardGap : P₀.card + 1 ≤ R.root.card := by
        dsimp only [P] at hnew
        omega
      have htotal₀ : P₀.card + (outsideVertices P₀).card =
          Fintype.card V := by
        have hcardUniv : P₀.card ≤ Fintype.card V := by
          simpa using Finset.card_le_univ P₀
        rw [houtCards₀]
        omega
      have htotal : R.root.card + (outsideVertices R.root).card =
          Fintype.card V := by
        have hcardUniv : R.root.card ≤ Fintype.card V := by
          simpa using Finset.card_le_univ R.root
        dsimp only [P] at houtCards
        rw [houtCards]
        omega
      dsimp only [P] at hpartition
      change (missingColumn G R.root x).card ≤ D
      omega
  have hmaxMissing : maxMissingColumn G P ≤ D := by
    unfold maxMissingColumn
    exact Finset.sup_le fun x hx ↦ hmissingEach x hx
  have hcliqueNum : (outsideGraph G P).cliqueNum ≤ w₀ :=
    (cliqueNum_outsideGraph_mono G hP₀P).trans hw₀
  have hpromoted : 7 * P₀.card * (P.card - P₀.card) ≤
      4 * (outsideEdges G P₀).card := by
    have henergy := R.energy_min P₀ Finset.Subset.rfl hP₀
    have hcard := Finset.card_le_card hP₀P
    let h := P.card - P₀.card
    have hpEq : P.card = P₀.card + h := by dsimp only [h]; omega
    have hpoly : P₀.card * (P₀.card - 1) +
        2 * P₀.card * h ≤ P.card * (P.card - 1) := by
      have hsub : P₀.card + h - 1 = (P₀.card - 1) + h := by omega
      rw [hpEq, hsub]
      by_cases hh : h = 0
      · simp [hh]
      · let k := h - 1
        let a := P₀.card - 1
        have hk : h = k + 1 := by dsimp only [k]; omega
        have ha : P₀.card = a + 1 := by dsimp only [a]; omega
        have hdecomp :
            (P₀.card + h) * (P₀.card - 1 + h) =
              P₀.card * (P₀.card - 1) + 2 * P₀.card * h + h * k := by
          rw [ha, hk]
          simp only [Nat.add_sub_cancel]
          ring
        rw [hdecomp]
        omega
    have hpolyScaled : 7 * (P₀.card * (P₀.card - 1) +
        2 * P₀.card * h) ≤
        7 * (P.card * (P.card - 1)) :=
      Nat.mul_le_mul_left 7 hpoly
    have hpolyBudget :
        7 * (P₀.card * (P₀.card - 1)) + 14 * P₀.card * h ≤
          7 * (P.card * (P.card - 1)) := by
      calc
        7 * (P₀.card * (P₀.card - 1)) + 14 * P₀.card * h =
            7 * (P₀.card * (P₀.card - 1) + 2 * P₀.card * h) := by ring
        _ ≤ 7 * (P.card * (P.card - 1)) := hpolyScaled
    unfold rootEnergy at henergy
    dsimp only [h, P] at hpolyBudget
    have henergy' :
        8 * (outsideEdges G R.root).card +
            7 * (R.root.card * (R.root.card - 1)) ≤
          8 * (outsideEdges G P₀).card +
            7 * (P₀.card * (P₀.card - 1)) := by
      simpa only [Nat.mul_assoc] using henergy
    have htwice :
        14 * (P₀.card * (R.root.card - P₀.card)) ≤
          8 * (outsideEdges G P₀).card := by
      rw [Nat.mul_assoc] at hpolyBudget
      omega
    have hhalf :
        7 * (P₀.card * (R.root.card - P₀.card)) ≤
          4 * (outsideEdges G P₀).card := by
      omega
    simpa only [P, Nat.mul_assoc] using hhalf
  have hdegreeAll : ∀ u : V,
      4 * (outsideGraph G P).degree u < 7 * P.card := by
    intro u
    by_cases huOut : u ∈ outsideVertices P
    · by_cases hcomplete : ∀ x ∈ P, G.Adj u x
      · exact complete_outside_degree_lt R huOut hcomplete
      · push_neg at hcomplete
        obtain ⟨x, hxP, hnotAdj⟩ := hcomplete
        have hux : u ≠ x := by
          intro hux
          subst x
          exact (mem_outsideVertices.mp huOut) hxP
        have hcliqueBound : ∀ K : Finset V, K ⊆ outsideVertices P →
            G.IsClique (K : Set V) → K.card ≤ w₀ := by
          intro K hKout hKclique
          have hKout₀ := hKout.trans houtMono
          have hKoutsideClique : (outsideGraph G P₀).IsClique (K : Set V) := by
            rw [(outsideGraph G P₀).isClique_iff]
            intro a ha b hb hab
            rw [outsideGraph_adj]
            exact ⟨hKclique ha hb hab,
              mem_outsideVertices.mp (hKout₀ ha),
              mem_outsideVertices.mp (hKout₀ hb)⟩
          exact (hKoutsideClique.card_le_cliqueNum).trans hw₀
        have hcolumn := hmissingEach x hxP
        have hbound := root_nonadjacency_degree_bound G hchordal
          (outsideVertices P) w₀ D huOut hux hnotAdj hcliqueBound
          (by simpa [missingColumn] using hcolumn)
        have hdegreeEq : (outsideGraph G P).degree u =
            ((outsideVertices P).filter fun v ↦ G.Adj u v).card := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          congr 1
          ext v
          have huNot : u ∉ P := mem_outsideVertices.mp huOut
          simp [outsideGraph_adj, huNot, mem_outsideVertices,
            and_comm, and_left_comm]
        rw [hdegreeEq]
        have hP₀card := Finset.card_le_card hP₀P
        omega
    · have hisolated : (outsideGraph G P).degree u = 0 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,
          Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hvAdj : (outsideGraph G P).Adj u v := by simpa using hv
        exact huOut (mem_outsideVertices.mpr
          (outsideGraph_adj G P u v |>.mp hvAdj).2.1)
      rw [hisolated]
      omega
  have hmaxDegree : 4 * (outsideGraph G P).maxDegree < 7 * P.card := by
    obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hPpos
    letI : Nonempty V := ⟨u₀⟩
    obtain ⟨u, hu⟩ := (outsideGraph G P).exists_maximal_degree_vertex
    rw [hu]
    exact hdegreeAll u
  exact ⟨⟨P, hP₀P, R.isClique, hmaxMissing, hcliqueNum,
    hpromoted, hmaxDegree⟩⟩

end RootOptimization
end Erdos81
