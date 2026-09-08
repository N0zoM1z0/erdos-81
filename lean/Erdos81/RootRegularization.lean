import Erdos81.RootArithmetic
import Erdos81.RootDemotion
import Erdos81.RootOptimization
import Erdos81.StrictTerminalBound
import Mathlib.Tactic

/-!
# From a regularized root to a strict clique partition

This module isolates the final, exact step of root regularization.  Once a
clique root has the strict `7p/4` outside-degree bound, bounded missing
columns, the outside clique-number bound, and enough unused outside hosts,
the two published colouring inputs produce an actual partition into edges and
triangles.  The conclusion is the strict defect-sensitive estimate used in
local stability.

All ceiling arithmetic is over natural numbers.  In particular the chosen
colour count is exactly `ceil(7p/4) = (7p+3)/4`; no real-valued rounding is
hidden in the statement.
-/

namespace Erdos81
namespace RootRegularization

open SimpleGraph MixedModel ExternalInputs EdgeColoring RootedGraph
  RootedPEO TerminalConstruction StrictTerminalBound

attribute [-instance] MixedModel.resourceFintype

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The integer colour count used after root promotion. -/
def regularizedColorCount (p : ℕ) : ℕ :=
  (7 * p + 3) / 4

theorem degree_succ_le_regularizedColorCount {d p : ℕ}
    (hdegree : 4 * d < 7 * p) :
    d + 1 ≤ regularizedColorCount p := by
  unfold regularizedColorCount
  omega

theorem root_le_regularizedColorCount {p : ℕ} :
    p ≤ regularizedColorCount p := by
  unfold regularizedColorCount
  omega

theorem regularizedColorCount_pos {p : ℕ} (hp : 0 < p) :
    0 < regularizedColorCount p := by
  exact lt_of_lt_of_le hp root_le_regularizedColorCount

theorem regularizedColorCount_ratio {p : ℕ} (hp : 15 ≤ p) :
    5 * regularizedColorCount p ≤ 9 * p := by
  exact RootArithmetic.ceil_seven_quarters_le_nine_fifths hp

/-- A root carrying precisely the inequalities needed by the terminal
construction after promotion. -/
structure AdmissibleRoot (G : SimpleGraph V) [DecidableRel G.Adj] where
  root : Finset V
  isClique : G.IsClique (root : Set V)
  card_ge : 15 ≤ root.card
  maxDegree_threshold :
    4 * (outsideGraph G root).maxDegree < 7 * root.card
  outsideClique_ratio :
    4 * ((outsideGraph G root).cliqueNum - 1) ≤ root.card
  host_margin :
    root.card + 2 * maxMissingColumn G root +
        4 * classCeiling
          (Nat.card (Resource (outsideGraph G root)))
          (regularizedColorCount root.card) ≤
      (outsideVertices root).card

/-- An admissible regularized root yields a concrete order-at-most-three
partition satisfying the strict rational bound. -/
theorem exists_strict_partition
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hv : VizingInput) (hHJ : HaggkvistJanssenInput)
    (hchordal : IsChordal G) (R : AdmissibleRoot G) :
    ∃ P : CliquePartition G,
      P.OrderAtMost 3 ∧
      (P.size : ℚ) ≤
        (R.root.card : ℚ) * (outsideVertices R.root).card -
          (Nat.choose R.root.card 2 : ℚ) -
          (outsideEdges G R.root).card / 9 -
          missingIncidences G R.root / 2 := by
  let c := regularizedColorCount R.root.card
  have hp : 0 < R.root.card := lt_of_lt_of_le (by norm_num) R.card_ge
  have hc : 0 < c := regularizedColorCount_pos hp
  have hdegree : (outsideGraph G R.root).maxDegree + 1 ≤ c :=
    degree_succ_le_regularizedColorCount R.maxDegree_threshold
  have hcolors : R.root.card ≤ c := root_le_regularizedColorCount
  obtain ⟨O⟩ := RootedPEO.exists_order R.root hchordal R.isClique
  obtain ⟨C⟩ := exists_certificate hv hHJ R.root R.isClique O hp
    hdegree hcolors R.host_margin
  exact ⟨C.partition, C.orderAtMost,
    certificate_strict_bound R.root c C hp hc
      (regularizedColorCount_ratio R.card_ge) R.outsideClique_ratio⟩

theorem outsideEdgeCard_mono {G : SimpleGraph V} [DecidableRel G.Adj]
    {P Q : Finset V} (hPQ : P ⊆ Q) :
    (outsideEdges G Q).card ≤ (outsideEdges G P).card := by
  rw [← card_outsideGraph_edges, ← card_outsideGraph_edges]
  exact Finset.card_le_card
    (SimpleGraph.edgeFinset_mono (RootOptimization.outsideGraph_mono G hPQ))

/-- A convenient upper estimate for natural ceiling division. -/
theorem classCeiling_le_of_mul_bound {m c s : ℕ} (hc : 0 < c)
    (hms : m ≤ c * s) : classCeiling m c ≤ s := by
  exact (ceilDiv_le_iff_le_mul hc).mpr hms

/-- Quantitative hypotheses, in denominator-cleared form, which turn the
output of optimized promotion into an admissible root.  The reference scale
`p` is the size of the root before demotion; `P₀` is the retained root.

This lemma is deliberately independent of how `P₀`, `D`, and `w₀` were
obtained.  `RootDemotion` supplies them in the application to local
stability. -/
theorem exists_admissibleRoot_of_optimized
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hchordal : IsChordal G) (P₀ : Finset V)
    (hP₀ : G.IsClique (P₀ : Set V)) (p D w₀ : ℕ)
    (hp : 128 ≤ p)
    (hp₀ : 99 * p ≤ 100 * P₀.card)
    (hm₀ : 400 * (outsideEdges G P₀).card < p * p)
    (hD₀ : maxMissingColumn G P₀ ≤ D)
    (hD : 3 * D ≤ p)
    (hw₀ : (outsideGraph G P₀).cliqueNum ≤ w₀)
    (hw : 10 * (w₀ - 1) < p)
    (hbalance : 4 * (outsideVertices P₀).card ≤
      7 * P₀.card + 4 * D)
    (hseparation : 4 * (D + w₀) < 7 * P₀.card)
    (hlowerGap : 63 * p + 64 * P₀.card ≤
      64 * (outsideVertices P₀).card) :
    Nonempty (AdmissibleRoot G) := by
  classical
  have hP₀pos : 0 < P₀.card := by
    have hpPos : 0 < p := by omega
    nlinarith
  have hDcolumns : ∀ x ∈ P₀, (missingColumn G P₀ x).card ≤ D := by
    intro x hx
    exact (card_missingColumn_le_max G P₀ hx).trans hD₀
  obtain ⟨B⟩ := RootOptimization.optimizedRoot_bounds hchordal P₀ hP₀
    hP₀pos D w₀ hDcolumns hw₀ hbalance hseparation
  let P := B.root
  let h := P.card - P₀.card
  have hcard : P₀.card ≤ P.card := Finset.card_le_card B.base_subset
  have hcardEq : P.card = P₀.card + h := by
    dsimp only [h]
    omega
  have hmP : (outsideEdges G P).card ≤ (outsideEdges G P₀).card :=
    outsideEdgeCard_mono B.base_subset
  have hpromotion := B.promoted_mul_le
  have hpTimesH : 693 * p * h < p * p := by
    have hscale := Nat.mul_le_mul_right h hp₀
    dsimp only [h, P] at hpromotion hscale ⊢
    nlinarith
  have hh : 600 * h ≤ p := by
    have hpPos : 0 < p := by omega
    have hcancel : 693 * h < p := by
      apply (Nat.mul_lt_mul_left hpPos).mp
      nlinarith
    omega
  have hcliqueRatio :
      4 * ((outsideGraph G P).cliqueNum - 1) ≤ P.card := by
    have hclique := B.outsideCliqueNum_le
    dsimp only [P] at hclique hcard ⊢
    omega
  let c := regularizedColorCount P.card
  let t := classCeiling
    (Nat.card (Resource (outsideGraph G P))) c
  have hc : 0 < c := by
    apply regularizedColorCount_pos
    exact lt_of_lt_of_le hP₀pos hcard
  have hresource : Nat.card (Resource (outsideGraph G P)) =
      (outsideEdges G P).card := natCard_outside_resources P
  have hp_le_300t : p ≤ 300 * (p / 300 + 1) := by omega
  have hm₀_le_product :
      (outsideEdges G P₀).card ≤ P₀.card * (p / 300 + 1) := by
    have hscaled := Nat.mul_le_mul_right (p / 300 + 1) hp₀
    nlinarith
  have hmP_le_product :
      Nat.card (Resource (outsideGraph G P)) ≤
        c * (p / 300 + 1) := by
    rw [hresource]
    calc
      (outsideEdges G P).card ≤ (outsideEdges G P₀).card := hmP
      _ ≤ P₀.card * (p / 300 + 1) := hm₀_le_product
      _ ≤ P.card * (p / 300 + 1) :=
        Nat.mul_le_mul_right _ hcard
      _ ≤ c * (p / 300 + 1) := by
        exact Nat.mul_le_mul_right _ root_le_regularizedColorCount
  have ht : t ≤ p / 300 + 1 := by
    exact classCeiling_le_of_mul_bound hc hmP_le_product
  have houtsideCard :
      (outsideVertices P).card + h = (outsideVertices P₀).card := by
    have houtP := card_outsideVertices P
    have houtP₀ := card_outsideVertices P₀
    have hPcard : P.card ≤ Fintype.card V := by
      simpa using Finset.card_le_univ P
    have hP₀card : P₀.card ≤ Fintype.card V := by
      simpa using Finset.card_le_univ P₀
    omega
  have hhost : P.card + 2 * maxMissingColumn G P + 4 * t ≤
      (outsideVertices P).card := by
    have hmissing := B.maxMissing_le
    dsimp only [P] at hmissing hcardEq houtsideCard ⊢
    dsimp only [t] at ht ⊢
    omega
  refine ⟨⟨P, B.isClique, ?_, B.maxDegree_threshold,
    hcliqueRatio, ?_⟩⟩
  · have : 15 ≤ P₀.card := by nlinarith
    exact this.trans hcard
  · simpa only [c, t] using hhost

/-- The fixed missing-column bound after simultaneous demotion.  The second
term is the integer version of `q₀ - 7p₀/4`; using floor here can enlarge the
bound by less than one, which is absorbed by the large numerical margins. -/
noncomputable def demotedDefectBound (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : ℕ :=
  max (P.card / 64)
    ((outsideVertices (RootDemotion.retainedRoot G P)).card -
      (7 * (RootDemotion.retainedRoot G P).card) / 4)

/-- Strict root regularization from the manuscript's initial hypotheses,
written with denominators cleared.  The conclusion is an admissible root;
`exists_strict_partition` then performs the actual colouring construction.
-/
theorem exists_admissibleRoot
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hchordal : IsChordal G) (P : Finset V)
    (hP : G.IsClique (P : Set V))
    (hp : 128 ≤ P.card)
    (hbalanceLower : 127 * P.card ≤
      64 * (outsideVertices P).card)
    (hbalanceUpper : 64 * (outsideVertices P).card ≤
      129 * P.card)
    (hdefect : 65536 *
      ((outsideEdges G P).card + missingIncidences G P) ≤
        P.card * P.card) :
    Nonempty (AdmissibleRoot G) := by
  classical
  let P₀ := RootDemotion.retainedRoot G P
  let R := RootDemotion.heavyColumns G P
  let r := R.card
  let D := demotedDefectBound G P
  let w₀ := (outsideGraph G P₀).cliqueNum
  have hparts := RootDemotion.card_retained_add_card_heavy G P
  have hout := RootDemotion.card_outside_retained G P
  have hcharge := RootDemotion.heavy_count_charge G P
  have hA : 65536 * missingIncidences G P ≤ P.card * P.card := by
    nlinarith
  have hr : 1024 * r ≤ P.card := by
    dsimp only [r, R] at hcharge ⊢
    nlinarith
  have hP₀card : 99 * P.card ≤ 100 * P₀.card := by
    dsimp only [P₀, r, R] at hparts hr ⊢
    omega
  have houtsideBound := RootDemotion.outsideEdges_retained_le hP
  have hrSq : 1024 * 1024 * (r * r) ≤ P.card * P.card := by
    have hmul := Nat.mul_le_mul hr hr
    nlinarith
  have hrq : 65536 * (r * (outsideVertices P).card) ≤
      129 * (P.card * P.card) := by
    have hqmul := Nat.mul_le_mul_left (1024 * r) hbalanceUpper
    have hrmul := Nat.mul_le_mul_right (129 * P.card) hr
    nlinarith
  have hm : 65536 * (outsideEdges G P).card ≤ P.card * P.card := by
    nlinarith
  have hchoose : Nat.choose r 2 ≤ r * r := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans
      (Nat.mul_le_mul_left r (Nat.sub_le r 1))
  have hm₀ :
      400 * (outsideEdges G P₀).card < P.card * P.card := by
    nlinarith
  have hD₀ : maxMissingColumn G P₀ ≤ D := by
    have hmissing := RootDemotion.maxMissingColumn_retained_le hP
    dsimp only [P₀, D, demotedDefectBound]
    exact hmissing.trans (Nat.le_max_left _ _)
  have hD : 3 * D ≤ P.card := by
    have hfirst : 3 * (P.card / 64) ≤ P.card := by omega
    have hsecond :
        3 * ((outsideVertices P₀).card - (7 * P₀.card) / 4) ≤
          P.card := by
      dsimp only [P₀, r, R] at hparts hout hr ⊢
      omega
    dsimp only [D, demotedDefectBound, P₀]
    by_cases hmax : P.card / 64 ≤
        (outsideVertices (RootDemotion.retainedRoot G P)).card -
          (7 * (RootDemotion.retainedRoot G P).card) / 4
    · rw [max_eq_right hmax]
      exact hsecond
    · rw [max_eq_left (le_of_not_ge hmax)]
      exact hfirst
  have hcliqueEdges : Nat.choose w₀ 2 ≤ (outsideEdges G P₀).card := by
    obtain ⟨K, hK⟩ := (outsideGraph G P₀).exists_isNClique_cliqueNum
    have hblock :
        (CliquePartitionCounting.blockEdges (outsideGraph G P₀) K).card ≤
          (outsideGraph G P₀).edgeFinset.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [CliquePartitionCounting.card_blockEdges K hK.isClique,
      hK.card_eq, outsideGraph_edgeFinset] at hblock
    exact hblock
  have htwoChoose : 2 * Nat.choose w₀ 2 = w₀ * (w₀ - 1) := by
    rw [Nat.choose_two_right, Nat.mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self w₀)]
  have hw : 10 * (w₀ - 1) < P.card := by
    by_contra hnot
    have hwm : w₀ * (w₀ - 1) ≤
        2 * (outsideEdges G P₀).card := by
      rw [← htwoChoose]
      exact Nat.mul_le_mul_left 2 hcliqueEdges
    have hsquare : (w₀ - 1) * (w₀ - 1) ≤ w₀ * (w₀ - 1) := by
      exact Nat.mul_le_mul_right (w₀ - 1) (Nat.sub_le w₀ 1)
    nlinarith
  have hbalance : 4 * (outsideVertices P₀).card ≤
      7 * P₀.card + 4 * D := by
    dsimp only [D, demotedDefectBound]
    have hmax := Nat.le_max_right (P.card / 64)
      ((outsideVertices (RootDemotion.retainedRoot G P)).card -
        (7 * (RootDemotion.retainedRoot G P).card) / 4)
    dsimp only [P₀] at hmax ⊢
    omega
  have hseparation : 4 * (D + w₀) < 7 * P₀.card := by
    have hP₀pos : 0 < P₀.card := by nlinarith
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hP₀pos
    have hwpos : 1 ≤ w₀ := by
      have hs : (outsideGraph G P₀).IsClique
          (({x} : Finset V) : Set V) := by simp
      have hsingleton := hs.card_le_cliqueNum
      simpa only [Finset.card_singleton, w₀] using hsingleton
    omega
  have hlowerGap : 63 * P.card + 64 * P₀.card ≤
      64 * (outsideVertices P₀).card := by
    dsimp only [P₀, r, R] at hparts hout ⊢
    omega
  exact exists_admissibleRoot_of_optimized hchordal P₀
    (RootDemotion.retainedRoot_isClique hP) P.card D w₀ hp hP₀card hm₀
    hD₀ hD le_rfl hw hbalance hseparation hlowerGap

/-- Complete strict regularization: from an initially balanced low-defect
clique root, construct the partition and prove its defect-sensitive bound at
the automatically selected final root. -/
theorem exists_regularized_strict_partition
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hv : VizingInput) (hHJ : HaggkvistJanssenInput)
    (hchordal : IsChordal G) (P : Finset V)
    (hP : G.IsClique (P : Set V))
    (hp : 128 ≤ P.card)
    (hbalanceLower : 127 * P.card ≤
      64 * (outsideVertices P).card)
    (hbalanceUpper : 64 * (outsideVertices P).card ≤
      129 * P.card)
    (hdefect : 65536 *
      ((outsideEdges G P).card + missingIncidences G P) ≤
        P.card * P.card) :
    ∃ R : AdmissibleRoot G, ∃ Q : CliquePartition G,
      Q.OrderAtMost 3 ∧
      (Q.size : ℚ) ≤
        (R.root.card : ℚ) * (outsideVertices R.root).card -
          (Nat.choose R.root.card 2 : ℚ) -
          (outsideEdges G R.root).card / 9 -
          missingIncidences G R.root / 2 := by
  obtain ⟨R⟩ := exists_admissibleRoot hchordal P hP hp
    hbalanceLower hbalanceUpper hdefect
  obtain ⟨Q, hQorder, hQbound⟩ :=
    exists_strict_partition hv hHJ hchordal R
  exact ⟨R, Q, hQorder, hQbound⟩

end RootRegularization
end Erdos81
