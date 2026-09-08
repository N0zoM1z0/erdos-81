import Erdos81.FirstEntryGraph
import Erdos81.IntegralFractional
import Erdos81.LocalRegularization
import Erdos81.RootDistance

/-!
# Local potential stability

This module closes the quantitative local implication used by the first-entry
argument.  A chordal graph at normalized split distance below `10^-12` and
within `10^-30 n^2` of the continuous potential envelope is in fact at split
distance below one quarter of that radius.
-/

namespace Erdos81
namespace LocalPotential

open EditDistance RootedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Convert the strict normalized-radius hypothesis to the weak integer edit
bound needed by the structural local-root theorem. -/
theorem scaled_distance_of_normalized_lt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 0 < Fintype.card V)
    (hclose : FirstEntryGraph.normalizedSplitDistance G <
      (1 : ℚ) / 10 ^ 12) :
    10 ^ 12 * splitEditDistance G ≤
      Fintype.card V * Fintype.card V := by
  have hnQ : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  have hn2Q : (0 : ℚ) < (Fintype.card V : ℚ) ^ 2 := sq_pos_of_pos hnQ
  unfold FirstEntryGraph.normalizedSplitDistance at hclose
  have hfraction := (div_lt_iff₀ hn2Q).mp hclose
  have hscaledQ :
      (10 ^ 12 : ℚ) * (splitEditDistance G : ℚ) <
        (Fintype.card V : ℚ) * Fintype.card V := by
    norm_num at hfraction ⊢
    nlinarith
  have hstrictNat :
      (10 ^ 12 * splitEditDistance G : ℕ) <
        Fintype.card V * Fintype.card V := by
    exact_mod_cast hscaledQ
  omega

/-- Quantitative local stability at the manuscript constants. -/
theorem near_extremal_split_contraction
    {G : SimpleGraph V} [DecidableRel G.Adj] {w : ℚ}
    (hv : ExternalInputs.VizingInput)
    (hHJ : ExternalInputs.HaggkvistJanssenInput)
    (hchordal : IsChordal G)
    (hlarge : 10 ^ 32 ≤ Fintype.card V)
    (hOpt : MixedModel.IsPackingOptimum (G := G) w)
    (hnear : Arithmetic.Q (Fintype.card V : ℚ) -
        (Fintype.card V : ℚ) ^ 2 / (10 : ℚ) ^ 30 ≤
      MixedModel.potential G w)
    (hclose : FirstEntryGraph.normalizedSplitDistance G <
      (1 : ℚ) / 10 ^ 12) :
    FirstEntryGraph.normalizedSplitDistance G <
      ((1 : ℚ) / 10 ^ 12) / 4 := by
  let n : ℚ := Fintype.card V
  have hn : 0 < Fintype.card V := by omega
  have hn1000 : 1000 ≤ Fintype.card V := by omega
  have hscale := scaled_distance_of_normalized_lt G hn hclose
  obtain ⟨R, P, horder, hstrict⟩ :=
    LocalRegularization.exists_strict_partition_of_split_close
      hv hHJ hchordal hn1000 hscale
  have hpotential : MixedModel.potential G w ≤ (P.size : ℚ) :=
    IntegralFractional.potential_le_size_of_orderAtMost_three hOpt P horder
  have hfirst :
      (R.root.card : ℚ) * (outsideVertices R.root).card -
          (Nat.choose R.root.card 2 : ℚ) =
        Arithmetic.splitFirstBranch n R.root.card := by
    dsimp only [n]
    exact CompleteSplitPotential.first_expression_eq_splitFirstBranch
      R.root (Nat.le_trans (by norm_num) R.card_ge)
  have hm : 0 ≤ ((outsideEdges G R.root).card : ℚ) := by positivity
  have hA : 0 ≤ (missingIncidences G R.root : ℚ) := by positivity
  have hchain :
      Arithmetic.Q n - n ^ 2 / (10 : ℚ) ^ 30 ≤
        Arithmetic.splitFirstBranch n R.root.card -
          (outsideEdges G R.root).card / 9 -
          missingIncidences G R.root / 2 := by
    calc
      Arithmetic.Q n - n ^ 2 / (10 : ℚ) ^ 30 ≤
          MixedModel.potential G w := by simpa only [n] using hnear
      _ ≤ (P.size : ℚ) := hpotential
      _ ≤ (R.root.card : ℚ) * (outsideVertices R.root).card -
          (Nat.choose R.root.card 2 : ℚ) -
          (outsideEdges G R.root).card / 9 -
          missingIncidences G R.root / 2 := hstrict
      _ = Arithmetic.splitFirstBranch n R.root.card -
          (outsideEdges G R.root).card / 9 -
          missingIncidences G R.root / 2 := by rw [hfirst]
  have hdeficit :
      (6 * (R.root.card : ℚ) - 2 * n - 1) ^ 2 / 24 +
          (outsideEdges G R.root).card / 9 +
          missingIncidences G R.root / 2 ≤
        n ^ 2 / (10 : ℚ) ^ 30 := by
    rw [← Arithmetic.square_identity]
    linarith
  have hdefects :
      ((outsideEdges G R.root).card : ℚ) +
          missingIncidences G R.root ≤
        9 * (n ^ 2 / (10 : ℚ) ^ 30) :=
    LocalStability.defect_sum_le_nine_delta hm hA hdeficit
  have hsquareTerm :
      (6 * (R.root.card : ℚ) - 2 * n - 1) ^ 2 / 24 ≤
        n ^ 2 / (10 : ℚ) ^ 30 := by
    nlinarith
  have hdisplacement :
      ((R.root.card : ℚ) - (2 * n + 1) / 6) ^ 2 ≤
        2 * (n ^ 2 / (10 : ℚ) ^ 30) / 3 :=
    LocalStability.root_displacement_squared hsquareTerm
  have hdistanceNat :=
    RootDistance.splitEditDistance_le_rootDefects_add_roles
      G R.root R.isClique
  have hdistanceQ :
      (splitEditDistance G : ℚ) ≤
        ((outsideEdges G R.root).card : ℚ) +
          missingIncidences G R.root +
          (Nat.dist R.root.card (Fintype.card V / 3) : ℚ) * n := by
    dsimp only [n]
    exact_mod_cast hdistanceNat
  have hroles :=
    LocalRootArithmetic.cast_dist_div_three_le_abs_displacement
      (Fintype.card V) R.root.card
  have hnNonneg : (0 : ℚ) ≤ n := by positivity
  have hroleProduct := mul_le_mul_of_nonneg_right hroles hnNonneg
  have hdistance :
      (splitEditDistance G : ℚ) ≤
        (((outsideEdges G R.root).card : ℚ) +
          missingIncidences G R.root) +
          n * (|(R.root.card : ℚ) - (2 * n + 1) / 6| + 1) := by
    nlinarith
  unfold FirstEntryGraph.normalizedSplitDistance
  apply LocalStability.manuscript_contraction_numerics
    (n := n) (delta := n ^ 2 / (10 : ℚ) ^ 30)
    (defects := ((outsideEdges G R.root).card : ℚ) +
      missingIncidences G R.root)
    (displacement := (R.root.card : ℚ) - (2 * n + 1) / 6)
  · dsimp only [n]
    exact_mod_cast hlarge
  · rfl
  · exact hdefects
  · exact hdisplacement
  · simpa only [n] using hdistance

end LocalPotential
end Erdos81
