import Erdos81.LocalRoot
import Erdos81.LocalRootArithmetic
import Erdos81.RootRegularization
import Erdos81.LocalStability
import Erdos81.CompleteSplitPotential

/-!
# Local strict regularization from split edit distance

This module joins the structural clique-root extraction, its exact numerical
certificate, and the strict root-regularization construction.
-/

namespace Erdos81
namespace LocalRegularization

open EditDistance RootedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- At manuscript scale, every chordal graph within `10^-12 n^2` edits of the
balanced complete-split family admits the strict order-at-most-three rooted
partition produced by `RootRegularization`. -/
theorem exists_strict_partition_of_split_close
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hv : ExternalInputs.VizingInput)
    (hHJ : ExternalInputs.HaggkvistJanssenInput)
    (hchordal : IsChordal G)
    (hn : 1000 ≤ Fintype.card V)
    (hclose : 10 ^ 12 * splitEditDistance G ≤
      Fintype.card V * Fintype.card V) :
    ∃ R : RootRegularization.AdmissibleRoot G,
      ∃ Q : CliquePartition G,
        Q.OrderAtMost 3 ∧
        (Q.size : ℚ) ≤
          (R.root.card : ℚ) * (outsideVertices R.root).card -
            (Nat.choose R.root.card 2 : ℚ) -
            (outsideEdges G R.root).card / 9 -
            missingIncidences G R.root / 2 := by
  obtain ⟨A, P, hAcard, hPA, hPclique, hchoose, hdefect⟩ :=
    LocalRoot.exists_initialRoot G hchordal (by omega)
  have hPcard : P.card ≤ A.card := Finset.card_le_card hPA
  obtain ⟨hp, hlower, hupper, hbudget⟩ :=
    LocalRootArithmetic.initialRoot_numerics hn hAcard hPcard hchoose
      hclose hdefect
  have hlower' : 127 * P.card ≤
      64 * (outsideVertices P).card := by
    rw [card_outsideVertices]
    exact hlower
  have hupper' : 64 * (outsideVertices P).card ≤
      129 * P.card := by
    rw [card_outsideVertices]
    exact hupper
  exact RootRegularization.exists_regularized_strict_partition
    hv hHJ hchordal P hPclique hp hlower' hupper' hbudget

/-- Local sharp upper bound: closeness to the balanced split family already
forces a clique partition no larger than the exact integer target. -/
theorem exists_partition_le_sharpBound_of_split_close
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hv : ExternalInputs.VizingInput)
    (hHJ : ExternalInputs.HaggkvistJanssenInput)
    (hchordal : IsChordal G)
    (hn : 1000 ≤ Fintype.card V)
    (hclose : 10 ^ 12 * splitEditDistance G ≤
      Fintype.card V * Fintype.card V) :
    ∃ Q : CliquePartition G,
      Q.OrderAtMost 3 ∧ Q.size ≤ sharpBound (Fintype.card V) := by
  obtain ⟨R, Q, horder, hstrict⟩ :=
    exists_strict_partition_of_split_close hv hHJ hchordal hn hclose
  have hfirst :
      (R.root.card : ℚ) * (outsideVertices R.root).card -
          (Nat.choose R.root.card 2 : ℚ) =
        Arithmetic.splitFirstBranch (Fintype.card V : ℚ) R.root.card :=
    CompleteSplitPotential.first_expression_eq_splitFirstBranch R.root
      (Nat.le_trans (by norm_num) R.card_ge)
  have hm : 0 ≤ ((outsideEdges G R.root).card : ℚ) := by positivity
  have hA : 0 ≤ (missingIncidences G R.root : ℚ) := by positivity
  have hQ : (Q.size : ℚ) ≤ Arithmetic.Q (Fintype.card V : ℚ) := by
    calc
      (Q.size : ℚ) ≤
          (R.root.card : ℚ) * (outsideVertices R.root).card -
            (Nat.choose R.root.card 2 : ℚ) -
            (outsideEdges G R.root).card / 9 -
            missingIncidences G R.root / 2 := hstrict
      _ ≤ (R.root.card : ℚ) * (outsideVertices R.root).card -
          (Nat.choose R.root.card 2 : ℚ) := by
        nlinarith
      _ = Arithmetic.splitFirstBranch (Fintype.card V : ℚ)
          R.root.card := hfirst
      _ ≤ Arithmetic.Q (Fintype.card V : ℚ) :=
        Arithmetic.splitFirstBranch_le_Q _ _
  exact ⟨Q, horder,
    LocalStability.nat_le_sharpBound_of_le_Q _ _ hQ⟩

end LocalRegularization
end Erdos81
