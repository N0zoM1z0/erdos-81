import Erdos81.GlobalStability
import Erdos81.IntegralPacking
import Erdos81.LocalRegularization
import Erdos81.SharpBound

/-!
# End-to-end conditional theorem

This file assembles the near and far cases.  The theorem takes exactly the
three published inputs exposed in `ExternalInputs.Inputs`; every other step is
proved in this project.  In the near case, global stability enters the local
regularization neighbourhood.  In the far case, the transfer gap and the
integral packing identity give a strict bound below the integer target.
-/

namespace Erdos81

open MixedModel Symmetrization

/-- The manuscript's eventual sharp upper bound follows from its three
explicit published inputs. -/
theorem eventualSharpUpperBound_of_inputs
    (inputs : ExternalInputs.Inputs) : EventualSharpUpperBound := by
  classical
  obtain ⟨T, htransfer⟩ := inputs.packingTransfer
    (((1 : ℚ) / 10 ^ 30) / 2) (by norm_num)
  refine ⟨max T (10 ^ 32), ?_⟩
  intro n hn G hchordal
  have hTn : T ≤ n := (Nat.le_max_left T (10 ^ 32)).trans hn
  have hlarge : 10 ^ 32 ≤ n := (Nat.le_max_right T (10 ^ 32)).trans hn
  have hlargeFin : 10 ^ 32 ≤ Fintype.card (Fin n) := by
    simpa using hlarge
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hfamily := htransfer n hTn
  let value : SimpleGraph (Fin n) → ℚ := fun H ↦
    Classical.choose (hfamily H)
  let integralValue : SimpleGraph (Fin n) → ℕ := fun H ↦
    Classical.choose (Classical.choose_spec (hfamily H))
  have hdata : ∀ H : SimpleGraph (Fin n),
      ExternalInputs.CertifiedFractionalOptimum H (value H) ∧
      IntegralPacking.IsIntegralOptimum H (integralValue H) ∧
      0 ≤ value H - integralValue H ∧
      value H - integralValue H ≤
        (((1 : ℚ) / 10 ^ 30) / 2) * (n : ℚ) ^ 2 := by
    intro H
    dsimp only [value, integralValue]
    exact Classical.choose_spec (Classical.choose_spec (hfamily H))
  let w : ℚ := value G
  let z : ℕ := integralValue G
  have hcert : ∀ H : SimpleGraph (Fin n),
      ExternalInputs.CertifiedFractionalOptimum H (value H) :=
    fun H ↦ (hdata H).1
  have hGdata := hdata G
  by_cases hnear :
      (n : ℚ) ^ 2 / 6 - (n : ℚ) ^ 2 / (10 : ℚ) ^ 30 ≤
        potential G w
  · have hnearCertified :
        (n : ℚ) ^ 2 / 6 - (n : ℚ) ^ 2 / (10 : ℚ) ^ 30 ≤
          certifiedPotential value G := by
      rw [Symmetrization.certifiedPotential_eq_potential]
      simpa only [w] using hnear
    have hclose := GlobalStability.near_extremal_implies_close
      value hcert inputs.vizing inputs.haggkvistJanssen
      hchordal hlargeFin (by simpa using hnearCertified)
    have hinside : FirstEntryGraph.normalizedSplitDistance G <
        (1 : ℚ) / 10 ^ 12 := hclose.trans (by norm_num)
    have hscale := LocalPotential.scaled_distance_of_normalized_lt
      G (by simpa using (show 0 < n by omega)) hinside
    obtain ⟨P, horder, hsize⟩ :=
      LocalRegularization.exists_partition_le_sharpBound_of_split_close
        inputs.vizing inputs.haggkvistJanssen hchordal
          (by simpa using (show 1000 ≤ n by omega)) hscale
    exact ⟨P, (fun K hK ↦ (horder K hK).trans (by omega)),
      by simpa using hsize⟩
  · have hfar : potential G w <
        (n : ℚ) ^ 2 / 6 - ((1 : ℚ) / 10 ^ 30) * (n : ℚ) ^ 2 := by
      push Not at hnear
      nlinarith
    have hInt : IntegralPacking.IsIntegralOptimum G z := by
      simpa only [z] using hGdata.2.1
    obtain ⟨p, hpGain⟩ := hInt.1
    let P : CliquePartition G := IntegralPacking.toCliquePartition p
    have hzle : z ≤ G.edgeFinset.card := by
      rw [← hpGain]
      exact IntegralPacking.gain_le_card_edges p
    have hPsize : P.size = G.edgeFinset.card - z := by
      dsimp only [P]
      rw [IntegralPacking.size_toCliquePartition, hpGain]
      rfl
    have hdecomp : (P.size : ℚ) =
        potential G w + (w - (z : ℚ)) := by
      rw [hPsize, Nat.cast_sub hzle]
      unfold potential
      ring
    have hgap : w - (z : ℚ) ≤
        (((1 : ℚ) / 10 ^ 30) / 2) * (n : ℚ) ^ 2 := by
      simpa only [w, z] using hGdata.2.2.2
    have htarget : (n : ℚ) ^ 2 / 6 ≤ (sharpBound n : ℚ) :=
      SharpBound.sq_div_six_le_sharpBound (by omega)
    have hstrict := Arithmetic.far_case_closure
      (n := (n : ℚ)) (eta := (1 : ℚ) / 10 ^ 30)
      (potential := potential G w) (integralityGap := w - (z : ℚ))
      (cliquePartition := (P.size : ℚ))
      (target := (sharpBound n : ℚ))
      (by positivity) (by positivity) hdecomp hfar hgap htarget
    have hstrictNat : P.size < sharpBound n := by exact_mod_cast hstrict
    exact ⟨P, IntegralPacking.orderAtMost_toCliquePartition p, hstrictNat.le⟩

/-- Conditional kernel-level resolution of Erdős Problem 81. -/
theorem erdos81_of_inputs (inputs : ExternalInputs.Inputs) :
    Erdos81Statement :=
  eventualSharpUpperBound_implies_erdos81
    (eventualSharpUpperBound_of_inputs inputs)

end Erdos81
