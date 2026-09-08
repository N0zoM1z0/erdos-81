import Erdos81.RootArithmetic
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

end RootRegularization
end Erdos81
