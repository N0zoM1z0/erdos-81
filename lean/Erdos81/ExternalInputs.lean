import Erdos81.IntegralFractional
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Exact interfaces for the three published inputs

The conditional formalization uses Vizing's edge-colouring theorem, the
Häggkvist--Janssen list-edge-colouring theorem for complete graphs, and the
uniform finite-family packing-transfer theorem.  This file gives those inputs
literal Lean propositions.  It proves none of them and introduces no axiom;
the final conditional theorem will take a value of `ExternalInputs` as an
ordinary explicit hypothesis.

The packing-transfer interface includes witnesses that the fractional value
is attained on both sides of the finite LP.  This records exactly what the
notation `W_4^*(G)` means in the manuscript and prevents strong duality or
attainment from being used silently.
-/

namespace Erdos81
namespace ExternalInputs

open MixedModel IntegralPacking

/-- Two graph edges meet when they have a common endpoint. -/
def EdgesMeet {V : Type*} {G : SimpleGraph V}
    (e f : Resource G) : Prop :=
  ∃ v : V, v ∈ e.val ∧ v ∈ f.val

/-- A proper edge colouring by an arbitrary colour type. -/
structure ProperEdgeColoring {V : Type*} (G : SimpleGraph V)
    (Color : Type*) where
  color : Resource G → Color
  proper : ∀ ⦃e f : Resource G⦄, e ≠ f → EdgesMeet e f →
    color e ≠ color f

/-- Vizing's theorem in its exact `Delta + 1` form. -/
def VizingInput : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Nonempty (ProperEdgeColoring G (Fin (G.maxDegree + 1)))

/-- The Häggkvist--Janssen theorem in the list form used by the terminal
construction.  The colour type need not itself be finite because only the
assigned finite lists matter. -/
def HaggkvistJanssenInput : Prop :=
  ∀ {V Color : Type} [Fintype V] [DecidableEq V] [DecidableEq Color]
    (lists : Resource (⊤ : SimpleGraph V) → Finset Color),
    (∀ e, Fintype.card V ≤ (lists e).card) →
      ∃ coloring : ProperEdgeColoring (⊤ : SimpleGraph V) Color,
        ∀ e, coloring.color e ∈ lists e

/-- A value certified as both the attained mixed primal maximum and attained
dual minimum. -/
structure CertifiedFractionalOptimum {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (w : ℚ) : Prop where
  primal : MixedModel.IsPackingOptimum (G := G) w
  dual : MixedModel.IsCoverOptimum (G := G) w

/-- Uniform weighted finite-family transfer for triangles of gain two and
four-cliques of gain five.

The returned witnesses make all optimization notation explicit.  Uniformity
is expressed by choosing `T` before the order and graph. -/
def PackingTransferInput : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
    ∀ G : SimpleGraph (Fin n), ∃ w : ℚ, ∃ z : ℕ,
      CertifiedFractionalOptimum G w ∧
      IsIntegralOptimum G z ∧
      0 ≤ w - z ∧
      w - z ≤ ε * (n : ℚ) ^ 2

/-- The complete collection of external hypotheses used by the conditional
formalization. -/
structure Inputs : Prop where
  vizing : VizingInput
  haggkvistJanssen : HaggkvistJanssenInput
  packingTransfer : PackingTransferInput

end ExternalInputs
end Erdos81
