import Erdos81.FiniteLP
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The mixed triangle--K₄ relaxation

This file gives a literal finite LP model for the functional in the
manuscript.  Items are triangles and four-cliques, resources are graph edges,
and their gains are respectively `2` and `5`.
-/

namespace Erdos81
namespace MixedModel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A clique of exactly `r` vertices in `G`. -/
def CliqueOfOrder (G : SimpleGraph V) (r : ℕ) :=
  {K : Finset V // K.card = r ∧ G.IsClique (K : Set V)}

noncomputable instance cliqueOfOrderFintype (G : SimpleGraph V) (r : ℕ) :
    Fintype (CliqueOfOrder G r) := by
  classical
  unfold CliqueOfOrder
  infer_instance

/-- The item type of the mixed packing: triangles or four-cliques. -/
abbrev Item (G : SimpleGraph V) :=
  CliqueOfOrder G 3 ⊕ CliqueOfOrder G 4

/-- The resource type: an edge of `G`. -/
abbrev Resource (G : SimpleGraph V) :=
  G.edgeSet

noncomputable instance resourceFintype (G : SimpleGraph V) : Fintype (Resource G) :=
  by
    classical
    unfold Resource
    infer_instance

/-- The vertex set underlying a mixed-packing item. -/
def vertices {G : SimpleGraph V} : Item G → Finset V
  | Sum.inl T => T.1
  | Sum.inr K => K.1

/-- The gain is `2` for a triangle and `5` for a four-clique. -/
def gain {G : SimpleGraph V} : Item G → ℚ
  | Sum.inl _ => 2
  | Sum.inr _ => 5

/-- Whether a graph edge is used by a mixed-packing item. -/
def Uses {G : SimpleGraph V} (i : Item G) (e : Resource G) : Prop :=
  e.1.toFinset ⊆ vertices i

/-- The `0`--`1` edge/item incidence matrix. -/
noncomputable def incidence {G : SimpleGraph V} (i : Item G) (e : Resource G) : ℚ :=
  by
    classical
    exact if Uses i e then 1 else 0

/-- A feasible fractional mixed triangle--four-clique packing. -/
abbrev FractionalPacking (G : SimpleGraph V) :=
  FiniteLP.PrimalFeasible (incidence (G := G))

/-- A feasible fractional edge cover for the mixed dual. -/
abbrev FractionalCover (G : SimpleGraph V) :=
  FiniteLP.DualFeasible (incidence (G := G)) (gain (G := G))

/-- Value of a feasible mixed fractional packing. -/
noncomputable def packingValue {G : SimpleGraph V} (p : FractionalPacking G) : ℚ :=
  FiniteLP.primalValue (gain (G := G)) p

/-- Value of a feasible mixed fractional cover. -/
noncomputable def coverValue {G : SimpleGraph V} (d : FractionalCover G) : ℚ :=
  FiniteLP.dualValue d

omit [Fintype V] in
theorem incidence_nonnegative {G : SimpleGraph V} (i : Item G) (e : Resource G) :
    0 ≤ incidence i e := by
  classical
  by_cases h : Uses i e <;> simp [incidence, h]

omit [Fintype V] [DecidableEq V] in
theorem vertices_card_three_or_four {G : SimpleGraph V} (i : Item G) :
    (vertices i).card = 3 ∨ (vertices i).card = 4 := by
  cases i with
  | inl T => exact Or.inl T.2.1
  | inr K => exact Or.inr K.2.1

omit [Fintype V] [DecidableEq V] in
theorem item_isClique {G : SimpleGraph V} (i : Item G) :
    G.IsClique (vertices i : Set V) := by
  cases i with
  | inl T => exact T.2.2
  | inr K => exact K.2.2

/-- Weak duality for the precise mixed functional used in the manuscript. -/
theorem weak_duality {G : SimpleGraph V}
    (p : FractionalPacking G) (d : FractionalCover G) :
    packingValue p ≤ coverValue d :=
  FiniteLP.weak_duality p d

/-- A rational `w` is the primal optimum when it is attained and dominates all packings. -/
def IsPackingOptimum {G : SimpleGraph V} (w : ℚ) : Prop :=
  (∃ p : FractionalPacking G, packingValue p = w) ∧
    ∀ p : FractionalPacking G, packingValue p ≤ w

/-- A rational `w` is the dual optimum when it is attained and is below all covers. -/
def IsCoverOptimum {G : SimpleGraph V} (w : ℚ) : Prop :=
  (∃ d : FractionalCover G, coverValue d = w) ∧
    ∀ d : FractionalCover G, w ≤ coverValue d

/-- The potential `Phi(G) = e(G) - W₄*(G)`, relative to a certified optimum. -/
noncomputable def potential (G : SimpleGraph V) [DecidableRel G.Adj] (w : ℚ) : ℚ :=
  G.edgeFinset.card - w

end MixedModel
end Erdos81
