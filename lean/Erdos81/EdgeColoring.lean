import Erdos81.ExternalInputs
import Erdos81.LargeClasses
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Finite edge-colouring bookkeeping

This module separates the elementary finite bookkeeping around a proper edge
colouring from the terminal clique-partition construction.  Colour classes
are defined as actual finite sets of graph edges.  They partition the edge
set, and properness says precisely that every class is a matching.
-/

namespace Erdos81
namespace EdgeColoring

open MixedModel ExternalInputs

variable {V Color : Type*} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- The graph edges assigned a specified colour. -/
noncomputable def colorClass {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) (a : Color) :
    Finset (Resource G) := by
  classical
  exact Finset.univ.filter fun e ↦ C.color e = a

omit [DecidableEq V] [Fintype Color] in
@[simp]
theorem mem_colorClass {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) {a : Color} {e : Resource G} :
    e ∈ colorClass C a ↔ C.color e = a := by
  simp [colorClass]

omit [DecidableEq V] in
/-- The colour classes count every graph edge exactly once. -/
theorem sum_card_colorClass {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) :
    ∑ a : Color, (colorClass C a).card = G.edgeFinset.card := by
  classical
  calc
    ∑ a : Color, (colorClass C a).card =
        Fintype.card (Resource G) := by
      rw [← Finset.card_univ]
      simpa [colorClass] using
        (Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Resource G))
          (Finset.univ : Finset Color) C.color)
    _ = G.edgeFinset.card := G.edgeFinset_card.symm

/-- A finite edge family is a matching when distinct edges in the family do
not meet. -/
def IsMatching {G : SimpleGraph V} (S : Finset (Resource G)) : Prop :=
  ∀ ⦃e f : Resource G⦄, e ∈ S → f ∈ S → e ≠ f → ¬ EdgesMeet e f

omit [DecidableEq V] [Fintype Color] in
/-- Every class of a proper edge colouring is a matching. -/
theorem colorClass_isMatching {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) (a : Color) :
    IsMatching (colorClass C a) := by
  intro e f he hf hne hmeet
  exact C.proper hne hmeet ((mem_colorClass C).mp he |>.trans
    ((mem_colorClass C).mp hf |>.symm))

/-- All graph edges whose colours lie in a selected palette. -/
noncomputable def selectedEdges {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) (S : Finset Color) :
    Finset (Resource G) := by
  classical
  exact Finset.univ.filter fun e ↦ C.color e ∈ S

omit [DecidableEq V] [Fintype Color] in
@[simp]
theorem mem_selectedEdges {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) {S : Finset Color} {e : Resource G} :
    e ∈ selectedEdges C S ↔ C.color e ∈ S := by
  simp [selectedEdges]

omit [DecidableEq V] [Fintype Color] in
/-- Selected colour classes are a disjoint decomposition of the selected
edge family. -/
theorem sum_card_colorClass_selected {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) (S : Finset Color) :
    ∑ a ∈ S, (colorClass C a).card = (selectedEdges C S).card := by
  classical
  simpa [colorClass, selectedEdges] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Resource G)) S C.color)

omit [DecidableEq V] in
/-- Some `p` colours carry at least the fraction `p / c` of all edges. -/
theorem exists_large_selected_palette {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) (p : ℕ)
    (hp : p ≤ Fintype.card Color) :
    ∃ S : Finset Color, S.card = p ∧
      p * G.edgeFinset.card ≤
        Fintype.card Color * (selectedEdges C S).card := by
  obtain ⟨S, hScard, hlarge⟩ :=
    LargeClasses.exists_subset_mul_total_le_card_mul_sum
      (fun a ↦ (colorClass C a).card) p hp
  refine ⟨S, hScard, ?_⟩
  rw [sum_card_colorClass C, sum_card_colorClass_selected C S] at hlarge
  exact hlarge

/-- A proper colouring whose classes have a common explicit size bound. -/
structure BoundedColoring (G : SimpleGraph V) (Color : Type*)
    [Fintype Color] [DecidableEq Color] (t : ℕ) where
  toProper : ProperEdgeColoring G Color
  class_card_le : ∀ a, (colorClass toProper a).card ≤ t

/-- Recolour injectively into a larger palette. -/
def mapColors {G : SimpleGraph V} {Color' : Type*}
    (C : ProperEdgeColoring G Color) (f : Color → Color')
    (hf : Function.Injective f) : ProperEdgeColoring G Color' where
  color e := f (C.color e)
  proper _ _ hne hmeet := hf.ne (C.proper hne hmeet)

/-- Vizing's exact `Delta + 1` colouring may be regarded as a colouring by
any larger finite initial segment. -/
theorem exists_coloring_of_vizing {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hv : VizingInput) {c : ℕ}
    (hc : G.maxDegree + 1 ≤ c) :
    Nonempty (ProperEdgeColoring G (Fin c)) := by
  let C := Classical.choice (hv G)
  exact ⟨mapColors C (Fin.castLE hc) (Fin.castLEEmb hc).injective⟩

/-- The natural integer version of `ceil(m/c)`. -/
def classCeiling (m c : ℕ) : ℕ :=
  m ⌈/⌉ c

theorem edge_count_le_colors_mul_ceiling (m c : ℕ) (hc : 0 < c) :
    m ≤ c * classCeiling m c := by
  simpa [classCeiling, Nat.nsmul_eq_mul] using
    (le_smul_ceilDiv (a := c) (b := m) hc)

end EdgeColoring
end Erdos81
