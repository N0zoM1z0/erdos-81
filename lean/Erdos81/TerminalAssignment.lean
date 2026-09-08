import Erdos81.AssignmentAverage
import Erdos81.EdgeColoring
import Erdos81.RootedPEO
import Mathlib.Tactic

/-!
# Assigning selected colour classes to root vertices

For each outside-edge colour and root vertex, the cost is the number of edges
in that class which the vertex cannot host.  The rooted PEO charge and cyclic
assignment averaging combine to give the exact denominator-cleared estimate
used in the terminal construction.
-/

namespace Erdos81
namespace TerminalAssignment

open MixedModel ExternalInputs EdgeColoring RootedGraph RootedPEO

attribute [-instance] MixedModel.resourceFintype

variable {V Color : Type*} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- Number of edges of colour `a` for which `x` is an invalid root host. -/
noncomputable def invalidCost {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (a : Color) (x : V) : ℕ := by
  classical
  exact ((colorClass C a).filter fun e ↦
    x ∈ invalidHostsForResource O e).card

/-- Summing over colours removes the colouring and counts all resources for
which `x` is invalid. -/
theorem sum_invalidCost_colors {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color) (x : V) :
    (∑ a : Color, invalidCost O C a x) =
      ((Finset.univ : Finset (Resource (outsideGraph G P))).filter
        fun e ↦ x ∈ invalidHostsForResource O e).card := by
  classical
  let E := (Finset.univ : Finset (Resource (outsideGraph G P))).filter
    fun e ↦ x ∈ invalidHostsForResource O e
  have hMaps : (E : Set (Resource (outsideGraph G P))).MapsTo C.color
      (Finset.univ : Finset Color) := by simp
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  apply Finset.sum_congr rfl
  intro a _ha
  apply congrArg Finset.card
  apply Finset.ext
  intro e
  simp [E, colorClass, and_comm]

/-- Double-counting invalid `(edge, root)` pairs. -/
theorem sum_invalidCost_all_pairs {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color) :
    (∑ a : Color, ∑ x ∈ P, invalidCost O C a x) =
      invalidHostIncidences O := by
  classical
  rw [Finset.sum_comm]
  simp_rw [sum_invalidCost_colors O C]
  calc
    ∑ x ∈ P,
        ((Finset.univ : Finset (Resource (outsideGraph G P))).filter
          fun e ↦ x ∈ invalidHostsForResource O e).card =
        ∑ e : Resource (outsideGraph G P),
          (invalidHostsForResource O e).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      have hsub : invalidHostsForResource O e ⊆ P := by
        intro x hx
        exact (mem_invalidHosts.mp hx).1
      have hfilter : P.filter (fun x ↦ x ∈ invalidHostsForResource O e) =
          invalidHostsForResource O e := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨hsub h, h⟩⟩
      rw [← Finset.sum_filter, hfilter]
    _ = invalidHostIncidences O := sum_card_invalidHostsForResource O

/-- A selected palette of size `p=|P|` can be assigned bijectively to the
root with total invalid cost at most `(omega(H)-1)A/p`. -/
theorem exists_assignment_with_charge {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (p : ℕ) (hS : S.card = p)
    (hP : P.card = p) (hp : 0 < p) :
    ∃ assign : ↑S ≃ ↑P,
      p * (∑ a : ↑S, invalidCost O C a (assign a)) ≤
        ((outsideGraph G P).cliqueNum - 1) * missingIncidences G P := by
  obtain ⟨assign, hassign⟩ :=
    AssignmentAverage.exists_equiv_with_small_cost S P p hS hP hp
      (invalidCost O C)
  refine ⟨assign, hassign.trans ?_⟩
  calc
    ∑ a ∈ S, ∑ x ∈ P, invalidCost O C a x
        ≤ ∑ a : Color, ∑ x ∈ P, invalidCost O C a x := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = invalidHostIncidences O := sum_invalidCost_all_pairs O C
    _ ≤ ((outsideGraph G P).cliqueNum - 1) *
        missingIncidences G P := invalidHostIncidences_le O

/-- The colour of a selected edge, regarded as an element of the selected
palette. -/
def assignedColor {G : SimpleGraph V} {P : Finset V}
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (e : ↑(selectedEdges C S)) : ↑S :=
  ⟨C.color e.1, (mem_selectedEdges C).mp e.2⟩

/-- Root host assigned to a selected outside edge. -/
def assignedHost {G : SimpleGraph V} {P : Finset V}
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (e : ↑(selectedEdges C S)) : V :=
  assign (assignedColor C S e)

/-- Selected outside edges rejected by their assigned root host. -/
noncomputable def invalidAssignedEdges {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P) :
    Finset ↑(selectedEdges C S) := by
  classical
  exact Finset.univ.filter fun e ↦
    assignedHost C S assign e ∈ invalidHostsForResource O e.1

/-- Selected outside edges accepted by their assigned root host. -/
noncomputable def retainedAssignedEdges {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P) :
    Finset ↑(selectedEdges C S) := by
  classical
  exact Finset.univ.filter fun e ↦
    assignedHost C S assign e ∉ invalidHostsForResource O e.1

/-- The rejected-edge count is the diagonal assignment cost. -/
theorem card_invalidAssignedEdges {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P) :
    (invalidAssignedEdges O C S assign).card =
      ∑ a : ↑S, invalidCost O C a (assign a) := by
  classical
  let I := invalidAssignedEdges O C S assign
  have hMaps : (I : Set ↑(selectedEdges C S)).MapsTo
      (assignedColor C S) (Finset.univ : Finset ↑S) := by simp
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  apply Finset.sum_congr rfl
  intro a _ha
  let liftEdge : ∀ (a : ↑S) (e : Resource (outsideGraph G P)),
      e ∈ colorClass C a → ↑(selectedEdges C S) :=
    fun a e he ↦ ⟨e, (mem_selectedEdges (S := S) C).mpr (by
      have hcolor : C.color e = (a : Color) := (mem_colorClass C).mp he
      exact hcolor ▸ a.property)⟩
  symm
  apply Finset.card_bij
    (fun e he ↦ liftEdge a e (Finset.mem_filter.mp he).1)
  · intro e he
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    constructor
    · change liftEdge a e he'.1 ∈ I
      rw [show I = invalidAssignedEdges O C S assign from rfl]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hcolor : assignedColor C S (liftEdge a e he'.1) = a := by
        apply Subtype.ext
        simp [assignedColor, liftEdge, (mem_colorClass C).mp he'.1]
      rw [assignedHost, hcolor]
      exact he'.2
    · apply Subtype.ext
      simp [assignedColor, liftEdge, (mem_colorClass C).mp he'.1]
  · intro e₁ he₁ e₂ he₂ heq
    exact congrArg (fun z : ↑(selectedEdges C S) ↦ z.1) heq
  · intro e he
    have he' := Finset.mem_filter.mp he
    have heI : e ∈ I := he'.1
    have hfiber : assignedColor C S e = a := he'.2
    refine ⟨e.1, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply (mem_colorClass C).mpr
        exact congrArg Subtype.val hfiber
      · have hinvalid : assignedHost C S assign e ∈
            invalidHostsForResource O e.1 := by
          simpa [I, invalidAssignedEdges] using
            (Finset.mem_filter.mp heI).2
        have hhost : assignedHost C S assign e = (assign a : V) := by
          exact congrArg Subtype.val (congrArg assign hfiber)
        rwa [hhost] at hinvalid
    · rfl

/-- Accepted and rejected selected edges form an exact partition. -/
theorem card_retained_add_invalid {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P) :
    (retainedAssignedEdges O C S assign).card +
      (invalidAssignedEdges O C S assign).card =
        (selectedEdges C S).card := by
  classical
  have hdisjoint : Disjoint
      (retainedAssignedEdges O C S assign)
      (invalidAssignedEdges O C S assign) := by
    rw [Finset.disjoint_left]
    simp [retainedAssignedEdges, invalidAssignedEdges]
  have hunion :
      retainedAssignedEdges O C S assign ∪
        invalidAssignedEdges O C S assign = Finset.univ := by
    ext e
    by_cases h : assignedHost C S assign e ∈ invalidHostsForResource O e.1
    · simp [retainedAssignedEdges, invalidAssignedEdges, h]
    · simp [retainedAssignedEdges, invalidAssignedEdges, h]
  calc
    (retainedAssignedEdges O C S assign).card +
        (invalidAssignedEdges O C S assign).card =
      (retainedAssignedEdges O C S assign ∪
        invalidAssignedEdges O C S assign).card :=
      (Finset.card_union_of_disjoint hdisjoint).symm
    _ = (Finset.univ : Finset ↑(selectedEdges C S)).card := by rw [hunion]
    _ = (selectedEdges C S).card := Fintype.card_coe _

/-- Combined selected-mass and invalid-charge estimate for the number `f` of
retained outside edges. -/
theorem retained_count_lower_cleared {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V}
    (O : RootedPEO.Order G P)
    (C : ProperEdgeColoring (outsideGraph G P) Color)
    (S : Finset Color) (assign : ↑S ≃ ↑P)
    (p c m : ℕ) (hP : P.card = p)
    (hselected : p * m ≤
      c * (selectedEdges C S).card)
    (hcharge : p * (∑ a : ↑S, invalidCost O C a (assign a)) ≤
      ((outsideGraph G P).cliqueNum - 1) * missingIncidences G P) :
    p * p * m ≤
      c * p * (retainedAssignedEdges O C S assign).card +
        c * (((outsideGraph G P).cliqueNum - 1) *
          missingIncidences G P) := by
  have hpartition := card_retained_add_invalid O C S assign
  have hinvalid := card_invalidAssignedEdges O C S assign
  rw [← hinvalid] at hcharge
  calc
    p * p * m
        ≤ p * (c * (selectedEdges C S).card) := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left p hselected
    _ = c * p * ((retainedAssignedEdges O C S assign).card +
        (invalidAssignedEdges O C S assign).card) := by
      rw [hpartition]
      ring
    _ = c * p * (retainedAssignedEdges O C S assign).card +
        c * (p * (invalidAssignedEdges O C S assign).card) := by ring
    _ ≤ c * p * (retainedAssignedEdges O C S assign).card +
        c * (((outsideGraph G P).cliqueNum - 1) *
          missingIncidences G P) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left c hcharge) _

end TerminalAssignment
end Erdos81
