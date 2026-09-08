import Erdos81.EdgeColoring
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic

/-!
# Equitable refinement of a proper edge colouring

The union of two colour classes of a proper edge colouring has connected
components that are alternating paths or even cycles.  We use an equivalent
counting proof of the only fact needed below: in each connected component the
two class sizes differ by at most one.  Indeed, either class is a matching,
so it has at most half as many edges as the component has vertices, while a
connected component has at least `|V|-1` edges.
-/

namespace Erdos81
namespace EquitableEdgeColoring

open MixedModel ExternalInputs EdgeColoring

variable {V Color : Type*} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- The endpoints of distinct edges in one colour class are disjoint. -/
theorem colorClass_endpoint_pairwiseDisjoint {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) (a : Color) :
    ((colorClass C a : Finset (Resource G)) : Set (Resource G)).PairwiseDisjoint
      fun e ↦ e.1.toFinset := by
  classical
  intro e he f hf hef
  change Disjoint e.1.toFinset f.1.toFinset
  rw [Finset.disjoint_left]
  intro v hve hvf
  exact colorClass_isMatching C a he hf hef
    ⟨v, Sym2.mem_toFinset.mp hve, Sym2.mem_toFinset.mp hvf⟩

/-- A colour class, being a matching, uses twice as many distinct endpoints
as it has edges. -/
theorem two_mul_card_colorClass_le_vertices {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) (a : Color) :
    2 * (colorClass C a).card ≤ Fintype.card V := by
  classical
  let endpoints : Finset V :=
    (colorClass C a).biUnion fun e ↦ e.1.toFinset
  have hedgeCard (e : Resource G) : e.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e.1
      (G.not_isDiag_of_mem_edgeSet e.2)
  have hendpoints : endpoints.card = 2 * (colorClass C a).card := by
    rw [show endpoints = (colorClass C a).biUnion
      (fun e ↦ e.1.toFinset) from rfl,
      Finset.card_biUnion (colorClass_endpoint_pairwiseDisjoint C a)]
    simp_rw [hedgeCard]
    simp [Nat.mul_comm]
  calc
    2 * (colorClass C a).card = endpoints.card := hendpoints.symm
    _ ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ endpoints)
    _ = Fintype.card V := Finset.card_univ

/-- In a connected graph properly edge-coloured with two colours, colour
zero has at most one edge more than colour one. -/
theorem card_colorClass_zero_le_one_add_one
    {G : SimpleGraph V} (hconnected : G.Connected)
    (C : ProperEdgeColoring G (Fin 2)) :
    (colorClass C 0).card ≤ (colorClass C 1).card + 1 := by
  have hmatching := two_mul_card_colorClass_le_vertices C (0 : Fin 2)
  have hmatching' : 2 * (colorClass C 0).card ≤ Nat.card V := by
    simpa [Nat.card_eq_fintype_card] using hmatching
  have hconnectedEdges := hconnected.card_vert_le_card_edgeSet_add_one
  have hsum := sum_card_colorClass C
  have hsum' : (colorClass C 0).card + (colorClass C 1).card =
      Nat.card (Resource G) := by
    simpa [Fin.sum_univ_two] using hsum
  change Nat.card V ≤ Nat.card (Resource G) + 1 at hconnectedEdges
  omega

/-- The symmetric bound for colour one. -/
theorem card_colorClass_one_le_zero_add_one
    {G : SimpleGraph V} (hconnected : G.Connected)
    (C : ProperEdgeColoring G (Fin 2)) :
    (colorClass C 1).card ≤ (colorClass C 0).card + 1 := by
  have hmatching := two_mul_card_colorClass_le_vertices C (1 : Fin 2)
  have hmatching' : 2 * (colorClass C 1).card ≤ Nat.card V := by
    simpa [Nat.card_eq_fintype_card] using hmatching
  have hconnectedEdges := hconnected.card_vert_le_card_edgeSet_add_one
  have hsum := sum_card_colorClass C
  have hsum' : (colorClass C 0).card + (colorClass C 1).card =
      Nat.card (Resource G) := by
    simpa [Fin.sum_univ_two] using hsum
  change Nat.card V ≤ Nat.card (Resource G) + 1 at hconnectedEdges
  omega

section TwoColors

variable {G : SimpleGraph V}

/-- The spanning graph consisting of two colour classes. -/
def twoColorGraph (C : ProperEdgeColoring G Color) (a b : Color) :
    SimpleGraph V where
  Adj u v := ∃ e : Resource G,
    e.1 = s(u, v) ∧ (C.color e = a ∨ C.color e = b)
  symm.symm := by
    rintro u v ⟨e, he, hcolor⟩
    exact ⟨e, he.trans Sym2.eq_swap, hcolor⟩
  loopless.irrefl := by
    rintro u ⟨e, he, _hcolor⟩
    have huu : G.Adj u u := G.mem_edgeSet.mp (he ▸ e.2)
    exact G.loopless.irrefl u huu

noncomputable instance twoColorGraphDecidableAdj
    (C : ProperEdgeColoring G Color) (a b : Color) :
    DecidableRel (twoColorGraph C a b).Adj :=
  fun _ _ ↦ Classical.propDecidable _

/-- We use the first representative selected by `Sym2.out` only to name the
connected component containing an edge. -/
noncomputable def edgeAnchor (e : Resource G) : V := e.1.out.1

theorem edgeAnchor_mem (e : Resource G) : edgeAnchor e ∈ e.1 := by
  exact Sym2.out_fst_mem e.1

/-- Edges of colour `x` whose anchor lies in a specified two-colour
component. -/
noncomputable def componentClass
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent) (x : Color) :
    Finset (Resource G) := by
  classical
  exact (colorClass C x).filter fun e ↦
    (twoColorGraph C a b).connectedComponentMk (edgeAnchor e) = c

@[simp]
theorem mem_componentClass
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent) (x : Color)
    (e : Resource G) :
    e ∈ componentClass C a b c x ↔
      C.color e = x ∧
        (twoColorGraph C a b).connectedComponentMk (edgeAnchor e) = c := by
  classical
  simp [componentClass]

/-- Splitting a colour class over the connected components preserves its
total size. -/
theorem sum_card_componentClass
    (C : ProperEdgeColoring G Color) (a b x : Color) :
    ∑ c : (twoColorGraph C a b).ConnectedComponent,
      (componentClass C a b c x).card = (colorClass C x).card := by
  classical
  simpa [componentClass] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (colorClass C x)
      (Finset.univ : Finset (twoColorGraph C a b).ConnectedComponent)
      (fun e ↦ (twoColorGraph C a b).connectedComponentMk (edgeAnchor e)))

/-- If the first global colour class is larger, it is larger on at least one
two-colour connected component. -/
theorem exists_component_card_lt
    (C : ProperEdgeColoring G Color) {a b : Color}
    (hlarge : (colorClass C b).card < (colorClass C a).card) :
    ∃ c : (twoColorGraph C a b).ConnectedComponent,
      (componentClass C a b c b).card <
        (componentClass C a b c a).card := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum :
      (∑ c : (twoColorGraph C a b).ConnectedComponent,
        (componentClass C a b c a).card) ≤
      ∑ c : (twoColorGraph C a b).ConnectedComponent,
        (componentClass C a b c b).card := by
    exact Finset.sum_le_sum fun c _ ↦ hnone c
  rw [sum_card_componentClass, sum_card_componentClass] at hsum
  omega

/-- Embed an edge of a two-colour component back into the original graph. -/
noncomputable def liftComponentResource
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent)
    (e : Resource c.toSimpleGraph) : Resource G := by
  classical
  refine ⟨Sym2.map Subtype.val e.1, ?_⟩
  rcases e with ⟨z, hz⟩
  revert hz
  refine Sym2.inductionOn z ?_
  intro u v huv
  change G.Adj u.1 v.1
  change (twoColorGraph C a b).Adj u.1 v.1 at huv
  obtain ⟨f, hf, _hcolor⟩ := huv
  exact G.mem_edgeSet.mp (hf ▸ f.2)

@[simp]
theorem liftComponentResource_val
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent)
    (e : Resource c.toSimpleGraph) :
    (liftComponentResource C a b c e).1 =
      Sym2.map Subtype.val e.1 := rfl

theorem liftComponentResource_injective
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    Function.Injective (liftComponentResource C a b c) := by
  intro e f hef
  apply Subtype.ext
  apply (Function.Embedding.subtype (fun v : V ↦ v ∈ c.supp)).sym2Map.injective
  exact congrArg Subtype.val hef

theorem color_of_mem_twoColorGraph
    (C : ProperEdgeColoring G Color) (a b : Color)
    (e : Resource G) (he : e.1 ∈ (twoColorGraph C a b).edgeSet) :
    C.color e = a ∨ C.color e = b := by
  rcases e with ⟨z, hz⟩
  revert hz he
  refine Sym2.inductionOn z ?_
  intro u v hz he
  change (twoColorGraph C a b).Adj u v at he
  obtain ⟨f, hf, hcolor⟩ := he
  have hfe : f = (⟨s(u, v), hz⟩ : Resource G) := by
    apply Subtype.ext
    exact hf
  simpa [hfe] using hcolor

theorem liftComponentResource_mem_twoColorGraph
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent)
    (e : Resource c.toSimpleGraph) :
    (liftComponentResource C a b c e).1 ∈
      (twoColorGraph C a b).edgeSet := by
  rcases e with ⟨z, hz⟩
  revert hz
  refine Sym2.inductionOn z ?_
  intro u v huv
  change (twoColorGraph C a b).Adj u.1 v.1
  exact huv

theorem liftComponentResource_color
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent)
    (e : Resource c.toSimpleGraph) :
    C.color (liftComponentResource C a b c e) = a ∨
      C.color (liftComponentResource C a b c e) = b :=
  color_of_mem_twoColorGraph C a b _
    (liftComponentResource_mem_twoColorGraph C a b c e)

/-- Encode the two selected colours by `Fin 2`. -/
def twoColorCode (a : Color) (x : Color) : Fin 2 :=
  if x = a then 0 else 1

theorem twoColorCode_injective_on_pair {a b x y : Color} (hab : a ≠ b)
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b)
    (hcode : twoColorCode a x = twoColorCode a y) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · simp [twoColorCode, hab, hab.symm] at hcode
  · simp [twoColorCode, hab, hab.symm] at hcode
  · rfl

/-- The restriction of the original colouring to one two-colour component,
encoded by `Fin 2`. -/
noncomputable def componentColoring
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    ProperEdgeColoring c.toSimpleGraph (Fin 2) where
  color e := twoColorCode a (C.color (liftComponentResource C a b c e))
  proper := by
    intro e f hef hmeet hsame
    apply C.proper
      (fun hlift ↦ hef (liftComponentResource_injective C a b c hlift))
      ?_ ?_
    · obtain ⟨v, hve, hvf⟩ := hmeet
      exact ⟨v.1,
        Sym2.mem_map.mpr ⟨v, hve, rfl⟩,
        Sym2.mem_map.mpr ⟨v, hvf, rfl⟩⟩
    · exact twoColorCode_injective_on_pair hab
        (liftComponentResource_color C a b c e)
        (liftComponentResource_color C a b c f) hsame

/-- Every endpoint of a two-coloured edge belongs to the component named by
its anchor. -/
theorem endpoint_mem_component_of_anchor
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent)
    (e : Resource G) (hcolor : C.color e = a ∨ C.color e = b)
    (hcomponent : (twoColorGraph C a b).connectedComponentMk
      (edgeAnchor e) = c) :
    ∀ v ∈ e.1, v ∈ c.supp := by
  intro v hv
  have hadj : (twoColorGraph C a b).Adj e.1.out.1 e.1.out.2 :=
    ⟨e, e.1.out_eq.symm, hcolor⟩
  rw [← e.1.out_eq, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact hcomponent
  · change (twoColorGraph C a b).connectedComponentMk e.1.out.2 = c
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj.symm).trans hcomponent

/-- Restrict a two-coloured original edge to its named connected component. -/
noncomputable def restrictComponentResource
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent)
    (e : Resource G) (hcolor : C.color e = a ∨ C.color e = b)
    (hcomponent : (twoColorGraph C a b).connectedComponentMk
      (edgeAnchor e) = c) : Resource c.toSimpleGraph := by
  classical
  let hu : e.1.out.1 ∈ c.supp :=
    endpoint_mem_component_of_anchor C a b c e hcolor hcomponent
      e.1.out.1 (Sym2.out_fst_mem e.1)
  let hv : e.1.out.2 ∈ c.supp :=
    endpoint_mem_component_of_anchor C a b c e hcolor hcomponent
      e.1.out.2 (Sym2.out_snd_mem e.1)
  refine ⟨s((⟨e.1.out.1, hu⟩ : c), (⟨e.1.out.2, hv⟩ : c)), ?_⟩
  change (twoColorGraph C a b).Adj e.1.out.1 e.1.out.2
  exact ⟨e, e.1.out_eq.symm, hcolor⟩

@[simp]
theorem lift_restrictComponentResource
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent)
    (e : Resource G) (hcolor : C.color e = a ∨ C.color e = b)
    (hcomponent : (twoColorGraph C a b).connectedComponentMk
      (edgeAnchor e) = c) :
    liftComponentResource C a b c
      (restrictComponentResource C a b c e hcolor hcomponent) = e := by
  apply Subtype.ext
  exact e.1.out_eq

/-- The local zero class is exactly the original `a`-class in this
component. -/
theorem card_componentClass_left
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) [Fintype c] :
    (componentClass C a b c a).card =
      (colorClass (componentColoring C hab c) 0).card := by
  classical
  apply Finset.card_bij
    (fun e he ↦ restrictComponentResource C a b c e
      (Or.inl ((mem_componentClass C a b c a e).mp he).1)
      ((mem_componentClass C a b c a e).mp he).2)
  · intro e he
    apply (mem_colorClass (componentColoring C hab c)).mpr
    simp [componentColoring, twoColorCode,
      lift_restrictComponentResource]
    exact ((mem_componentClass C a b c a e).mp he).1
  · intro e he f hf hef
    apply Subtype.ext
    have hlift := congrArg (liftComponentResource C a b c) hef
    have hef' : e = f := by simpa using hlift
    exact congrArg Subtype.val hef'
  · intro f hf
    have hcode := (mem_colorClass (componentColoring C hab c)).mp hf
    have hfcolor : C.color (liftComponentResource C a b c f) = a := by
      simpa [componentColoring, twoColorCode] using hcode
    let e := liftComponentResource C a b c f
    have heAnchor : edgeAnchor e ∈ c.supp := by
      have hmem : edgeAnchor e ∈
          Sym2.map Subtype.val f.1 := by
        rw [← liftComponentResource_val C a b c f]
        exact edgeAnchor_mem e
      obtain ⟨v, hv, hval⟩ := Sym2.mem_map.mp hmem
      exact hval ▸ v.2
    have heComponent : (twoColorGraph C a b).connectedComponentMk
        (edgeAnchor e) = c := heAnchor
    refine ⟨e, ?_, ?_⟩
    · exact (mem_componentClass C a b c a e).mpr
        ⟨hfcolor, heComponent⟩
    · apply liftComponentResource_injective C a b c
      simp [e]

/-- The local one class is exactly the original `b`-class in this
component. -/
theorem card_componentClass_right
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) [Fintype c] :
    (componentClass C a b c b).card =
      (colorClass (componentColoring C hab c) 1).card := by
  classical
  apply Finset.card_bij
    (fun e he ↦ restrictComponentResource C a b c e
      (Or.inr ((mem_componentClass C a b c b e).mp he).1)
      ((mem_componentClass C a b c b e).mp he).2)
  · intro e he
    apply (mem_colorClass (componentColoring C hab c)).mpr
    simp [componentColoring, twoColorCode, hab,
      lift_restrictComponentResource]
    intro ha
    have hb := ((mem_componentClass C a b c b e).mp he).1
    exact hab (ha.symm.trans hb)
  · intro e he f hf hef
    apply Subtype.ext
    have hlift := congrArg (liftComponentResource C a b c) hef
    have hef' : e = f := by simpa using hlift
    exact congrArg Subtype.val hef'
  · intro f hf
    have hcode := (mem_colorClass (componentColoring C hab c)).mp hf
    have hpair := liftComponentResource_color C a b c f
    have hfcolor : C.color (liftComponentResource C a b c f) = b := by
      rcases hpair with ha | hb
      · simp [componentColoring, twoColorCode, ha] at hcode
      · exact hb
    let e := liftComponentResource C a b c f
    have heAnchor : edgeAnchor e ∈ c.supp := by
      have hmem : edgeAnchor e ∈
          Sym2.map Subtype.val f.1 := by
        rw [← liftComponentResource_val C a b c f]
        exact edgeAnchor_mem e
      obtain ⟨v, hv, hval⟩ := Sym2.mem_map.mp hmem
      exact hval ▸ v.2
    have heComponent : (twoColorGraph C a b).connectedComponentMk
        (edgeAnchor e) = c := heAnchor
    refine ⟨e, ?_, ?_⟩
    · exact (mem_componentClass C a b c b e).mpr
        ⟨hfcolor, heComponent⟩
    · apply liftComponentResource_injective C a b c
      simp [e]

/-- On every two-colour component, either original colour has at most one
edge more than the other. -/
theorem componentClass_left_le_right_add_one
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) [Fintype c] :
    (componentClass C a b c a).card ≤
      (componentClass C a b c b).card + 1 := by
  rw [card_componentClass_left C hab c,
    card_componentClass_right C hab c]
  exact card_colorClass_zero_le_one_add_one c.connected_toSimpleGraph
    (componentColoring C hab c)

/-- Anchors of two selected-colour edges that meet lie in the same
two-colour component. -/
theorem anchor_components_eq_of_meet
    (C : ProperEdgeColoring G Color) (a b : Color)
    {e f : Resource G}
    (he : C.color e = a ∨ C.color e = b)
    (hf : C.color f = a ∨ C.color f = b)
    (hmeet : EdgesMeet e f) :
    (twoColorGraph C a b).connectedComponentMk (edgeAnchor e) =
      (twoColorGraph C a b).connectedComponentMk (edgeAnchor f) := by
  obtain ⟨v, hve, hvf⟩ := hmeet
  let ce := (twoColorGraph C a b).connectedComponentMk (edgeAnchor e)
  let cf := (twoColorGraph C a b).connectedComponentMk (edgeAnchor f)
  have hve' : v ∈ ce.supp :=
    endpoint_mem_component_of_anchor C a b ce e he rfl v hve
  have hvf' : v ∈ cf.supp :=
    endpoint_mem_component_of_anchor C a b cf f hf rfl v hvf
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hve' hvf'

/-- Predicate saying that a selected-colour edge lies in the component to be
swapped. -/
def InSwappedComponent
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent) (e : Resource G) : Prop :=
  (C.color e = a ∨ C.color e = b) ∧
    (twoColorGraph C a b).connectedComponentMk (edgeAnchor e) = c

/-- Swap two colours on one connected component of their union. -/
noncomputable def swapComponent
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    ProperEdgeColoring G Color where
  color e := by
    classical
    exact if InSwappedComponent C a b c e then
      Equiv.swap a b (C.color e) else C.color e
  proper := by
    classical
    intro e f hef hmeet
    by_cases he : InSwappedComponent C a b c e <;>
      by_cases hf : InSwappedComponent C a b c f
    · simp only [he, hf, if_true]
      exact (Equiv.swap a b).injective.ne (C.proper hef hmeet)
    · simp only [he, if_true, hf, if_false]
      intro hsame
      have heSwap : Equiv.swap a b (C.color e) = a ∨
          Equiv.swap a b (C.color e) = b := by
        rcases he.1 with hea | heb
        · rw [hea, Equiv.swap_apply_left]
          exact Or.inr rfl
        · rw [heb, Equiv.swap_apply_right]
          exact Or.inl rfl
      have hfcolor : C.color f = a ∨ C.color f = b := by
        rwa [hsame] at heSwap
      apply hf
      refine ⟨hfcolor, ?_⟩
      have hcomp := anchor_components_eq_of_meet C a b he.1 hfcolor hmeet
      exact hcomp.symm.trans he.2
    · simp only [he, if_false, hf, if_true]
      intro hsame
      have hfSwap : Equiv.swap a b (C.color f) = a ∨
          Equiv.swap a b (C.color f) = b := by
        rcases hf.1 with hfa | hfb
        · rw [hfa, Equiv.swap_apply_left]
          exact Or.inr rfl
        · rw [hfb, Equiv.swap_apply_right]
          exact Or.inl rfl
      have hecolor : C.color e = a ∨ C.color e = b := by
        rw [hsame]
        exact hfSwap
      apply he
      refine ⟨hecolor, ?_⟩
      have hcomp := anchor_components_eq_of_meet C a b hecolor hf.1 hmeet
      exact hcomp.trans hf.2
    · simp only [he, hf, if_false]
      exact C.proper hef hmeet

/-- Exact description of the left colour class after a component swap. -/
theorem colorClass_swapComponent_left
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    colorClass (swapComponent C a b c) a =
      (colorClass C a \ componentClass C a b c a) ∪
        componentClass C a b c b := by
  classical
  ext e
  by_cases ha : C.color e = a
  · have hnb : C.color e ≠ b := fun hb ↦ hab (ha.symm.trans hb)
    by_cases hc : (twoColorGraph C a b).connectedComponentMk
        (edgeAnchor e) = c
    · simp [colorClass, swapComponent, InSwappedComponent,
        componentClass, ha, hnb, hc, Equiv.swap_apply_def, hab, hab.symm]
    · simp [colorClass, swapComponent, InSwappedComponent,
        componentClass, ha, hnb, hc, Equiv.swap_apply_def, hab, hab.symm]
  · by_cases hb : C.color e = b
    · by_cases hc : (twoColorGraph C a b).connectedComponentMk
          (edgeAnchor e) = c
      · simp [colorClass, swapComponent, InSwappedComponent,
          componentClass, ha, hb, hc, Equiv.swap_apply_def, hab, hab.symm]
      · simp [colorClass, swapComponent, InSwappedComponent,
          componentClass, ha, hb, hc, Equiv.swap_apply_def, hab, hab.symm]
    · simp [colorClass, swapComponent, InSwappedComponent,
        componentClass, ha, hb, Equiv.swap_apply_def]

/-- Exact description of the right colour class after a component swap. -/
theorem colorClass_swapComponent_right
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    colorClass (swapComponent C a b c) b =
      (colorClass C b \ componentClass C a b c b) ∪
        componentClass C a b c a := by
  classical
  ext e
  by_cases ha : C.color e = a
  · have hnb : C.color e ≠ b := fun hb ↦ hab (ha.symm.trans hb)
    by_cases hc : (twoColorGraph C a b).connectedComponentMk
        (edgeAnchor e) = c
    · simp [colorClass, swapComponent, InSwappedComponent,
        componentClass, ha, hnb, hc, Equiv.swap_apply_def, hab, hab.symm]
    · simp [colorClass, swapComponent, InSwappedComponent,
        componentClass, ha, hnb, hc, Equiv.swap_apply_def, hab, hab.symm]
  · by_cases hb : C.color e = b
    · by_cases hc : (twoColorGraph C a b).connectedComponentMk
          (edgeAnchor e) = c
      · simp [colorClass, swapComponent, InSwappedComponent,
          componentClass, ha, hb, hc, Equiv.swap_apply_def, hab, hab.symm]
      · simp [colorClass, swapComponent, InSwappedComponent,
          componentClass, ha, hb, hc, Equiv.swap_apply_def, hab, hab.symm]
    · simp [colorClass, swapComponent, InSwappedComponent,
        componentClass, ha, hb, Equiv.swap_apply_def]

theorem componentClass_subset_colorClass
    (C : ProperEdgeColoring G Color) (a b : Color)
    (c : (twoColorGraph C a b).ConnectedComponent) (x : Color) :
    componentClass C a b c x ⊆ colorClass C x := by
  classical
  intro e he
  exact (Finset.mem_filter.mp he).1

/-- Subtraction-free cardinal update for the left colour class. -/
theorem card_swapComponent_left_add
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    (colorClass (swapComponent C a b c) a).card +
        (componentClass C a b c a).card =
      (colorClass C a).card + (componentClass C a b c b).card := by
  classical
  rw [colorClass_swapComponent_left C hab c]
  have hdisjoint : Disjoint
      (colorClass C a \ componentClass C a b c a)
      (componentClass C a b c b) := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have hea : C.color e = a :=
      (mem_colorClass C).mp (Finset.mem_sdiff.mp heA).1
    have heb : C.color e = b :=
      (mem_componentClass C a b c b e).mp heB |>.1
    exact hab (hea.symm.trans heb)
  rw [Finset.card_union_of_disjoint hdisjoint,
    Finset.card_sdiff_of_subset
      (componentClass_subset_colorClass C a b c a)]
  have hcard := Finset.card_le_card
    (componentClass_subset_colorClass C a b c a)
  omega

/-- Subtraction-free cardinal update for the right colour class. -/
theorem card_swapComponent_right_add
    (C : ProperEdgeColoring G Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    (colorClass (swapComponent C a b c) b).card +
        (componentClass C a b c b).card =
      (colorClass C b).card + (componentClass C a b c a).card := by
  classical
  rw [colorClass_swapComponent_right C hab c]
  have hdisjoint : Disjoint
      (colorClass C b \ componentClass C a b c b)
      (componentClass C a b c a) := by
    rw [Finset.disjoint_left]
    intro e heB heA
    have heb : C.color e = b :=
      (mem_colorClass C).mp (Finset.mem_sdiff.mp heB).1
    have hea : C.color e = a :=
      (mem_componentClass C a b c a e).mp heA |>.1
    exact hab (hea.symm.trans heb)
  rw [Finset.card_union_of_disjoint hdisjoint,
    Finset.card_sdiff_of_subset
      (componentClass_subset_colorClass C a b c b)]
  have hcard := Finset.card_le_card
    (componentClass_subset_colorClass C a b c b)
  omega

/-- All colours other than the swapped pair are unchanged. -/
theorem colorClass_swapComponent_of_ne
    (C : ProperEdgeColoring G Color) {a b x : Color}
    (hxa : x ≠ a) (hxb : x ≠ b)
    (c : (twoColorGraph C a b).ConnectedComponent) :
    colorClass (swapComponent C a b c) x = colorClass C x := by
  classical
  by_cases hab : a = b
  · subst b
    ext e
    simp [colorClass, swapComponent, Equiv.swap_apply_def]
  ext e
  by_cases ha : C.color e = a
  · by_cases hc : (twoColorGraph C a b).connectedComponentMk
        (edgeAnchor e) = c
    · simp [colorClass, swapComponent, InSwappedComponent, ha, hc,
        Equiv.swap_apply_def, hxa, hxb, hxa.symm, hxb.symm, hab]
    · simp [colorClass, swapComponent, InSwappedComponent, ha, hc,
        Equiv.swap_apply_def, hxa, hxa.symm, hab]
  · by_cases hb : C.color e = b
    · by_cases hc : (twoColorGraph C a b).connectedComponentMk
          (edgeAnchor e) = c
      · simp [colorClass, swapComponent, InSwappedComponent, ha, hb, hc,
          Equiv.swap_apply_def, hxa, hxb, hxa.symm, hxb.symm, hab, Ne.symm hab]
      · simp [colorClass, swapComponent, InSwappedComponent, ha, hb, hc,
          Equiv.swap_apply_def, hxb, hxb.symm, hab, Ne.symm hab]
    · simp [colorClass, swapComponent, InSwappedComponent, ha, hb,
        Equiv.swap_apply_def]

end TwoColors

/-- Sum-of-squares energy used to terminate equitable refinement. -/
noncomputable def energy {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) : ℕ :=
  ∑ a : Color, (colorClass C a).card ^ 2

/-- All colour-class sizes differ by at most one. -/
def IsEquitable {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) : Prop :=
  ∀ a b, (colorClass C a).card ≤ (colorClass C b).card + 1

theorem sum_eq_two_add_rest (f : Color → ℕ) {a b : Color} (hab : a ≠ b) :
    ∑ x : Color, f x = f a + f b +
      ∑ x ∈ (Finset.univ.erase a).erase b, f x := by
  classical
  have ha : a ∈ (Finset.univ : Finset Color) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ : Finset Color).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ ha,
    ← Finset.sum_erase_add _ _ hb]
  omega

/-- If two class sizes differ by at least two, swapping a component strictly
decreases the sum-of-squares energy. -/
theorem exists_energy_decreasing_swap {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) {a b : Color}
    (hgap : (colorClass C b).card + 1 < (colorClass C a).card) :
    ∃ C' : ProperEdgeColoring G Color, energy C' < energy C := by
  classical
  have hab : a ≠ b := by
    intro hab
    subst b
    omega
  obtain ⟨c, hcLarge⟩ := exists_component_card_lt C (by omega :
    (colorClass C b).card < (colorClass C a).card)
  letI := Fintype.ofFinite c
  have hcSmall := componentClass_left_le_right_add_one C hab c
  have hcEq : (componentClass C a b c a).card =
      (componentClass C a b c b).card + 1 := by omega
  let C' := swapComponent C a b c
  have hleft := card_swapComponent_left_add C hab c
  have hright := card_swapComponent_right_add C hab c
  have hleft' : (colorClass C' a).card + 1 = (colorClass C a).card := by
    change (colorClass (swapComponent C a b c) a).card + 1 =
      (colorClass C a).card
    omega
  have hright' : (colorClass C' b).card = (colorClass C b).card + 1 := by
    change (colorClass (swapComponent C a b c) b).card =
      (colorClass C b).card + 1
    omega
  have hrest :
      (∑ x ∈ (Finset.univ.erase a).erase b,
        (colorClass C' x).card ^ 2) =
      ∑ x ∈ (Finset.univ.erase a).erase b,
        (colorClass C x).card ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxa : x ≠ a := by
      exact fun h ↦ (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1 h
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    rw [colorClass_swapComponent_of_ne C hxa hxb c]
  refine ⟨C', ?_⟩
  change (∑ x : Color, (colorClass C' x).card ^ 2) <
    ∑ x : Color, (colorClass C x).card ^ 2
  rw [sum_eq_two_add_rest _ hab,
    sum_eq_two_add_rest _ hab, hrest]
  nlinarith

/-- Every finite proper edge colouring admits an equitable proper refinement
using exactly the same colour type. -/
theorem exists_equitable_coloring {G : SimpleGraph V}
    (C : ProperEdgeColoring G Color) :
    ∃ C' : ProperEdgeColoring G Color, IsEquitable C' := by
  classical
  generalize hn : energy C = n
  induction n using Nat.strong_induction_on generalizing C with
  | h n ih =>
      by_cases heq : IsEquitable C
      · exact ⟨C, heq⟩
      · unfold IsEquitable at heq
        push Not at heq
        obtain ⟨a, b, hab⟩ := heq
        obtain ⟨C', henergy⟩ :=
          exists_energy_decreasing_swap C (by omega)
        exact ih (energy C') (hn ▸ henergy) C' rfl

/-- In an equitable colouring, every class has size at most the ceiling of
the average class size. -/
theorem class_card_le_ceiling_of_equitable {G : SimpleGraph V}
    [Nonempty Color] (C : ProperEdgeColoring G Color) (hC : IsEquitable C)
    (a : Color) :
    (colorClass C a).card ≤
      classCeiling (Nat.card (Resource G)) (Fintype.card Color) := by
  classical
  let t := classCeiling (Nat.card (Resource G)) (Fintype.card Color)
  have hc : 0 < Fintype.card Color := Fintype.card_pos
  have htotal := sum_card_colorClass C
  have hceil := edge_count_le_colors_mul_ceiling
    (Nat.card (Resource G)) (Fintype.card Color) hc
  by_contra hnot
  have ha : t < (colorClass C a).card := by
    simpa [t] using Nat.lt_of_not_ge hnot
  have hall : ∀ b : Color, t ≤ (colorClass C b).card := by
    intro b
    have := hC a b
    omega
  have hstrict :
      (∑ _b : Color, t) < ∑ b : Color, (colorClass C b).card := by
    exact Finset.sum_lt_sum (fun b _ ↦ hall b)
      ⟨a, Finset.mem_univ a, ha⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstrict
  rw [htotal] at hstrict
  have hstrict' : Fintype.card Color * t < Nat.card (Resource G) := by
    simpa [Nat.mul_comm] using hstrict
  simp only [t] at hstrict'
  omega

/-- Package an equitable colouring as the bounded colouring required by the
terminal construction. -/
noncomputable def equitableBoundedColoring {G : SimpleGraph V}
    [Nonempty Color] (C : ProperEdgeColoring G Color) (hC : IsEquitable C) :
    BoundedColoring G Color
      (classCeiling (Nat.card (Resource G)) (Fintype.card Color)) where
  toProper := C
  class_card_le := class_card_le_ceiling_of_equitable C hC

/-- Vizing's theorem followed by the internal equitable-refinement argument
gives the bounded colouring used in the terminal construction. -/
theorem exists_bounded_coloring_of_vizing
    {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj]
    (hv : VizingInput) {c : ℕ} (hc : G.maxDegree + 1 ≤ c) :
    Nonempty (BoundedColoring G (Fin c)
      (classCeiling (Nat.card (Resource G)) c)) := by
  let C : ProperEdgeColoring G (Fin c) :=
    Classical.choice (exists_coloring_of_vizing (G := G) hv hc)
  obtain ⟨C', hC'⟩ := exists_equitable_coloring C
  have hcpos : 0 < c := lt_of_lt_of_le (Nat.zero_lt_succ _) hc
  letI : Nonempty (Fin c) := Fin.pos_iff_nonempty.mp hcpos
  exact ⟨by simpa using equitableBoundedColoring C' hC'⟩

end EquitableEdgeColoring
end Erdos81
