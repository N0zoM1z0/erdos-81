import Erdos81.CompleteSplit
import Erdos81.IntegralFractional
import Mathlib.Tactic

/-!
# Symmetric fractional packings of complete-split graphs

The complete-split calculation is certified on the primal side.  Mixed
triangles are indexed by a root pair and one outside vertex; mixed
four-cliques by a root triple and one outside vertex; root four-cliques by a
root four-set.  Later sections assign uniform rational weights to these three
finite families and check edge capacities exactly.
-/

namespace Erdos81
namespace CompleteSplitPacking

open SimpleGraph MixedModel RootedGraph EditDistance CompleteSplit

attribute [-instance] MixedModel.resourceFintype

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Choices of `d` root vertices and one outside vertex. -/
abbrev MixedDomain (K : Finset V) (d : ℕ) :=
  ↥(K.powersetCard d) × ↥(outsideVertices K)

/-- Vertex set represented by a mixed-domain choice. -/
def mixedVertices {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) : Finset V :=
  insert a.2.1 a.1.1

theorem mixed_root_subset {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) : a.1.1 ⊆ K :=
  (Finset.mem_powersetCard.mp a.1.2).1

theorem mixed_root_card {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) : a.1.1.card = d :=
  (Finset.mem_powersetCard.mp a.1.2).2

theorem mixed_outside_not_root {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) : a.2.1 ∉ K :=
  mem_outsideVertices.mp a.2.2

theorem mixed_outside_not_mem_rootChoice {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) : a.2.1 ∉ a.1.1 :=
  fun h ↦ mixed_outside_not_root a (mixed_root_subset a h)

theorem card_mixedVertices {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) : (mixedVertices a).card = d + 1 := by
  rw [mixedVertices, Finset.card_insert_of_notMem
    (mixed_outside_not_mem_rootChoice a), mixed_root_card]

theorem mixedVertices_sdiff_root {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) : mixedVertices a \ K = {a.2.1} := by
  ext z
  simp only [mixedVertices, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | hz, hnot⟩
    · rfl
    · exact (hnot (mixed_root_subset a hz)).elim
  · rintro rfl
    exact ⟨Or.inl rfl, mixed_outside_not_root a⟩

theorem mixedVertices_isClique {K : Finset V} {d : ℕ}
    (a : MixedDomain K d) :
    (completeSplitGraph K).IsClique (mixedVertices a : Set V) := by
  rw [isClique_iff_card_sdiff_le_one, mixedVertices_sdiff_root]
  simp

/-- The triangle item associated with two root vertices and one outside
vertex. -/
def mixedTriangle (K : Finset V) (a : MixedDomain K 2) :
    CliqueOfOrder (completeSplitGraph K) 3 :=
  ⟨mixedVertices a, by simpa using card_mixedVertices a,
    mixedVertices_isClique a⟩

/-- The four-clique item associated with three root vertices and one outside
vertex. -/
def mixedFourClique (K : Finset V) (a : MixedDomain K 3) :
    CliqueOfOrder (completeSplitGraph K) 4 :=
  ⟨mixedVertices a, by simpa using card_mixedVertices a,
    mixedVertices_isClique a⟩

/-- A root-side four-clique. -/
def rootFourClique (K : Finset V)
    (R : ↥(K.powersetCard 4)) :
    CliqueOfOrder (completeSplitGraph K) 4 :=
  ⟨R.1, (Finset.mem_powersetCard.mp R.2).2,
    root_isClique K |>.subset (Finset.mem_powersetCard.mp R.2).1⟩

theorem mixedVertices_injective {K : Finset V} {d : ℕ} :
    Function.Injective (mixedVertices : MixedDomain K d → Finset V) := by
  intro a b hab
  have haz : a.2.1 ∈ mixedVertices b := by
    rw [← hab]
    simp [mixedVertices]
  have hz : a.2.1 = b.2.1 := by
    rw [mixedVertices, Finset.mem_insert] at haz
    rcases haz with haz | haz
    · exact haz
    · exact (mixed_outside_not_root a (mixed_root_subset b haz)).elim
  have hroot : a.1.1 = b.1.1 := by
    change insert a.2.1 a.1.1 = insert b.2.1 b.1.1 at hab
    have hab' : insert a.2.1 a.1.1 = insert a.2.1 b.1.1 := by
      simpa only [hz] using hab
    have haNot : a.2.1 ∉ b.1.1 := by
      rw [hz]
      exact mixed_outside_not_mem_rootChoice b
    have herase := congrArg (fun S : Finset V ↦ S.erase a.2.1) hab'
    simpa [mixed_outside_not_mem_rootChoice a, haNot] using herase
  exact Prod.ext (Subtype.ext hroot) (Subtype.ext hz)

theorem mixedTriangle_injective (K : Finset V) :
    Function.Injective (mixedTriangle K) := by
  intro a b h
  exact mixedVertices_injective (congrArg Subtype.val h)

theorem mixedFourClique_injective (K : Finset V) :
    Function.Injective (mixedFourClique K) := by
  intro a b h
  exact mixedVertices_injective (congrArg Subtype.val h)

theorem rootFourClique_injective (K : Finset V) :
    Function.Injective (rootFourClique K) := by
  intro R S h
  apply Subtype.ext
  exact congrArg (fun Q : CliqueOfOrder (completeSplitGraph K) 4 ↦ Q.1) h

/-- The generated family of mixed triangles, embedded in the sum item type. -/
noncomputable def mixedTriangles (K : Finset V) :
    Finset (Item (completeSplitGraph K)) := by
  classical
  exact Finset.univ.image fun a : MixedDomain K 2 ↦ Sum.inl (mixedTriangle K a)

/-- The generated family of mixed four-cliques. -/
noncomputable def mixedFourCliques (K : Finset V) :
    Finset (Item (completeSplitGraph K)) := by
  classical
  exact Finset.univ.image fun a : MixedDomain K 3 ↦ Sum.inr (mixedFourClique K a)

/-- The generated family of root-side four-cliques. -/
noncomputable def rootFourCliques (K : Finset V) :
    Finset (Item (completeSplitGraph K)) := by
  classical
  exact Finset.univ.image fun R : ↥(K.powersetCard 4) ↦
    Sum.inr (rootFourClique K R)

theorem card_mixedDomain (K : Finset V) (d : ℕ) :
    Fintype.card (MixedDomain K d) =
      Nat.choose K.card d * (outsideVertices K).card := by
  classical
  simp only [MixedDomain, Fintype.card_prod, Fintype.card_coe,
    Finset.card_powersetCard]

theorem card_mixedTriangles (K : Finset V) :
    (mixedTriangles K).card =
      Nat.choose K.card 2 * (outsideVertices K).card := by
  classical
  rw [mixedTriangles, Finset.card_image_of_injective]
  · exact card_mixedDomain K 2
  · exact Sum.inl_injective.comp (mixedTriangle_injective K)

theorem card_mixedFourCliques (K : Finset V) :
    (mixedFourCliques K).card =
      Nat.choose K.card 3 * (outsideVertices K).card := by
  classical
  rw [mixedFourCliques, Finset.card_image_of_injective]
  · exact card_mixedDomain K 3
  · exact Sum.inr_injective.comp (mixedFourClique_injective K)

theorem card_rootFourCliques (K : Finset V) :
    (rootFourCliques K).card = Nat.choose K.card 4 := by
  classical
  rw [rootFourCliques, Finset.card_image_of_injective]
  · simp
  · exact Sum.inr_injective.comp (rootFourClique_injective K)

/-- Domain choices whose generated mixed clique contains a fixed graph edge. -/
noncomputable def mixedDomainUsing (K : Finset V) (d : ℕ)
    (e : Resource (completeSplitGraph K)) : Finset (MixedDomain K d) := by
  classical
  exact Finset.univ.filter fun a ↦ e.1.toFinset ⊆ mixedVertices a

/-- Number of members of an item family which use a fixed edge. -/
noncomputable def familyUses {G : SimpleGraph V}
    (F : Finset (Item G)) (e : Resource G) : ℕ := by
  classical
  exact (F.filter fun i ↦ Uses i e).card

/-- Generated mixed triangles containing a fixed edge are counted by their
domain choices. -/
theorem card_mixedTriangles_filter_uses (K : Finset V)
    (e : Resource (completeSplitGraph K)) :
    familyUses (mixedTriangles K) e =
      (mixedDomainUsing K 2 e).card := by
  classical
  rw [familyUses, mixedTriangles, Finset.filter_image,
    Finset.card_image_of_injective]
  · congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      MixedModel.Uses, MixedModel.vertices, mixedTriangle]
    simp [mixedDomainUsing]
  · exact Sum.inl_injective.comp (mixedTriangle_injective K)

/-- Generated mixed four-cliques containing a fixed edge are counted by their
domain choices. -/
theorem card_mixedFourCliques_filter_uses (K : Finset V)
    (e : Resource (completeSplitGraph K)) :
    familyUses (mixedFourCliques K) e =
      (mixedDomainUsing K 3 e).card := by
  classical
  rw [familyUses, mixedFourCliques, Finset.filter_image,
    Finset.card_image_of_injective]
  · congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      MixedModel.Uses, MixedModel.vertices, mixedFourClique]
    simp [mixedDomainUsing]
  · exact Sum.inr_injective.comp (mixedFourClique_injective K)

/-- A root edge contained in a mixed clique must already lie in the selected
root subset. -/
theorem root_edge_subset_rootChoice {K : Finset V} {d : ℕ}
    {e : Resource (completeSplitGraph K)} (heRoot : e.1.toFinset ⊆ K)
    {a : MixedDomain K d} (huses : e.1.toFinset ⊆ mixedVertices a) :
    e.1.toFinset ⊆ a.1.1 := by
  intro x hx
  have hxMixed := huses hx
  rw [mixedVertices, Finset.mem_insert] at hxMixed
  rcases hxMixed with hxa | hxa
  · subst x
    exact (mixed_outside_not_root a (heRoot hx)).elim
  · exact hxa

/-- Capacity count for a root edge in the generated mixed `d+1` cliques. -/
theorem card_mixedDomainUsing_le_of_root
    (K : Finset V) (d : ℕ) (e : Resource (completeSplitGraph K))
    (heRoot : e.1.toFinset ⊆ K) (hd : 2 ≤ d) :
    (mixedDomainUsing K d e).card ≤
      Nat.choose (K.card - 2) (d - 2) * (outsideVertices K).card := by
  classical
  let target := ((K.powersetCard d).filter (e.1.toFinset ⊆ ·)).product
    (outsideVertices K)
  have hmaps : Set.MapsTo
      (fun a : MixedDomain K d ↦ (a.1.1, a.2.1))
      (mixedDomainUsing K d e : Set (MixedDomain K d)) target := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨a.1.2,
      root_edge_subset_rootChoice heRoot ha'.2⟩, a.2.2⟩
  have hinj : Set.InjOn
      (fun a : MixedDomain K d ↦ (a.1.1, a.2.1))
      (mixedDomainUsing K d e : Set (MixedDomain K d)) := by
    intro a _ b _ hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hab))
      (Subtype.ext (congrArg Prod.snd hab))
  calc
    (mixedDomainUsing K d e).card ≤ target.card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ((K.powersetCard d).filter (e.1.toFinset ⊆ ·)).card *
        (outsideVertices K).card := Finset.card_product _ _
    _ = Nat.choose (K.card - 2) (d - 2) *
        (outsideVertices K).card := by
      rw [Finset.card_filter_powersetCard_subset e.1.toFinset K d heRoot]
      · have hedgeCard : e.1.toFinset.card = 2 :=
          Sym2.card_toFinset_of_not_isDiag e.1
            ((completeSplitGraph K).not_isDiag_of_mem_edgeSet e.2)
        rw [hedgeCard]
      · have hedgeCard : e.1.toFinset.card = 2 :=
          Sym2.card_toFinset_of_not_isDiag e.1
            ((completeSplitGraph K).not_isDiag_of_mem_edgeSet e.2)
        simpa [hedgeCard] using hd

/-- A spoke contained in a generated mixed clique determines its outside
choice, so forgetting that choice is injective. -/
theorem card_mixedDomainUsing_le_of_spoke
    (K : Finset V) (d : ℕ) (e : Resource (completeSplitGraph K))
    (heSpoke : (e.1.toFinset \ K).card = 1) (hd : 1 ≤ d) :
    (mixedDomainUsing K d e).card ≤ Nat.choose (K.card - 1) (d - 1) := by
  classical
  let rootPart := e.1.toFinset ∩ K
  let target := (K.powersetCard d).filter (rootPart ⊆ ·)
  have hedgeCard : e.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e.1
      ((completeSplitGraph K).not_isDiag_of_mem_edgeSet e.2)
  have hrootCard : rootPart.card = 1 := by
    have hsplit := Finset.card_sdiff_add_card_inter e.1.toFinset K
    dsimp only [rootPart]
    omega
  have hmaps : Set.MapsTo (fun a : MixedDomain K d ↦ a.1.1)
      (mixedDomainUsing K d e : Set (MixedDomain K d)) target := by
    intro a ha
    apply Finset.mem_filter.mpr
    refine ⟨a.1.2, ?_⟩
    intro x hx
    have hx' : x ∈ e.1.toFinset ∧ x ∈ K := by
      simpa only [rootPart, Finset.mem_inter] using hx
    have hxMixed := (Finset.mem_filter.mp ha).2 hx'.1
    rw [mixedVertices, Finset.mem_insert] at hxMixed
    rcases hxMixed with hxa | hxa
    · subst x
      exact (mixed_outside_not_root a hx'.2).elim
    · exact hxa
  have hinj : Set.InjOn (fun a : MixedDomain K d ↦ a.1.1)
      (mixedDomainUsing K d e : Set (MixedDomain K d)) := by
    intro a ha b hb hroot
    apply Prod.ext
    · exact Subtype.ext hroot
    · apply Subtype.ext
      have houtNonempty : (e.1.toFinset \ K).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨z, hz⟩ := houtNonempty
      have outside_eq (c : MixedDomain K d)
          (hc : c ∈ mixedDomainUsing K d e) : z = c.2.1 := by
        have hzc := (Finset.mem_filter.mp hc).2 (Finset.mem_sdiff.mp hz).1
        rw [mixedVertices, Finset.mem_insert] at hzc
        rcases hzc with hzc | hzc
        · exact hzc
        · exact ((Finset.mem_sdiff.mp hz).2 (mixed_root_subset c hzc)).elim
      exact (outside_eq a ha).symm.trans (outside_eq b hb)
  calc
    (mixedDomainUsing K d e).card ≤ target.card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ = Nat.choose (K.card - 1) (d - 1) := by
      rw [Finset.card_filter_powersetCard_subset rootPart K d]
      · rw [hrootCard]
      · intro x hx
        have hx' : x ∈ e.1.toFinset ∧ x ∈ K := by
          simpa only [rootPart, Finset.mem_inter] using hx
        exact hx'.2
      · simpa [hrootCard] using hd

theorem mixedTriangle_uses_le_root (K : Finset V)
    (e : Resource (completeSplitGraph K)) (heRoot : e.1.toFinset ⊆ K) :
    familyUses (mixedTriangles K) e ≤
      (outsideVertices K).card := by
  rw [card_mixedTriangles_filter_uses]
  simpa using card_mixedDomainUsing_le_of_root K 2 e heRoot (by omega)

theorem mixedTriangle_uses_le_spoke (K : Finset V)
    (e : Resource (completeSplitGraph K))
    (heSpoke : (e.1.toFinset \ K).card = 1) :
    familyUses (mixedTriangles K) e ≤ K.card - 1 := by
  rw [card_mixedTriangles_filter_uses]
  simpa using card_mixedDomainUsing_le_of_spoke K 2 e heSpoke (by omega)

theorem mixedFourClique_uses_le_root (K : Finset V)
    (e : Resource (completeSplitGraph K)) (heRoot : e.1.toFinset ⊆ K) :
    familyUses (mixedFourCliques K) e ≤
      (K.card - 2) * (outsideVertices K).card := by
  rw [card_mixedFourCliques_filter_uses]
  simpa [Nat.choose_one_right] using
    card_mixedDomainUsing_le_of_root K 3 e heRoot (by omega)

theorem mixedFourClique_uses_le_spoke (K : Finset V)
    (e : Resource (completeSplitGraph K))
    (heSpoke : (e.1.toFinset \ K).card = 1) :
    familyUses (mixedFourCliques K) e ≤
      Nat.choose (K.card - 1) 2 := by
  rw [card_mixedFourCliques_filter_uses]
  simpa using card_mixedDomainUsing_le_of_spoke K 3 e heSpoke (by omega)

/-- Root four-set choices whose clique contains a fixed edge. -/
noncomputable def rootDomainUsing (K : Finset V)
    (e : Resource (completeSplitGraph K)) :
    Finset ↑(K.powersetCard 4) := by
  classical
  exact Finset.univ.filter fun R ↦ e.1.toFinset ⊆ R.1

/-- Generated root four-cliques containing an edge are counted by their
four-set choices. -/
theorem card_rootFourCliques_filter_uses (K : Finset V)
    (e : Resource (completeSplitGraph K)) :
    familyUses (rootFourCliques K) e = (rootDomainUsing K e).card := by
  classical
  rw [familyUses, rootFourCliques, Finset.filter_image,
    Finset.card_image_of_injective]
  · congr 1
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      MixedModel.Uses, MixedModel.vertices, rootFourClique]
    simp [rootDomainUsing]
  · exact Sum.inr_injective.comp (rootFourClique_injective K)

/-- A root edge belongs to at most `choose (|K|-2) 2` root four-cliques. -/
theorem rootFourClique_uses_le_root (K : Finset V)
    (e : Resource (completeSplitGraph K)) (heRoot : e.1.toFinset ⊆ K) :
    familyUses (rootFourCliques K) e ≤ Nat.choose (K.card - 2) 2 := by
  classical
  rw [card_rootFourCliques_filter_uses]
  let target := (K.powersetCard 4).filter (e.1.toFinset ⊆ ·)
  have hmaps : Set.MapsTo
      (fun R : ↑(K.powersetCard 4) ↦ R.1)
      (rootDomainUsing K e : Set ↑(K.powersetCard 4)) target := by
    intro R hR
    exact Finset.mem_filter.mpr ⟨R.2, (Finset.mem_filter.mp hR).2⟩
  have hinj : Set.InjOn
      (fun R : ↑(K.powersetCard 4) ↦ R.1)
      (rootDomainUsing K e : Set ↑(K.powersetCard 4)) := by
    intro R _ S _ hRS
    exact Subtype.ext hRS
  calc
    (rootDomainUsing K e).card ≤ target.card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ = Nat.choose (K.card - 2) (4 - 2) := by
      rw [Finset.card_filter_powersetCard_subset e.1.toFinset K 4 heRoot]
      · rw [Sym2.card_toFinset_of_not_isDiag e.1
          ((completeSplitGraph K).not_isDiag_of_mem_edgeSet e.2)]
      · have hedgeCard : e.1.toFinset.card = 2 :=
          Sym2.card_toFinset_of_not_isDiag e.1
            ((completeSplitGraph K).not_isDiag_of_mem_edgeSet e.2)
        omega
    _ = Nat.choose (K.card - 2) 2 := by norm_num

/-- A spoke belongs to no root four-clique. -/
theorem rootFourClique_uses_eq_zero_of_spoke (K : Finset V)
    (e : Resource (completeSplitGraph K))
    (heSpoke : (e.1.toFinset \ K).card = 1) :
    familyUses (rootFourCliques K) e = 0 := by
  classical
  rw [card_rootFourCliques_filter_uses, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  have hout : (e.1.toFinset \ K).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hout
  have hzR := (Finset.mem_filter.mp hR).2 (Finset.mem_sdiff.mp hz).1
  exact (Finset.mem_sdiff.mp hz).2
    ((Finset.mem_powersetCard.mp R.2).1 hzR)

attribute [local instance] MixedModel.resourceFintype

/-- Rational indicator of membership in a finite item family. -/
noncomputable def familyIndicator {G : SimpleGraph V}
    (F : Finset (Item G)) (i : Item G) : ℚ := by
  classical
  exact if i ∈ F then 1 else 0

/-- Summing incidence against a family indicator counts precisely the family
members which contain the resource. -/
theorem sum_incidence_familyIndicator {G : SimpleGraph V}
    (F : Finset (Item G)) (e : Resource G) :
    (∑ i, incidence i e * familyIndicator F i) = familyUses F e := by
  classical
  rw [familyUses]
  simp only [incidence, familyIndicator]
  simp

/-- The weight obtained by assigning uniform coefficients to the three
generated complete-split families and zero elsewhere. -/
noncomputable def generatedWeight (K : Finset V) (α β γ : ℚ)
    (i : Item (completeSplitGraph K)) : ℚ :=
  α * familyIndicator (mixedTriangles K) i +
    β * familyIndicator (mixedFourCliques K) i +
    γ * familyIndicator (rootFourCliques K) i

theorem sum_incidence_generatedWeight (K : Finset V) (α β γ : ℚ)
    (e : Resource (completeSplitGraph K)) :
    (∑ i, incidence i e * generatedWeight K α β γ i) =
      α * familyUses (mixedTriangles K) e +
      β * familyUses (mixedFourCliques K) e +
      γ * familyUses (rootFourCliques K) e := by
  classical
  calc
    (∑ i, incidence i e * generatedWeight K α β γ i) =
        α * (∑ i, incidence i e * familyIndicator (mixedTriangles K) i) +
        β * (∑ i, incidence i e * familyIndicator (mixedFourCliques K) i) +
        γ * (∑ i, incidence i e * familyIndicator (rootFourCliques K) i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [generatedWeight]
      ring
    _ = _ := by
      rw [sum_incidence_familyIndicator, sum_incidence_familyIndicator,
        sum_incidence_familyIndicator]

/-- Reusable primal constructor.  Its only graph-dependent obligation is the
displayed capacity inequality for each edge. -/
noncomputable def generatedPacking (K : Finset V) (α β γ : ℚ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hcapacity : ∀ e : Resource (completeSplitGraph K),
      α * familyUses (mixedTriangles K) e +
        β * familyUses (mixedFourCliques K) e +
        γ * familyUses (rootFourCliques K) e ≤ 1) :
    FractionalPacking (completeSplitGraph K) where
  weight := generatedWeight K α β γ
  weight_nonnegative := by
    intro i
    unfold generatedWeight familyIndicator
    split_ifs <;> positivity
  capacity := by
    intro e
    rw [sum_incidence_generatedWeight]
    exact hcapacity e

/-- Objective contribution of one constant-gain finite family. -/
theorem sum_gain_familyIndicator {G : SimpleGraph V}
    (F : Finset (Item G)) (c : ℚ)
    (hgain : ∀ i ∈ F, gain i = c) :
    (∑ i, gain i * familyIndicator F i) = c * F.card := by
  classical
  calc
    (∑ i, gain i * familyIndicator F i) = ∑ i ∈ F, gain i := by
      simp [familyIndicator]
    _ = ∑ _i ∈ F, c := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hgain i hi
    _ = c * F.card := by simp; ring

theorem mixedTriangles_gain (K : Finset V)
    (i : Item (completeSplitGraph K)) (hi : i ∈ mixedTriangles K) :
    gain i = 2 := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

theorem mixedFourCliques_gain (K : Finset V)
    (i : Item (completeSplitGraph K)) (hi : i ∈ mixedFourCliques K) :
    gain i = 5 := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

theorem rootFourCliques_gain (K : Finset V)
    (i : Item (completeSplitGraph K)) (hi : i ∈ rootFourCliques K) :
    gain i = 5 := by
  classical
  obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

/-- Exact objective of the uniform generated packing. -/
theorem packingValue_generatedPacking (K : Finset V) (α β γ : ℚ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hcapacity : ∀ e : Resource (completeSplitGraph K),
      α * familyUses (mixedTriangles K) e +
        β * familyUses (mixedFourCliques K) e +
        γ * familyUses (rootFourCliques K) e ≤ 1) :
    packingValue (generatedPacking K α β γ hα hβ hγ hcapacity) =
      2 * α * (mixedTriangles K).card +
        5 * β * (mixedFourCliques K).card +
        5 * γ * (rootFourCliques K).card := by
  classical
  unfold packingValue FiniteLP.primalValue
  change (∑ i, gain i * generatedWeight K α β γ i) = _
  calc
    (∑ i, gain i * generatedWeight K α β γ i) =
        α * (∑ i, gain i * familyIndicator (mixedTriangles K) i) +
        β * (∑ i, gain i * familyIndicator (mixedFourCliques K) i) +
        γ * (∑ i, gain i * familyIndicator (rootFourCliques K) i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [generatedWeight]
      ring
    _ = _ := by
      rw [sum_gain_familyIndicator _ 2 (mixedTriangles_gain K),
        sum_gain_familyIndicator _ 5 (mixedFourCliques_gain K),
        sum_gain_familyIndicator _ 5 (rootFourCliques_gain K)]
      ring

end CompleteSplitPacking
end Erdos81
