import Erdos81.CopyCover
import Erdos81.TerminalCharacterization
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# Fine monotone symmetrization

We construct a finite path of single-vertex copies from a chordal graph to a
complete-split graph.  Every step copies one simplicial vertex onto a
nonadjacent simplicial vertex, preserves chordality, changes only the target's
incident pairs, and does not decrease the certified mixed potential.

Termination is organized as a finite lexicographic ascent.  The primary
coordinate is the mixed potential.  The secondary coordinate is the largest
open-neighbourhood class among simplicial vertices.  If neither opposite copy
strictly increases the primary coordinate, copying a largest class onto a
different simplicial class strictly increases the secondary coordinate.
-/

namespace Erdos81
namespace Symmetrization

open SimpleGraph MixedModel Copying CopyCover TerminalCharacterization

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem right_strict_of_two_le_sum {a b c : ℚ}
    (hsum : 2 * a ≤ b + c) (hb : b < a) : a < c := by
  linarith

/-- Vertices with the same open neighbourhood as `u`. -/
noncomputable def neighborhoodClass (G : SimpleGraph V) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ G.neighborSet v = G.neighborSet u

@[simp]
theorem mem_neighborhoodClass {G : SimpleGraph V} {u v : V} :
    v ∈ neighborhoodClass G u ↔
      G.neighborSet v = G.neighborSet u := by
  classical
  simp [neighborhoodClass]

/-- Simplicial vertices of a graph. -/
noncomputable def simplicialVertices (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (IsSimplicial G)

@[simp]
theorem mem_simplicialVertices {G : SimpleGraph V} {u : V} :
    u ∈ simplicialVertices G ↔ IsSimplicial G u := by
  classical
  simp [simplicialVertices]

/-- Size of the largest open-neighbourhood class represented by a simplicial
vertex.  It is zero only when there is no simplicial vertex. -/
noncomputable def maxSimplicialClass (G : SimpleGraph V) : ℕ :=
  (simplicialVertices G).sup fun u ↦ (neighborhoodClass G u).card

theorem class_card_le_maxSimplicialClass {G : SimpleGraph V} {u : V}
    (hu : IsSimplicial G u) :
    (neighborhoodClass G u).card ≤ maxSimplicialClass G := by
  classical
  exact Finset.le_sup (f := fun v ↦ (neighborhoodClass G v).card)
    (mem_simplicialVertices.mpr hu)

/-- A largest simplicial neighbourhood class can be represented by an actual
simplicial vertex in every nonempty chordal graph. -/
theorem exists_maximal_simplicial_class
    {G : SimpleGraph V} [Nonempty V] (hchordal : IsChordal G) :
    ∃ u : V, IsSimplicial G u ∧
      maxSimplicialClass G = (neighborhoodClass G u).card ∧
      ∀ v : V, IsSimplicial G v →
        (neighborhoodClass G v).card ≤ (neighborhoodClass G u).card := by
  classical
  obtain ⟨u, hu⟩ := Dirac.exists_simplicial (G := G) hchordal
  have hnonempty : (simplicialVertices G).Nonempty :=
    ⟨u, mem_simplicialVertices.mpr hu⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image
    (simplicialVertices G) (fun v ↦ (neighborhoodClass G v).card) hnonempty
  have haSimp : IsSimplicial G a := mem_simplicialVertices.mp ha
  have hsup : maxSimplicialClass G = (neighborhoodClass G a).card := by
    apply le_antisymm
    · exact Finset.sup_le fun v hv ↦ hmax v hv
    · exact class_card_le_maxSimplicialClass haSimp
  exact ⟨a, haSimp, hsup,
    fun v hv ↦ hmax v (mem_simplicialVertices.mpr hv)⟩

/-- If the terminal condition fails, every simplicial vertex can be compared
with one member of a witnessing nonadjacent pair; in particular a largest
class has a nonadjacent simplicial vertex with a different neighbourhood. -/
theorem exists_different_simplicial_partner
    {G : SimpleGraph V} (hnot : ¬IsTerminal G)
    {u : V} (hu : IsSimplicial G u) :
    ∃ v : V, u ≠ v ∧ ¬G.Adj u v ∧ IsSimplicial G v ∧
      G.neighborSet u ≠ G.neighborSet v := by
  classical
  simp only [IsTerminal, not_forall, Classical.not_imp] at hnot
  obtain ⟨a, b, hab, hnab, ha, hb, hdiff⟩ := hnot
  by_cases hua : G.Adj u a
  · have hnub : ¬G.Adj u b := by
      intro hub
      exact hnab (hu (by simpa using hua) (by simpa using hub) hab)
    have hubNe : u ≠ b := by
      intro h
      subst b
      exact hnab hua.symm
    have hNuNb : G.neighborSet u ≠ G.neighborSet b := by
      intro hEq
      have haNu : a ∈ G.neighborSet u := hua
      have haNb : a ∈ G.neighborSet b := hEq ▸ haNu
      exact hnab haNb.symm
    exact ⟨b, hubNe, hnub, hb, hNuNb⟩
  · by_cases hNuNa : G.neighborSet u = G.neighborSet a
    · have hnub : ¬G.Adj u b := by
        intro hub
        have hbNu : b ∈ G.neighborSet u := hub
        have hbNa : b ∈ G.neighborSet a := hNuNa ▸ hbNu
        exact hnab hbNa
      have hubNe : u ≠ b := by
        intro h
        subst b
        exact hdiff hNuNa.symm
      have hNuNb : G.neighborSet u ≠ G.neighborSet b :=
        fun hEq ↦ hdiff (hNuNa.symm.trans hEq)
      exact ⟨b, hubNe, hnub, hb, hNuNb⟩
    · have huaNe : u ≠ a := by
        intro h
        subst a
        exact hNuNa rfl
      exact ⟨a, huaNe, hua, ha, hNuNa⟩

/-- An old member of the source neighbourhood class remains equal to the
source neighbourhood after a nonadjacent target is replaced by a copy. -/
theorem neighborSet_replaceVertex_of_mem_source_class
    {G : SimpleGraph V} {s t x : V} (hn : ¬G.Adj s t)
    (hdiff : G.neighborSet s ≠ G.neighborSet t)
    (hx : x ∈ neighborhoodClass G s) :
    (G.replaceVertex s t).neighborSet x = G.neighborSet s := by
  classical
  have hNx : G.neighborSet x = G.neighborSet s :=
    mem_neighborhoodClass.mp hx
  have hxt : x ≠ t := by
    intro h
    subst x
    exact hdiff hNx.symm
  ext z
  simp only [SimpleGraph.mem_neighborSet]
  by_cases hzt : z = t
  · subst z
    have hxs : ¬G.Adj x s := by
      intro hxs
      have hsNx : s ∈ G.neighborSet x := hxs
      have hsNs : s ∈ G.neighborSet s := hNx ▸ hsNx
      exact G.loopless.irrefl s hsNs
    simpa [SimpleGraph.replaceVertex, hxt, hn, hxs]
  · rw [G.adj_replaceVertex_iff_of_ne s hxt hzt]
    exact Set.ext_iff.mp hNx z

/-- Copying a largest simplicial neighbourhood class onto a different class
strictly increases the secondary termination measure. -/
theorem maxSimplicialClass_lt_replaceVertex
    {G : SimpleGraph V} {s t : V} (hn : ¬G.Adj s t)
    (hs : IsSimplicial G s)
    (hmax : maxSimplicialClass G = (neighborhoodClass G s).card)
    (hdiff : G.neighborSet s ≠ G.neighborSet t) :
    maxSimplicialClass G < maxSimplicialClass (G.replaceVertex s t) := by
  classical
  let H := G.replaceVertex s t
  have htSimp : IsSimplicial H t :=
    simplicial_target_of_simplicial_source G hn hs
  have htNotClass : t ∉ neighborhoodClass G s := by
    simpa only [mem_neighborhoodClass] using hdiff.symm
  have hsubset : insert t (neighborhoodClass G s) ⊆ neighborhoodClass H t := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact mem_neighborhoodClass.mpr rfl
    · rw [mem_neighborhoodClass]
      exact (neighborSet_replaceVertex_of_mem_source_class hn hdiff hx).trans
        (neighborSet_replaceVertex_target G hn).symm
  have hcard : (neighborhoodClass G s).card + 1 ≤
      (neighborhoodClass H t).card := by
    rw [← Finset.card_insert_of_notMem htNotClass]
    exact Finset.card_le_card hsubset
  have htoMax : (neighborhoodClass H t).card ≤ maxSimplicialClass H :=
    class_card_le_maxSimplicialClass htSimp
  dsimp only [H] at hcard htoMax ⊢
  omega

/-- Certified potential chosen graph by graph. -/
noncomputable def certifiedPotential
    (value : SimpleGraph V → ℚ) (G : SimpleGraph V) : ℚ := by
  classical
  exact potential G (value G)

/-- Lexicographic ascent score: potential first, largest simplicial class
second. -/
noncomputable def score (value : SimpleGraph V → ℚ) (G : SimpleGraph V)
    : ℚ ×ₗ ℕ :=
  toLex (certifiedPotential value G, maxSimplicialClass G)

/-- A legal strict ascent by one simplicial copy. -/
def ImprovingCopy (value : SimpleGraph V → ℚ)
    (G H : SimpleGraph V) : Prop :=
  ∃ s t : V, s ≠ t ∧ ¬G.Adj s t ∧ IsSimplicial G s ∧
    IsSimplicial G t ∧ H = G.replaceVertex s t ∧
      score value G < score value H

/-- Every nonterminal chordal graph admits a legal lexicographically
improving copy. -/
theorem exists_improvingCopy
    (value : SimpleGraph V → ℚ)
    (hcover : ∀ H : SimpleGraph V,
      IsCoverOptimum (G := H) (value H))
    {G : SimpleGraph V} [Nonempty V]
    (hchordal : IsChordal G) (hnot : ¬IsTerminal G) :
    ∃ H : SimpleGraph V, ImprovingCopy value G H := by
  classical
  obtain ⟨s, hs, hsmax, hlargest⟩ :=
    exists_maximal_simplicial_class hchordal
  obtain ⟨t, hst, hnst, ht, hdiff⟩ :=
    exists_different_simplicial_partner hnot hs
  let Hst := G.replaceVertex s t
  let Hts := G.replaceVertex t s
  have hcopy := potential_opposite_copy_inequality G hnst
    (hcover G) (hcover Hst) (hcover Hts)
  by_cases hprimary : certifiedPotential value G < certifiedPotential value Hst
  · refine ⟨Hst, s, t, hst, hnst, hs, ht, rfl, ?_⟩
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hprimary)
  · have hstLe : certifiedPotential value Hst ≤ certifiedPotential value G :=
      le_of_not_gt hprimary
    by_cases heq : certifiedPotential value Hst = certifiedPotential value G
    · refine ⟨Hst, s, t, hst, hnst, hs, ht, rfl, ?_⟩
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨heq.symm,
        maxSimplicialClass_lt_replaceVertex hnst hs hsmax hdiff⟩
      )
    · have hstrictSt : certifiedPotential value Hst < certifiedPotential value G :=
        lt_of_le_of_ne hstLe heq
      have hstrictTs : certifiedPotential value G < certifiedPotential value Hts := by
        unfold certifiedPotential at hcopy hstrictSt ⊢
        dsimp only [Hst, Hts] at hcopy hstrictSt ⊢
        exact right_strict_of_two_le_sum hcopy hstrictSt
      refine ⟨Hts, t, s, hst.symm, ?_, ht, hs, rfl, ?_⟩
      · simpa only [SimpleGraph.adj_comm] using hnst
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hstrictTs)

/-- Reflexive-transitive reachability by improving single-vertex copies. -/
def ImprovingReachable (value : SimpleGraph V → ℚ)
    (G H : SimpleGraph V) : Prop :=
  Relation.ReflTransGen (ImprovingCopy value) G H

/-- Every graph reachable by improving simplicial copies from a chordal graph
is chordal. -/
theorem chordal_of_improvingReachable
    (value : SimpleGraph V → ℚ) {G H : SimpleGraph V}
    (hG : IsChordal G) (hreach : ImprovingReachable value G H) :
    IsChordal H := by
  induction hreach with
  | refl => exact hG
  | tail hprev hstep ih =>
      obtain ⟨s, t, -, -, hs, -, rfl, -⟩ := hstep
      exact chordal_replaceVertex_of_simplicial_source
        (G := _) (s := s) (t := t) ih hs

/-- The primary coordinate of the score is nondecreasing at every improving
copy. -/
theorem certifiedPotential_le_of_improvingCopy
    {value : SimpleGraph V → ℚ} {G H : SimpleGraph V}
    (h : ImprovingCopy value G H) :
    certifiedPotential value G ≤ certifiedPotential value H := by
  obtain ⟨s, t, -, -, -, -, -, hscore⟩ := h
  rw [score, score, Prod.Lex.toLex_lt_toLex] at hscore
  rcases hscore with hstrict | ⟨heq, -⟩
  · exact hstrict.le
  · exact heq.le

/-- A concrete natural-number-indexed path extracted from improvement
reachability.  Values after `length` are irrelevant. -/
structure FinePath (value : SimpleGraph V → ℚ)
    (G H : SimpleGraph V) where
  length : ℕ
  graph : ℕ → SimpleGraph V
  start : graph 0 = G
  finish : graph length = H
  step : ∀ i : ℕ, i < length → ImprovingCopy value (graph i) (graph (i + 1))

/-- The certified potential is nondecreasing along a concrete fine path. -/
theorem FinePath.certifiedPotential_le
    {value : SimpleGraph V → ℚ} {G H : SimpleGraph V}
    (P : FinePath value G H) :
    certifiedPotential value G ≤ certifiedPotential value H := by
  have hprefix : ∀ i : ℕ, i ≤ P.length →
      certifiedPotential value (P.graph 0) ≤
        certifiedPotential value (P.graph i) := by
    intro i hi
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
        exact (ih (by omega)).trans
          (certifiedPotential_le_of_improvingCopy (P.step i (by omega)))
  simpa only [P.start, P.finish] using hprefix P.length le_rfl

/-- Every reflexive-transitive improvement witness has a concrete fine path. -/
theorem finePath_of_improvingReachable
    (value : SimpleGraph V → ℚ) {G H : SimpleGraph V}
    (hreach : ImprovingReachable value G H) :
    Nonempty (FinePath value G H) := by
  induction hreach with
  | refl =>
      exact ⟨⟨0, fun _ ↦ G, rfl, rfl, by omega⟩⟩
  | @tail B C hGB hBC ih =>
      obtain ⟨P⟩ := ih
      let next : ℕ → SimpleGraph V := fun i ↦
        if i ≤ P.length then P.graph i else C
      refine ⟨⟨P.length + 1, next, ?_, ?_, ?_⟩⟩
      · simp [next]
        exact P.start
      · simp [next]
      · intro i hi
        by_cases hilast : i = P.length
        · subst i
          simpa [next, P.finish] using hBC
        · have hiold : i < P.length := by omega
          have hi1 : i + 1 ≤ P.length := by omega
          simpa [next, hiold.le, hi1] using P.step i hiold

/-- The finite set of graphs reachable through strict score ascents. -/
noncomputable def reachableGraphs (value : SimpleGraph V → ℚ)
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter fun H ↦ ImprovingReachable value G H

theorem mem_reachableGraphs {value : SimpleGraph V → ℚ}
    {G H : SimpleGraph V} :
    H ∈ reachableGraphs value G ↔ ImprovingReachable value G H := by
  classical
  simp [reachableGraphs]

/-- Finite lexicographic ascent terminates at a terminal chordal graph. -/
theorem exists_terminal_reachable
    (value : SimpleGraph V → ℚ)
    (hcover : ∀ H : SimpleGraph V,
      IsCoverOptimum (G := H) (value H))
    {G : SimpleGraph V} [Nonempty V] (hchordal : IsChordal G) :
    ∃ H : SimpleGraph V,
      ImprovingReachable value G H ∧ IsTerminal H := by
  classical
  have hnonempty : (reachableGraphs value G).Nonempty := by
    refine ⟨G, mem_reachableGraphs.mpr ?_⟩
    exact Relation.ReflTransGen.refl
  obtain ⟨H, hHmem, hmax⟩ := Finset.exists_max_image
    (reachableGraphs value G) (score value) hnonempty
  have hreach : ImprovingReachable value G H := mem_reachableGraphs.mp hHmem
  refine ⟨H, hreach, ?_⟩
  by_contra hnot
  have hHchordal := chordal_of_improvingReachable value hchordal hreach
  obtain ⟨H', hstep⟩ := exists_improvingCopy value hcover hHchordal hnot
  have hreach' : ImprovingReachable value G H' := hreach.tail hstep
  have hH'mem : H' ∈ reachableGraphs value G :=
    mem_reachableGraphs.mpr hreach'
  exact (not_lt_of_ge (hmax H' hH'mem))
    (by obtain ⟨_, _, _, _, _, _, _, hs⟩ := hstep; exact hs)

/-- Fine monotone symmetrization to a labelled complete-split graph. -/
theorem exists_completeSplit_finePath
    (value : SimpleGraph V → ℚ)
    (hcover : ∀ H : SimpleGraph V,
      IsCoverOptimum (G := H) (value H))
    {G : SimpleGraph V} [Nonempty V] (hchordal : IsChordal G) :
    ∃ H : SimpleGraph V,
      Nonempty (FinePath value G H) ∧ IsCompleteSplit H := by
  classical
  obtain ⟨H, hreach, hterminal⟩ :=
    exists_terminal_reachable value hcover hchordal
  exact ⟨H, finePath_of_improvingReachable value hreach,
    isCompleteSplit_of_terminal
      (chordal_of_improvingReachable value hchordal hreach) hterminal⟩

end Symmetrization
end Erdos81
