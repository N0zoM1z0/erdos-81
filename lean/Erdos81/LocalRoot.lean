import Erdos81.PEOExistence
import Erdos81.RootDistance

/-!
# Extracting a balanced clique root from split edit distance

A chordal graph which is close to the balanced complete-split family has a
large clique inside a nearest template root.  Chordality supplies the missing
pair bound through a perfect elimination order; the edit-distance identities
then control both rooted defects.
-/

namespace Erdos81
namespace LocalRoot

open EditDistance RootedGraph RootDistance

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A nearest member of the balanced complete-split family can be represented
by its clique side. -/
theorem exists_nearestSplitRoot (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ A : Finset V, A.card = Fintype.card V / 3 ∧
      edgeEditDistance G (completeSplitGraph A) = splitEditDistance G := by
  classical
  obtain ⟨T, hT, hmin⟩ :=
    exists_distanceToFamily_minimizer G splitTemplates splitTemplates_nonempty
  obtain ⟨A, hAcard, hTA⟩ := mem_splitTemplates.mp hT
  subst T
  exact ⟨A, hAcard, hmin⟩

/-- Inside a nonempty set, a maximum induced clique satisfies the chordal PEO
missing-pair bound. -/
theorem exists_peoCliqueRoot (G : SimpleGraph V)
    [DecidableRel G.Adj] (hchordal : IsChordal G) (A : Finset V)
    (hApos : 0 < A.card) :
    ∃ P : Finset V,
      P ⊆ A ∧
      G.IsClique (P : Set V) ∧
      Nat.choose (A.card - P.card + 1) 2 ≤
        (G.induce (A : Set V))ᶜ.edgeFinset.card := by
  classical
  obtain ⟨K, hK⟩ :=
    (G.induce (A : Set V)).exists_isNClique_cliqueNum
  let inclusion : A ↪ V := Function.Embedding.subtype _
  let P : Finset V := K.map inclusion
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hApos
  have hJpos : 1 ≤ (G.induce (A : Set V)).cliqueNum := by
    have hsingleton : (G.induce (A : Set V)).IsClique
        (({⟨x, hx⟩} : Finset A) : Set A) := by
      simp
    have hcard := hsingleton.card_le_cliqueNum
    simpa using hcard
  have hJcard : (G.induce (A : Set V)).cliqueNum ≤ Fintype.card A := by
    rw [← hK.card_eq]
    exact Finset.card_le_univ K
  have hJchordal : IsChordal (G.induce (A : Set V)) := by
    exact Chordal.induce_isChordal G hchordal (A : Set V)
  have hJclique : ∀ L : Finset A,
      (G.induce (A : Set V)).IsClique (L : Set A) →
        L.card ≤ (G.induce (A : Set V)).cliqueNum := by
    intro L hL
    exact hL.card_le_cliqueNum
  have hmissingJ :
      Nat.choose
          (Fintype.card A - (G.induce (A : Set V)).cliqueNum + 1) 2 ≤
        (G.induce (A : Set V))ᶜ.edgeFinset.card :=
    PEOExistence.complement_edge_bound_of_chordal_finite
      hJpos hJcard hJchordal hJclique
  have hPcard : P.card = (G.induce (A : Set V)).cliqueNum := by
    dsimp only [P]
    rw [Finset.card_map, hK.card_eq]
  have hPA : P ⊆ A := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
    exact v'.property
  have hPclique : G.IsClique (P : Set V) := by
    intro u hu v hv huv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
    have huv' : u' ≠ v' := by
      intro h
      exact huv (congrArg inclusion h)
    exact hK.isClique hu' hv' huv'
  have hmissing : Nat.choose (A.card - P.card + 1) 2 ≤
      (G.induce (A : Set V))ᶜ.edgeFinset.card := by
    calc
      Nat.choose (A.card - P.card + 1) 2 =
          Nat.choose
            (Fintype.card A - (G.induce (A : Set V)).cliqueNum + 1) 2 := by
        rw [Fintype.card_coe, hPcard]
      _ ≤ (G.induce (A : Set V))ᶜ.edgeFinset.card := hmissingJ
  exact ⟨P, hPA, hPclique, hmissing⟩

/-- Convert the induced missing-pair certificate into edit-distance and
rooted-defect bounds. -/
theorem cliqueRoot_distance_bounds (G : SimpleGraph V)
    [DecidableRel G.Adj] {P A : Finset V} (hPA : P ⊆ A)
    (hPclique : G.IsClique (P : Set V))
    (hmissing : Nat.choose (A.card - P.card + 1) 2 ≤
      (G.induce (A : Set V))ᶜ.edgeFinset.card) :
    Nat.choose (A.card - P.card + 1) 2 ≤
        edgeEditDistance G (completeSplitGraph A) ∧
      (outsideEdges G P).card + missingIncidences G P ≤
        edgeEditDistance G (completeSplitGraph A) +
          (A.card - P.card) * Fintype.card V := by
  constructor
  · exact hmissing.trans (induced_complement_edges_le_distance G A)
  · rw [← edgeEditDistance_completeSplitGraph G P hPclique]
    calc
      edgeEditDistance G (completeSplitGraph P) ≤
          edgeEditDistance G (completeSplitGraph A) +
            edgeEditDistance (completeSplitGraph A)
              (completeSplitGraph P) :=
        edgeEditDistance_triangle _ _ _
      _ ≤ edgeEditDistance G (completeSplitGraph A) +
          (A.card - P.card) * Fintype.card V :=
        Nat.add_le_add_left
          (edgeEditDistance_nested_completeSplitGraph_le hPA) _

/-- A fixed nonempty template root contains a clique with both local
edit-distance bounds. -/
theorem exists_cliqueRoot_in_template (G : SimpleGraph V)
    [DecidableRel G.Adj] (hchordal : IsChordal G) (A : Finset V)
    (hApos : 0 < A.card) :
    ∃ P : Finset V,
      P ⊆ A ∧
      G.IsClique (P : Set V) ∧
      Nat.choose (A.card - P.card + 1) 2 ≤
        edgeEditDistance G (completeSplitGraph A) ∧
      (outsideEdges G P).card + missingIncidences G P ≤
        edgeEditDistance G (completeSplitGraph A) +
          (A.card - P.card) * Fintype.card V := by
  obtain ⟨P, hPA, hPclique, hmissing⟩ :=
    exists_peoCliqueRoot G hchordal A hApos
  obtain ⟨hdistance, hdefect⟩ :=
    cliqueRoot_distance_bounds G hPA hPclique hmissing
  exact ⟨P, hPA, hPclique, hdistance, hdefect⟩

/-- Structural local-root extraction, before numerical constants are applied.
The root `P` is a maximum clique in the graph induced by a nearest balanced
split-template root `A`. -/
theorem exists_initialRoot (G : SimpleGraph V) [DecidableRel G.Adj]
    (hchordal : IsChordal G) (hn : 3 ≤ Fintype.card V) :
    ∃ A P : Finset V,
      A.card = Fintype.card V / 3 ∧
      P ⊆ A ∧
      G.IsClique (P : Set V) ∧
      Nat.choose (A.card - P.card + 1) 2 ≤ splitEditDistance G ∧
      (outsideEdges G P).card + missingIncidences G P ≤
        splitEditDistance G +
          (A.card - P.card) * Fintype.card V := by
  obtain ⟨A, hAcard, hmin⟩ := exists_nearestSplitRoot G
  have hApos : 0 < A.card := by
    rw [hAcard]
    omega
  obtain ⟨P, hPA, hPclique, hmissing, hdefect⟩ :=
    exists_cliqueRoot_in_template G hchordal A hApos
  rw [hmin] at hmissing hdefect
  exact ⟨A, P, hAcard, hPA, hPclique, hmissing, hdefect⟩

end LocalRoot
end Erdos81
