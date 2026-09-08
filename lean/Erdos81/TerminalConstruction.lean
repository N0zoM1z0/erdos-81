import Erdos81.TerminalPacking
import Mathlib.Tactic

/-!
# The quantitative terminal construction

This module assembles the finite combinatorial construction around a root
clique.  Starting with a bounded proper colouring of the outside graph, it
selects the largest colour classes, assigns them to root vertices by the
deterministic averaging lemma, applies the Häggkvist--Janssen interface to the
actual remaining host lists, and completes the resulting edge-disjoint
triangles to a clique partition.

The conclusion records the two identities needed later without division:

* exact edge accounting for the completed partition; and
* the denominator-cleared lower bound for retained outside triangles.
-/

namespace Erdos81
namespace TerminalConstruction

open MixedModel ExternalInputs EdgeColoring RootedGraph RootedPEO
  TerminalAssignment RootHostLists

attribute [-instance] MixedModel.resourceFintype

variable {V Color : Type} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- A certificate returned by the terminal construction.  The equation
`accounting` is the subtraction-free form of

`Q.size = p*q - choose(p,2) + m - A - 2*f`.

The inequality `retained_lower` is the subtraction-free form of

`f >= p*m/c - (w-1)*A/p`.
-/
structure Certificate {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finset V) (c : ℕ) where
  partition : CliquePartition G
  orderAtMost : partition.OrderAtMost 3
  retained : ℕ
  accounting :
    partition.size + 2 * (retained + Nat.choose P.card 2) +
        missingIncidences G P =
      Nat.choose P.card 2 + P.card * (outsideVertices P).card +
        (outsideEdges G P).card
  retained_lower :
    P.card * P.card * Nat.card (Resource (outsideGraph G P)) ≤
      c * P.card * retained +
        c * (((outsideGraph G P).cliqueNum - 1) *
          missingIncidences G P)

/-- The full terminal witness construction from a bounded outside-edge
colouring.  No probabilistic choice remains in the statement or proof. -/
theorem exists_certificate_of_bounded_coloring
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hHJ : HaggkvistJanssenInput)
    (P : Finset V) (hClique : G.IsClique (P : Set V))
    (O : RootedPEO.Order G P)
    {t : ℕ} (C : BoundedColoring (outsideGraph G P) Color t)
    (hp : 0 < P.card)
    (hcolors : P.card ≤ Fintype.card Color)
    (hhost : P.card + 2 * maxMissingColumn G P + 4 * t ≤
      (outsideVertices P).card) :
    Nonempty (Certificate (G := G) P (Fintype.card Color)) := by
  classical
  obtain ⟨S, hScard, hselected⟩ :=
    exists_large_selected_palette C.toProper P.card hcolors
  obtain ⟨assign, hcharge⟩ :=
    exists_assignment_with_charge O C.toProper S P.card hScard rfl hp
  obtain ⟨R, hR⟩ :=
    exists_root_host_coloring hHJ P O C S assign hhost
  let pack := TerminalPacking.packing hClique hR
  obtain ⟨Q, hQorder, hQsize⟩ := TrianglePacking.exists_partition pack
  let f := (retainedAssignedEdges O C.toProper S assign).card
  have hpackCard : pack.triangles.card = f + Nat.choose P.card 2 := by
    simpa [pack, f] using TerminalPacking.card_packing hClique hR
  have hgain : 2 * pack.triangles.card ≤ G.edgeFinset.card := by
    simpa [TrianglePacking.gain_toMixed] using
      IntegralPacking.gain_le_card_edges (TrianglePacking.toMixed pack)
  have hsizeAdd : Q.size + 2 * pack.triangles.card = G.edgeFinset.card := by
    omega
  have hmissing : missingIncidences G P ≤
      P.card * (outsideVertices P).card := by
    have hcross := crossing_add_missing G P
    omega
  have hedgeAdd : G.edgeFinset.card + missingIncidences G P =
      Nat.choose P.card 2 + P.card * (outsideVertices P).card +
        (outsideEdges G P).card := by
    have hedge := edge_count_identity G P hClique
    omega
  refine ⟨⟨Q, hQorder, f, ?_, ?_⟩⟩
  · rw [← hedgeAdd, ← hsizeAdd, hpackCard]
  · exact retained_count_lower_cleared O C.toProper S assign
      P.card (Fintype.card Color) (Nat.card (Resource (outsideGraph G P)))
      rfl hselected hcharge

end TerminalConstruction
end Erdos81
