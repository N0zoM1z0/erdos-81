import Erdos81.CliquePartitionCounting
import Erdos81.CompleteSplit
import Erdos81.PerfectElimination
import Erdos81.SharpBound
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# The complete-split lower-bound witness

This module formalizes the signed edge-count behind the sharpness example.
Root edges have weight `-1` and spokes have weight `+1`.  Every clique has
total weight at most one, so every clique partition has at least the total
weight of the graph.  Choosing the root order nearest to `(2n+1)/6` gives
exactly `sharpBound n`.
-/

open scoped BigOperators

namespace Erdos81
namespace CompleteSplitLowerBound

open SimpleGraph CompleteSplit CliquePartitionCounting EditDistance RootedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private def IsRootEdge (K : Finset V) (e : Sym2 V) : Prop :=
  e.toFinset ⊆ K

private instance (K : Finset V) : DecidablePred (IsRootEdge K) :=
  fun e ↦ inferInstanceAs (Decidable (e.toFinset ⊆ K))

private theorem filtered_root_blockEdges_eq (K L : Finset V) :
    ((blockEdges (completeSplitGraph K) L).filter (IsRootEdge K)) =
      blockEdges (completeSplitGraph K) (L ∩ K) := by
  classical
  ext e
  simp only [blockEdges, IsRootEdge, Finset.mem_filter]
  constructor
  · rintro ⟨⟨he, heL⟩, heK⟩
    exact ⟨he, fun x hx ↦ Finset.mem_inter.mpr ⟨heL hx, heK hx⟩⟩
  · rintro ⟨he, heLK⟩
    exact ⟨⟨he, fun x hx ↦ (Finset.mem_inter.mp (heLK hx)).1⟩,
      fun x hx ↦ (Finset.mem_inter.mp (heLK hx)).2⟩

private theorem card_filtered_root_blockEdges (K L : Finset V)
    (hL : (completeSplitGraph K).IsClique (L : Set V)) :
    ((blockEdges (completeSplitGraph K) L).filter (IsRootEdge K)).card =
      Nat.choose (L ∩ K).card 2 := by
  rw [filtered_root_blockEdges_eq]
  exact card_blockEdges (L ∩ K)
    (hL.subset fun _ hx ↦ (Finset.mem_inter.mp hx).1)

private theorem card_filtered_root_edges (K : Finset V) :
    ((completeSplitGraph K).edgeFinset.filter (IsRootEdge K)).card =
      Nat.choose K.card 2 := by
  classical
  have heq :
      (completeSplitGraph K).edgeFinset.filter (IsRootEdge K) =
        blockEdges (completeSplitGraph K) K := by
    ext e
    simp [blockEdges, IsRootEdge]
  rw [heq]
  exact card_blockEdges K (root_isClique K)

private theorem le_one_add_choose_two (r : ℕ) :
    r ≤ 1 + Nat.choose r 2 := by
  cases r with
  | zero => simp
  | succ r =>
      rw [Nat.choose_succ_succ]
      simp
      omega

private theorem choose_card_le_one_add_twice_inter (K L : Finset V)
    (hout : (L \ K).card ≤ 1) :
    Nat.choose L.card 2 ≤ 1 + 2 * Nat.choose (L ∩ K).card 2 := by
  have hcard := Finset.card_inter_add_card_sdiff L K
  interval_cases h : (L \ K).card
  · have hLK : L.card = (L ∩ K).card := by omega
    rw [hLK]
    omega
  · have hLK : L.card = (L ∩ K).card + 1 := by omega
    have hr := le_one_add_choose_two (L ∩ K).card
    calc
      Nat.choose L.card 2 =
          (L ∩ K).card + Nat.choose (L ∩ K).card 2 := by
        rw [hLK, Nat.choose_succ_succ']
        simp
      _ ≤ 1 + 2 * Nat.choose (L ∩ K).card 2 := by omega

private theorem block_spokes_le_one_add_rootEdges (K L : Finset V)
    (hL : (completeSplitGraph K).IsClique (L : Set V)) :
    ((blockEdges (completeSplitGraph K) L).filter
        (fun e ↦ ¬ IsRootEdge K e)).card ≤
      1 + ((blockEdges (completeSplitGraph K) L).filter
        (IsRootEdge K)).card := by
  classical
  let B := blockEdges (completeSplitGraph K) L
  have hsplit := Finset.card_filter_add_card_filter_not (s := B) (IsRootEdge K)
  have htotal : B.card = Nat.choose L.card 2 := card_blockEdges L hL
  have hroot : (B.filter (IsRootEdge K)).card =
      Nat.choose (L ∩ K).card 2 := card_filtered_root_blockEdges K L hL
  have hout := (isClique_iff_card_sdiff_le_one K L).mp hL
  have hchoose := choose_card_le_one_add_twice_inter K L hout
  dsimp only [B] at hsplit htotal hroot ⊢
  omega

/-- In a complete-split graph, the number of spoke edges is at most the
number of partition blocks plus the number of root edges. -/
theorem spokeEdges_le_size_add_rootEdges (K : Finset V)
    (P : CliquePartition (completeSplitGraph K)) :
    ((completeSplitGraph K).edgeFinset.filter
        (fun e ↦ ¬ IsRootEdge K e)).card ≤
      P.size + ((completeSplitGraph K).edgeFinset.filter
        (IsRootEdge K)).card := by
  classical
  have hsum :
      (∑ L ∈ P.blocks,
        ((blockEdges (completeSplitGraph K) L).filter
          (fun e ↦ ¬ IsRootEdge K e)).card) ≤
      ∑ L ∈ P.blocks,
        (1 + ((blockEdges (completeSplitGraph K) L).filter
          (IsRootEdge K)).card) := by
    apply Finset.sum_le_sum
    intro L hL
    exact block_spokes_le_one_add_rootEdges K L (P.isClique L hL)
  have hroot := sum_card_filtered_blockEdges P (IsRootEdge K)
  calc
    ((completeSplitGraph K).edgeFinset.filter
        (fun e ↦ ¬ IsRootEdge K e)).card =
        ∑ L ∈ P.blocks,
          ((blockEdges (completeSplitGraph K) L).filter
            (fun e ↦ ¬ IsRootEdge K e)).card :=
      (sum_card_filtered_blockEdges P (fun e ↦ ¬ IsRootEdge K e)).symm
    _ ≤ ∑ L ∈ P.blocks,
        (1 + ((blockEdges (completeSplitGraph K) L).filter
          (IsRootEdge K)).card) := hsum
    _ = P.blocks.card + ∑ L ∈ P.blocks,
        ((blockEdges (completeSplitGraph K) L).filter
          (IsRootEdge K)).card := by
      simp [Finset.sum_add_distrib]
    _ = P.size + ((completeSplitGraph K).edgeFinset.filter
        (IsRootEdge K)).card := by
      rw [hroot]
      rfl

private theorem card_filtered_spoke_edges (K : Finset V) :
    ((completeSplitGraph K).edgeFinset.filter
        (fun e ↦ ¬ IsRootEdge K e)).card =
      K.card * (Fintype.card V - K.card) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (completeSplitGraph K).edgeFinset) (IsRootEdge K)
  rw [card_filtered_root_edges K, CompleteSplit.card_edgeFinset K] at hsplit
  omega

/-- The signed-count lower bound for every clique partition of a labelled
complete-split graph. -/
theorem partition_size_ge (K : Finset V)
    (P : CliquePartition (completeSplitGraph K)) :
    K.card * (Fintype.card V - K.card) - Nat.choose K.card 2 ≤ P.size := by
  have h := spokeEdges_le_size_add_rootEdges K P
  rw [card_filtered_spoke_edges K, card_filtered_root_edges K] at h
  omega

section FinWitness

private theorem finalSegment_isPEO {n : ℕ} (t : Fin n) :
    PerfectElimination.IsPEO (completeSplitGraph (Finset.Ici t)) := by
  classical
  intro i x hx y hy hxy
  have hix : i < x := Finset.mem_Ioi.mp (Finset.mem_filter.mp hx).1
  have hixAdj : (completeSplitGraph (Finset.Ici t)).Adj i x :=
    (Finset.mem_filter.mp hx).2
  have hxRoot : x ∈ Finset.Ici t := by
    by_cases hiRoot : i ∈ Finset.Ici t
    · exact Finset.mem_Ici.mpr ((Finset.mem_Ici.mp hiRoot).trans hix.le)
    · exact ((completeSplitGraph_adj (Finset.Ici t) i x).mp hixAdj).2.resolve_left hiRoot
  exact (completeSplitGraph_adj (Finset.Ici t) x y).mpr
    ⟨hxy, Or.inl hxRoot⟩

private theorem extremal_arithmetic (n : ℕ) (hn : 2 ≤ n) :
    let k := (n + 1) / 3
    k * (n - k) - Nat.choose k 2 = sharpBound n := by
  let k := (n + 1) / 3
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hkn : k ≤ n := by dsimp only [k]; omega
  have hkout : k ≤ n - k := by dsimp only [k]; omega
  have hchooseSquare : Nat.choose k 2 ≤ k * k := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans
      (Nat.mul_le_mul_left k (Nat.sub_le k 1))
  have hchoose : Nat.choose k 2 ≤ k * (n - k) :=
    hchooseSquare.trans (Nat.mul_le_mul_left k hkout)
  let f := k * (n - k) - Nat.choose k 2
  have hcast : (f : ℚ) = Arithmetic.splitFirstBranch n k := by
    dsimp only [f]
    rw [Nat.cast_sub hchoose, Nat.cast_mul, Nat.cast_sub hkn,
      Nat.cast_choose_two]
    simp only [Arithmetic.splitFirstBranch]
  let r := (n + 1) % 3
  have hr : r < 3 := by dsimp only [r]; omega
  have hdivision : n + 1 = r + 3 * k := by
    dsimp only [r, k]
    omega
  have hdivisionQ : (n : ℚ) + 1 = r + 3 * k := by
    exact_mod_cast hdivision
  have hdLower : (-3 : ℚ) ≤ 6 * (k : ℚ) - 2 * n - 1 := by
    have hrQ : (r : ℚ) ≤ 2 := by exact_mod_cast (show r ≤ 2 by omega)
    linarith
  have hdUpper : 6 * (k : ℚ) - 2 * n - 1 ≤ 1 := by
    have hrQ : (0 : ℚ) ≤ r := by positivity
    linarith
  have hdSquare : (6 * (k : ℚ) - 2 * n - 1) ^ 2 ≤ 9 := by
    have hleft : 0 ≤ (6 * (k : ℚ) - 2 * n - 1) + 3 := by linarith
    have hright : 0 ≤ 3 - (6 * (k : ℚ) - 2 * n - 1) := by linarith
    nlinarith [mul_nonneg hleft hright]
  have hfLeQ : (f : ℚ) ≤ Arithmetic.Q n := by
    rw [hcast]
    exact Arithmetic.splitFirstBranch_le_Q n k
  have hQLt : Arithmetic.Q n < (f : ℚ) + 1 := by
    rw [hcast]
    nlinarith [Arithmetic.square_identity (n : ℚ) (k : ℚ)]
  have hfloor : ⌊Arithmetic.Q (n : ℚ)⌋₊ = f :=
    (Nat.floor_eq_iff (show 0 ≤ Arithmetic.Q (n : ℚ) by
      simp only [Arithmetic.Q]
      positivity)).2 ⟨hfLeQ, hQLt⟩
  exact (hfloor.symm.trans (SharpBound.floor_Q_eq_sharpBound n))

/-- For every order at least two there is a chordal complete-split graph on
`Fin n` whose every clique partition has at least `sharpBound n` blocks. -/
theorem exists_completeSplit_sharp_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ G : SimpleGraph (Fin n), IsChordal G ∧
      ∀ P : CliquePartition G, sharpBound n ≤ P.size := by
  let k := (n + 1) / 3
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hkn : k ≤ n := by dsimp only [k]; omega
  let t : Fin n := ⟨n - k, by omega⟩
  let K : Finset (Fin n) := Finset.Ici t
  have hKcard : K.card = k := by
    dsimp only [K, t]
    simp
    omega
  refine ⟨completeSplitGraph K,
    PerfectElimination.isChordal_of_peo (finalSegment_isPEO t), ?_⟩
  intro P
  have hlower := partition_size_ge K P
  rw [hKcard] at hlower
  have hexact := extremal_arithmetic n hn
  dsimp only [k] at hexact
  rw [← hexact]
  simpa only [Fintype.card_fin] using hlower

end FinWitness

end CompleteSplitLowerBound
end Erdos81
