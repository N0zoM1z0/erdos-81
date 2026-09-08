import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# The exact statement of Erdős Problem 81

This file fixes the finite-graph model used by the formalization.  A chordal
graph is defined by the forbidden-induced-cycle characterization: it has no
induced copy of the cycle graph `C_k` for any `k >= 4`.

A clique partition is a finite family of nontrivial vertex sets, each inducing
a clique, such that every edge belongs to exactly one member of the family.
The original asymptotic assertion is stated with denominators cleared.  Thus
`6 * P.size <= n^2 + C*n` is exactly an `n^2 / 6 + O(n)` upper bound, with an
inessential rescaling of the absolute constant.
-/

open scoped SimpleGraph

namespace Erdos81

/-- A graph is chordal when it has no induced cycle of length at least four. -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 4 ≤ k → ¬(SimpleGraph.cycleGraph k ⊴ G)

/-- A partition of the edge set of `G` into nontrivial complete subgraphs. -/
structure CliquePartition {V : Type*} [DecidableEq V] (G : SimpleGraph V) where
  /-- The vertex sets of the complete subgraphs. -/
  blocks : Finset (Finset V)
  /-- Empty and singleton blocks are excluded. -/
  nontrivial : ∀ K ∈ blocks, 2 ≤ K.card
  /-- Every block spans a clique. -/
  isClique : ∀ K ∈ blocks, G.IsClique (K : Set V)
  /-- Every graph edge occurs in exactly one block. -/
  coversOnce : ∀ ⦃u v : V⦄, G.Adj u v →
    ∃! K : Finset V, K ∈ blocks ∧ u ∈ K ∧ v ∈ K

namespace CliquePartition

/-- The number of cliques in a clique partition. -/
def size {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (P : CliquePartition G) : ℕ :=
  P.blocks.card

/-- All blocks in the partition have order at most `r`. -/
def OrderAtMost {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (P : CliquePartition G) (r : ℕ) : Prop :=
  ∀ K ∈ P.blocks, K.card ≤ r

end CliquePartition

/-- The integer target `floor(n(n+1)/6)` proved for all sufficiently large `n`. -/
def sharpBound (n : ℕ) : ℕ :=
  n * (n + 1) / 6

/--
The stronger upper bound established by the manuscript: eventually every
chordal graph has a clique partition of size at most `floor(n(n+1)/6)`, using
only cliques of orders two, three, and four.
-/
def EventualSharpUpperBound : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin n), IsChordal G →
    ∃ P : CliquePartition G,
      P.OrderAtMost 4 ∧ P.size ≤ sharpBound n

/--
The exact eventual extremal statement.  The first conjunct is the universal
upper bound; the second supplies a chordal witness for which every clique
partition has at least the target number of blocks.
-/
def EventualSharpEquality : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (∀ G : SimpleGraph (Fin n), IsChordal G →
      ∃ P : CliquePartition G, P.size ≤ sharpBound n) ∧
    (∃ G : SimpleGraph (Fin n), IsChordal G ∧
      ∀ P : CliquePartition G, sharpBound n ≤ P.size)

/--
Erdős Problem 81, with the denominator cleared and the absolute linear
constant correspondingly rescaled.
-/
def Erdos81Statement : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), IsChordal G →
    ∃ P : CliquePartition G, 6 * P.size ≤ n * n + C * n

section PairPartition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The fallback partition that treats every edge as a two-vertex clique. -/
noncomputable def pairPartition (G : SimpleGraph V) : CliquePartition G := by
  classical
  let B : Finset (Finset V) :=
    (Finset.univ.powersetCard 2).filter fun K : Finset V ↦ G.IsClique (K : Set V)
  refine
    { blocks := B
      nontrivial := ?_
      isClique := ?_
      coversOnce := ?_ }
  · intro K hK
    have hK' : K ∈ (Finset.univ.powersetCard 2).filter
        (fun L : Finset V ↦ G.IsClique (L : Set V)) := by
      simpa [B] using hK
    exact ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hK').1).2).ge
  · intro K hK
    have hK' : K ∈ (Finset.univ.powersetCard 2).filter
        (fun L : Finset V ↦ G.IsClique (L : Set V)) := by
      simpa [B] using hK
    exact (Finset.mem_filter.mp hK').2
  · intro u v huv
    have huv_ne : u ≠ v := huv.ne
    refine ⟨{u, v}, ?_, ?_⟩
    · constructor
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp [huv_ne]⟩
        · simpa using (SimpleGraph.isClique_pair.mpr fun _ ↦ huv)
      · simp
    · intro K hK
      have hK' : K ∈ (Finset.univ.powersetCard 2).filter
          (fun L : Finset V ↦ G.IsClique (L : Set V)) := by
        simpa [B] using hK.1
      have hKcard : K.card = 2 :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hK').1).2
      have hsubset : {u, v} ⊆ K := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hK.2.1
        · exact hK.2.2
      have hEq : {u, v} = K :=
        Finset.eq_of_subset_of_card_le hsubset (by simp [hKcard, huv_ne])
      exact hEq.symm

theorem pairPartition_size_le_choose (G : SimpleGraph V) :
    (pairPartition G).size ≤ Nat.choose (Fintype.card V) 2 := by
  classical
  change ((Finset.univ.powersetCard 2).filter
    (fun K : Finset V ↦ G.IsClique (K : Set V))).card ≤ Nat.choose (Fintype.card V) 2
  calc
    ((Finset.univ.powersetCard 2).filter
      (fun K : Finset V ↦ G.IsClique (K : Set V))).card ≤
        (Finset.univ.powersetCard 2).card := Finset.card_filter_le _ _
    _ = Nat.choose (Fintype.card V) 2 := by simp

theorem pairPartition_size_le_square (G : SimpleGraph V) :
    (pairPartition G).size ≤ Fintype.card V * Fintype.card V := by
  calc
    (pairPartition G).size ≤ Nat.choose (Fintype.card V) 2 :=
      pairPartition_size_le_choose G
    _ = Fintype.card V * (Fintype.card V - 1) / 2 :=
      Nat.choose_two_right (Fintype.card V)
    _ ≤ Fintype.card V * (Fintype.card V - 1) := Nat.div_le_self _ _
    _ ≤ Fintype.card V * Fintype.card V :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end PairPartition

/-- The manuscript's eventual sharp upper bound implies the original problem. -/
theorem eventualSharpUpperBound_implies_erdos81 :
    EventualSharpUpperBound → Erdos81Statement := by
  rintro ⟨N, hN⟩
  refine ⟨5 * N + 1, ?_⟩
  intro n G hG
  by_cases hn : N ≤ n
  · obtain ⟨P, -, hP⟩ := hN n hn G hG
    refine ⟨P, ?_⟩
    calc
      6 * P.size ≤ 6 * sharpBound n := Nat.mul_le_mul_left 6 hP
      _ ≤ n * (n + 1) := by
        simpa [sharpBound, Nat.mul_comm] using Nat.div_mul_le_self (n * (n + 1)) 6
      _ = n * n + n := by ring
      _ ≤ n * n + (5 * N + 1) * n := by
        exact Nat.add_le_add_left
          (by simpa using Nat.mul_le_mul_right n (show 1 ≤ 5 * N + 1 by omega)) _
  · have hnN : n ≤ N := by omega
    let P := pairPartition G
    refine ⟨P, ?_⟩
    have hP : P.size ≤ n * n := by
      simpa [P] using pairPartition_size_le_square G
    calc
      6 * P.size ≤ 6 * (n * n) := Nat.mul_le_mul_left 6 hP
      _ = n * n + 5 * (n * n) := by ring
      _ ≤ n * n + 5 * (N * n) := by
        gcongr
      _ ≤ n * n + (5 * N + 1) * n := by
        ring_nf
        omega

end Erdos81
