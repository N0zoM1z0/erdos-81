import Erdos81.Statement
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

open scoped BigOperators

/-!
# Edge counting from a perfect-elimination order

This module gives a self-contained finite counting proof of the standard
chordal edge bound, assuming that the natural order on `Fin n` is a
perfect-elimination order.  In particular, if all cliques have order at most
`p`, then

`|E(G)| + choose(p, 2) <= (p - 1) n`.

The separate characterization asserting that every finite chordal graph has
a perfect-elimination order is not proved here.  It remains an explicit item
in the formalization ledger rather than being introduced as an axiom.
-/

namespace Erdos81
namespace PerfectElimination

variable {n : ℕ}

/-- Neighbors of `i` occurring later in the natural order on `Fin n`. -/
def laterNeighbors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : Fin n) : Finset (Fin n) :=
  (Finset.Ioi i).filter (G.Adj i)

/-- The natural order on `Fin n` is a perfect-elimination ordering. -/
def IsPEO (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ i : Fin n, G.IsClique (laterNeighbors G i : Set (Fin n))

/-- Every clique in `G` has order at most `p`. -/
def CliqueOrderAtMost (G : SimpleGraph (Fin n)) (p : ℕ) : Prop :=
  ∀ K : Finset (Fin n), G.IsClique (K : Set (Fin n)) → K.card ≤ p

/-- Oriented edges, always stored from the earlier to the later endpoint. -/
def orientedEdges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Σ _i : Fin n, Fin n) :=
  Finset.univ.sigma (laterNeighbors G)

theorem mem_orientedEdges {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {e : Σ _i : Fin n, Fin n} :
    e ∈ orientedEdges G ↔ e.1 < e.2 ∧ G.Adj e.1 e.2 := by
  simp [orientedEdges, laterNeighbors]

theorem oriented_pair_injectiveOn (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Set.InjOn (fun e : Σ _i : Fin n, Fin n ↦ s(e.1, e.2)) (orientedEdges G) := by
  rintro ⟨e₁, e₂⟩ he ⟨d₁, d₂⟩ hd hed
  have he' := mem_orientedEdges.mp he
  have hd' := mem_orientedEdges.mp hd
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hed
  rcases hed with hed | hed
  · cases hed.1
    cases hed.2
    rfl
  · exfalso
    have hrev : e₂ < e₁ := by
      calc
        e₂ = d₁ := hed.2
        _ < d₂ := hd'.1
        _ = e₁ := hed.1.symm
    exact lt_asymm he'.1 hrev

theorem edgeFinset_eq_oriented_image (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    G.edgeFinset = (orientedEdges G).image (fun e ↦ s(e.1, e.2)) := by
  ext z
  refine Sym2.inductionOn z ?_
  intro x y
  constructor
  · intro hxy
    have hadj : G.Adj x y := G.mem_edgeFinset.mp hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · apply Finset.mem_image.mpr
      exact ⟨⟨x, y⟩, mem_orientedEdges.mpr ⟨hlt, hadj⟩, rfl⟩
    · subst y
      exact (G.irrefl hadj).elim
    · apply Finset.mem_image.mpr
      refine ⟨⟨y, x⟩, mem_orientedEdges.mpr ⟨hgt, hadj.symm⟩, ?_⟩
      exact Sym2.eq_swap
  · intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    rw [← heq]
    exact G.mem_edgeFinset.mpr (mem_orientedEdges.mp he).2

theorem card_edgeFinset_eq_sum_laterNeighbors (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    G.edgeFinset.card = ∑ i, (laterNeighbors G i).card := by
  rw [edgeFinset_eq_oriented_image]
  rw [Finset.card_image_of_injOn (oriented_pair_injectiveOn G)]
  simp [orientedEdges, Finset.card_sigma]

theorem choose_neighbor_identity (k : ℕ) :
    Nat.choose (k + 1) 2 + Nat.choose k 2 = k * k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_zero_right] at ih ⊢
      ring_nf at ih ⊢
      omega

theorem sum_range_min_add_choose (k n : ℕ) (hkn : k ≤ n) :
    (∑ i ∈ Finset.range n, min k i) + Nat.choose (k + 1) 2 = k * n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  induction d with
  | zero =>
      rw [Nat.add_zero]
      have hsum : (∑ i ∈ Finset.range k, min k i) = ∑ i ∈ Finset.range k, i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [min_eq_right]
        exact Nat.le_of_lt (Finset.mem_range.mp hi)
      rw [hsum, Finset.sum_range_id]
      rw [← Nat.choose_two_right k]
      simpa [add_comm] using choose_neighbor_identity k
  | succ d ih =>
      rw [Nat.add_succ, Finset.sum_range_succ]
      rw [min_eq_left (by omega)]
      have hi := ih (by omega)
      calc
        (∑ x ∈ Finset.range (k + d), min k x) + k +
            Nat.choose (k + 1) 2 =
          ((∑ x ∈ Finset.range (k + d), min k x) +
            Nat.choose (k + 1) 2) + k := by omega
        _ = k * (k + d) + k := by rw [hi]
        _ = k * (k + d).succ := by simp [Nat.succ_eq_add_one]; ring

theorem sum_range_min_pred_add_choose (p n : ℕ) (hpn : p ≤ n) :
    (∑ i ∈ Finset.range n, min (p - 1) i) + Nat.choose p 2 =
      (p - 1) * n := by
  cases p with
  | zero => simp
  | succ k =>
      simpa using sum_range_min_add_choose k n (by omega)

theorem insert_laterNeighbors_isClique {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hpeo : IsPEO G) (i : Fin n) :
    G.IsClique ((insert i (laterNeighbors G i) : Finset (Fin n)) : Set (Fin n)) := by
  rw [Finset.coe_insert]
  apply (hpeo i).insert
  intro j hj _hne
  exact (Finset.mem_filter.mp hj).2

theorem card_laterNeighbors_add_one_le {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {p : ℕ} (hpeo : IsPEO G)
    (hclique : CliqueOrderAtMost G p) (i : Fin n) :
    (laterNeighbors G i).card + 1 ≤ p := by
  have hi : i ∉ laterNeighbors G i := by simp [laterNeighbors]
  have h := hclique (insert i (laterNeighbors G i))
    (insert_laterNeighbors_isClique hpeo i)
  simpa [Finset.card_insert_of_notMem hi] using h

theorem card_laterNeighbors_le_remaining (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) :
    (laterNeighbors G i).card ≤ n - 1 - i.val := by
  calc
    (laterNeighbors G i).card ≤ (Finset.Ioi i).card := Finset.card_filter_le _ _
    _ = n - 1 - i.val := by simp

theorem card_laterNeighbors_le_min {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {p : ℕ} (hpeo : IsPEO G)
    (hclique : CliqueOrderAtMost G p) (i : Fin n) :
    (laterNeighbors G i).card ≤ min (p - 1) (n - 1 - i.val) := by
  apply le_min
  · have h := card_laterNeighbors_add_one_le hpeo hclique i
    omega
  · exact card_laterNeighbors_le_remaining G i

theorem sum_fin_reflected_min (p n : ℕ) :
    (∑ i : Fin n, min (p - 1) (n - 1 - i.val)) =
      ∑ j ∈ Finset.range n, min (p - 1) j := by
  calc
    (∑ i : Fin n, min (p - 1) (n - 1 - i.val)) =
        ∑ j ∈ Finset.range n, min (p - 1) (n - 1 - j) := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun j ↦ min (p - 1) (n - 1 - j)) n
    _ = ∑ j ∈ Finset.range n, min (p - 1) j :=
      Finset.sum_range_reflect (fun j ↦ min (p - 1) j) n

theorem edge_bound_of_peo {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {p : ℕ} (hpn : p ≤ n) (hpeo : IsPEO G)
    (hclique : CliqueOrderAtMost G p) :
    G.edgeFinset.card + Nat.choose p 2 ≤ (p - 1) * n := by
  rw [card_edgeFinset_eq_sum_laterNeighbors]
  calc
    (∑ i : Fin n, (laterNeighbors G i).card) + Nat.choose p 2 ≤
        (∑ i : Fin n, min (p - 1) (n - 1 - i.val)) + Nat.choose p 2 := by
      gcongr with i
      exact card_laterNeighbors_le_min hpeo hclique i
    _ = (∑ j ∈ Finset.range n, min (p - 1) j) + Nat.choose p 2 := by
      rw [sum_fin_reflected_min]
    _ = (p - 1) * n := sum_range_min_pred_add_choose p n hpn

/-- Pascal's recurrence in the orientation convenient for pair counting. -/
theorem choose_two_succ (n : ℕ) :
    Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
  rw [Nat.choose_succ_succ]
  simp [Nat.add_comm]

/-- Twice the number of pairs in a `p`-set is `p(p-1)`. -/
theorem two_mul_choose_two (p : ℕ) :
    Nat.choose p 2 + Nat.choose p 2 = (p - 1) * p := by
  have h := Nat.choose_succ_right_eq p 1
  calc
    Nat.choose p 2 + Nat.choose p 2 = Nat.choose p 2 * 2 := by omega
    _ = p * (p - 1) := by simpa using h
    _ = (p - 1) * p := Nat.mul_comm _ _

/--
The exact pair-count identity behind the missing-pair consequence of the PEO
edge bound.  The positivity assumption is necessary because natural-number
subtraction truncates `p - 1` when `p = 0`.
-/
theorem choose_complement_identity (p u : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (p + u) + Nat.choose (u + 1) 2 =
      Nat.choose (p + u) 2 + Nat.choose p 2 := by
  induction u with
  | zero =>
      simpa using (two_mul_choose_two p).symm
  | succ u ih =>
      rw [← Nat.add_assoc p u 1, Nat.mul_add, Nat.mul_one,
        choose_two_succ (u + 1), choose_two_succ (p + u)]
      omega

/-- The edge sets of a graph and its complement partition all vertex pairs. -/
theorem card_edges_add_card_complement (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = Nat.choose n 2 := by
  classical
  calc
    G.edgeFinset.card + Gᶜ.edgeFinset.card =
        (G.edgeFinset ∪ Gᶜ.edgeFinset).card := by
      rw [Finset.card_union_of_disjoint]
      exact SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
    _ = (⊤ : SimpleGraph (Fin n)).edgeFinset.card := by
      congr 1
      ext e
      refine Sym2.inductionOn e ?_
      intro x y
      simp [SimpleGraph.mem_edgeFinset]
      constructor
      · rintro (hxy | ⟨hne, _hnxy⟩)
        · exact G.ne_of_adj hxy
        · exact hne
      · intro hne
        by_cases hxy : G.Adj x y
        · exact Or.inl hxy
        · exact Or.inr ⟨hne, hxy⟩
    _ = Nat.choose n 2 := by
      simpa using
        (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))

/--
If a PEO graph on `n` vertices has clique order at most `p`, its complement
has at least `choose(n-p+1,2)` edges.  In the manuscript, `u = n-p`; these
complement edges are precisely the missing pairs and give `choose(u+1,2)`.
-/
theorem complement_edge_bound_of_peo {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {p : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n)
    (hpeo : IsPEO G) (hclique : CliqueOrderAtMost G p) :
    Nat.choose (n - p + 1) 2 ≤ Gᶜ.edgeFinset.card := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hpn
  have hedge := edge_bound_of_peo (G := G) (p := p) (by omega) hpeo hclique
  have hpairs := choose_complement_identity p u hp
  have htotal := card_edges_add_card_complement G
  simp only [Nat.add_sub_cancel_left] at hedge hpairs htotal ⊢
  omega

end PerfectElimination
end Erdos81
