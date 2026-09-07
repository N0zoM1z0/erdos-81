import Erdos81.Chordal
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Tactic

/-!
# Chordless paths and induced cycles

This module develops the walk lemmas used in the self-contained proof of
Dirac's simplicial-vertex theorem.  The key bridge turns a chordless cyclic
walk into the `cycleGraph` embedding excluded by `Erdos81.IsChordal`.
-/

namespace Erdos81
namespace ChordalWalk

open SimpleGraph
open SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- A shortest path has no edge joining positions separated by a gap. -/
theorem geodesic_not_adj_of_gap {x y : V} (P : G.Walk x y)
    (hshort : P.length = G.dist x y) {i j : ℕ}
    (hgap : i + 1 < j) (hj : j ≤ P.length) :
    ¬G.Adj (P.getVert i) (P.getVert j) := by
  intro hij
  let shortcut : G.Walk x y :=
    ((P.take i).append hij.toWalk).append (P.drop j)
  have htake : min i P.length = i := Nat.min_eq_left (by omega)
  have hlength : shortcut.length = i + 1 + (P.length - j) := by
    simp [shortcut, htake]
  have hdist := SimpleGraph.dist_le shortcut
  rw [← hshort, hlength] at hdist
  omega

/--
Two edge-disjoint paths with distinct endpoints and disjoint interiors form a
cycle when one is followed by the reverse of the other.
-/
theorem append_reverse_isCycle {x y : V} {P Q : G.Walk x y}
    (hP : P.IsPath) (hQ : Q.IsPath) (hxy : x ≠ y)
    (hedges : List.Disjoint P.edges Q.edges)
    (hinterior : List.Disjoint P.support.tail Q.reverse.support.tail) :
    (P.append Q.reverse).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  constructor
  · rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse]
    exact List.Nodup.append hP.isTrail.edges_nodup
      (List.nodup_reverse.mpr hQ.isTrail.edges_nodup)
      (by simpa [List.disjoint_reverse_right] using hedges)
  constructor
  · intro hempty
    have hzero : (P.append Q.reverse).length = 0 := by
      rw [hempty, SimpleGraph.Walk.length_nil]
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hzero
    have hPzero : P.length = 0 := by omega
    exact (SimpleGraph.Walk.not_nil_of_ne hxy)
      (SimpleGraph.Walk.length_eq_zero_iff.mp hPzero)
  · rw [SimpleGraph.Walk.tail_support_append]
    exact List.Nodup.append
      (hP.support_nodup.sublist (List.tail_sublist _))
      (hQ.reverse.support_nodup.sublist (List.tail_sublist _)) hinterior

/--
Adjacency in a cycle of order at least four, expressed without modular
subtraction: the indices are consecutive or form the wrap-around pair.
-/
theorem cycleGraph_adj_iff_values {k : ℕ} (hk : 4 ≤ k) (i j : Fin k) :
    (SimpleGraph.cycleGraph k).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = k - 1) ∨ (j.val = 0 ∧ i.val = k - 1) := by
  rw [SimpleGraph.cycleGraph_adj']
  constructor
  · rintro (h | h)
    · apply_fun (Nat.cast : ℕ → ℤ) at h
      rw [Fin.coe_int_sub_eq_ite] at h
      fin_omega
    · apply_fun (Nat.cast : ℕ → ℤ) at h
      rw [Fin.coe_int_sub_eq_ite] at h
      fin_omega
  · rintro (h | h | h | h)
    · right
      rw [← @Nat.cast_inj ℤ, Fin.coe_int_sub_eq_ite]
      fin_omega
    · left
      rw [← @Nat.cast_inj ℤ, Fin.coe_int_sub_eq_ite]
      fin_omega
    · left
      rw [← @Nat.cast_inj ℤ, Fin.coe_int_sub_eq_ite]
      fin_omega
    · right
      rw [← @Nat.cast_inj ℤ, Fin.coe_int_sub_eq_ite]
      fin_omega

/--
A cyclic path whose only ambient adjacencies are cyclically consecutive gives
an induced embedding of the corresponding `cycleGraph`.
-/
theorem inducedCycleEmbedding {x : V} {k : ℕ} (hk : 4 ≤ k)
    (C : G.Walk x x) (hcycle : C.IsCycle) (hlen : C.length = k)
    (hreflect : ∀ i j : Fin k,
      G.Adj (C.getVert i.val) (C.getVert j.val) →
        (SimpleGraph.cycleGraph k).Adj i j) :
    SimpleGraph.cycleGraph k ⊴ G := by
  refine ⟨⟨⟨fun i ↦ C.getVert i.val, ?_⟩, ?_⟩⟩
  · intro i j hij
    apply Fin.ext
    have hi : i.val ≤ C.length - 1 := by omega
    have hj : j.val ≤ C.length - 1 := by omega
    exact hcycle.getVert_injOn' hi hj hij
  · intro i j
    change G.Adj (C.getVert i.val) (C.getVert j.val) ↔
      (SimpleGraph.cycleGraph k).Adj i j
    constructor
    · exact hreflect i j
    · intro hadj
      rw [cycleGraph_adj_iff_values hk] at hadj
      have hi := i.isLt
      have hj := j.isLt
      have hend : C.getVert k = x := by
        rw [← hlen]
        exact C.getVert_length
      rcases hadj with hsucc | hpred | hwrap | hwrap
      · have h := C.adj_getVert_succ (i := i.val) (by omega)
        simpa [hsucc] using h
      · have h := C.adj_getVert_succ (i := j.val) (by omega)
        rw [hpred] at h
        exact h.symm
      · have h := C.adj_getVert_succ (i := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega, hend] at h
        rw [hwrap.1, hwrap.2, C.getVert_zero]
        exact h.symm
      · have h := C.adj_getVert_succ (i := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega, hend] at h
        rw [hwrap.1, hwrap.2, C.getVert_zero]
        exact h

/--
Two chordless `x`--`y` arcs with disjoint interiors and no cross-edge form an
induced cycle.  This is the precise interface used for two components of a
minimal vertex separator.
-/
theorem inducedCycleEmbedding_of_two_arcs {x y : V} (hxy : x ≠ y)
    (P Q : G.Walk x y) (hP : P.IsPath) (hQ : Q.IsPath)
    (hPtwo : 2 ≤ P.length) (hQtwo : 2 ≤ Q.length)
    (hPfar : ∀ i j, i + 1 < j → j ≤ P.length →
      ¬G.Adj (P.getVert i) (P.getVert j))
    (hQfar : ∀ i j, i + 1 < j → j ≤ Q.length →
      ¬G.Adj (Q.getVert i) (Q.getVert j))
    (hcross : ∀ i j, 0 < i → i < P.length → 0 < j → j < Q.length →
      ¬G.Adj (P.getVert i) (Q.getVert j))
    (hedges : List.Disjoint P.edges Q.edges)
    (hinterior : List.Disjoint P.support.tail Q.reverse.support.tail) :
    SimpleGraph.cycleGraph (P.length + Q.length) ⊴ G := by
  let C : G.Walk x x := P.append Q.reverse
  have hCcycle : C.IsCycle := append_reverse_isCycle hP hQ hxy hedges hinterior
  have hClength : C.length = P.length + Q.length := by
    simp [C]
  have hvertex : ∀ t : ℕ, C.getVert t =
      if t < P.length then P.getVert t
      else Q.getVert (Q.length - (t - P.length)) := by
    intro t
    simp [C, SimpleGraph.Walk.getVert_append, SimpleGraph.Walk.getVert_reverse]
  apply inducedCycleEmbedding (by omega) C hCcycle hClength
  have ordered : ∀ a b : Fin (P.length + Q.length), a.val ≤ b.val →
      G.Adj (C.getVert a.val) (C.getVert b.val) →
        (SimpleGraph.cycleGraph (P.length + Q.length)).Adj a b := by
    intro a b hab hadj
    have haBound := a.isLt
    have hbBound := b.isLt
    rw [hvertex a.val, hvertex b.val] at hadj
    rw [cycleGraph_adj_iff_values (by omega)]
    by_cases haP : a.val < P.length
    · by_cases hbP : b.val < P.length
      · rw [if_pos haP, if_pos hbP] at hadj
        have habne : a.val ≠ b.val := by
          intro heq
          exact hadj.ne (by rw [heq])
        by_cases hgap : a.val + 1 < b.val
        · exact (hPfar a.val b.val hgap (by omega) hadj).elim
        · exact Or.inl (by omega)
      · rw [if_pos haP, if_neg hbP] at hadj
        let qpos := Q.length - (b.val - P.length)
        have hadjQ : G.Adj (P.getVert a.val) (Q.getVert qpos) := by
          simpa [qpos] using hadj
        by_cases ha0 : a.val = 0
        · by_cases hqsmall : qpos < 2
          · exact Or.inr (Or.inr (Or.inl
              ⟨ha0, by dsimp [qpos] at hqsmall; omega⟩))
          · have hqgap : 0 + 1 < qpos := by omega
            have hqle : qpos ≤ Q.length := Nat.sub_le _ _
            have hforbidden := hQfar 0 qpos hqgap hqle
            have hzeroAdj : G.Adj (Q.getVert 0) (Q.getVert qpos) := by
              simpa only [ha0, P.getVert_zero, Q.getVert_zero] using hadjQ
            exact (hforbidden hzeroAdj).elim
        · by_cases hqy : qpos = Q.length
          · have hends : Q.getVert Q.length = P.getVert P.length := by
              rw [Q.getVert_length, P.getVert_length]
            rw [hqy, hends] at hadjQ
            by_cases hgap : a.val + 1 < P.length
            · exact (hPfar a.val P.length hgap le_rfl hadjQ).elim
            · exact Or.inl (by dsimp [qpos] at hqy; omega)
          · have hqpos : 0 < qpos := by
              dsimp [qpos]
              omega
            have hqinside : qpos < Q.length := by omega
            exact (hcross a.val qpos (by omega) haP hqpos hqinside hadjQ).elim
    · by_cases hbP : b.val < P.length
      · omega
      · rw [if_neg haP, if_neg hbP] at hadj
        let qa := Q.length - (a.val - P.length)
        let qb := Q.length - (b.val - P.length)
        have hadjQ : G.Adj (Q.getVert qa) (Q.getVert qb) := by
          simpa [qa, qb] using hadj
        have hqne : qa ≠ qb := by
          intro heq
          exact hadjQ.ne (congrArg Q.getVert heq)
        by_cases hgap : qb + 1 < qa
        · exact (hQfar qb qa hgap (by dsimp [qa]; omega) hadjQ.symm).elim
        · exact Or.inl (by dsimp [qa, qb] at hqne ⊢; omega)
  intro a b hadj
  rcases le_total a.val b.val with hab | hba
  · exact ordered a b hab hadj
  · exact (ordered b a hba hadj.symm).symm

end ChordalWalk
end Erdos81
