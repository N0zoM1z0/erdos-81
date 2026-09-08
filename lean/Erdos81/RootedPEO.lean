import Erdos81.PEOExistence
import Erdos81.RootedGraph
import Mathlib.Tactic

/-!
# Perfect-elimination orders rooted at a clique

For a chordal graph and a prescribed clique `P`, an elimination list may be
chosen with `P` as its final segment.  This file packages that list as an
order on the original vertex type and proves the monotonicity of root
neighbourhoods along oriented outside edges.
-/

namespace Erdos81
namespace RootedPEO

open RootedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A perfect-elimination list whose final segment is the chosen root. -/
structure Order (G : SimpleGraph V) (P : Finset V) where
  list : List V
  nodup : list.Nodup
  covers : ∀ v : V, v ∈ list
  cliqueSuffixes : PEOExistence.HasCliqueSuffixes G list
  endsInRoot : P.toList <:+ list

omit [DecidableEq V] in
/-- Chordality supplies a rooted perfect-elimination order. -/
theorem exists_order {G : SimpleGraph V} (P : Finset V)
    (hchordal : IsChordal G) (hP : G.IsClique (P : Set V)) :
    Nonempty (Order G P) := by
  obtain ⟨l, hnodup, hcovers, hsuffixes, hends⟩ :=
    PEOExistence.exists_elimination_list_ending_clique hchordal P hP
  exact ⟨⟨l, hnodup, hcovers, hsuffixes, hends⟩⟩

/-- Position of a vertex in the elimination list. -/
def Order.index {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) (v : V) : Fin O.list.length :=
  ⟨O.list.idxOf v, List.idxOf_lt_length_of_mem (O.covers v)⟩

omit [Fintype V] in
@[simp]
theorem Order.get_index {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) (v : V) : O.list.get (O.index v) = v := by
  exact List.idxOf_get (List.idxOf_lt_length_of_mem (O.covers v))

theorem Order.index_injective {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) : Function.Injective O.index := by
  intro u v huv
  calc
    u = O.list.get (O.index u) := (O.get_index u).symm
    _ = O.list.get (O.index v) := congrArg O.list.get huv
    _ = v := O.get_index v

/-- Vertices later than `u` and adjacent to `u` form a clique. -/
theorem later_neighbors_isClique {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) (u : V) :
    G.IsClique {v | O.index u < O.index v ∧ G.Adj u v} := by
  intro a ha b hb hab
  have haTail : a ∈ O.list.drop ((O.index u).val + 1) := by
    have h := PEOExistence.get_mem_drop_succ
      (O.index u) (O.index a) ha.1
    rw [O.get_index] at h
    exact h
  have hbTail : b ∈ O.list.drop ((O.index u).val + 1) := by
    have h := PEOExistence.get_mem_drop_succ
      (O.index u) (O.index b) hb.1
    rw [O.get_index] at h
    exact h
  have hsuffixAt :
      O.list.get (O.index u) :: O.list.drop ((O.index u).val + 1)
        <:+ O.list := by
    rw [List.cons_get_drop_succ]
    exact List.drop_suffix _ _
  have hadj := O.cliqueSuffixes
    (O.list.get (O.index u))
    (O.list.drop ((O.index u).val + 1)) hsuffixAt
    ⟨haTail, by rw [O.get_index]; exact ha.2⟩
    ⟨hbTail, by rw [O.get_index]; exact hb.2⟩ hab
  exact hadj

/-- Every outside vertex occurs before every root vertex. -/
theorem outside_before_root {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) {u x : V} (hu : u ∈ outsideVertices P)
    (hx : x ∈ P) : O.index u < O.index x := by
  obtain ⟨pre, hlist⟩ := O.endsInRoot
  have huNotRootList : u ∉ P.toList := by
    simpa using (mem_outsideVertices.mp hu)
  have huList : u ∈ pre ++ P.toList := by
    rw [hlist]
    exact O.covers u
  have huPrefix : u ∈ pre := by
    rcases List.mem_append.mp huList with huPrefix | huRoot
    · exact huPrefix
    · exact (huNotRootList huRoot).elim
  have hxRootList : x ∈ P.toList := by simpa using hx
  have hnodupAppend : (pre ++ P.toList).Nodup := by
    rw [hlist]
    exact O.nodup
  have hxNotPrefix : x ∉ pre := by
    intro hxPrefix
    exact (List.nodup_append.mp hnodupAppend).2.2 x hxPrefix x hxRootList rfl
  change O.list.idxOf u < O.list.idxOf x
  rw [← hlist, List.idxOf_append, if_pos huPrefix,
    List.idxOf_append, if_neg hxNotPrefix]
  have huIndex : pre.idxOf u < pre.length :=
    List.idxOf_lt_length_of_mem huPrefix
  omega

/-- Along an outside edge oriented by the rooted PEO, the root neighbourhood
can only grow. -/
theorem root_neighbors_mono {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) {u v : V}
    (hu : u ∈ outsideVertices P) (hv : v ∈ outsideVertices P)
    (huvOrder : O.index u < O.index v) (huv : G.Adj u v) :
    ∀ ⦃x : V⦄, x ∈ P → G.Adj u x → G.Adj v x := by
  intro x hx hux
  have huxOrder : O.index u < O.index x := outside_before_root O hu hx
  have hvxNe : v ≠ x := by
    intro hvx
    subst x
    exact (mem_outsideVertices.mp hv) hx
  exact later_neighbors_isClique O u
    ⟨huvOrder, huv⟩ ⟨huxOrder, hux⟩ hvxNe

/-- Later outside neighbours in the rooted elimination order. -/
noncomputable def forwardNeighbors {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) (u : V) : Finset V := by
  classical
  exact (outsideVertices P).filter fun v ↦
    O.index u < O.index v ∧ G.Adj u v

@[simp]
theorem mem_forwardNeighbors {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) {u v : V} :
    v ∈ forwardNeighbors O u ↔
      v ∈ outsideVertices P ∧ O.index u < O.index v ∧ G.Adj u v := by
  classical
  simp [forwardNeighbors]

/-- Outside edges oriented from their earlier to their later endpoint. -/
noncomputable def forwardEdges {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) : Finset (Σ _u : V, V) := by
  classical
  exact (outsideVertices P).sigma (forwardNeighbors O)

@[simp]
theorem mem_forwardEdges {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) {e : Σ _u : V, V} :
    e ∈ forwardEdges O ↔ e.1 ∈ outsideVertices P ∧
      e.2 ∈ outsideVertices P ∧ O.index e.1 < O.index e.2 ∧
        G.Adj e.1 e.2 := by
  classical
  simp [forwardEdges]

theorem forward_pair_injectiveOn {G : SimpleGraph V} {P : Finset V}
    (O : Order G P) :
    Set.InjOn (fun e : Σ _u : V, V ↦ s(e.1, e.2)) (forwardEdges O) := by
  classical
  rintro ⟨u, v⟩ huv ⟨x, y⟩ hxy heq
  have huv' := (mem_forwardEdges O).mp huv
  have hxy' := (mem_forwardEdges O).mp hxy
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk] at heq
  rcases heq with heq | heq
  · cases heq.1
    cases heq.2
    rfl
  · exfalso
    have hvu : O.index v < O.index u := by
      calc
        O.index v = O.index x := congrArg O.index heq.2
        _ < O.index y := hxy'.2.2.1
        _ = O.index u := congrArg O.index heq.1.symm
    exact lt_asymm huv'.2.2.1 hvu

/-- The unoriented images of the forward edges are exactly the outside
edges. -/
theorem outsideEdges_eq_forward_image {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V} (O : Order G P) :
    outsideEdges G P =
      (forwardEdges O).image fun e ↦ s(e.1, e.2) := by
  classical
  ext e
  refine Sym2.inductionOn e ?_
  intro u v
  constructor
  · intro huv
    have huv' := Finset.mem_filter.mp huv
    have hadj : G.Adj u v := G.mem_edgeFinset.mp huv'.1
    have huOut : u ∈ outsideVertices P := huv'.2 (by simp)
    have hvOut : v ∈ outsideVertices P := huv'.2 (by simp)
    rcases lt_trichotomy (O.index u) (O.index v) with hlt | heq | hgt
    · exact Finset.mem_image.mpr
        ⟨⟨u, v⟩, (mem_forwardEdges O).mpr
          ⟨huOut, hvOut, hlt, hadj⟩, rfl⟩
    · exact (hadj.ne (O.index_injective heq)).elim
    · exact Finset.mem_image.mpr
        ⟨⟨v, u⟩, (mem_forwardEdges O).mpr
          ⟨hvOut, huOut, hgt, hadj.symm⟩, Sym2.eq_swap⟩
  · intro huv
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp huv
    have hxy' := (mem_forwardEdges O).mp hxy
    rw [← heq]
    apply Finset.mem_filter.mpr
    refine ⟨G.mem_edgeFinset.mpr hxy'.2.2.2, ?_⟩
    simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using ⟨hxy'.1, hxy'.2.1⟩

/-- Forward degrees sum to the number of outside edges. -/
theorem sum_card_forwardNeighbors {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V} (O : Order G P) :
    ∑ u ∈ outsideVertices P, (forwardNeighbors O u).card =
      (outsideEdges G P).card := by
  rw [outsideEdges_eq_forward_image O,
    Finset.card_image_of_injOn (forward_pair_injectiveOn O)]
  simp [forwardEdges, Finset.card_sigma]

/-- A vertex together with its forward outside neighbours is a clique in the
outside graph. -/
theorem insert_forwardNeighbors_isClique {G : SimpleGraph V}
    {P : Finset V} (O : Order G P) {u : V}
    (hu : u ∈ outsideVertices P) :
    (outsideGraph G P).IsClique
      ((insert u (forwardNeighbors O u) : Finset V) : Set V) := by
  classical
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
  rcases ha with ha | ha
  · subst a
    rcases hb with hb | hb
    · exact (hab hb.symm).elim
    · have hb' := (mem_forwardNeighbors O).mp hb
      exact (outsideGraph_adj G P u b).mpr
        ⟨hb'.2.2, mem_outsideVertices.mp hu,
          mem_outsideVertices.mp hb'.1⟩
  · rcases hb with hb | hb
    · subst b
      have ha' := (mem_forwardNeighbors O).mp ha
      exact (outsideGraph_adj G P a u).mpr
        ⟨ha'.2.2.symm, mem_outsideVertices.mp ha'.1,
          mem_outsideVertices.mp hu⟩
    · have ha' := (mem_forwardNeighbors O).mp ha
      have hb' := (mem_forwardNeighbors O).mp hb
      exact (outsideGraph_adj G P a b).mpr
        ⟨later_neighbors_isClique O u
          ⟨ha'.2.1, ha'.2.2⟩ ⟨hb'.2.1, hb'.2.2⟩ hab,
          mem_outsideVertices.mp ha'.1, mem_outsideVertices.mp hb'.1⟩

/-- Each forward outside degree is at most `omega(H)-1`. -/
theorem card_forwardNeighbors_le_cliqueNum_sub_one {G : SimpleGraph V}
    {P : Finset V} (O : Order G P) {u : V}
    (hu : u ∈ outsideVertices P) :
    (forwardNeighbors O u).card ≤ (outsideGraph G P).cliqueNum - 1 := by
  classical
  have huNotForward : u ∉ forwardNeighbors O u := by simp
  have hcard := (insert_forwardNeighbors_isClique O hu).card_le_cliqueNum
  rw [Finset.card_insert_of_notMem huNotForward] at hcard
  omega

/-- Root vertices which cannot host the outside edge `uv`. -/
noncomputable def invalidHosts (G : SimpleGraph V) (P : Finset V)
    (u v : V) : Finset V := by
  classical
  exact P.filter fun x ↦ ¬ (G.Adj u x ∧ G.Adj v x)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem mem_invalidHosts {G : SimpleGraph V} {P : Finset V}
    {u v x : V} :
    x ∈ invalidHosts G P u v ↔
      x ∈ P ∧ ¬ (G.Adj u x ∧ G.Adj v x) := by
  classical
  simp [invalidHosts]

/-- For an oriented outside edge, invalid hosts are exactly the missing root
neighbours of its earlier endpoint. -/
theorem invalidHosts_eq_missingRow {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V}
    (O : Order G P) {u v : V} (hu : u ∈ outsideVertices P)
    (hv : v ∈ forwardNeighbors O u) :
    invalidHosts G P u v = missingRow G P u := by
  classical
  have hv' := (mem_forwardNeighbors O).mp hv
  apply Finset.ext
  intro x
  rw [mem_invalidHosts, mem_missingRow]
  constructor
  · rintro ⟨hx, hinvalid⟩
    refine ⟨hx, ?_⟩
    intro hux
    have hvx := root_neighbors_mono O hu hv'.1
      hv'.2.1 hv'.2.2 hx hux
    exact hinvalid ⟨hux, hvx⟩
  · rintro ⟨hx, hux⟩
    exact ⟨hx, fun hboth ↦ hux hboth.1⟩

/-- Total number of pairs `(outside edge, invalid root host)`. -/
noncomputable def invalidHostIncidences {G : SimpleGraph V}
    [DecidableRel G.Adj]
    {P : Finset V} (O : Order G P) : ℕ :=
  ∑ e ∈ forwardEdges O, (invalidHosts G P e.1 e.2).card

theorem invalidHostIncidences_eq_sum {G : SimpleGraph V}
    [DecidableRel G.Adj]
    {P : Finset V} (O : Order G P) :
    invalidHostIncidences O =
      ∑ u ∈ outsideVertices P,
        (forwardNeighbors O u).card * (missingRow G P u).card := by
  classical
  rw [invalidHostIncidences]
  simp only [forwardEdges]
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro u hu
  calc
    ∑ v ∈ forwardNeighbors O u, (invalidHosts G P u v).card =
        ∑ _v ∈ forwardNeighbors O u, (missingRow G P u).card := by
      exact Finset.sum_congr rfl fun v hv ↦
        congrArg Finset.card (invalidHosts_eq_missingRow O hu hv)
    _ = (forwardNeighbors O u).card * (missingRow G P u).card := by
      simp

/-- The total invalid-host charge over all oriented outside edges is bounded
by `(omega(H)-1) A`. -/
theorem invalid_host_charge_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset V} (O : Order G P) :
    ∑ u ∈ outsideVertices P,
        (forwardNeighbors O u).card * (missingRow G P u).card ≤
      ((outsideGraph G P).cliqueNum - 1) * missingIncidences G P := by
  calc
    ∑ u ∈ outsideVertices P,
        (forwardNeighbors O u).card * (missingRow G P u).card
      ≤ ∑ u ∈ outsideVertices P,
          ((outsideGraph G P).cliqueNum - 1) *
            (missingRow G P u).card := by
        exact Finset.sum_le_sum fun u hu ↦
          Nat.mul_le_mul_right _
            (card_forwardNeighbors_le_cliqueNum_sub_one O hu)
    _ = ((outsideGraph G P).cliqueNum - 1) *
        missingIncidences G P := by
      rw [← Finset.mul_sum, sum_card_missingRow]

theorem invalidHostIncidences_le {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V} (O : Order G P) :
    invalidHostIncidences O ≤
      ((outsideGraph G P).cliqueNum - 1) * missingIncidences G P := by
  rw [invalidHostIncidences_eq_sum]
  exact invalid_host_charge_le O

end RootedPEO
end Erdos81
