/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Nikoghosyan.Basic
import Nikoghosyan.Prerequisites.TwoFactorCriterion
import Nikoghosyan.Prerequisites.TwoFactorParity

/-!
# Extremal negative barriers and the host 2-factor

Finite selection of a maximum-`|S|` then minimum-`|T|` negative pair,
component persistence for returning `t ∈ T` and moving `x` into `S`,
matching `D–T` interfaces, the three-edge forbidden-pattern bound, and
`thm:factor` for 1-tough induced-`(P₄ ∪ P₁)`-free graphs of order at
least three.

No supplied factor, barrier certificate, or cited biased-barrier theorem
is taken as a premise of the exported existence theorem.
-/

universe u

namespace Nikoghosyan
namespace TwoFactor

open Classical
open scoped BigOperators
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ## Finite negative pairs and extremal selection -/

/-- Disjoint pairs with strictly negative barrier. -/
noncomputable def negativePairs (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V × Finset V) :=
  (univ : Finset (Finset V × Finset V)).filter
    fun p => Disjoint p.1 p.2 ∧ delta G p.1 p.2 < 0

lemma mem_negativePairs {p : Finset V × Finset V} :
    p ∈ negativePairs G ↔ Disjoint p.1 p.2 ∧ delta G p.1 p.2 < 0 := by
  simp [negativePairs]

lemma exists_negative_of_not_cycleFactor
    (h : ¬ Nonempty (CycleFactor G)) :
    (negativePairs G).Nonempty := by
  have hiff := delta_nonneg_iff_exists_cycleFactor (G := G)
  have : ¬ ∀ S T : Finset V, Disjoint S T → 0 ≤ delta G S T := by
    intro hall
    exact h (hiff.mp hall)
  push_neg at this
  obtain ⟨S, T, hdis, hneg⟩ := this
  exact ⟨(S, T), (mem_negativePairs (G := G)).2 ⟨hdis, hneg⟩⟩

/-- A finite negative pair of maximum `|S|` and then minimum `|T|`.
The fields record only extremality, not the later matching restrictions. -/
structure ExtremalBarrier (G : SimpleGraph V) [DecidableRel G.Adj] where
  S : Finset V
  T : Finset V
  disjoint : Disjoint S T
  neg : delta G S T ≤ -2
  maxS : ∀ S' T' : Finset V,
    Disjoint S' T' → delta G S' T' < 0 → S'.card ≤ S.card
  minT : ∀ S' T' : Finset V,
    Disjoint S' T' → delta G S' T' < 0 → S'.card = S.card → T.card ≤ T'.card

lemma exists_extremalBarrier (hP : (negativePairs G).Nonempty) :
    Nonempty (ExtremalBarrier G) := by
  obtain ⟨p, hp, hmax⟩ :=
    exists_max_image (negativePairs G) (fun q => q.1.card) hP
  let P1 := (negativePairs G).filter fun q => q.1.card = p.1.card
  have hP1 : P1.Nonempty := ⟨p, mem_filter.mpr ⟨hp, rfl⟩⟩
  obtain ⟨q, hq, hmin⟩ := exists_min_image P1 (fun r => r.2.card) hP1
  have hNP : Disjoint q.1 q.2 ∧ delta G q.1 q.2 < 0 :=
    (mem_negativePairs (G := G)).1 (mem_filter.mp hq).1
  have hqcard : q.1.card = p.1.card := (mem_filter.mp hq).2
  refine ⟨⟨q.1, q.2, hNP.1,
    delta_neg_le_neg_two (G := G) hNP.1 hNP.2, ?_, ?_⟩⟩
  · intro S' T' hdis' hneg'
    have : S'.card ≤ p.1.card :=
      hmax (S', T') ((mem_negativePairs (G := G)).2 ⟨hdis', hneg'⟩)
    simpa [hqcard] using this
  · intro S' T' hdis' hneg' hcard
    have hmem : (S', T') ∈ P1 :=
      mem_filter.mpr ⟨(mem_negativePairs (G := G)).2 ⟨hdis', hneg'⟩,
        by simp [hcard, hqcard]⟩
    exact hmin (S', T') hmem

lemma exists_extremalBarrier_of_not_cycleFactor
    (h : ¬ Nonempty (CycleFactor G)) : Nonempty (ExtremalBarrier G) :=
  exists_extremalBarrier (G := G) (exists_negative_of_not_cycleFactor (G := G) h)

lemma ExtremalBarrier.not_neg_erase {B : ExtremalBarrier G} {t : V}
    (ht : t ∈ B.T) : ¬ delta G B.S (B.T.erase t) < 0 := by
  intro hneg
  have hdis' : Disjoint B.S (B.T.erase t) :=
    B.disjoint.mono_right (erase_subset t B.T)
  have hle := B.minT B.S (B.T.erase t) hdis' hneg rfl
  have hlt : (B.T.erase t).card < B.T.card := card_erase_lt_of_mem ht
  exact (not_le_of_gt hlt) hle

lemma ExtremalBarrier.nonneg_erase {B : ExtremalBarrier G} {t : V}
    (ht : t ∈ B.T) : 0 ≤ delta G B.S (B.T.erase t) :=
  le_of_not_gt (B.not_neg_erase ht)

lemma ExtremalBarrier.not_neg_insert {B : ExtremalBarrier G} {x : V}
    (hx : x ∉ B.S ∪ B.T) : ¬ delta G (insert x B.S) B.T < 0 := by
  intro hneg
  have hxS : x ∉ B.S := fun hS => hx (mem_union.mpr (Or.inl hS))
  have hxT : x ∉ B.T := fun hT => hx (mem_union.mpr (Or.inr hT))
  have hdis' : Disjoint (insert x B.S) B.T :=
    (disjoint_insert_left).2 ⟨hxT, B.disjoint⟩
  have hle := B.maxS (insert x B.S) B.T hdis' hneg
  have : B.S.card < (insert x B.S).card := card_lt_card (ssubset_insert hxS)
  exact (not_le_of_gt this) hle

lemma ExtremalBarrier.nonneg_insert {B : ExtremalBarrier G} {x : V}
    (hx : x ∉ B.S ∪ B.T) : 0 ≤ delta G (insert x B.S) B.T :=
  le_of_not_gt (B.not_neg_insert hx)

/-! ## Barrier identities for `T.erase t` and `insert x S` -/

lemma remainder_erase_t {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T) :
    remainderVerts G S (T.erase t) = insert t (remainderVerts G S T) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∉ S ∪ T.erase t := (mem_remainderVerts_iff (G := G)).1 hx
    by_cases hxt : x = t
    · simp [hxt]
    · have hxST : x ∉ S ∪ T := by
        intro h
        rcases mem_union.mp h with hS | hT
        · exact hx' (mem_union.mpr (Or.inl hS))
        · exact hx' (mem_union.mpr (Or.inr (mem_erase.mpr ⟨hxt, hT⟩)))
      exact mem_insert_of_mem ((mem_remainderVerts_iff (G := G)).2 hxST)
  · intro hx
    rcases mem_insert.mp hx with rfl | hxU
    · refine (mem_remainderVerts_iff (G := G)).2 ?_
      intro hST
      rcases mem_union.mp hST with hS | hTe
      · exact Finset.disjoint_left.1 hdis hS ht
      · exact (mem_erase.mp hTe).1 rfl
    · have hxST : x ∉ S ∪ T := (mem_remainderVerts_iff (G := G)).1 hxU
      refine (mem_remainderVerts_iff (G := G)).2 ?_
      intro hST
      rcases mem_union.mp hST with hS | hTe
      · exact hxST (mem_union.mpr (Or.inl hS))
      · exact hxST (mem_union.mpr (Or.inr (mem_erase.mp hTe).2))

lemma t_not_mem_remainder {S T : Finset V} {t : V} (ht : t ∈ T) :
    t ∉ remainderVerts G S T := by
  simp [remainderVerts, ht]

lemma card_erase_t_int {T : Finset V} {t : V} (ht : t ∈ T) :
    ((T.erase t).card : ℤ) = (T.card : ℤ) - 1 := by
  have hpos : 1 ≤ T.card := Nat.succ_le_iff.mpr (card_pos.mpr ⟨t, ht⟩)
  rw [card_erase_of_mem ht, Nat.cast_sub hpos, Nat.cast_one]

lemma sum_degDelete_erase_int {S T : Finset V} {t : V} (ht : t ∈ T) :
    ∑ u ∈ T.erase t, (degDelete G S u : ℤ) =
      (∑ u ∈ T, (degDelete G S u : ℤ)) - (degDelete G S t : ℤ) := by
  let f : V → ℤ := fun u => (degDelete G S u : ℤ)
  have h := add_sum_erase (s := T) (f := f) ht
  exact eq_sub_of_add_eq (by simpa [add_comm] using h)

lemma delta_erase_t {S T : Finset V} {t : V} (ht : t ∈ T) :
    delta G S (T.erase t) =
      delta G S T + 2 - (degDelete G S t : ℤ)
        + (hCount G S T : ℤ) - (hCount G S (T.erase t) : ℤ) := by
  unfold delta
  have hcard := card_erase_t_int (T := T) ht
  have hsum := sum_degDelete_erase_int (G := G) (S := S) ht
  rw [hcard, hsum]
  ring

lemma degDelete_insert {S : Finset V} {x t : V} (hx : x ∉ S) :
    (degDelete G (insert x S) t : ℤ) =
      (degDelete G S t : ℤ) - if G.Adj t x then (1 : ℤ) else 0 := by
  have hset :
      G.neighborFinset t \ insert x S = (G.neighborFinset t \ S).erase x := by
    simp [sdiff_insert, sdiff_singleton_eq_erase]
  by_cases hAdj : G.Adj t x
  · have hxN : x ∈ G.neighborFinset t \ S := by
      simp [mem_neighborFinset, hAdj, hx]
    have hpos : 1 ≤ (G.neighborFinset t \ S).card :=
      Nat.succ_le_iff.mpr (card_pos.mpr ⟨x, hxN⟩)
    have hcard := card_erase_of_mem hxN
    simp [degDelete, hset, hAdj, hcard, Nat.cast_sub hpos]
  · have hxN : x ∉ G.neighborFinset t \ S := by
      simp [mem_neighborFinset, hAdj]
    simp [degDelete, hset, hAdj, erase_eq_of_notMem hxN]

lemma orderedEdgeCount_singleton_right (A : Finset V) (x : V) :
    orderedEdgeCount G A {x} = (A.filter fun a => G.Adj a x).card := by
  have hprod :
      ((A ×ˢ ({x} : Finset V)).filter fun p => G.Adj p.1 p.2) =
        (A.filter fun a => G.Adj a x) ×ˢ {x} := by
    ext p
    constructor
    · intro hp
      have hp' := mem_filter.mp hp
      have hAB := mem_product.mp hp'.1
      have hx : p.2 = x := mem_singleton.mp hAB.2
      refine mem_product.mpr ⟨mem_filter.mpr ⟨hAB.1, by simpa [hx] using hp'.2⟩,
        mem_singleton.mpr hx⟩
    · intro hp
      have hAB := mem_product.mp hp
      have hf := mem_filter.mp hAB.1
      have hx : p.2 = x := mem_singleton.mp hAB.2
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hf.1, hAB.2⟩, by simpa [hx] using hf.2⟩
  rw [orderedEdgeCount, hprod, card_product, card_singleton, mul_one]

lemma sum_degDelete_insert_int {S T : Finset V} {x : V} (hx : x ∉ S) :
    ∑ t ∈ T, (degDelete G (insert x S) t : ℤ) =
      ∑ t ∈ T, (degDelete G S t : ℤ)
        - (orderedEdgeCount G T {x} : ℤ) := by
  have hpt :
      ∑ t ∈ T, (if G.Adj t x then (1 : ℤ) else 0) =
        (orderedEdgeCount G T {x} : ℤ) := by
    rw [orderedEdgeCount_singleton_right, sum_boole]
  rw [sum_congr rfl fun t _ => degDelete_insert (G := G) (t := t) hx,
    sum_sub_distrib, hpt]

lemma card_insert_int {S : Finset V} {x : V} (hx : x ∉ S) :
    ((insert x S).card : ℤ) = (S.card : ℤ) + 1 := by
  simp [card_insert_of_notMem hx]

lemma delta_insert_S {S T : Finset V} {x : V} (hx : x ∉ S) :
    delta G (insert x S) T =
      delta G S T + 2 - (orderedEdgeCount G T {x} : ℤ)
        + (hCount G S T : ℤ) - (hCount G (insert x S) T : ℤ) := by
  unfold delta
  have hcard := card_insert_int (S := S) hx
  have hsum := sum_degDelete_insert_int (G := G) (T := T) hx
  rw [hcard, hsum]
  ring

/-! ## Meeting odd components after returning `t` -/

/-- An original remainder component meets `t` if it sends an original edge to `t`. -/
def MeetsVertex (S T : Finset V) (c : (Remain G S T).ConnectedComponent)
    (t : V) : Prop :=
  ∃ x ∈ componentVerts G S T c, G.Adj x t

lemma MeetsVertex_iff_attach_pos {S T : Finset V}
    (c : (Remain G S T).ConnectedComponent) {t : V} :
    MeetsVertex S T c t ↔
      0 < orderedEdgeCount G (componentVerts G S T c) {t} := by
  constructor
  · rintro ⟨x, hx, hadj⟩
    have : (x, t) ∈ (componentVerts G S T c ×ˢ ({t} : Finset V)).filter
        fun p => G.Adj p.1 p.2 :=
      mem_filter.mpr ⟨mem_product.mpr ⟨hx, mem_singleton_self t⟩, hadj⟩
    exact Finset.card_pos.mpr ⟨_, this⟩
  · intro hpos
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hp' := mem_filter.mp hp
    have hprod := mem_product.mp hp'.1
    have ht : p.2 = t := mem_singleton.mp hprod.2
    exact ⟨p.1, hprod.1, by simpa [ht] using hp'.2⟩

lemma remainder_subset_erase {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T) :
    remainderVerts G S T ⊆ remainderVerts G S (T.erase t) := by
  rw [remainder_erase_t hdis ht]
  exact subset_insert _ _

/-- Number of odd-attachment remainder components that meet `t`. -/
noncomputable def oddMeetCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (t : V) : ℕ :=
  ((univ : Finset (Remain G S T).ConnectedComponent).filter
    fun c => Odd (componentAttach G S T c) ∧ MeetsVertex S T c t).card

lemma oddMeetCount_le_hCount (S T : Finset V) (t : V) :
    oddMeetCount G S T t ≤ hCount G S T := by
  classical
  refine card_le_card ?_
  intro c hc
  have hc' := mem_filter.mp hc
  exact mem_filter.mpr ⟨hc'.1, hc'.2.1⟩

lemma hCount_eq_oddMeet_add_persist (S T : Finset V) (t : V) :
    hCount G S T =
      oddMeetCount G S T t +
        ((univ : Finset (Remain G S T).ConnectedComponent).filter
          fun c => Odd (componentAttach G S T c) ∧ ¬ MeetsVertex S T c t).card := by
  classical
  have hunion :
      (univ.filter fun c : (Remain G S T).ConnectedComponent =>
          Odd (componentAttach G S T c)) =
        (univ.filter fun c => Odd (componentAttach G S T c) ∧ MeetsVertex S T c t) ∪
          (univ.filter fun c =>
            Odd (componentAttach G S T c) ∧ ¬ MeetsVertex S T c t) := by
    ext c
    simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      by_cases hm : MeetsVertex S T c t
      · exact Or.inl ⟨h, hm⟩
      · exact Or.inr ⟨h, hm⟩
    · intro h
      rcases h with h | h <;> exact h.1
  have hdis :
      Disjoint
        (univ.filter fun c : (Remain G S T).ConnectedComponent =>
          Odd (componentAttach G S T c) ∧ MeetsVertex S T c t)
        (univ.filter fun c =>
          Odd (componentAttach G S T c) ∧ ¬ MeetsVertex S T c t) := by
    rw [Finset.disjoint_left]
    intro c hc hn
    exact (mem_filter.mp hn).2.2 (mem_filter.mp hc).2.2
  simp only [hCount, oddMeetCount]
  rw [hunion, card_union_of_disjoint hdis]

/-! ## Support-preserving persistence after returning `t ∈ T` -/

/-- Vertex type of the induced remainder graph `Remain G S T`. -/
abbrev RemainVert (S T : Finset V) :=
  {x : V // x ∈ ((S ∪ T : Finset V) : Set V)ᶜ}

lemma remainder_set_subset_erase {S T : Finset V} {t : V} (ht : t ∈ T) :
    ((S ∪ T : Finset V) : Set V)ᶜ ⊆ ((S ∪ T.erase t : Finset V) : Set V)ᶜ := by
  intro x hx
  have hxST : x ∉ (S ∪ T : Finset V) := (Set.mem_compl_iff _ _).1 hx
  refine (Set.mem_compl_iff _ _).2 ?_
  intro h
  apply hxST
  rcases mem_union.mp h with hS | hTe
  · exact mem_union.mpr (Or.inl hS)
  · exact mem_union.mpr (Or.inr (mem_erase.mp hTe).2)

lemma componentVerts_nonempty {S T : Finset V}
    (c : (Remain G S T).ConnectedComponent) :
    (componentVerts G S T c).Nonempty := by
  obtain ⟨x, hx⟩ := c.nonempty_supp
  refine ⟨x.val, ?_⟩
  exact (mem_componentVerts_iff (c := c)).mpr
    ⟨x.property, (ConnectedComponent.mem_supp_iff _ _).mp hx⟩

lemma eq_of_mem_componentVerts {S T : Finset V}
    {c d : (Remain G S T).ConnectedComponent} {x : V}
    (hc : x ∈ componentVerts G S T c) (hd : x ∈ componentVerts G S T d) :
    c = d := by
  have ⟨_, hc'⟩ := (mem_componentVerts_iff (c := c)).mp hc
  have ⟨_, hd'⟩ := (mem_componentVerts_iff (c := d)).mp hd
  exact hc'.symm.trans hd'

lemma remain_adj_mem_component {S T : Finset V}
    {c : (Remain G S T).ConnectedComponent}
    {u v : RemainVert S T}
    (hu : u.val ∈ componentVerts G S T c)
    (hadj : (Remain G S T).Adj u v) :
    v.val ∈ componentVerts G S T c := by
  have ⟨_, hmk⟩ := (mem_componentVerts_iff (c := c)).mp hu
  exact (mem_componentVerts_iff (c := c)).mpr
    ⟨v.property,
      (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hmk⟩

lemma remain_walk_mem_component {S T : Finset V}
    {c : (Remain G S T).ConnectedComponent}
    {u v : RemainVert S T}
    (hu : u.val ∈ componentVerts G S T c)
    (p : (Remain G S T).Walk u v) :
    v.val ∈ componentVerts G S T c := by
  match p with
  | .nil => exact hu
  | .cons hadj q =>
    exact remain_walk_mem_component
      (remain_adj_mem_component hu hadj) q

/-- Image of an old remainder component after returning `t` to the remainder. -/
noncomputable def persistErase {S T : Finset V} {t : V} (ht : t ∈ T)
    (c : (Remain G S T).ConnectedComponent) :
    (Remain G S (T.erase t)).ConnectedComponent :=
  c.map (G.induceHomOfLE (remainder_set_subset_erase ht)).toHom

lemma persistErase_mk {S T : Finset V} {t : V} (ht : t ∈ T)
    {x : V} (hx : x ∈ ((S ∪ T : Finset V) : Set V)ᶜ) :
    persistErase (G := G) ht ((Remain G S T).connectedComponentMk ⟨x, hx⟩) =
      (Remain G S (T.erase t)).connectedComponentMk
        ⟨x, remainder_set_subset_erase ht hx⟩ := by
  unfold persistErase
  rw [ConnectedComponent.map_mk]
  exact congrArg _ (Subtype.ext rfl)

lemma mem_persistErase_of_mem_old {S T : Finset V} {t : V} (ht : t ∈ T)
    {c : (Remain G S T).ConnectedComponent} {x : V}
    (hx : x ∈ componentVerts G S T c) :
    x ∈ componentVerts G S (T.erase t) (persistErase (G := G) ht c) := by
  have ⟨hxold, hmk⟩ := (mem_componentVerts_iff (c := c)).mp hx
  have hxnew := remainder_set_subset_erase ht hxold
  have hcomp :
      persistErase (G := G) ht c =
        (Remain G S (T.erase t)).connectedComponentMk ⟨x, hxnew⟩ := by
    simpa [hmk] using persistErase_mk (G := G) ht hxold
  exact (mem_componentVerts_iff).mpr ⟨hxnew, hcomp.symm⟩

lemma persist_adj_mem_old {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T)
    {c : (Remain G S T).ConnectedComponent}
    (hnomeet : ¬ MeetsVertex S T c t)
    {x y : RemainVert S (T.erase t)}
    (hx : x.val ∈ componentVerts G S T c)
    (hadj : (Remain G S (T.erase t)).Adj x y) :
    y.val ∈ componentVerts G S T c := by
  have hadjG : G.Adj x.val y.val := by simpa [induce_adj] using hadj
  have hy_ne_t : y.val ≠ t := by
    intro hy
    exact hnomeet ⟨x.val, hx, by simpa [hy] using hadjG⟩
  have hy_new : y.val ∈ remainderVerts G S (T.erase t) :=
    (mem_remainderVerts_iff (G := G)).2 ((Set.mem_compl_iff _ _).1 y.property)
  have hy_insert : y.val ∈ insert t (remainderVerts G S T) := by
    have hU := remainder_erase_t (G := G) hdis ht
    simpa [hU] using hy_new
  have hyU : y.val ∈ remainderVerts G S T :=
    (mem_insert.mp hy_insert).resolve_left hy_ne_t
  have hxU : x.val ∈ remainderVerts G S T :=
    componentVerts_subset_remainder c hx
  have hxold : x.val ∈ ((S ∪ T : Finset V) : Set V)ᶜ := by
    simpa [remainderVerts] using hxU
  have hyold : y.val ∈ ((S ∪ T : Finset V) : Set V)ᶜ := by
    simpa [remainderVerts] using hyU
  have hadjOld : (Remain G S T).Adj ⟨x.val, hxold⟩ ⟨y.val, hyold⟩ := by
    simpa [induce_adj] using hadjG
  have hxmk : (Remain G S T).connectedComponentMk ⟨x.val, hxold⟩ = c :=
    (mem_componentVerts_iff (c := c)).mp hx |>.2
  exact (mem_componentVerts_iff (c := c)).mpr
    ⟨hyold,
      (ConnectedComponent.connectedComponentMk_eq_of_adj hadjOld).symm.trans hxmk⟩

lemma persist_walk_mem_old {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T)
    {c : (Remain G S T).ConnectedComponent}
    (hnomeet : ¬ MeetsVertex S T c t)
    {u v : RemainVert S (T.erase t)}
    (hu : u.val ∈ componentVerts G S T c)
    (p : (Remain G S (T.erase t)).Walk u v) :
    v.val ∈ componentVerts G S T c := by
  match p with
  | .nil => exact hu
  | .cons hadj q =>
    exact persist_walk_mem_old hdis ht hnomeet
      (persist_adj_mem_old hdis ht hnomeet hu hadj) q

lemma persistErase_support_eq {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T)
    {c : (Remain G S T).ConnectedComponent}
    (hnomeet : ¬ MeetsVertex S T c t) :
    componentVerts G S (T.erase t) (persistErase (G := G) ht c) =
      componentVerts G S T c := by
  ext x
  constructor
  · intro hx
    have ⟨hxnew, hmk⟩ :=
      (mem_componentVerts_iff (c := persistErase (G := G) ht c)).mp hx
    obtain ⟨y, hy⟩ := componentVerts_nonempty (G := G) (S := S) (T := T) c
    have hynew := mem_persistErase_of_mem_old (G := G) ht hy
    have ⟨hynew', hmkY⟩ :=
      (mem_componentVerts_iff (c := persistErase (G := G) ht c)).mp hynew
    have hreach : (Remain G S (T.erase t)).Reachable
        ⟨y, hynew'⟩ ⟨x, hxnew⟩ :=
      ConnectedComponent.exact (hmkY.trans hmk.symm)
    obtain ⟨p⟩ := hreach
    exact persist_walk_mem_old hdis ht hnomeet hy p
  · exact mem_persistErase_of_mem_old (G := G) ht

lemma persistErase_injOn_nomet {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T) :
    Set.InjOn (persistErase (G := G) ht)
      {c : (Remain G S T).ConnectedComponent | ¬ MeetsVertex S T c t} := by
  intro c hc d hd heq
  have hs := persistErase_support_eq (G := G) hdis ht hc
  have ht' := persistErase_support_eq (G := G) hdis ht hd
  have hsup : componentVerts G S T c = componentVerts G S T d := by
    rw [← hs, heq, ht']
  obtain ⟨x, hx⟩ := componentVerts_nonempty (G := G) (S := S) (T := T) c
  exact eq_of_mem_componentVerts hx (hsup ▸ hx)

lemma orderedEdgeCount_union_right (A B C : Finset V) (hdis : Disjoint B C) :
    orderedEdgeCount G A (B ∪ C) =
      orderedEdgeCount G A B + orderedEdgeCount G A C := by
  simp only [orderedEdgeCount]
  have hunion :
      ((A ×ˢ (B ∪ C)).filter fun p => G.Adj p.1 p.2) =
        ((A ×ˢ B).filter fun p => G.Adj p.1 p.2) ∪
          ((A ×ˢ C).filter fun p => G.Adj p.1 p.2) := by
    ext p
    constructor
    · intro hp
      have hp' := mem_filter.mp hp
      have hprod := mem_product.mp hp'.1
      rcases mem_union.mp hprod.2 with hB | hC
      · exact mem_union.mpr (Or.inl
          (mem_filter.mpr ⟨mem_product.mpr ⟨hprod.1, hB⟩, hp'.2⟩))
      · exact mem_union.mpr (Or.inr
          (mem_filter.mpr ⟨mem_product.mpr ⟨hprod.1, hC⟩, hp'.2⟩))
    · intro hp
      rcases mem_union.mp hp with hB | hC
      · have hB' := mem_filter.mp hB
        have hprod := mem_product.mp hB'.1
        exact mem_filter.mpr
          ⟨mem_product.mpr ⟨hprod.1, mem_union.mpr (Or.inl hprod.2)⟩, hB'.2⟩
      · have hC' := mem_filter.mp hC
        have hprod := mem_product.mp hC'.1
        exact mem_filter.mpr
          ⟨mem_product.mpr ⟨hprod.1, mem_union.mpr (Or.inr hprod.2)⟩, hC'.2⟩
  have hdis' :
      Disjoint ((A ×ˢ B).filter fun p => G.Adj p.1 p.2)
        ((A ×ˢ C).filter fun p => G.Adj p.1 p.2) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have hB : p.2 ∈ B := (mem_product.mp (mem_filter.mp hp).1).2
    have hC : p.2 ∈ C := (mem_product.mp (mem_filter.mp hq).1).2
    exact Finset.disjoint_left.1 hdis hB hC
  rw [hunion, card_union_of_disjoint hdis']

lemma orderedEdgeCount_erase_add {A T : Finset V} {t : V} (ht : t ∈ T) :
    orderedEdgeCount G A T =
      orderedEdgeCount G A (T.erase t) + orderedEdgeCount G A {t} := by
  have hdis : Disjoint (T.erase t) ({t} : Finset V) := by
    simp [disjoint_singleton_right]
  calc
    orderedEdgeCount G A T
        = orderedEdgeCount G A (insert t (T.erase t)) := by rw [insert_erase ht]
      _ = orderedEdgeCount G A ({t} ∪ T.erase t) := by rw [insert_eq]
      _ = orderedEdgeCount G A (T.erase t ∪ {t}) := by rw [union_comm]
      _ = orderedEdgeCount G A (T.erase t) + orderedEdgeCount G A {t} :=
          orderedEdgeCount_union_right (G := G) A (T.erase t) {t} hdis

lemma persistErase_attach_eq {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T)
    {c : (Remain G S T).ConnectedComponent}
    (hnomeet : ¬ MeetsVertex S T c t) :
    componentAttach G S (T.erase t) (persistErase (G := G) ht c) =
      componentAttach G S T c := by
  have hsup := persistErase_support_eq (G := G) hdis ht hnomeet
  have hzero : orderedEdgeCount G (componentVerts G S T c) {t} = 0 := by
    have : ¬ 0 < orderedEdgeCount G (componentVerts G S T c) {t} := by
      simpa [MeetsVertex_iff_attach_pos (G := G) (c := c) (t := t)] using hnomeet
    omega
  unfold componentAttach
  rw [hsup, orderedEdgeCount_erase_add (G := G) ht, hzero, add_zero]

lemma persistErase_odd {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T)
    {c : (Remain G S T).ConnectedComponent}
    (hnomeet : ¬ MeetsVertex S T c t)
    (hodd : Odd (componentAttach G S T c)) :
    Odd (componentAttach G S (T.erase t) (persistErase (G := G) ht c)) := by
  simpa [persistErase_attach_eq (G := G) hdis ht hnomeet] using hodd

/-- Non-meeting odd remainder components inject into odd components after
returning `t`, so `h(S, T \ {t}) + h_t ≥ h(S,T)`. Oddness is attachment
parity, not vertex-order parity. -/
theorem hCount_erase_t_add_oddMeet_ge {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T) :
    hCount G S T ≤
      hCount G S (T.erase t) + oddMeetCount G S T t := by
  classical
  let s : Finset (Remain G S T).ConnectedComponent :=
    univ.filter fun c =>
      Odd (componentAttach G S T c) ∧ ¬ MeetsVertex S T c t
  have hsplit := hCount_eq_oddMeet_add_persist (G := G) (S := S) (T := T) t
  let tOdd : Finset (Remain G S (T.erase t)).ConnectedComponent :=
    univ.filter fun c => Odd (componentAttach G S (T.erase t) c)
  have himg : s.image (persistErase (G := G) ht) ⊆ tOdd := by
    intro c hc
    rcases mem_image.mp hc with ⟨d, hd, rfl⟩
    have hd' := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_univ _,
      persistErase_odd (G := G) hdis ht hd'.2.2 hd'.2.1⟩
  have hle : s.card ≤ hCount G S (T.erase t) := by
    have hcard : (s.image (persistErase (G := G) ht)).card = s.card :=
      card_image_of_injOn fun c hc d hd heq =>
        persistErase_injOn_nomet (G := G) hdis ht
          (mem_filter.mp hc).2.2 (mem_filter.mp hd).2.2 heq
    have hle' := card_le_card himg
    simpa [hCount, tOdd, hcard] using hle'
  rw [hsplit, add_comm (oddMeetCount G S T t), Nat.add_le_add_iff_right]
  exact hle

/-! ## Support-preserving persistence after moving `x` into `S` -/

lemma remainder_set_subset_insert {S T : Finset V} {x : V} :
    ((insert x S ∪ T : Finset V) : Set V)ᶜ ⊆ ((S ∪ T : Finset V) : Set V)ᶜ := by
  intro y hy
  have hy' : y ∉ insert x S ∪ T := by simpa using hy
  intro hST
  have hST' : y ∈ S ∪ T := by simpa using hST
  rcases mem_union.mp hST' with hS | hT
  · exact hy' (mem_union.mpr (Or.inl (mem_insert_of_mem hS)))
  · exact hy' (mem_union.mpr (Or.inr hT))

lemma mem_insert_remainder {S T : Finset V} {x y : V}
    (hyU : y ∈ remainderVerts G S T) (hyx : y ≠ x) :
    y ∈ ((insert x S ∪ T : Finset V) : Set V)ᶜ := by
  intro h
  have h' : y ∈ insert x S ∪ T := by simpa using h
  rcases mem_union.mp h' with hxS | hT
  · rcases mem_insert.mp hxS with rfl | hyS
    · exact hyx rfl
    · exact (mem_remainderVerts_iff (G := G)).1 hyU (mem_union.mpr (Or.inl hyS))
  · exact (mem_remainderVerts_iff (G := G)).1 hyU (mem_union.mpr (Or.inr hT))

lemma mem_old_of_mem_insert_component {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c)
    {y : V} (hy : y ∈ componentVerts G S T c) :
    y ∈ ((insert x S ∪ T : Finset V) : Set V)ᶜ :=
  mem_insert_remainder (G := G)
    (componentVerts_subset_remainder c hy)
    (fun h => hxc (by simpa [h] using hy))

lemma insert_adj_mem_old {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (_hxc : x ∉ componentVerts G S T c)
    {u v : RemainVert (insert x S) T}
    (hu : u.val ∈ componentVerts G S T c)
    (hadj : (Remain G (insert x S) T).Adj u v) :
    v.val ∈ componentVerts G S T c := by
  have hadjG : G.Adj u.val v.val := by simpa [induce_adj] using hadj
  have hvnew : v.val ∉ insert x S ∪ T := by simpa using v.property
  have hvST : v.val ∉ S ∪ T := by
    intro hST
    rcases mem_union.mp hST with hS | hT
    · exact hvnew (mem_union.mpr (Or.inl (mem_insert_of_mem hS)))
    · exact hvnew (mem_union.mpr (Or.inr hT))
  have hvU : v.val ∈ remainderVerts G S T := by simpa [remainderVerts] using hvST
  have huU : u.val ∈ remainderVerts G S T :=
    componentVerts_subset_remainder c hu
  have huold : u.val ∈ ((S ∪ T : Finset V) : Set V)ᶜ := by
    simpa [remainderVerts] using huU
  have hvold : v.val ∈ ((S ∪ T : Finset V) : Set V)ᶜ := by
    simpa [remainderVerts] using hvU
  have hadjOld : (Remain G S T).Adj ⟨u.val, huold⟩ ⟨v.val, hvold⟩ := by
    simpa [induce_adj] using hadjG
  have humk : (Remain G S T).connectedComponentMk ⟨u.val, huold⟩ = c :=
    (mem_componentVerts_iff (c := c)).mp hu |>.2
  exact (mem_componentVerts_iff (c := c)).mpr
    ⟨hvold,
      (ConnectedComponent.connectedComponentMk_eq_of_adj hadjOld).symm.trans humk⟩

lemma insert_walk_mem_old {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c)
    {u v : RemainVert (insert x S) T}
    (hu : u.val ∈ componentVerts G S T c)
    (p : (Remain G (insert x S) T).Walk u v) :
    v.val ∈ componentVerts G S T c := by
  match p with
  | .nil => exact hu
  | .cons hadj q =>
    exact insert_walk_mem_old hxc
      (insert_adj_mem_old hxc hu hadj) q

lemma insert_reachable_of_old_walk {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c)
    {u v : RemainVert S T}
    (hu : u.val ∈ componentVerts G S T c)
    (p : (Remain G S T).Walk u v) :
    (Remain G (insert x S) T).Reachable
      ⟨u.val, mem_old_of_mem_insert_component hxc hu⟩
      ⟨v.val, mem_old_of_mem_insert_component hxc
        (remain_walk_mem_component hu p)⟩ := by
  match p with
  | .nil => exact Reachable.rfl
  | .cons hadj q =>
    rename_i y
    have hy : y.val ∈ componentVerts G S T c :=
      remain_adj_mem_component hu hadj
    have hadjNew : (Remain G (insert x S) T).Adj
        ⟨u.val, mem_old_of_mem_insert_component hxc hu⟩
        ⟨y.val, mem_old_of_mem_insert_component hxc hy⟩ := by
      simpa [induce_adj] using hadj
    have hrest := insert_reachable_of_old_walk hxc hy q
    exact (Adj.reachable hadjNew).trans hrest


/-- Image of an old remainder component that does not contain `x`. -/
noncomputable def persistInsert {S T : Finset V} {x : V}
    (c : (Remain G S T).ConnectedComponent)
    (hxc : x ∉ componentVerts G S T c) :
    (Remain G (insert x S) T).ConnectedComponent :=
  (Remain G (insert x S) T).connectedComponentMk
    ⟨(componentVerts_nonempty (G := G) (S := S) (T := T) c).choose,
      mem_old_of_mem_insert_component (G := G) hxc
        (componentVerts_nonempty (G := G) (S := S) (T := T) c).choose_spec⟩

lemma persistInsert_eq_mk {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c)
    {y : V} (hy : y ∈ componentVerts G S T c) :
    persistInsert (G := G) c hxc =
      (Remain G (insert x S) T).connectedComponentMk
        ⟨y, mem_old_of_mem_insert_component (G := G) hxc hy⟩ := by
  have hz := (componentVerts_nonempty (G := G) (S := S) (T := T) c).choose_spec
  have ⟨hyold, hmkY⟩ := (mem_componentVerts_iff (c := c)).mp hy
  have ⟨hzold, hmkZ⟩ := (mem_componentVerts_iff (c := c)).mp hz
  have hold : (Remain G S T).Reachable
      ⟨(componentVerts_nonempty (G := G) (S := S) (T := T) c).choose, hzold⟩
      ⟨y, hyold⟩ :=
    ConnectedComponent.exact (hmkZ.trans hmkY.symm)
  obtain ⟨p⟩ := hold
  have hnew := insert_reachable_of_old_walk hxc hz p
  have : (⟨y, mem_old_of_mem_insert_component hxc
        (remain_walk_mem_component hz p)⟩ :
      RemainVert (insert x S) T) =
      ⟨y, mem_old_of_mem_insert_component hxc hy⟩ := Subtype.ext rfl
  exact ConnectedComponent.sound (this ▸ hnew)

lemma mem_persistInsert_of_mem_old {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c) {y : V}
    (hy : y ∈ componentVerts G S T c) :
    y ∈ componentVerts G (insert x S) T (persistInsert (G := G) c hxc) := by
  have hmk := persistInsert_eq_mk (G := G) hxc hy
  exact (mem_componentVerts_iff).mpr
    ⟨mem_old_of_mem_insert_component (G := G) hxc hy, hmk.symm⟩

lemma persistInsert_support_eq {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c) :
    componentVerts G (insert x S) T (persistInsert (G := G) c hxc) =
      componentVerts G S T c := by
  ext y
  constructor
  · intro hy
    have ⟨hynew, hmk⟩ :=
      (mem_componentVerts_iff (c := persistInsert (G := G) c hxc)).mp hy
    have hz := (componentVerts_nonempty (G := G) (S := S) (T := T) c).choose_spec
    have hznew := mem_persistInsert_of_mem_old (G := G) hxc hz
    have ⟨hznew', hmkZ⟩ :=
      (mem_componentVerts_iff (c := persistInsert (G := G) c hxc)).mp hznew
    have hreach : (Remain G (insert x S) T).Reachable
        ⟨(componentVerts_nonempty (G := G) (S := S) (T := T) c).choose, hznew'⟩
        ⟨y, hynew⟩ :=
      ConnectedComponent.exact (hmkZ.trans hmk.symm)
    obtain ⟨p⟩ := hreach
    exact insert_walk_mem_old hxc hz p
  · exact mem_persistInsert_of_mem_old (G := G) hxc

lemma persistInsert_attach_eq {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c) :
    componentAttach G (insert x S) T (persistInsert (G := G) c hxc) =
      componentAttach G S T c := by
  unfold componentAttach
  rw [persistInsert_support_eq (G := G) hxc]

lemma persistInsert_odd {S T : Finset V} {x : V}
    {c : (Remain G S T).ConnectedComponent}
    (hxc : x ∉ componentVerts G S T c)
    (hodd : Odd (componentAttach G S T c)) :
    Odd (componentAttach G (insert x S) T (persistInsert (G := G) c hxc)) := by
  simpa [persistInsert_attach_eq (G := G) hxc] using hodd

/-- Other old odd components persist after moving `x` into `S`, giving
`h(S ∪ {x}, T) ≥ h(S,T) - 1`. -/
theorem hCount_insert_ge {S T : Finset V} {x : V} (_hxST : x ∉ S ∪ T) :
    hCount G S T ≤ hCount G (insert x S) T + 1 := by
  classical
  let s : Finset (Remain G S T).ConnectedComponent :=
    univ.filter fun c =>
      Odd (componentAttach G S T c) ∧ x ∉ componentVerts G S T c
  let sX : Finset (Remain G S T).ConnectedComponent :=
    univ.filter fun c =>
      Odd (componentAttach G S T c) ∧ x ∈ componentVerts G S T c
  have hunion :
      (univ.filter fun c : (Remain G S T).ConnectedComponent =>
        Odd (componentAttach G S T c)) = sX ∪ s := by
    ext c
    simp only [mem_union, mem_filter, mem_univ, true_and, s, sX]
    constructor
    · intro h
      by_cases hx : x ∈ componentVerts G S T c
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
    · intro h
      rcases h with h | h <;> exact h.1
  have hdis : Disjoint sX s := by
    rw [Finset.disjoint_left]
    intro c hc hn
    exact (mem_filter.mp hn).2.2 (mem_filter.mp hc).2.2
  have hle1 : sX.card ≤ 1 := by
    refine card_le_one.mpr ?_
    intro c hc d hd
    exact eq_of_mem_componentVerts (mem_filter.mp hc).2.2 (mem_filter.mp hd).2.2
  let t : Finset (Remain G (insert x S) T).ConnectedComponent :=
    univ.filter fun c => Odd (componentAttach G (insert x S) T c)
  let f : {c // c ∈ s} → {c // c ∈ t} := fun c =>
    ⟨persistInsert (G := G) c.1 (mem_filter.mp c.2).2.2,
      by
        have hxc : x ∉ componentVerts G S T c.1 := (mem_filter.mp c.2).2.2
        have hodd' : Odd (componentAttach G S T c.1) := (mem_filter.mp c.2).2.1
        exact mem_filter.mpr ⟨mem_univ _, persistInsert_odd (G := G) hxc hodd'⟩⟩
  have hf : Function.Injective f := by
    intro c d hcd
    have hxc : x ∉ componentVerts G S T c.1 := (mem_filter.mp c.2).2.2
    have hxd : x ∉ componentVerts G S T d.1 := (mem_filter.mp d.2).2.2
    have heq : persistInsert (G := G) c.1 hxc = persistInsert (G := G) d.1 hxd :=
      congrArg Subtype.val hcd
    have hsup : componentVerts G S T c.1 = componentVerts G S T d.1 := by
      rw [← persistInsert_support_eq (G := G) hxc, heq,
        persistInsert_support_eq (G := G) hxd]
    obtain ⟨z, hz⟩ := componentVerts_nonempty (G := G) (S := S) (T := T) c.1
    exact Subtype.ext (eq_of_mem_componentVerts hz (hsup ▸ hz))
  have hle : s.card ≤ t.card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hle' : s.card ≤ hCount G (insert x S) T := by
    simpa [hCount, t] using hle
  have hcount : hCount G S T = sX.card + s.card := by
    simp only [hCount, hunion, card_union_of_disjoint hdis]
  linarith [hle']

lemma oddMeetCount_le_degDelete {S T : Finset V} {t : V}
    (_hdis : Disjoint S T) (_ht : t ∈ T) :
    oddMeetCount G S T t ≤ degDelete G S t := by
  classical
  let s : Finset (Remain G S T).ConnectedComponent :=
    univ.filter fun c => Odd (componentAttach G S T c) ∧ MeetsVertex S T c t
  let f : (Remain G S T).ConnectedComponent → V := fun c =>
    if h : MeetsVertex S T c t then Classical.choose h else t
  have himg : Set.MapsTo f (s : Set _) ((G.neighborFinset t \ S : Finset V) : Set V) := by
    intro c hc
    have hmeet : MeetsVertex S T c t := (mem_filter.mp (show c ∈ s from hc)).2.2
    have ⟨hxD, hadj⟩ := Classical.choose_spec hmeet
    have hxU := componentVerts_subset_remainder c hxD
    have hxS : Classical.choose hmeet ∉ S := by
      have : Classical.choose hmeet ∉ S ∪ T :=
        (mem_remainderVerts_iff (G := G)).1 hxU
      exact fun hS => this (mem_union.mpr (Or.inl hS))
    have : f c = Classical.choose hmeet := by simp [f, hmeet]
    rw [this]
    refine mem_sdiff.mpr ⟨?_, hxS⟩
    simp [mem_neighborFinset, hadj.symm]
  have hinj : Set.InjOn f (s : Set _) := by
    intro c hc d hd heq
    have hmc : MeetsVertex S T c t := (mem_filter.mp (show c ∈ s from hc)).2.2
    have hmd : MeetsVertex S T d t := (mem_filter.mp (show d ∈ s from hd)).2.2
    have heq' : Classical.choose hmc = Classical.choose hmd := by
      simpa [f, hmc, hmd] using heq
    exact eq_of_mem_componentVerts (Classical.choose_spec hmc).1
      (heq' ▸ (Classical.choose_spec hmd).1)
  have hle : s.card ≤ (G.neighborFinset t \ S).card :=
    card_le_card_of_injOn f himg hinj
  simpa [oddMeetCount, degDelete, s] using hle

lemma ExtremalBarrier.degDelete_eq_oddMeet (B : ExtremalBarrier G) {t : V}
    (ht : t ∈ B.T) :
    degDelete G B.S t = oddMeetCount G B.S B.T t := by
  have hΔ := delta_erase_t (G := G) (S := B.S) (T := B.T) ht
  have hnn := B.nonneg_erase ht
  have hge := hCount_erase_t_add_oddMeet_ge (G := G) B.disjoint ht
  have hsub : (hCount G B.S B.T : ℤ) - (hCount G B.S (B.T.erase t) : ℤ) ≤
      (oddMeetCount G B.S B.T t : ℤ) := by
    have : (hCount G B.S B.T : ℤ) ≤
        (hCount G B.S (B.T.erase t) : ℤ) + (oddMeetCount G B.S B.T t : ℤ) :=
      Nat.cast_le.mpr hge
    linarith
  have hdge : (oddMeetCount G B.S B.T t : ℤ) ≤ (degDelete G B.S t : ℤ) :=
    Nat.cast_le.mpr (oddMeetCount_le_degDelete (G := G) B.disjoint ht)
  have : (degDelete G B.S t : ℤ) = (oddMeetCount G B.S B.T t : ℤ) := by
    linarith [B.neg]
  exact Int.natCast_inj.mp this

lemma ExtremalBarrier.attach_le_one (B : ExtremalBarrier G) {x : V}
    (hx : x ∉ B.S ∪ B.T) :
    orderedEdgeCount G B.T {x} ≤ 1 := by
  have hΔ := delta_insert_S (G := G) (S := B.S) (T := B.T)
    (fun hxS => hx (mem_union.mpr (Or.inl hxS)))
  have hnn := B.nonneg_insert hx
  have hge := hCount_insert_ge (G := G) hx
  have hsub : (hCount G B.S B.T : ℤ) - (hCount G (insert x B.S) B.T : ℤ) ≤ 1 := by
    have : (hCount G B.S B.T : ℤ) ≤
        (hCount G (insert x B.S) B.T : ℤ) + 1 := Nat.cast_le.mpr hge
    linarith
  have : (orderedEdgeCount G B.T {x} : ℤ) ≤ 1 := by
    linarith [B.neg]
  exact_mod_cast this

lemma oddMeetCount_le_remainderNeighbors {S T : Finset V} {t : V} :
    oddMeetCount G S T t ≤
      (G.neighborFinset t ∩ remainderVerts G S T).card := by
  classical
  let s : Finset (Remain G S T).ConnectedComponent :=
    univ.filter fun c => Odd (componentAttach G S T c) ∧ MeetsVertex S T c t
  let f : (Remain G S T).ConnectedComponent → V := fun c =>
    if h : MeetsVertex S T c t then Classical.choose h else t
  have himg : s.image f ⊆ G.neighborFinset t ∩ remainderVerts G S T := by
    intro x hx
    rcases mem_image.mp hx with ⟨c, hc, rfl⟩
    have hmeet : MeetsVertex S T c t := (mem_filter.mp hc).2.2
    have ⟨hxD, hadj⟩ := Classical.choose_spec hmeet
    have hxU := componentVerts_subset_remainder c hxD
    have : f c = Classical.choose hmeet := by simp [f, hmeet]
    rw [this]
    refine mem_inter.mpr ⟨?_, hxU⟩
    simp [mem_neighborFinset, hadj.symm]
  have hcard : (s.image f).card = s.card :=
    card_image_of_injOn fun c hc d hd heq => by
      have hmc : MeetsVertex S T c t := (mem_filter.mp hc).2.2
      have hmd : MeetsVertex S T d t := (mem_filter.mp hd).2.2
      have heq' : Classical.choose hmc = Classical.choose hmd := by
        simpa [f, hmc, hmd] using heq
      exact eq_of_mem_componentVerts (Classical.choose_spec hmc).1
        (heq' ▸ (Classical.choose_spec hmd).1)
  have hle := card_le_card himg
  simpa [oddMeetCount, s, hcard] using hle

lemma ExtremalBarrier.neighbor_T_eq_empty (B : ExtremalBarrier G) {t : V}
    (ht : t ∈ B.T) :
    G.neighborFinset t ∩ B.T = ∅ := by
  have hsplit := degDelete_split (G := G) B.disjoint ht
  have heq := B.degDelete_eq_oddMeet ht
  have hU := oddMeetCount_le_remainderNeighbors (G := G) (S := B.S) (T := B.T)
    (t := t)
  have : (G.neighborFinset t ∩ B.T).card = 0 := by
    have : (G.neighborFinset t ∩ B.T).card +
        (G.neighborFinset t ∩ remainderVerts G B.S B.T).card =
        oddMeetCount G B.S B.T t := by
      simpa [hsplit] using heq
    omega
  exact card_eq_zero.mp this

lemma ExtremalBarrier.T_independent (B : ExtremalBarrier G) {t₁ t₂ : V}
    (ht₁ : t₁ ∈ B.T) (ht₂ : t₂ ∈ B.T) : ¬ G.Adj t₁ t₂ := by
  intro hadj
  have : t₂ ∈ G.neighborFinset t₁ ∩ B.T := by
    simp [mem_neighborFinset, hadj, ht₂]
  have hempty := B.neighbor_T_eq_empty ht₁
  simp [hempty] at this

lemma ExtremalBarrier.remainderNeighbors_eq_oddMeet (B : ExtremalBarrier G)
    {t : V} (ht : t ∈ B.T) :
    (G.neighborFinset t ∩ remainderVerts G B.S B.T).card =
      oddMeetCount G B.S B.T t := by
  have hsplit := degDelete_split (G := G) B.disjoint ht
  have heq := B.degDelete_eq_oddMeet ht
  have hempty := B.neighbor_T_eq_empty ht
  have : (G.neighborFinset t ∩ B.T).card = 0 := by simp [hempty]
  have : (G.neighborFinset t ∩ remainderVerts G B.S B.T).card =
      oddMeetCount G B.S B.T t := by
    simpa [hsplit, this] using heq
  exact this

/-- At most one original neighbor of `t` lies in a given remainder component. -/
lemma ExtremalBarrier.one_neighbor_in_component (B : ExtremalBarrier G)
    {t : V} (ht : t ∈ B.T)
    (c : (Remain G B.S B.T).ConnectedComponent) :
    ((componentVerts G B.S B.T c).filter fun x => G.Adj t x).card ≤ 1 := by
  classical
  let N := (componentVerts G B.S B.T c).filter fun x => G.Adj t x
  let U := G.neighborFinset t ∩ remainderVerts G B.S B.T
  let s : Finset (Remain G B.S B.T).ConnectedComponent :=
    univ.filter fun d =>
      Odd (componentAttach G B.S B.T d) ∧ MeetsVertex B.S B.T d t
  have hNsub : N ⊆ U := by
    intro x hx
    have hx' := mem_filter.mp hx
    exact mem_inter.mpr ⟨by simp [mem_neighborFinset, hx'.2],
      componentVerts_subset_remainder c hx'.1⟩
  have hUeq : U.card = s.card := by
    simpa [oddMeetCount, s] using B.remainderNeighbors_eq_oddMeet ht
  by_contra h
  have h2 : 2 ≤ N.card := Nat.succ_le_of_lt (lt_of_not_ge h)
  let s' := s.erase c
  let f : (Remain G B.S B.T).ConnectedComponent → V := fun d =>
    if hmeet : MeetsVertex B.S B.T d t then Classical.choose hmeet else t
  have himg : s'.image f ⊆ U \ N := by
    intro x hx
    rcases mem_image.mp hx with ⟨d, hd, rfl⟩
    have hd' := mem_filter.mp (mem_of_mem_erase hd)
    have hmeet : MeetsVertex B.S B.T d t := hd'.2.2
    have ⟨hxD, hadj⟩ := Classical.choose_spec hmeet
    have hxU := componentVerts_subset_remainder d hxD
    have hf : f d = Classical.choose hmeet := by simp [f, hmeet]
    rw [hf]
    have hxN : Classical.choose hmeet ∉ N := by
      intro hN
      have : Classical.choose hmeet ∈ componentVerts G B.S B.T c :=
        (mem_filter.mp hN).1
      have hdc : d = c := eq_of_mem_componentVerts hxD this
      exact (mem_erase.mp hd).1 hdc
    refine mem_sdiff.mpr ⟨?_, hxN⟩
    exact mem_inter.mpr ⟨by simp [mem_neighborFinset, hadj.symm], hxU⟩
  have hinj : (s'.image f).card = s'.card :=
    card_image_of_injOn fun d hd e he heq => by
      have hmd : MeetsVertex B.S B.T d t :=
        (mem_filter.mp (mem_of_mem_erase hd)).2.2
      have hme : MeetsVertex B.S B.T e t :=
        (mem_filter.mp (mem_of_mem_erase he)).2.2
      have heq' : Classical.choose hmd = Classical.choose hme := by
        simpa [f, hmd, hme] using heq
      exact eq_of_mem_componentVerts (Classical.choose_spec hmd).1
        (heq' ▸ (Classical.choose_spec hme).1)
  have hle' : s'.card ≤ (U \ N).card := by
    have := card_le_card himg
    rwa [hinj] at this
  have hsum : (U \ N).card + N.card = U.card :=
    card_sdiff_add_card_eq_card hNsub
  have hcomb : s'.card + N.card ≤ s.card := by
    have hleAdd : s'.card + N.card ≤ (U \ N).card + N.card :=
      Nat.add_le_add_right hle' N.card
    have : s'.card + N.card ≤ U.card := hleAdd.trans_eq hsum
    simpa [hUeq] using this
  have hs'le : s.card ≤ s'.card + 1 := by
    by_cases hc : c ∈ s
    · have hcard : s'.card = s.card - 1 := card_erase_of_mem hc
      have hpos : 1 ≤ s.card := Nat.succ_le_iff.mpr (card_pos.mpr ⟨c, hc⟩)
      exact le_of_eq (by rw [hcard, Nat.sub_add_cancel hpos])
    · have hs'eq : s' = s := erase_eq_of_notMem hc
      rw [hs'eq]
      exact Nat.le_add_right _ 1
  have hleN : N.card ≤ 1 := by
    have : s'.card + N.card ≤ s'.card + 1 := hcomb.trans hs'le
    exact Nat.add_le_add_iff_left.mp this
  exact (not_le_of_gt (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) h2)) hleN

lemma remainder_disjoint_T {S T : Finset V}
    (c : (Remain G S T).ConnectedComponent) {x : V}
    (hx : x ∈ componentVerts G S T c) : x ∉ T := by
  have hxU := componentVerts_subset_remainder c hx
  exact fun hT =>
    (mem_remainderVerts_iff (G := G)).1 hxU (mem_union.mpr (Or.inr hT))

/-- Three matching D–T edges: attachment vertices are pairwise nonadjacent,
because t1,d1,d2,t2 would induce a P4 isolated from t3. -/
lemma ExtremalBarrier.matching_attachments_not_adj
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    {c : (Remain G B.S B.T).ConnectedComponent}
    {t1 t2 t3 d1 d2 d3 : V}
    (ht1 : t1 ∈ B.T) (ht2 : t2 ∈ B.T) (ht3 : t3 ∈ B.T)
    (hneT12 : t1 ≠ t2) (hneT13 : t1 ≠ t3) (hneT23 : t2 ≠ t3)
    (hd1 : d1 ∈ componentVerts G B.S B.T c)
    (hd2 : d2 ∈ componentVerts G B.S B.T c)
    (hd3 : d3 ∈ componentVerts G B.S B.T c)
    (hneD12 : d1 ≠ d2) (hneD13 : d1 ≠ d3) (hneD23 : d2 ≠ d3)
    (hadj1 : G.Adj t1 d1) (hadj2 : G.Adj t2 d2) (hadj3 : G.Adj t3 d3) :
    ¬ G.Adj d1 d2 := by
  intro hadjD
  have hd1T : d1 ∉ B.T := remainder_disjoint_T (G := G) c hd1
  have hd2T : d2 ∉ B.T := remainder_disjoint_T (G := G) c hd2
  have hd3T : d3 ∉ B.T := remainder_disjoint_T (G := G) c hd3
  have hne_t1d1 : t1 ≠ d1 := hadj1.ne
  have hne_t2d2 : t2 ≠ d2 := hadj2.ne
  have hne_t1d2 : t1 ≠ d2 := by
    intro h; subst h; exact hd2T ht1
  have hne_t2d1 : t2 ≠ d1 := by
    intro h; subst h; exact hd1T ht2
  have hne_t3d1 : t3 ≠ d1 := by
    intro h; subst h; exact hd1T ht3
  have hne_t3d2 : t3 ≠ d2 := by
    intro h; subst h; exact hd2T ht3
  have hne_t1d3 : t1 ≠ d3 := by
    intro h; subst h; exact hd3T ht1
  have hne_t2d3 : t2 ≠ d3 := by
    intro h; subst h; exact hd3T ht2
  have hne_t3d3 : t3 ≠ d3 := hadj3.ne
  have nAdj_t1d2 : ¬ G.Adj t1 d2 := by
    intro h
    have hle := B.one_neighbor_in_component ht1 c
    have hN :
        ({d1, d2} : Finset V) ⊆
          (componentVerts G B.S B.T c).filter (fun x => G.Adj t1 x) := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx2
      · exact mem_filter.mpr ⟨hd1, hadj1⟩
      · have : x = d2 := mem_singleton.mp hx2
        subst this
        exact mem_filter.mpr ⟨hd2, h⟩
    have h2 : 2 ≤ ({d1, d2} : Finset V).card := by
      simp [card_insert_of_notMem, hneD12]
    have : 2 ≤ ((componentVerts G B.S B.T c).filter
        fun x => G.Adj t1 x).card :=
      le_trans h2 (card_le_card hN)
    omega
  have nAdj_t2d1 : ¬ G.Adj t2 d1 := by
    intro h
    have hle := B.one_neighbor_in_component ht2 c
    have hN :
        ({d1, d2} : Finset V) ⊆
          (componentVerts G B.S B.T c).filter (fun x => G.Adj t2 x) := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx2
      · exact mem_filter.mpr ⟨hd1, h⟩
      · have : x = d2 := mem_singleton.mp hx2
        subst this
        exact mem_filter.mpr ⟨hd2, hadj2⟩
    have h2 : 2 ≤ ({d1, d2} : Finset V).card := by
      simp [card_insert_of_notMem, hneD12]
    have : 2 ≤ ((componentVerts G B.S B.T c).filter
        fun x => G.Adj t2 x).card :=
      le_trans h2 (card_le_card hN)
    omega
  have hp4 : InducedP4 G t1 d1 d2 t2 :=
    ⟨hne_t1d1, hne_t1d2, hneT12, hneD12, hne_t2d1.symm, hne_t2d2.symm,
      hadj1, hadjD, hadj2.symm,
      nAdj_t1d2, B.T_independent ht1 ht2, (fun h => nAdj_t2d1 h.symm)⟩
  have hiso := hpat hp4 hneT13.symm hne_t3d1 hne_t3d2 hneT23.symm
  rcases hiso with h31 | h3d1 | h3d2 | h32
  · exact B.T_independent ht3 ht1 h31
  · have hle := B.one_neighbor_in_component ht3 c
    have hN :
        ({d1, d3} : Finset V) ⊆
          (componentVerts G B.S B.T c).filter (fun x => G.Adj t3 x) := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx2
      · exact mem_filter.mpr ⟨hd1, h3d1⟩
      · have : x = d3 := mem_singleton.mp hx2
        subst this
        exact mem_filter.mpr ⟨hd3, hadj3⟩
    have h2 : 2 ≤ ({d1, d3} : Finset V).card := by
      simp [card_insert_of_notMem, hneD13]
    have : 2 ≤ ((componentVerts G B.S B.T c).filter
        fun x => G.Adj t3 x).card :=
      le_trans h2 (card_le_card hN)
    omega
  · have hle := B.one_neighbor_in_component ht3 c
    have hN :
        ({d2, d3} : Finset V) ⊆
          (componentVerts G B.S B.T c).filter (fun x => G.Adj t3 x) := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx2
      · exact mem_filter.mpr ⟨hd2, h3d2⟩
      · have : x = d3 := mem_singleton.mp hx2
        subst this
        exact mem_filter.mpr ⟨hd3, hadj3⟩
    have h2 : 2 ≤ ({d2, d3} : Finset V).card := by
      simp [card_insert_of_notMem, hneD23]
    have : 2 ≤ ((componentVerts G B.S B.T c).filter
        fun x => G.Adj t3 x).card :=
      le_trans h2 (card_le_card hN)
    omega
  · exact B.T_independent ht3 ht2 h32

/-! ## Matching uniqueness helpers -/

lemma ExtremalBarrier.eq_of_two_T_neighbors
    (B : ExtremalBarrier G) {x t1 t2 : V}
    (hx : x ∉ B.S ∪ B.T) (ht1 : t1 ∈ B.T) (ht2 : t2 ∈ B.T)
    (h1 : G.Adj x t1) (h2 : G.Adj x t2) : t1 = t2 := by
  have hle := B.attach_le_one hx
  have hcard := orderedEdgeCount_singleton_right (G := G) B.T x
  have hs :
      ({t1, t2} : Finset V) ⊆ B.T.filter fun t => G.Adj t x := by
    intro t ht
    rcases mem_insert.mp ht with rfl | ht'
    · exact mem_filter.mpr ⟨ht1, h1.symm⟩
    · have : t = t2 := mem_singleton.mp ht'
      subst this
      exact mem_filter.mpr ⟨ht2, h2.symm⟩
  by_contra hne
  have h2card : 2 ≤ ({t1, t2} : Finset V).card := by
    simp [card_insert_of_notMem, hne]
  have : 2 ≤ orderedEdgeCount G B.T {x} := by
    simpa [hcard] using le_trans h2card (card_le_card hs)
  omega

lemma ExtremalBarrier.eq_of_two_D_neighbors
    (B : ExtremalBarrier G) {t x y : V}
    {c : (Remain G B.S B.T).ConnectedComponent}
    (ht : t ∈ B.T)
    (hx : x ∈ componentVerts G B.S B.T c)
    (hy : y ∈ componentVerts G B.S B.T c)
    (h1 : G.Adj t x) (h2 : G.Adj t y) : x = y := by
  have hle := B.one_neighbor_in_component ht c
  have hs :
      ({x, y} : Finset V) ⊆
        (componentVerts G B.S B.T c).filter fun z => G.Adj t z := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz'
    · exact mem_filter.mpr ⟨hx, h1⟩
    · have : z = y := mem_singleton.mp hz'
      subst this
      exact mem_filter.mpr ⟨hy, h2⟩
  by_contra hne
  have h2card : 2 ≤ ({x, y} : Finset V).card := by
    simp [card_insert_of_notMem, hne]
  have : 2 ≤ ((componentVerts G B.S B.T c).filter fun z => G.Adj t z).card :=
    le_trans h2card (card_le_card hs)
  omega

lemma remain_mk_mem {S T : Finset V} {x : V}
    (hx : x ∈ remainderVerts G S T) :
    x ∈ componentVerts G S T
      ((Remain G S T).connectedComponentMk
        ⟨x, by simpa [remainderVerts] using hx⟩) :=
  (mem_componentVerts_iff).mpr ⟨by simpa [remainderVerts] using hx, rfl⟩

lemma remain_reachable_of_mem_component {S T : Finset V}
    {c : (Remain G S T).ConnectedComponent} {d1 d2 : V}
    (hd1 : d1 ∈ componentVerts G S T c)
    (hd2 : d2 ∈ componentVerts G S T c) :
    (Remain G S T).Reachable
      ⟨d1, (mem_componentVerts_iff (c := c)).mp hd1 |>.1⟩
      ⟨d2, (mem_componentVerts_iff (c := c)).mp hd2 |>.1⟩ := by
  have ⟨_, mk1⟩ := (mem_componentVerts_iff (c := c)).mp hd1
  have ⟨_, mk2⟩ := (mem_componentVerts_iff (c := c)).mp hd2
  exact ConnectedComponent.exact (mk1.trans mk2.symm)

/-! ## No even-component attachment -/

/-- Every original neighbour of `t` outside `S` lies in an odd old remainder
component. An even component cannot contain such a neighbour: the chosen-neighbour
injection from odd-meeting components is already of cardinality `degDelete`. -/
lemma ExtremalBarrier.even_not_meet (B : ExtremalBarrier G) {t : V}
    (ht : t ∈ B.T)
    (c : (Remain G B.S B.T).ConnectedComponent)
    (heven : Even (componentAttach G B.S B.T c)) :
    ¬ MeetsVertex B.S B.T c t := by
  classical
  intro hmeet
  let U := G.neighborFinset t ∩ remainderVerts G B.S B.T
  let s : Finset (Remain G B.S B.T).ConnectedComponent :=
    univ.filter fun d =>
      Odd (componentAttach G B.S B.T d) ∧ MeetsVertex B.S B.T d t
  let f : (Remain G B.S B.T).ConnectedComponent → V := fun d =>
    if h : MeetsVertex B.S B.T d t then Classical.choose h else t
  have hUeq : U.card = s.card := by
    simpa [oddMeetCount, s, U] using B.remainderNeighbors_eq_oddMeet ht
  have ⟨x, hxD, hadj⟩ := hmeet
  have hxU : x ∈ U := by
    refine mem_inter.mpr ⟨?_, componentVerts_subset_remainder c hxD⟩
    simp [mem_neighborFinset, hadj.symm]
  have himg : s.image f ⊆ U := by
    intro y hy
    rcases mem_image.mp hy with ⟨d, hd, rfl⟩
    have hmeet' : MeetsVertex B.S B.T d t := (mem_filter.mp hd).2.2
    have ⟨hyD, hyadj⟩ := Classical.choose_spec hmeet'
    have : f d = Classical.choose hmeet' := by simp [f, hmeet']
    rw [this]
    refine mem_inter.mpr ⟨?_, componentVerts_subset_remainder d hyD⟩
    simp [mem_neighborFinset, hyadj.symm]
  have hinj : (s.image f).card = s.card :=
    card_image_of_injOn fun d hd e he heq => by
      have hmd : MeetsVertex B.S B.T d t := (mem_filter.mp hd).2.2
      have hme : MeetsVertex B.S B.T e t := (mem_filter.mp he).2.2
      have heq' : Classical.choose hmd = Classical.choose hme := by
        simpa [f, hmd, hme] using heq
      exact eq_of_mem_componentVerts (Classical.choose_spec hmd).1
        (heq' ▸ (Classical.choose_spec hme).1)
  have hx_not : x ∉ s.image f := by
    intro hximg
    rcases mem_image.mp hximg with ⟨d, hd, hdf⟩
    have hmeet' : MeetsVertex B.S B.T d t := (mem_filter.mp hd).2.2
    have hf : f d = Classical.choose hmeet' := by simp [f, hmeet']
    have hxeq : Classical.choose hmeet' = x := by
      rw [← hf, hdf]
    have hdc : d = c :=
      eq_of_mem_componentVerts (hxeq ▸ (Classical.choose_spec hmeet').1) hxD
    have hodd : Odd (componentAttach G B.S B.T c) := by
      simpa [hdc] using (mem_filter.mp hd).2.1
    exact Nat.not_odd_iff_even.2 heven hodd
  have hsub : s.image f ⊆ U.erase x := by
    intro y hy
    exact mem_erase.mpr ⟨fun h => hx_not (h ▸ hy), himg hy⟩
  have hle : s.card ≤ (U.erase x).card := by
    have := card_le_card hsub
    rwa [hinj] at this
  have hpos : 1 ≤ U.card := Nat.succ_le_iff.mpr (card_pos.mpr ⟨x, hxU⟩)
  have : s.card ≤ U.card - 1 := by
    simpa [card_erase_of_mem hxU] using hle
  omega

lemma componentAttach_pos_iff_exists_meet {S T : Finset V}
    (c : (Remain G S T).ConnectedComponent) :
    0 < componentAttach G S T c ↔
      ∃ t ∈ T, MeetsVertex S T c t := by
  constructor
  · intro hpos
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hp' := mem_filter.mp hp
    have hprod := mem_product.mp hp'.1
    exact ⟨p.2, hprod.2, ⟨p.1, hprod.1, hp'.2⟩⟩
  · rintro ⟨t, ht, x, hx, hadj⟩
    have : (x, t) ∈ (componentVerts G S T c ×ˢ T).filter fun q => G.Adj q.1 q.2 :=
      mem_filter.mpr ⟨mem_product.mpr ⟨hx, ht⟩, hadj⟩
    exact Finset.card_pos.mpr ⟨_, this⟩

lemma ExtremalBarrier.even_attach_eq_zero (B : ExtremalBarrier G)
    (c : (Remain G B.S B.T).ConnectedComponent)
    (heven : Even (componentAttach G B.S B.T c)) :
    componentAttach G B.S B.T c = 0 := by
  by_contra hne
  have hpos : 0 < componentAttach G B.S B.T c := Nat.pos_of_ne_zero hne
  obtain ⟨t, ht, hmeet⟩ := (componentAttach_pos_iff_exists_meet (G := G) c).1 hpos
  exact B.even_not_meet ht c heven hmeet

/-! ## Shortest-path chords and the three-edge bound -/

/-- On a shortest walk, vertices at index distance at least two are nonadjacent.
This is the generic Mathlib-style chord fact used by `Cograph.Basic`. -/
lemma not_adj_getVert_of_length_eq_dist {W : Type*} {H : SimpleGraph W}
    {u w : W} {p : H.Walk u w}
    (hp : p.length = H.dist u w) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hgap : i + 2 ≤ j) :
    ¬ H.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  let q : H.Walk u w :=
    ((p.take i).append hadj.toWalk).append (p.drop j)
  have hlen : q.length = i + 1 + (p.length - j) := by
    simp [q, Walk.length_append, Walk.take_length, Walk.drop_length, Adj.toWalk,
      Walk.length_cons, hi, Nat.min_eq_left hi]
  have hlt : q.length < p.length := by
    have : i + 1 + (p.length - j) < p.length := by
      have : i + 1 < j := Nat.lt_of_succ_le (by omega)
      have hsub : p.length - j + j = p.length := Nat.sub_add_cancel hj
      omega
    simpa [hlen] using this
  have : H.dist u w ≤ q.length := dist_le q
  omega

lemma remain_getVert_mem_component {S T : Finset V}
    {c : (Remain G S T).ConnectedComponent}
    {u v : RemainVert S T} (p : (Remain G S T).Walk u v)
    (hu : u.val ∈ componentVerts G S T c) (n : ℕ) :
    (p.getVert n).val ∈ componentVerts G S T c :=
  remain_walk_mem_component hu (p.take n)

lemma remain_path_getVert_val_inj {S T : Finset V}
    {u v : RemainVert S T} {p : (Remain G S T).Walk u v}
    (hp : p.IsPath) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (heq : (p.getVert i).val = (p.getVert j).val) : i = j :=
  hp.getVert_injOn (show i ∈ {k | k ≤ p.length} from hi)
    (show j ∈ {k | k ≤ p.length} from hj) (Subtype.ext heq)

lemma mem_componentVerts_not_ST {S T : Finset V}
    {c : (Remain G S T).ConnectedComponent} {x : V}
    (hx : x ∈ componentVerts G S T c) : x ∉ S ∪ T :=
  (mem_remainderVerts_iff (G := G)).1 (componentVerts_subset_remainder c hx)

lemma ExtremalBarrier.exists_three_matching
    (B : ExtremalBarrier G)
    {c : (Remain G B.S B.T).ConnectedComponent}
    (h3 : 3 ≤ componentAttach G B.S B.T c) :
    ∃ t1 t2 t3 d1 d2 d3,
      t1 ∈ B.T ∧ t2 ∈ B.T ∧ t3 ∈ B.T ∧
      t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
      d1 ∈ componentVerts G B.S B.T c ∧
      d2 ∈ componentVerts G B.S B.T c ∧
      d3 ∈ componentVerts G B.S B.T c ∧
      d1 ≠ d2 ∧ d1 ≠ d3 ∧ d2 ≠ d3 ∧
      G.Adj t1 d1 ∧ G.Adj t2 d2 ∧ G.Adj t3 d3 := by
  classical
  let E := (componentVerts G B.S B.T c ×ˢ B.T).filter fun p => G.Adj p.1 p.2
  have hE : 3 ≤ E.card := h3
  obtain ⟨s, hsub, hscard⟩ := exists_subset_card_eq hE
  obtain ⟨p1, p2, p3, h12, h13, h23, rfl⟩ := card_eq_three.mp hscard
  have hp1 := mem_filter.mp (hsub (mem_insert_self p1 {p2, p3}))
  have hp2 := mem_filter.mp
    (hsub (mem_insert_of_mem (mem_insert_self p2 {p3})))
  have hp3 := mem_filter.mp
    (hsub (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self p3))))
  have hprod1 := mem_product.mp hp1.1
  have hprod2 := mem_product.mp hp2.1
  have hprod3 := mem_product.mp hp3.1
  refine ⟨p1.2, p2.2, p3.2, p1.1, p2.1, p3.1,
    hprod1.2, hprod2.2, hprod3.2, ?_, ?_, ?_,
    hprod1.1, hprod2.1, hprod3.1, ?_, ?_, ?_,
    hp1.2.symm, hp2.2.symm, hp3.2.symm⟩
  · intro hteq
    have hdeq : p1.1 = p2.1 :=
      B.eq_of_two_D_neighbors (c := c) hprod1.2 hprod1.1 hprod2.1
        hp1.2.symm (by simpa [hteq] using hp2.2.symm)
    exact h12 (Prod.ext hdeq hteq)
  · intro hteq
    have hdeq : p1.1 = p3.1 :=
      B.eq_of_two_D_neighbors (c := c) hprod1.2 hprod1.1 hprod3.1
        hp1.2.symm (by simpa [hteq] using hp3.2.symm)
    exact h13 (Prod.ext hdeq hteq)
  · intro hteq
    have hdeq : p2.1 = p3.1 :=
      B.eq_of_two_D_neighbors (c := c) hprod2.2 hprod2.1 hprod3.1
        hp2.2.symm (by simpa [hteq] using hp3.2.symm)
    exact h23 (Prod.ext hdeq hteq)
  · intro hdeq
    have hteq : p1.2 = p2.2 :=
      B.eq_of_two_T_neighbors (mem_componentVerts_not_ST (G := G) hprod1.1)
        hprod1.2 hprod2.2 hp1.2 (by simpa [hdeq] using hp2.2)
    exact h12 (Prod.ext hdeq hteq)
  · intro hdeq
    have hteq : p1.2 = p3.2 :=
      B.eq_of_two_T_neighbors (mem_componentVerts_not_ST (G := G) hprod1.1)
        hprod1.2 hprod3.2 hp1.2 (by simpa [hdeq] using hp3.2)
    exact h13 (Prod.ext hdeq hteq)
  · intro hdeq
    have hteq : p2.2 = p3.2 :=
      B.eq_of_two_T_neighbors (mem_componentVerts_not_ST (G := G) hprod2.1)
        hprod2.2 hprod3.2 hp2.2 (by simpa [hdeq] using hp3.2)
    exact h23 (Prod.ext hdeq hteq)

/-- Three distinct matching `D–T` edges cannot exist under `NoInducedP4UnionP1`.
Attachment vertices have distance at most two; an edge among them isolates `t3`;
a length-two path forces the middle vertex to be the third attachment. -/
lemma ExtremalBarrier.matching_three_edges_false
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    {c : (Remain G B.S B.T).ConnectedComponent}
    {t1 t2 t3 d1 d2 d3 : V}
    (ht1 : t1 ∈ B.T) (ht2 : t2 ∈ B.T) (ht3 : t3 ∈ B.T)
    (hneT12 : t1 ≠ t2) (hneT13 : t1 ≠ t3) (hneT23 : t2 ≠ t3)
    (hd1 : d1 ∈ componentVerts G B.S B.T c)
    (hd2 : d2 ∈ componentVerts G B.S B.T c)
    (hd3 : d3 ∈ componentVerts G B.S B.T c)
    (hneD12 : d1 ≠ d2) (hneD13 : d1 ≠ d3) (hneD23 : d2 ≠ d3)
    (hadj1 : G.Adj t1 d1) (hadj2 : G.Adj t2 d2) (hadj3 : G.Adj t3 d3) :
    False := by
  have hreach := remain_reachable_of_mem_component (G := G) hd1 hd2
  obtain ⟨p, hpPath, hpDist⟩ := hreach.exists_path_of_dist
  have hd1T : d1 ∉ B.T := remainder_disjoint_T (G := G) c hd1
  have hd2T : d2 ∉ B.T := remainder_disjoint_T (G := G) c hd2
  have hne_t1d1 : t1 ≠ d1 := hadj1.ne
  have hlen : p.length = (Remain G B.S B.T).dist
      ⟨d1, (mem_componentVerts_iff (c := c)).mp hd1 |>.1⟩
      ⟨d2, (mem_componentVerts_iff (c := c)).mp hd2 |>.1⟩ := hpDist
  have h0 : (p.getVert 0).val = d1 := by
    simp [Walk.getVert_zero]
  by_cases hge3 : 3 ≤ p.length
  · have h1c : (p.getVert 1).val ∈ componentVerts G B.S B.T c :=
      remain_getVert_mem_component p hd1 1
    have h2c : (p.getVert 2).val ∈ componentVerts G B.S B.T c :=
      remain_getVert_mem_component p hd1 2
    have hlc : (p.getVert p.length).val ∈ componentVerts G B.S B.T c :=
      remain_getVert_mem_component p hd1 p.length
    have hend : (p.getVert p.length).val = d2 := by
      simp [Walk.getVert_length]
    have hne01 : (p.getVert 0).val ≠ (p.getVert 1).val := by
      intro h
      exact (by decide : (0 : ℕ) ≠ 1)
        (remain_path_getVert_val_inj hpPath (by omega) (by omega) h)
    have hne02 : (p.getVert 0).val ≠ (p.getVert 2).val := by
      intro h
      exact (by decide : (0 : ℕ) ≠ 2)
        (remain_path_getVert_val_inj hpPath (by omega) (by omega) h)
    have hne12 : (p.getVert 1).val ≠ (p.getVert 2).val := by
      intro h
      exact (by decide : (1 : ℕ) ≠ 2)
        (remain_path_getVert_val_inj hpPath (by omega) (by omega) h)
    have hne1end : (p.getVert 1).val ≠ d2 := by
      intro h
      have := remain_path_getVert_val_inj hpPath (by omega) le_rfl (h.trans hend.symm)
      omega
    have hne2end : (p.getVert 2).val ≠ d2 := by
      intro h
      have := remain_path_getVert_val_inj hpPath (by omega) le_rfl (h.trans hend.symm)
      omega
    have hadj_d1p1 : G.Adj d1 (p.getVert 1).val := by
      have := p.adj_getVert_succ (by omega : (0 : ℕ) < p.length)
      simpa [induce_adj, h0] using this
    have hadj_p1p2 : G.Adj (p.getVert 1).val (p.getVert 2).val := by
      have := p.adj_getVert_succ (by omega : (1 : ℕ) < p.length)
      simpa [induce_adj] using this
    have nAdj_t1p1 : ¬ G.Adj t1 (p.getVert 1).val := by
      intro h
      have : d1 = (p.getVert 1).val :=
        B.eq_of_two_D_neighbors ht1 (by simpa [h0] using hd1) h1c hadj1 h
      exact hne01 (h0.trans this)
    have nAdj_t1p2 : ¬ G.Adj t1 (p.getVert 2).val := by
      intro h
      have : d1 = (p.getVert 2).val :=
        B.eq_of_two_D_neighbors ht1 (by simpa [h0] using hd1) h2c hadj1 h
      exact hne02 (h0.trans this)
    have nAdj_d1p2 : ¬ G.Adj d1 (p.getVert 2).val := by
      have := not_adj_getVert_of_length_eq_dist (H := Remain G B.S B.T)
        hpDist (by omega : (0 : ℕ) ≤ p.length)
        (by omega : (2 : ℕ) ≤ p.length) (by decide : (0 : ℕ) + 2 ≤ 2)
      simpa [induce_adj, h0] using this
    have hne_t1p1 : t1 ≠ (p.getVert 1).val := by
      intro h; subst h; exact (mem_componentVerts_not_ST (G := G) h1c)
        (mem_union.mpr (Or.inr ht1))
    have hne_t1p2 : t1 ≠ (p.getVert 2).val := by
      intro h; subst h; exact (mem_componentVerts_not_ST (G := G) h2c)
        (mem_union.mpr (Or.inr ht1))
    have hne_t2d1 : t2 ≠ d1 := by
      intro h; subst h; exact hd1T ht2
    have hne_t2p1 : t2 ≠ (p.getVert 1).val := by
      intro h; subst h; exact (mem_componentVerts_not_ST (G := G) h1c)
        (mem_union.mpr (Or.inr ht2))
    have hne_t2p2 : t2 ≠ (p.getVert 2).val := by
      intro h; subst h; exact (mem_componentVerts_not_ST (G := G) h2c)
        (mem_union.mpr (Or.inr ht2))
    have nAdj_t2d1 : ¬ G.Adj t2 d1 := by
      intro h
      have : d2 = d1 :=
        B.eq_of_two_D_neighbors ht2 hd2 hd1 hadj2 h
      exact hneD12 this.symm
    have nAdj_t2p1 : ¬ G.Adj t2 (p.getVert 1).val := by
      intro h
      have : d2 = (p.getVert 1).val :=
        B.eq_of_two_D_neighbors ht2 hd2 h1c hadj2 h
      exact hne1end this.symm
    have nAdj_t2p2 : ¬ G.Adj t2 (p.getVert 2).val := by
      intro h
      have : d2 = (p.getVert 2).val :=
        B.eq_of_two_D_neighbors ht2 hd2 h2c hadj2 h
      exact hne2end this.symm
    have hne_d1p1 : d1 ≠ (p.getVert 1).val := by
      intro h; exact hne01 (h0.trans h)
    have hne_d1p2 : d1 ≠ (p.getVert 2).val := by
      intro h; exact hne02 (h0.trans h)
    have hp4 : InducedP4 G t1 d1 (p.getVert 1).val (p.getVert 2).val :=
      ⟨hne_t1d1, hne_t1p1, hne_t1p2, hne_d1p1, hne_d1p2, hne12,
        hadj1, hadj_d1p1, hadj_p1p2,
        nAdj_t1p1, nAdj_t1p2, nAdj_d1p2⟩
    have hiso := hpat hp4 hneT12.symm hne_t2d1 hne_t2p1 hne_t2p2
    rcases hiso with h21 | h2d1 | h2p1 | h2p2
    · exact B.T_independent ht2 ht1 h21
    · exact nAdj_t2d1 h2d1
    · exact nAdj_t2p1 h2p1
    · exact nAdj_t2p2 h2p2
  · have hle2 : p.length ≤ 2 := Nat.lt_succ_iff.mp (lt_of_not_ge hge3)
    have hpos : 0 < p.length := by
      have hneUV :
          (⟨d1, (mem_componentVerts_iff (c := c)).mp hd1 |>.1⟩ :
            RemainVert B.S B.T) ≠
          ⟨d2, (mem_componentVerts_iff (c := c)).mp hd2 |>.1⟩ := by
        intro h
        exact hneD12 (congrArg Subtype.val h)
      have : 0 < (Remain G B.S B.T).dist
          ⟨d1, (mem_componentVerts_iff (c := c)).mp hd1 |>.1⟩
          ⟨d2, (mem_componentVerts_iff (c := c)).mp hd2 |>.1⟩ :=
        hreach.pos_dist_of_ne hneUV
      simpa [hpDist] using this
    have hlen12 : p.length = 1 ∨ p.length = 2 := by omega
    rcases hlen12 with hlen1 | hlen2
    · -- length 1: an original edge d1d2
      have hadjD : G.Adj d1 d2 := by
        have := p.adj_getVert_succ (by omega)
        have h0' : (p.getVert 0).val = d1 := by simp [Walk.getVert_zero]
        have h1' : (p.getVert 1).val = d2 := by
          have hlen := Walk.getVert_length p
          rw [hlen1] at hlen
          simp [hlen]
        simpa [induce_adj, h0', h1'] using this
      exact B.matching_attachments_not_adj hpat ht1 ht2 ht3 hneT12 hneT13 hneT23
        hd1 hd2 hd3 hneD12 hneD13 hneD23 hadj1 hadj2 hadj3 hadjD
    · -- length 2: path d1,w,d2
      have hw : (p.getVert 1).val ∈ componentVerts G B.S B.T c :=
        remain_getVert_mem_component p hd1 1
      have h0' : (p.getVert 0).val = d1 := by simp [Walk.getVert_zero]
      have h2' : (p.getVert 2).val = d2 := by
        have hlen := Walk.getVert_length p
        rw [hlen2] at hlen
        simp [hlen]
      have hlen2' : p.length = 2 := hlen2
      have hne_dw : d1 ≠ (p.getVert 1).val := by
        intro h
        exact (by decide : (0 : ℕ) ≠ 1)
          (remain_path_getVert_val_inj hpPath (by simp [hlen2']) (by simp [hlen2'])
            (h0'.trans h))
      have hne_wd : (p.getVert 1).val ≠ d2 := by
        intro h
        exact (by decide : (1 : ℕ) ≠ 2)
          (remain_path_getVert_val_inj hpPath (by simp [hlen2']) (by simp [hlen2'])
            (h.trans h2'.symm))
      have hadj_d1w : G.Adj d1 (p.getVert 1).val := by
        have := p.adj_getVert_succ (by omega : (0 : ℕ) < p.length)
        simpa [induce_adj, h0'] using this
      have hadj_wd2 : G.Adj (p.getVert 1).val d2 := by
        have := p.adj_getVert_succ (by omega : (1 : ℕ) < p.length)
        simpa [induce_adj, h2'] using this
      have nAdj_d1d2 : ¬ G.Adj d1 d2 :=
        B.matching_attachments_not_adj hpat ht1 ht2 ht3 hneT12 hneT13 hneT23
          hd1 hd2 hd3 hneD12 hneD13 hneD23 hadj1 hadj2 hadj3
      have nAdj_t1w : ¬ G.Adj t1 (p.getVert 1).val := by
        intro h
        have : d1 = (p.getVert 1).val :=
          B.eq_of_two_D_neighbors ht1 hd1 hw hadj1 h
        exact hne_dw this
      have nAdj_t1d2 : ¬ G.Adj t1 d2 := by
        intro h
        have : d1 = d2 :=
          B.eq_of_two_D_neighbors ht1 hd1 hd2 hadj1 h
        exact hneD12 this
      have hne_t1w : t1 ≠ (p.getVert 1).val := by
        intro h; subst h
        exact (mem_componentVerts_not_ST (G := G) hw) (mem_union.mpr (Or.inr ht1))
      have hne_t1d2 : t1 ≠ d2 := by
        intro h; subst h; exact hd2T ht1
      have hp4 : InducedP4 G t1 d1 (p.getVert 1).val d2 :=
        ⟨hne_t1d1, hne_t1w, hne_t1d2, hne_dw, hneD12, hne_wd,
          hadj1, hadj_d1w, hadj_wd2,
          nAdj_t1w, nAdj_t1d2, nAdj_d1d2⟩
      have hne_t3d1 : t3 ≠ d1 := by
        intro h; subst h; exact hd1T ht3
      have hne_t3w : t3 ≠ (p.getVert 1).val := by
        intro h; subst h
        exact (mem_componentVerts_not_ST (G := G) hw) (mem_union.mpr (Or.inr ht3))
      have hne_t3d2 : t3 ≠ d2 := by
        intro h; subst h; exact hd2T ht3
      have hiso := hpat hp4 hneT13.symm hne_t3d1 hne_t3w hne_t3d2
      rcases hiso with h31 | h3d1 | h3w | h32
      · exact B.T_independent ht3 ht1 h31
      · exact (B.eq_of_two_D_neighbors ht3 hd3 hd1 hadj3 h3d1 ▸ hneD13) rfl
      · have : d3 = (p.getVert 1).val :=
          B.eq_of_two_D_neighbors ht3 hd3 hw hadj3 h3w
        have hadj_d1d3 : G.Adj d1 d3 := by simpa [this] using hadj_d1w
        exact B.matching_attachments_not_adj hpat ht1 ht3 ht2 hneT13 hneT12 hneT23.symm
          hd1 hd3 hd2 hneD13 hneD12 hneD23.symm hadj1 hadj3 hadj2 hadj_d1d3
      · have : d3 = d2 :=
          B.eq_of_two_D_neighbors ht3 hd3 hd2 hadj3 h32
        exact hneD23 this.symm

lemma ExtremalBarrier.odd_attach_le_two
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    (c : (Remain G B.S B.T).ConnectedComponent) :
    componentAttach G B.S B.T c ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ componentAttach G B.S B.T c := Nat.succ_le_of_lt (lt_of_not_ge h)
  obtain ⟨t1, t2, t3, d1, d2, d3, ht1, ht2, ht3, hneT12, hneT13, hneT23,
      hd1, hd2, hd3, hneD12, hneD13, hneD23, hadj1, hadj2, hadj3⟩ :=
    B.exists_three_matching h3
  exact B.matching_three_edges_false hpat ht1 ht2 ht3 hneT12 hneT13 hneT23
    hd1 hd2 hd3 hneD12 hneD13 hneD23 hadj1 hadj2 hadj3

lemma ExtremalBarrier.componentAttach_le_one
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    (c : (Remain G B.S B.T).ConnectedComponent) :
    componentAttach G B.S B.T c ≤ 1 := by
  by_cases hodd : Odd (componentAttach G B.S B.T c)
  · have hle := B.odd_attach_le_two hpat c
    have hne2 : componentAttach G B.S B.T c ≠ 2 := by
      intro h2
      have : Even 2 := by decide
      exact Nat.not_odd_iff_even.2 (h2 ▸ this) hodd
    omega
  · have heven : Even (componentAttach G B.S B.T c) :=
      Nat.not_odd_iff_even.mp hodd
    simpa [B.even_attach_eq_zero c heven]

lemma ExtremalBarrier.odd_attach_eq_one
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    {c : (Remain G B.S B.T).ConnectedComponent}
    (hodd : Odd (componentAttach G B.S B.T c)) :
    componentAttach G B.S B.T c = 1 := by
  have hle := B.componentAttach_le_one hpat c
  have hpos : 0 < componentAttach G B.S B.T c :=
    Nat.pos_of_ne_zero fun h0 =>
      Nat.not_odd_zero (by simpa [h0] using hodd)
  omega

/-! ## Toughness cuts and host 2-factor existence -/

lemma ExtremalBarrier.internalEdgeCount_eq_zero (B : ExtremalBarrier G) :
    internalEdgeCount G B.T = 0 := by
  have hord : orderedEdgeCount G B.T B.T = 0 := by
    rw [orderedEdgeCount, card_eq_zero, filter_eq_empty_iff]
    intro p hp
    have hprod := mem_product.mp hp
    exact B.T_independent hprod.1 hprod.2
  have htwo := two_mul_internalEdgeCount (G := G) B.T
  omega

lemma ExtremalBarrier.sum_attach_div_two_eq_zero
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G) :
    (∑ c ∈ (univ : Finset (Remain G B.S B.T).ConnectedComponent),
        componentAttach G B.S B.T c / 2) = 0 := by
  refine sum_eq_zero fun c _ => Nat.div_eq_of_lt ?_
  exact Nat.lt_succ_iff.mpr (B.componentAttach_le_one hpat c)

lemma ExtremalBarrier.delta_eq_two_sub
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G) :
    delta G B.S B.T = 2 * ((B.S.card : ℤ) - (B.T.card : ℤ)) := by
  have hΔ := delta_eq_two_mul (G := G) B.disjoint
  have hinter := B.internalEdgeCount_eq_zero
  have hsum := B.sum_attach_div_two_eq_zero hpat
  simp [hΔ, hinter, hsum]

lemma ExtremalBarrier.card_T_gt_card_S
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G) :
    B.S.card < B.T.card := by
  have hΔ := B.delta_eq_two_sub hpat
  have : 2 * ((B.S.card : ℤ) - (B.T.card : ℤ)) ≤ -2 := by
    simpa [hΔ] using B.neg
  have hZ : (B.S.card : ℤ) < (B.T.card : ℤ) := by linarith
  exact_mod_cast hZ

lemma ExtremalBarrier.T_nonempty (B : ExtremalBarrier G)
    (hpat : NoInducedP4UnionP1 G) : B.T.Nonempty :=
  card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (B.card_T_gt_card_S hpat))

lemma ExtremalBarrier.eq_T_of_meet
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    {c : (Remain G B.S B.T).ConnectedComponent} {t t' x : V}
    (ht : t ∈ B.T) (hmeet : MeetsVertex B.S B.T c t)
    (ht' : t' ∈ B.T) (hx : x ∈ componentVerts G B.S B.T c)
    (hadj : G.Adj x t') : t' = t := by
  have hle := B.componentAttach_le_one hpat c
  obtain ⟨y, hy, hyadj⟩ := hmeet
  by_contra hne
  have hs :
      ({(y, t), (x, t')} : Finset (V × V)) ⊆
        (componentVerts G B.S B.T c ×ˢ B.T).filter fun p => G.Adj p.1 p.2 := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp'
    · exact mem_filter.mpr ⟨mem_product.mpr ⟨hy, ht⟩, hyadj⟩
    · have : p = (x, t') := mem_singleton.mp hp'
      subst this
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hx, ht'⟩, hadj⟩
  have hneP : (y, t) ≠ (x, t') := by
    intro h
    exact hne (congrArg Prod.snd h).symm
  have h2 : 2 ≤ ({(y, t), (x, t')} : Finset (V × V)).card := by
    simp [card_insert_of_notMem, hneP]
  have : 2 ≤ componentAttach G B.S B.T c :=
    le_trans h2 (card_le_card hs)
  omega

lemma coe_univ_sdiff_eq_compl (S : Finset V) :
    ((univ \ S : Finset V) : Set V) = (S : Set V)ᶜ := by
  ext x
  simp

lemma mem_compl_of_mem_T {S T : Finset V} (hdis : Disjoint S T) {t : V}
    (ht : t ∈ T) : t ∈ (S : Set V)ᶜ :=
  fun hS => Finset.disjoint_left.1 hdis hS ht

lemma remainderVerts_to_remain {S T : Finset V} {x : V}
    (hx : x ∈ remainderVerts G S T) :
    x ∈ ((S ∪ T : Finset V) : Set V)ᶜ :=
  (Set.mem_compl_iff _ _).2 (by
    simpa using (mem_remainderVerts_iff (G := G)).1 hx)

/-- After deleting `S`, a vertex is either the distinguished `t ∈ T` or lies in a
remainder component that meets `t`. -/
def meetsStar (S T : Finset V) (t : V) (v : {x : V // x ∈ (S : Set V)ᶜ}) : Prop :=
  v.val = t ∨
    ∃ hv : v.val ∈ remainderVerts G S T,
      MeetsVertex S T
        ((Remain G S T).connectedComponentMk
          ⟨v.val, remainderVerts_to_remain (G := G) hv⟩) t

lemma ExtremalBarrier.adj_preserves_meetsStar
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    {t : V} (ht : t ∈ B.T)
    {u w : {x : V // x ∈ (B.S : Set V)ᶜ}}
    (hadj : (G.induce (B.S : Set V)ᶜ).Adj u w)
    (hu : meetsStar (G := G) B.S B.T t u) :
    meetsStar (G := G) B.S B.T t w := by
  have hadjG : G.Adj u.val w.val := by simpa [induce_adj] using hadj
  rcases hu with hu | ⟨huU, hmeet⟩
  · -- `u` is `t`: the next vertex lies in a remainder component meeting `t`.
    have hwT : w.val ∉ B.T := by
      intro hwT
      have : G.Adj t w.val := by simpa [hu] using hadjG
      exact B.T_independent ht hwT this
    have hwU : w.val ∈ remainderVerts G B.S B.T := by
      refine (mem_remainderVerts_iff (G := G)).2 ?_
      intro hST
      rcases mem_union.mp hST with hS | hT
      · exact w.property hS
      · exact hwT hT
    refine Or.inr ⟨hwU, ?_⟩
    refine ⟨w.val, remain_mk_mem (G := G) hwU, ?_⟩
    simpa [hu] using hadjG.symm
  · -- `u` is in a remainder component meeting `t`.
    let c := (Remain G B.S B.T).connectedComponentMk
      ⟨u.val, remainderVerts_to_remain (G := G) huU⟩
    have huC : u.val ∈ componentVerts G B.S B.T c := remain_mk_mem (G := G) huU
    by_cases hwT : w.val ∈ B.T
    · have : w.val = t :=
        B.eq_T_of_meet hpat ht hmeet hwT huC hadjG
      exact Or.inl this
    · have hwU : w.val ∈ remainderVerts G B.S B.T := by
        refine (mem_remainderVerts_iff (G := G)).2 ?_
        intro hST
        rcases mem_union.mp hST with hS | hT
        · exact w.property hS
        · exact hwT hT
      have hadjR : (Remain G B.S B.T).Adj
          ⟨u.val, remainderVerts_to_remain (G := G) huU⟩
          ⟨w.val, remainderVerts_to_remain (G := G) hwU⟩ := by
        simpa [induce_adj] using hadjG
      have hwC : w.val ∈ componentVerts G B.S B.T c :=
        remain_adj_mem_component huC hadjR
      have hmk : (Remain G B.S B.T).connectedComponentMk
          ⟨w.val, remainderVerts_to_remain (G := G) hwU⟩ = c :=
        (mem_componentVerts_iff (c := c)).mp hwC |>.2
      refine Or.inr ⟨hwU, ?_⟩
      simpa [c, hmk] using hmeet

lemma ExtremalBarrier.walk_preserves_meetsStar
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    {t : V} (ht : t ∈ B.T)
    {u w : {x : V // x ∈ (B.S : Set V)ᶜ}}
    (p : (G.induce (B.S : Set V)ᶜ).Walk u w)
    (hu : meetsStar (G := G) B.S B.T t u) :
    meetsStar (G := G) B.S B.T t w := by
  induction p with
  | nil => exact hu
  | cons hadj q ih =>
    exact ih (B.adj_preserves_meetsStar hpat ht hadj hu)

lemma ExtremalBarrier.T_eq_of_reachable
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    {t1 t2 : V} (ht1 : t1 ∈ B.T) (ht2 : t2 ∈ B.T)
    (hr : (G.induce (B.S : Set V)ᶜ).Reachable
      ⟨t1, mem_compl_of_mem_T B.disjoint ht1⟩
      ⟨t2, mem_compl_of_mem_T B.disjoint ht2⟩) :
    t1 = t2 := by
  obtain ⟨p⟩ := hr
  have hstar := B.walk_preserves_meetsStar hpat ht1 p (Or.inl rfl)
  rcases hstar with h | ⟨hU, _⟩
  · exact h.symm
  · exact ((mem_remainderVerts_iff (G := G)).1 hU
      (mem_union.mpr (Or.inr ht2))).elim

lemma ExtremalBarrier.componentCount_sdiff_ge_T
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G) :
    B.T.card ≤ componentCount G (univ \ B.S) := by
  let f : {t // t ∈ B.T} → (G.induce (B.S : Set V)ᶜ).ConnectedComponent :=
    fun t => (G.induce (B.S : Set V)ᶜ).connectedComponentMk
      ⟨t.val, mem_compl_of_mem_T B.disjoint t.property⟩
  have hinj : Function.Injective f := by
    intro a b h
    exact Subtype.ext
      (B.T_eq_of_reachable hpat a.property b.property (ConnectedComponent.exact h))
  have hle : Fintype.card {t // t ∈ B.T} ≤
      Fintype.card (G.induce (B.S : Set V)ᶜ).ConnectedComponent :=
    Fintype.card_le_of_injective f hinj
  have hcoe : Fintype.card {t // t ∈ B.T} = B.T.card := Fintype.card_coe B.T
  have hcc : componentCount G (univ \ B.S) =
      Fintype.card (G.induce (B.S : Set V)ᶜ).ConnectedComponent := by
    rw [componentCount, coe_univ_sdiff_eq_compl, Nat.card_eq_fintype_card]
  simpa [hcoe, hcc] using hle

lemma ExtremalBarrier.false_of_card_T_ge_two
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    (htough : OneTough G) (hT : 2 ≤ B.T.card) : False := by
  have hge := B.componentCount_sdiff_ge_T hpat
  have h2 : 2 ≤ componentCount G (univ \ B.S) := le_trans hT hge
  have hle := htough B.S h2
  have hlt := B.card_T_gt_card_S hpat
  omega

lemma ExtremalBarrier.false_of_card_T_eq_one
    (B : ExtremalBarrier G) (hpat : NoInducedP4UnionP1 G)
    (hord : 3 ≤ Fintype.card V) (htough : OneTough G)
    (hT : B.T.card = 1) : False := by
  obtain ⟨t, hTeq⟩ := card_eq_one.mp hT
  have hS : B.S = ∅ := by
    have hlt := B.card_T_gt_card_S hpat
    have : B.S.card = 0 := by omega
    exact card_eq_zero.mp this
  have ht : t ∈ B.T := by simp [hTeq]
  have hdeg : 2 ≤ (G.neighborFinset t).card := by
    have := OneTough.two_le_ncard_neighborSet (G := G) htough hord t
    simpa [ncard_neighborSet, card_neighborFinset_eq_degree] using this
  obtain ⟨N, hNsub, hNcard⟩ := exists_subset_card_eq hdeg
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hNcard
  have hxN : x ∈ G.neighborFinset t := hNsub (mem_insert_self x {y})
  have hyN : y ∈ G.neighborFinset t :=
    hNsub (mem_insert_of_mem (mem_singleton_self y))
  have hxadj : G.Adj t x := by simpa [mem_neighborFinset] using hxN
  have hyadj : G.Adj t y := by simpa [mem_neighborFinset] using hyN
  have hxU : x ∈ remainderVerts G B.S B.T := by
    have hne : x ≠ t := hxadj.ne.symm
    simp [remainderVerts, hS, hTeq, hne]
  have hyU : y ∈ remainderVerts G B.S B.T := by
    have hne : y ≠ t := hyadj.ne.symm
    simp [remainderVerts, hS, hTeq, hne]
  let cx := (Remain G B.S B.T).connectedComponentMk
    ⟨x, remainderVerts_to_remain (G := G) hxU⟩
  let cy := (Remain G B.S B.T).connectedComponentMk
    ⟨y, remainderVerts_to_remain (G := G) hyU⟩
  have hxC : x ∈ componentVerts G B.S B.T cx := remain_mk_mem (G := G) hxU
  have hyC : y ∈ componentVerts G B.S B.T cy := remain_mk_mem (G := G) hyU
  have hcxcy : cx ≠ cy := by
    intro h
    have : x = y :=
      B.eq_of_two_D_neighbors (c := cx) ht hxC (by simpa [h] using hyC) hxadj hyadj
    exact hxy this
  have hxDel : x ∈ (univ \ {t} : Finset V) :=
    mem_sdiff.mpr ⟨mem_univ x, by simp [hxadj.ne.symm]⟩
  have hyDel : y ∈ (univ \ {t} : Finset V) :=
    mem_sdiff.mpr ⟨mem_univ y, by simp [hyadj.ne.symm]⟩
  have hxDelS : x ∈ ((univ \ {t} : Finset V) : Set V) := by simpa using hxDel
  have hyDelS : y ∈ ((univ \ {t} : Finset V) : Set V) := by simpa using hyDel
  let Dx := (G.induce ((univ \ {t} : Finset V) : Set V)).connectedComponentMk ⟨x, hxDelS⟩
  let Dy := (G.induce ((univ \ {t} : Finset V) : Set V)).connectedComponentMk ⟨y, hyDelS⟩
  have hsub : ((univ \ {t} : Finset V) : Set V) ⊆
      ((B.S ∪ B.T : Finset V) : Set V)ᶜ := by
    intro z hz
    have hz' : z ∈ univ \ {t} := by simpa using hz
    simpa [hS, hTeq] using hz'
  have hDxDy : Dx ≠ Dy := by
    intro h
    obtain ⟨p⟩ := ConnectedComponent.exact (show Dx = Dy from h)
    let φ := (G.induceHomOfLE hsub).toHom
    have hR : (Remain G B.S B.T).Reachable (φ ⟨x, hxDelS⟩) (φ ⟨y, hyDelS⟩) :=
      (p.map φ).reachable
    have hcx : cx = (Remain G B.S B.T).connectedComponentMk (φ ⟨x, hxDelS⟩) :=
      eq_of_mem_componentVerts (x := x) hxC (remain_mk_mem (G := G) hxU)
    have hcy : cy = (Remain G B.S B.T).connectedComponentMk (φ ⟨y, hyDelS⟩) :=
      eq_of_mem_componentVerts (x := y) hyC (remain_mk_mem (G := G) hyU)
    exact hcxcy (hcx.trans ((ConnectedComponent.sound hR).trans hcy.symm))
  have hnt : Nontrivial
      (G.induce ((univ \ {t} : Finset V) : Set V)).ConnectedComponent :=
    ⟨⟨Dx, Dy, hDxDy⟩⟩
  have h2 : 2 ≤ componentCount G (univ \ {t}) := by
    have : 1 < Fintype.card
        (G.induce ((univ \ {t} : Finset V) : Set V)).ConnectedComponent :=
      Fintype.one_lt_card_iff_nontrivial.mpr hnt
    simpa [componentCount, Nat.card_eq_fintype_card] using Nat.succ_le_iff.mpr this
  have hle := htough {t} (by simpa using h2)
  have : componentCount G (univ \ {t}) ≤ 1 := by simpa using hle
  omega

lemma ExtremalBarrier.false_of_oneTough
    (B : ExtremalBarrier G) (hord : 3 ≤ Fintype.card V)
    (htough : OneTough G) (hpat : NoInducedP4UnionP1 G) : False := by
  have hTpos : 1 ≤ B.T.card :=
    Nat.succ_le_iff.mpr (card_pos.mpr (B.T_nonempty hpat))
  cases Nat.eq_or_lt_of_le hTpos with
  | inl h1 => exact B.false_of_card_T_eq_one hpat hord htough h1.symm
  | inr h2 =>
    exact B.false_of_card_T_ge_two hpat htough (Nat.succ_le_of_lt h2)

/-- Manuscript `thm:factor`: a finite simple 1-tough graph of order at least
three with no induced `P₄ ∪ P₁` has an original-edge spanning 2-factor. -/
theorem exists_cycleFactor_of_oneTough_noInducedP4UnionP1
    (hord : 3 ≤ Fintype.card V)
    (htough : OneTough G)
    (hpat : NoInducedP4UnionP1 G) :
    Nonempty (CycleFactor G) := by
  by_contra h
  obtain ⟨B⟩ := exists_extremalBarrier_of_not_cycleFactor (G := G) h
  exact B.false_of_oneTough hord htough hpat

end TwoFactor
end Nikoghosyan
