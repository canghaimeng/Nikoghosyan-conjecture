/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Nikoghosyan.Prerequisites.TwoFactorDefs

/-!
# General evenness of the manuscript barrier `Δ(S,T)`

For an arbitrary finite simple graph and disjoint vertex sets `S,T`,
partition the original remainder `U = V \ (S ∪ T)` into its connected
components `D`. Degree counting gives
`∑_{t∈T} d_{G-S}(t) = 2 e(T) + ∑_D e(D,T)`. Writing each attachment as
`2 q_D + ε_D` with `ε_D ∈ {0,1}`, the odd-attachment count `h(S,T)` is
`∑_D ε_D`. Consequently
`Δ(S,T) = 2(|S| - |T| + e(T) + ∑_D q_D)` in `ℤ`.
Empty `T` and empty `U` are included. No toughness, forbidden-pattern,
or nonisolation hypothesis is used.
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

/-! ## Remainder components of `G - (S ∪ T)` -/

/-- Induced remainder graph `G[U]` with `U = V \ (S ∪ T)`. -/
abbrev Remain (G : SimpleGraph V) (S T : Finset V) :=
  G.induce ((S ∪ T : Finset V) : Set V)ᶜ

lemma mem_remainderVerts_iff {S T : Finset V} {v : V} :
    v ∈ remainderVerts G S T ↔ v ∉ S ∪ T := by
  simp [remainderVerts]

lemma mem_remainderVerts_iff' {S T : Finset V} {v : V} :
    v ∈ remainderVerts G S T ↔ v ∉ S ∧ v ∉ T := by
  simp [remainderVerts, mem_union]

lemma remainderVerts_eq_compl {S T : Finset V} :
    (remainderVerts G S T : Set V) = ((S ∪ T : Finset V) : Set V)ᶜ := by
  ext v
  simp [remainderVerts]

lemma mem_componentVerts_iff {S T : Finset V}
    {c : (Remain G S T).ConnectedComponent} {v : V} :
    v ∈ componentVerts G S T c ↔
      ∃ hv : v ∈ ((S ∪ T : Finset V) : Set V)ᶜ,
        (Remain G S T).connectedComponentMk ⟨v, hv⟩ = c := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨⟨w, hw⟩, hmem, rfl⟩
    refine ⟨hw, ?_⟩
    simpa using (ConnectedComponent.mem_supp_iff _ _).mp (Set.mem_toFinset.mp hmem)
  · rintro ⟨hv, h⟩
    refine Finset.mem_image.mpr ⟨⟨v, hv⟩, Set.mem_toFinset.mpr ?_, rfl⟩
    simpa using (ConnectedComponent.mem_supp_iff _ _).mpr h

lemma componentVerts_subset_remainder {S T : Finset V}
    (c : (Remain G S T).ConnectedComponent) :
    componentVerts G S T c ⊆ remainderVerts G S T := by
  intro v hv
  have ⟨hv', _⟩ := (mem_componentVerts_iff (c := c)).mp hv
  simpa [remainderVerts] using hv'

lemma disjoint_componentVerts {S T : Finset V}
    {c d : (Remain G S T).ConnectedComponent} (h : c ≠ d) :
    Disjoint (componentVerts G S T c) (componentVerts G S T d) := by
  rw [Finset.disjoint_left]
  intro v hvc hvd
  have ⟨hv, hc⟩ := (mem_componentVerts_iff (c := c)).mp hvc
  have ⟨_, hd⟩ := (mem_componentVerts_iff (c := d)).mp hvd
  exact h (hc.symm.trans hd)

lemma pairwiseDisjoint_componentVerts (S T : Finset V) :
    ((univ : Finset (Remain G S T).ConnectedComponent) : Set _).PairwiseDisjoint
      (componentVerts G S T) := by
  intro c _hc d _hd hcd
  change Disjoint (componentVerts G S T c) (componentVerts G S T d)
  exact disjoint_componentVerts hcd

lemma remainderVerts_eq_biUnion (S T : Finset V) :
    remainderVerts G S T =
      (univ : Finset (Remain G S T).ConnectedComponent).biUnion
        (componentVerts G S T) := by
  ext v
  constructor
  · intro hv
    have hv' : v ∈ ((S ∪ T : Finset V) : Set V)ᶜ := by
      simpa [remainderVerts] using hv
    refine mem_biUnion.mpr
      ⟨(Remain G S T).connectedComponentMk ⟨v, hv'⟩, mem_univ _, ?_⟩
    exact (mem_componentVerts_iff).mpr ⟨hv', rfl⟩
  · intro hv
    rcases mem_biUnion.mp hv with ⟨c, _, hvc⟩
    exact componentVerts_subset_remainder c hvc

/-! ## Ordered attachment counts -/

lemma orderedEdgeCount_eq_sum_parity (A B : Finset V) :
    orderedEdgeCount G A B = ∑ a ∈ A, (G.neighborFinset a ∩ B).card := by
  simp only [orderedEdgeCount, neighborFinset_inter]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ha => ?_
  exact (Finset.card_filter (G.Adj a) B).symm

lemma orderedEdgeCount_comm_parity (A B : Finset V) :
    orderedEdgeCount G A B = orderedEdgeCount G B A := by
  simp only [orderedEdgeCount]
  let e : Equiv {p // p ∈ (A ×ˢ B).filter fun p => G.Adj p.1 p.2}
      {p // p ∈ (B ×ˢ A).filter fun p => G.Adj p.1 p.2} :=
    { toFun := fun p =>
        ⟨(p.1.2, p.1.1), by
          have hp := p.2
          simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩⟩
      invFun := fun p =>
        ⟨(p.1.2, p.1.1), by
          have hp := p.2
          simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext rfl }
  simpa [← Fintype.card_coe] using Fintype.card_congr e

lemma orderedEdgeCount_self_eq_two_mul_parity (A : Finset V) :
    orderedEdgeCount G A A = 2 * (G.induce (A : Set V)).edgeFinset.card := by
  classical
  let H := G.induce (A : Set V)
  let e : {p : V × V // p ∈ (A ×ˢ A).filter fun q => G.Adj q.1 q.2} ≃
      {xy : (↥(A : Set V)) × (↥(A : Set V)) // H.Adj xy.1 xy.2} :=
    { toFun := fun p =>
        ⟨(⟨p.1.1, (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).1⟩,
          ⟨p.1.2, (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).2⟩),
          (Finset.mem_filter.mp p.2).2⟩
      invFun := fun q =>
        ⟨(q.1.1.val, q.1.2.val),
          Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨q.1.1.property, q.1.2.property⟩, q.2⟩⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun q =>
        Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)) }
  have hP : ((A ×ˢ A).filter fun q => G.Adj q.1 q.2).card =
      (Finset.univ.filter fun xy : (↥(A : Set V)) × (↥(A : Set V)) =>
        H.Adj xy.1 xy.2).card := by
    simpa [← Fintype.card_coe] using Fintype.card_congr e
  exact hP.trans H.two_mul_card_edgeFinset.symm

lemma even_orderedEdgeCount_self_parity (A : Finset V) :
    Even (orderedEdgeCount G A A) := by
  rw [orderedEdgeCount_self_eq_two_mul_parity]
  exact even_two_mul _

lemma two_mul_internalEdgeCount (T : Finset V) :
    2 * internalEdgeCount G T = orderedEdgeCount G T T := by
  simpa [internalEdgeCount] using
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_orderedEdgeCount_self_parity (G := G) T))

lemma orderedEdgeCount_biUnion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset V) (B : Finset V)
    (hd : (s : Set ι).PairwiseDisjoint f) :
    orderedEdgeCount G (s.biUnion f) B =
      ∑ i ∈ s, orderedEdgeCount G (f i) B := by
  simp only [orderedEdgeCount]
  let t : ι → Finset (V × V) :=
    fun i => (f i ×ˢ B).filter fun p => G.Adj p.1 p.2
  have hdis : (s : Set ι).PairwiseDisjoint t := by
    intro i hi j hj hij
    change Disjoint (t i) (t j)
    rw [Finset.disjoint_left]
    intro p hp hq
    have hiB : p.1 ∈ f i := (mem_product.mp (mem_filter.mp hp).1).1
    have hjB : p.1 ∈ f j := (mem_product.mp (mem_filter.mp hq).1).1
    exact (Finset.disjoint_left.1 (hd hi hj hij) hiB hjB).elim
  have hunion :
      ((s.biUnion f) ×ˢ B).filter (fun p => G.Adj p.1 p.2) = s.biUnion t := by
    ext p
    constructor
    · intro hp
      have hp' := mem_filter.mp hp
      have hprod := mem_product.mp hp'.1
      rcases mem_biUnion.mp hprod.1 with ⟨i, hi, hfi⟩
      exact mem_biUnion.mpr
        ⟨i, hi, mem_filter.mpr ⟨mem_product.mpr ⟨hfi, hprod.2⟩, hp'.2⟩⟩
    · intro hp
      rcases mem_biUnion.mp hp with ⟨i, hi, hpi⟩
      have hpi' := mem_filter.mp hpi
      have hprod := mem_product.mp hpi'.1
      exact mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_biUnion.mpr ⟨i, hi, hprod.1⟩, hprod.2⟩, hpi'.2⟩
  rw [hunion, card_biUnion hdis]

lemma orderedEdgeCount_remainder_eq_sum (S T : Finset V) :
    orderedEdgeCount G (remainderVerts G S T) T =
      ∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
        componentAttach G S T c := by
  rw [remainderVerts_eq_biUnion, orderedEdgeCount_biUnion]
  · simp [componentAttach]
  · exact pairwiseDisjoint_componentVerts S T

/-! ## Degree split: `∑_T d_{G-S} = 2e(T) + ∑_D e(D,T)` -/

lemma remainderVerts_disjoint_S (S T : Finset V) :
    Disjoint (remainderVerts G S T) S := by
  rw [Finset.disjoint_left]
  intro x hxU hxS
  have : x ∉ S ∪ T := by simpa [remainderVerts] using hxU
  exact this (mem_union.mpr (Or.inl hxS))

lemma remainderVerts_disjoint_T (S T : Finset V) :
    Disjoint (remainderVerts G S T) T := by
  rw [Finset.disjoint_left]
  intro x hxU hxT
  have : x ∉ S ∪ T := by simpa [remainderVerts] using hxU
  exact this (mem_union.mpr (Or.inr hxT))

lemma neighbor_sdiff_eq_union {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (_ht : t ∈ T) :
    G.neighborFinset t \ S =
      (G.neighborFinset t ∩ T) ∪
        (G.neighborFinset t ∩ remainderVerts G S T) := by
  ext x
  simp only [mem_sdiff, mem_union, mem_inter, mem_neighborFinset, remainderVerts,
    mem_univ, true_and]
  constructor
  · intro ⟨hadj, hxS⟩
    by_cases hxT : x ∈ T
    · exact Or.inl ⟨hadj, hxT⟩
    · exact Or.inr ⟨hadj, by
        simp [hxS, hxT]⟩
  · intro h
    rcases h with ⟨hadj, hxT⟩ | ⟨hadj, hxU⟩
    · exact ⟨hadj, fun hxS => Finset.disjoint_left.1 hdis hxS hxT⟩
    · exact ⟨hadj, by
        have : x ∉ S ∪ T := by
          simpa [remainderVerts] using hxU
        exact fun hxS => this (mem_union.mpr (Or.inl hxS))⟩

lemma disjoint_neighbor_T_remainder {S T : Finset V} {t : V} :
    Disjoint (G.neighborFinset t ∩ T)
      (G.neighborFinset t ∩ remainderVerts G S T) := by
  rw [Finset.disjoint_left]
  intro x hxT hxU
  exact Finset.disjoint_left.1 (remainderVerts_disjoint_T (G := G) S T)
    (mem_inter.mp hxU).2 (mem_inter.mp hxT).2

lemma degDelete_split {S T : Finset V} {t : V}
    (hdis : Disjoint S T) (ht : t ∈ T) :
    degDelete G S t =
      (G.neighborFinset t ∩ T).card +
        (G.neighborFinset t ∩ remainderVerts G S T).card := by
  rw [degDelete, neighbor_sdiff_eq_union (G := G) hdis ht,
    card_union_of_disjoint (disjoint_neighbor_T_remainder (G := G))]

lemma sum_degDelete {S T : Finset V} (hdis : Disjoint S T) :
    ∑ t ∈ T, degDelete G S t =
      orderedEdgeCount G T T +
        orderedEdgeCount G (remainderVerts G S T) T := by
  have hsplit :
      ∑ t ∈ T, degDelete G S t =
        ∑ t ∈ T, (G.neighborFinset t ∩ T).card +
          ∑ t ∈ T, (G.neighborFinset t ∩ remainderVerts G S T).card := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    exact degDelete_split (G := G) hdis ht
  have hT : ∑ t ∈ T, (G.neighborFinset t ∩ T).card = orderedEdgeCount G T T :=
    (orderedEdgeCount_eq_sum_parity (G := G) T T).symm
  have hU :
      ∑ t ∈ T, (G.neighborFinset t ∩ remainderVerts G S T).card =
        orderedEdgeCount G T (remainderVerts G S T) :=
    (orderedEdgeCount_eq_sum_parity (G := G) T (remainderVerts G S T)).symm
  rw [hsplit, hT, hU, orderedEdgeCount_comm_parity (G := G) T (remainderVerts G S T)]

/-- Degree handshake on the original remainder: internal `T`-edges counted
twice, each `D–T` incidence once. -/
theorem sum_degDelete_eq_internal_add_attach {S T : Finset V}
    (hdis : Disjoint S T) :
    ∑ t ∈ T, degDelete G S t =
      2 * internalEdgeCount G T +
        ∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
          componentAttach G S T c := by
  rw [sum_degDelete (G := G) hdis, two_mul_internalEdgeCount (G := G) T,
    orderedEdgeCount_remainder_eq_sum]

/-! ## Odd-attachment sum `h(S,T) = ∑_D ε_D` -/

lemma componentAttach_decompose (S T : Finset V)
    (c : (Remain G S T).ConnectedComponent) :
    componentAttach G S T c =
      2 * (componentAttach G S T c / 2) + componentAttach G S T c % 2 :=
  (Nat.div_add_mod (componentAttach G S T c) 2).symm

lemma attach_mod_two_eq (S T : Finset V)
    (c : (Remain G S T).ConnectedComponent) :
    componentAttach G S T c % 2 =
      if Odd (componentAttach G S T c) then 1 else 0 := by
  by_cases h : Odd (componentAttach G S T c)
  · simp [h, Nat.odd_iff.mp h]
  · have he : Even (componentAttach G S T c) := Nat.not_odd_iff_even.mp h
    simp [h, Nat.even_iff.mp he]

lemma hCount_eq_sum_odd_indicators (S T : Finset V) :
    hCount G S T =
      ∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
        (if Odd (componentAttach G S T c) then 1 else 0) := by
  simp [hCount, sum_boole]

/-- `h(S,T)` is the sum of the `{0,1}` remainders of the attachment counts. -/
theorem hCount_eq_sum_mod (S T : Finset V) :
    hCount G S T =
      ∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
        componentAttach G S T c % 2 := by
  rw [hCount_eq_sum_odd_indicators]
  refine sum_congr rfl fun c _ => (attach_mod_two_eq (G := G) S T c).symm

lemma sum_componentAttach_decompose (S T : Finset V) :
    ∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
        componentAttach G S T c =
      2 * ∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
            componentAttach G S T c / 2 +
        hCount G S T := by
  rw [sum_congr rfl fun c _ => componentAttach_decompose (G := G) S T c,
    sum_add_distrib, ← mul_sum, hCount_eq_sum_mod]

/-! ## Closed form, evenness, and negative values `≤ -2` -/

lemma natCast_sum_degDelete {S T : Finset V} (hdis : Disjoint S T) :
    ((∑ t ∈ T, degDelete G S t : ℕ) : ℤ) =
      2 * (internalEdgeCount G T : ℤ) +
        ((∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
            componentAttach G S T c : ℕ) : ℤ) := by
  rw [sum_degDelete_eq_internal_add_attach (G := G) hdis]
  simp [Nat.cast_add, Nat.cast_mul]

lemma natCast_sum_attach_decompose (S T : Finset V) :
    ((∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
        componentAttach G S T c : ℕ) : ℤ) =
      2 * ((∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
              componentAttach G S T c / 2 : ℕ) : ℤ) +
        (hCount G S T : ℤ) := by
  rw [sum_componentAttach_decompose (G := G) S T]
  simp [Nat.cast_add, Nat.cast_mul]

/-- Manuscript identity (1): `Δ(S,T)` is twice an integer combination of
`|S|`, `|T|`, the internal `T`-edge count, and the halved attachments. -/
theorem delta_eq_two_mul {S T : Finset V} (hdis : Disjoint S T) :
    delta G S T =
      2 * ((S.card : ℤ) - (T.card : ℤ) + (internalEdgeCount G T : ℤ) +
        ((∑ c ∈ (univ : Finset (Remain G S T).ConnectedComponent),
            componentAttach G S T c / 2 : ℕ) : ℤ)) := by
  unfold delta
  have hdeg := natCast_sum_degDelete (G := G) hdis
  have hatt := natCast_sum_attach_decompose (G := G) S T
  have hsum :
      (∑ t ∈ T, (degDelete G S t : ℤ)) = ((∑ t ∈ T, degDelete G S t : ℕ) : ℤ) := by
    simp
  rw [hsum, hdeg, hatt]
  ring

/-- Every barrier value is even, including empty `T` and empty remainder. -/
theorem even_delta {S T : Finset V} (hdis : Disjoint S T) :
    Even (delta G S T) := by
  rw [delta_eq_two_mul (G := G) hdis]
  exact even_two_mul _

/-- A negative barrier value is at most `-2`. -/
theorem delta_neg_le_neg_two {S T : Finset V} (hdis : Disjoint S T)
    (hneg : delta G S T < 0) : delta G S T ≤ -2 := by
  obtain ⟨k, hk⟩ := even_delta (G := G) hdis
  have hk' : delta G S T = 2 * k := by
    simpa [two_mul] using hk
  have hkneg : k < 0 := by
    have : (2 : ℤ) * k < 0 := by simpa [hk'] using hneg
    nlinarith
  have hk1 : k ≤ -1 := Int.le_sub_one_of_lt hkneg
  have : (2 : ℤ) * k ≤ 2 * (-1) :=
    mul_le_mul_of_nonneg_left hk1 (by decide)
  simpa [hk'] using this

theorem delta_neg_iff_le_neg_two {S T : Finset V} (hdis : Disjoint S T) :
    delta G S T < 0 ↔ delta G S T ≤ -2 := by
  constructor
  · exact delta_neg_le_neg_two (G := G) hdis
  · intro h
    exact lt_of_le_of_lt h (by decide : (-2 : ℤ) < 0)

end TwoFactor
end Nikoghosyan
