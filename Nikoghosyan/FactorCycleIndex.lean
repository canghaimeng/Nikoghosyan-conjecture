/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.FactorAuxiliaryClosure

/-!
Phase 11, item 1: raw index facts for an actual auxiliary `Walk.IsCycle`.

`Walk.getVert` is capped: `getVert n` for `n ≥ length` is the endpoint,
not a periodic extension. On a closed walk the identity
`getVert 0 = getVert length` is a *vertex* equality, never `0 = length`.
Injectivity of `getVert` is therefore stated for indices *strictly below*
`length`, via the pinned Mathlib lemma `IsCycle.getVert_injOn'`.

The auxiliary graph is bipartite, so every genuine cycle has even length
at least 4, independently of whether it starts at a block or a physical
vertex. Cyclic predecessor/successor live on `Fin k` with `k = length / 2`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Port : Type*} [DecidableEq Port]

/-! ### Capped `getVert` on a genuine cycle -/

/-- On a closed walk, index `0` and index `length` name the *same vertex*.
They are not equal as natural numbers. -/
lemma closed_getVert_zero_eq_length {α : Type*} {H : SimpleGraph α} {u : α}
    (w : H.Walk u u) : w.getVert 0 = w.getVert w.length := by
  simp [Walk.getVert_zero, Walk.getVert_length]

/-- `getVert` is injective on indices strictly below `length`.
Pinned to Mathlib `IsCycle.getVert_injOn'` (`i ≤ length - 1`). -/
lemma cycle_getVert_inj {α : Type*} {H : SimpleGraph α} {u : α}
    {w : H.Walk u u} (hc : w.IsCycle) {i j : ℕ}
    (hi : i < w.length) (hj : j < w.length)
    (heq : w.getVert i = w.getVert j) : i = j := by
  have h3 := hc.three_le_length
  have hi' : i ≤ w.length - 1 := Nat.le_sub_one_of_lt hi
  have hj' : j ≤ w.length - 1 := Nat.le_sub_one_of_lt hj
  exact hc.getVert_injOn' hi' hj' heq

lemma cycle_getVert_eq_start_iff {α : Type*} {H : SimpleGraph α} {u : α}
    {w : H.Walk u u} (hc : w.IsCycle) {i : ℕ} (hi : i ≤ w.length) :
    w.getVert i = u ↔ i = 0 ∨ i = w.length :=
  hc.getVert_endpoint_iff hi

/-! ### Auxiliary bipartite parity, any start type -/

lemma aux_cycle_even_length_any {P : BlockPartition V ι}
    {u : ι ⊕ PhysEdge (G := G) P}
    {w : (aux (G := G) P).Walk u u} (_hc : w.IsCycle) :
    Even w.length := by
  have hL : w.getVert w.length = u := Walk.getVert_length w
  have hiff := aux_getVert_isBlock w w.length le_rfl
  by_cases hblock : ∃ i : ι, u = .inl i
  · obtain ⟨i, hi⟩ := hblock
    have : ∃ j, w.getVert w.length = .inl j := ⟨i, hL.trans hi⟩
    exact (hiff.mp this).mp ⟨i, hi⟩
  · have hend : ¬ ∃ j, w.getVert w.length = .inl j := by
      intro ⟨j, hj⟩
      exact hblock ⟨j, hL.symm.trans hj⟩
    have hneg := hiff.not.mp hend
    simpa [iff_false_left hblock, not_not] using hneg

lemma aux_cycle_four_le_any {P : BlockPartition V ι}
    {u : ι ⊕ PhysEdge (G := G) P}
    {w : (aux (G := G) P).Walk u u} (hc : w.IsCycle) :
    4 ≤ w.length := by
  have h3 : 3 ≤ w.length := hc.three_le_length
  have he : Even w.length := aux_cycle_even_length_any hc
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp he
  have : 2 ≤ m := by omega
  omega

lemma aux_getVert_odd_inr {P : BlockPartition V ι} {i : ι}
    {x : ι ⊕ PhysEdge (G := G) P}
    (w : (aux (G := G) P).Walk (.inl i) x) {n : ℕ}
    (hn : n ≤ w.length) (ho : Odd n) :
    ∃ e, w.getVert n = .inr e := by
  have hiff := aux_getVert_isBlock w n hn
  have hnot : ¬ ∃ j, w.getVert n = .inl j := by
    intro hex
    have heven : Even n := (hiff.mp hex).mp ⟨i, rfl⟩
    exact Nat.not_even_iff_odd.mpr ho heven
  generalize hgv : w.getVert n = x at hnot ⊢
  cases x with
  | inl j => exact (hnot ⟨j, rfl⟩).elim
  | inr e => exact ⟨e, rfl⟩

lemma aux_getVert_odd_inl_of_phys {P : BlockPartition V ι}
    {e : PhysEdge (G := G) P} {x : ι ⊕ PhysEdge (G := G) P}
    (w : (aux (G := G) P).Walk (.inr e) x) {n : ℕ}
    (hn : n ≤ w.length) (ho : Odd n) :
    ∃ j, w.getVert n = .inl j := by
  have hiff := aux_getVert_isBlock w n hn
  refine hiff.mpr ?_
  have hstart : ¬ ∃ j, (Sum.inr e : ι ⊕ PhysEdge (G := G) P) = .inl j := by
    rintro ⟨j, h⟩
    cases h
  simpa [iff_false_left hstart] using (Nat.not_even_iff_odd.mpr ho)

lemma aux_getVert_even_inr_of_phys {P : BlockPartition V ι}
    {e : PhysEdge (G := G) P} {x : ι ⊕ PhysEdge (G := G) P}
    (w : (aux (G := G) P).Walk (.inr e) x) {n : ℕ}
    (hn : n ≤ w.length) (he : Even n) :
    ∃ f, w.getVert n = .inr f := by
  have hiff := aux_getVert_isBlock w n hn
  have hnot : ¬ ∃ j, w.getVert n = .inl j := by
    intro hex
    have hR : (∃ j, (Sum.inr e : ι ⊕ PhysEdge (G := G) P) = .inl j) ↔ Even n :=
      hiff.mp hex
    obtain ⟨j, hj⟩ := hR.mpr he
    cases hj
  generalize hgv : w.getVert n = x at hnot ⊢
  cases x with
  | inl j => exact (hnot ⟨j, rfl⟩).elim
  | inr f => exact ⟨f, rfl⟩

/-! ### Half-length arithmetic, `k = length / 2` -/

lemma two_mul_lt_of_div {n t : ℕ} (he : Even n) (ht : t < n / 2) :
    2 * t < n := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp he
  omega

lemma two_mul_add_one_lt_of_div {n t : ℕ} (he : Even n) (ht : t < n / 2) :
    2 * t + 1 < n := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp he
  omega

lemma two_mul_add_two_le_of_div {n t : ℕ} (he : Even n) (ht : t < n / 2) :
    2 * t + 2 ≤ n := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp he
  omega

lemma odd_two_mul_add_one (t : ℕ) : Odd (2 * t + 1) :=
  ⟨t, rfl⟩

lemma even_two_mul_add_two (t : ℕ) : Even (2 * t + 2) :=
  ⟨t + 1, by omega⟩

lemma two_le_half {n : ℕ} (he : Even n) (h4 : 4 ≤ n) : 2 ≤ n / 2 := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp he
  omega

lemma two_mul_half {n : ℕ} (he : Even n) : 2 * (n / 2) = n := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp he
  omega

lemma two_mul_pred_add_two_eq_length {n : ℕ} (he : Even n) (h2 : 2 ≤ n / 2) :
    2 * (n / 2 - 1) + 2 = n := by
  have hL := two_mul_half he
  omega

/-! ### Cyclic predecessor / successor on `Fin k` -/

def pcSucc {k : ℕ} (hk : 0 < k) (t : Fin k) : Fin k :=
  ⟨(t.1 + 1) % k, Nat.mod_lt _ hk⟩

def pcPred {k : ℕ} (hk : 0 < k) (t : Fin k) : Fin k :=
  ⟨(t.1 + k - 1) % k, Nat.mod_lt _ hk⟩

lemma pcSucc_ne {k : ℕ} (hk : 2 ≤ k) (t : Fin k) :
    t ≠ pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) t := by
  intro h
  have hv : t.1 = (t.1 + 1) % k := by
    simpa [pcSucc] using congrArg Fin.val h
  have ht : t.1 < k := t.2
  by_cases hlt : t.1 + 1 < k
  · rw [Nat.mod_eq_of_lt hlt] at hv
    exact Nat.ne_of_lt (Nat.lt_succ_self t.1) hv
  · have hEq : t.1 + 1 = k := by omega
    have : (t.1 + 1) % k = 0 := by simp [hEq]
    have : k = 1 := by omega
    omega

lemma pcPred_succ {k : ℕ} (hpos : 0 < k) (t : Fin k) :
    pcSucc hpos (pcPred hpos t) = t := by
  apply Fin.ext
  by_cases ht0 : t.1 = 0
  · have hk1 : k - 1 < k := Nat.sub_lt hpos (by decide)
    have hpred : (0 + k - 1) % k = k - 1 := by
      have : 0 + k - 1 = k - 1 := by omega
      rw [this, Nat.mod_eq_of_lt hk1]
    change ((t.1 + k - 1) % k + 1) % k = t.1
    simp [ht0]
    have : k - 1 + 1 = k := by omega
    simp [this]
  · have htlt : t.1 < k := t.2
    have hlt : t.1 - 1 < k := by omega
    have hrew : t.1 + k - 1 = t.1 - 1 + k := by omega
    have hpred : (t.1 + k - 1) % k = t.1 - 1 := by
      rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    change ((t.1 + k - 1) % k + 1) % k = t.1
    rw [hpred]
    have : t.1 - 1 + 1 = t.1 := by omega
    rw [this, Nat.mod_eq_of_lt htlt]

lemma pcSucc_pred {k : ℕ} (hpos : 0 < k) (t : Fin k) :
    pcPred hpos (pcSucc hpos t) = t := by
  apply Fin.ext
  have ht : t.1 < k := t.2
  by_cases hlt : t.1 + 1 < k
  · have hmod : (t.1 + 1) % k = t.1 + 1 := Nat.mod_eq_of_lt hlt
    change ((t.1 + 1) % k + k - 1) % k = t.1
    rw [hmod]
    have hrew : t.1 + 1 + k - 1 = t.1 + k := by omega
    rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · have hEq : t.1 + 1 = k := by omega
    have hmod0 : (t.1 + 1) % k = 0 := by rw [hEq, Nat.mod_self]
    change ((t.1 + 1) % k + k - 1) % k = t.1
    rw [hmod0]
    have hrew : 0 + k - 1 = k - 1 := by omega
    have hk1 : k - 1 < k := Nat.sub_lt hpos (by decide)
    rw [hrew, Nat.mod_eq_of_lt hk1]
    omega

lemma pcPred_val_pos {k : ℕ} (hpos : 0 < k) {t : Fin k} (ht : 0 < t.1) :
    (pcPred hpos t).1 = t.1 - 1 := by
  have hlt : t.1 - 1 < k := by omega
  have hrew : t.1 + k - 1 = t.1 - 1 + k := by omega
  change (t.1 + k - 1) % k = t.1 - 1
  rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

lemma pcPred_zero {k : ℕ} (hk : 2 ≤ k) :
    pcPred (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) ⟨0, by omega⟩ =
      ⟨k - 1, by omega⟩ := by
  apply Fin.ext
  change (0 + k - 1) % k = k - 1
  have hk1 : k - 1 < k := by omega
  have hrew : 0 + k - 1 = k - 1 := by omega
  rw [hrew, Nat.mod_eq_of_lt hk1]

lemma pcSucc_last {k : ℕ} (hk : 2 ≤ k) :
    pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) ⟨k - 1, by omega⟩ =
      ⟨0, by omega⟩ := by
  ext
  simp [pcSucc]
  have : k - 1 + 1 = k := by omega
  simp [this]

lemma pcSucc_of_lt {k : ℕ} (hpos : 0 < k) {t : Fin k}
    (ht : t.1 + 1 < k) :
    pcSucc hpos t = ⟨t.1 + 1, ht⟩ := by
  ext
  simp [pcSucc, Nat.mod_eq_of_lt ht]

/-! ### Dart colours of an auxiliary incidence -/

lemma dartColor_getVert {P : BlockPartition V ι} (port : V → Port)
    {u v : ι ⊕ PhysEdge (G := G) P}
    (w : (aux (G := G) P).Walk u v) {n : ℕ}
    (hn : n < w.length) :
    (auxColoring (G := G) P port).dartColor
        (w.darts[n]'(by simpa [Walk.length_darts] using hn)) =
      auxColor (G := G) P port (w.adj_getVert_succ hn) := by
  have hd := Walk.darts_getElem_eq_getVert (p := w) n
    (by simpa [Walk.length_darts] using hn)
  rw [hd, Yeo.EdgeColoring.dartColor]
  exact (auxColoring (G := G) P port).color_proof _ _

lemma ports_ne_of_prod {i : ι} {p q : Port}
    (h : ((i, p) : ι × Port) ≠ (i, q)) : p ≠ q := by
  intro hp
  exact h (by simp [hp])

lemma incident_of_adj_inl_inr {P : BlockPartition V ι} {i : ι}
    {e : PhysEdge (G := G) P}
    (h : (aux (G := G) P).Adj (.inl i) (.inr e)) :
    incident (G := G) P i e :=
  (aux_adj_inl_inr (G := G)).mp h

lemma incident_of_adj_inr_inl {P : BlockPartition V ι} {i : ι}
    {e : PhysEdge (G := G) P}
    (h : (aux (G := G) P).Adj (.inr e) (.inl i)) :
    incident (G := G) P i e :=
  (aux_adj_inr_inl (G := G)).mp h

lemma endpointOf_congr {P : BlockPartition V ι} {i : ι}
    {e e' : PhysEdge (G := G) P} (h : e = e')
    (hinc : incident (G := G) P i e) :
    endpointOf (G := G) P i e hinc =
      endpointOf (G := G) P i e' (h ▸ hinc) := by
  subst h
  rfl

lemma endpointOf_proof_irrel {P : BlockPartition V ι} {i : ι}
    {e : PhysEdge (G := G) P} (h1 h2 : incident (G := G) P i e) :
    endpointOf (G := G) P i e h1 = endpointOf (G := G) P i e h2 :=
  endpointOf_eq_of_mem (G := G) P h1
    (endpointOf_mem_edge (G := G) P i e h2)
    (endpointOf_mem_block (G := G) P i e h2)

lemma auxColor_of_inl_inr {P : BlockPartition V ι} (port : V → Port)
    {x y : ι ⊕ PhysEdge (G := G) P}
    (h : (aux (G := G) P).Adj x y) {i : ι} {e : PhysEdge (G := G) P}
    (hx : x = .inl i) (hy : y = .inr e) :
    ∃ hinc : incident (G := G) P i e,
      auxColor (G := G) P port h = (i, port (endpointOf (G := G) P i e hinc)) := by
  subst hx
  subst hy
  exact ⟨h, rfl⟩

lemma auxColor_of_inr_inl {P : BlockPartition V ι} (port : V → Port)
    {x y : ι ⊕ PhysEdge (G := G) P}
    (h : (aux (G := G) P).Adj x y) {i : ι} {e : PhysEdge (G := G) P}
    (hx : x = .inr e) (hy : y = .inl i) :
    ∃ hinc : incident (G := G) P i e,
      auxColor (G := G) P port h = (i, port (endpointOf (G := G) P i e hinc)) := by
  subst hx
  subst hy
  exact ⟨h, rfl⟩

end Nikoghosyan
