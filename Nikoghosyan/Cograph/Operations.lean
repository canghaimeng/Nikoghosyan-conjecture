/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Disjoint union and complete join preserve `P4`-freeness

These are the two cotree operations of `cog:lem:cotree`. The arguments are the
direct ones: an induced `P4` is connected, so it cannot meet both sides of a
disjoint union; an induced `P4` has maximum degree two and three edges, so it
cannot meet both sides of a complete join.
-/

universe u

namespace Nikoghosyan
namespace Cograph

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- No `G`-edge runs between the two sides of a partition with no cross edges. -/
lemma mem_of_adj_of_no_cross {A B : Set V} {a b : V}
    (hcover : A ∪ B = Set.univ) (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (ha : a ∈ A) (hadj : G.Adj a b) : b ∈ A := by
  have : b ∈ A ∨ b ∈ B := by
    have : b ∈ A ∪ B := by simp [hcover]
    simpa [Set.mem_union] using this
  rcases this with h | h
  · exact h
  · exact (hnocross a ha b h hadj).elim

lemma mem_of_adj_of_no_cross' {A B : Set V} {a b : V}
    (hcover : A ∪ B = Set.univ) (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (ha : a ∈ B) (hadj : G.Adj a b) : b ∈ B := by
  have hsym : ∀ x ∈ B, ∀ y ∈ A, ¬ G.Adj x y := fun x hx y hy hxy =>
    hnocross y hy x hx hxy.symm
  simpa [Set.union_comm] using
    mem_of_adj_of_no_cross (A := B) (B := A) (by simpa [Set.union_comm] using hcover)
      hsym ha hadj

/-- An induced `P4` cannot meet both sides of a disjoint union. -/
lemma inducedP4_subset_of_disjoint_union {A B : Set V} {a b c d : V}
    (hcover : A ∪ B = Set.univ) (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (hp : InducedP4 G a b c d) : ({a, b, c, d} : Set V) ⊆ A ∨ ({a, b, c, d} : Set V) ⊆ B := by
  have hab : G.Adj a b := hp.adj_ab
  have hbc : G.Adj b c := hp.adj_bc
  have hcd : G.Adj c d := hp.adj_cd
  have haAB : a ∈ A ∨ a ∈ B := by
    have : a ∈ A ∪ B := by simp [hcover]
    simpa [Set.mem_union] using this
  rcases haAB with haA | haB
  · refine Or.inl ?_
    intro x hx
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    have hbA : b ∈ A := mem_of_adj_of_no_cross hcover hnocross haA hab
    have hcA : c ∈ A := mem_of_adj_of_no_cross hcover hnocross hbA hbc
    have hdA : d ∈ A := mem_of_adj_of_no_cross hcover hnocross hcA hcd
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption
  · refine Or.inr ?_
    intro x hx
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    have hbB : b ∈ B := mem_of_adj_of_no_cross' hcover hnocross haB hab
    have hcB : c ∈ B := mem_of_adj_of_no_cross' hcover hnocross hbB hbc
    have hdB : d ∈ B := mem_of_adj_of_no_cross' hcover hnocross hcB hcd
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption

/-- Disjoint union preserves `P4`-freeness. -/
lemma isCographOn_disjoint_union {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (hA : IsCographOn G A) (hB : IsCographOn G B) : IsCographGraph G := by
  intro a b c d hp
  rcases inducedP4_subset_of_disjoint_union hcover hnocross hp with hA' | hB'
  · exact hA (hA' (by simp)) (hA' (by simp)) (hA' (by simp)) (hA' (by simp)) hp
  · exact hB (hB' (by simp)) (hB' (by simp)) (hB' (by simp)) (hB' (by simp)) hp

lemma isCographGraph_disjoint_union [Fintype V] {A B : Finset V} [DecidableEq V]
    (_hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hA : IsCograph G A) (hB : IsCograph G B) : IsCographGraph G := by
  refine isCographOn_disjoint_union (A := (A : Set V)) (B := (B : Set V)) ?_ ?_ hA hB
  · ext x
    constructor
    · intro
      simp
    · intro
      have : x ∈ A ∪ B := by simp [hcover]
      simpa [Finset.mem_union] using this
  · intro a ha b hb
    exact hnocross a ha b hb

/-- Adjacent pairs among the four vertices of an induced `P4` are exactly the three
path edges. -/
lemma inducedP4_adj_mem_path_edges [DecidableEq V] {a b c d x y : V}
    (hp : InducedP4 G a b c d)
    (hx : x ∈ ({a, b, c, d} : Finset V)) (hy : y ∈ ({a, b, c, d} : Finset V))
    (hne : x ≠ y) (hadj : G.Adj x y) :
    s(x, y) = s(a, b) ∨ s(x, y) = s(b, c) ∨ s(x, y) = s(c, d) := by
  have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx
  have hy' : y = a ∨ y = b ∨ y = c ∨ y = d := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hy
  rcases hx' with rfl | rfl | rfl | rfl
  · rcases hy' with rfl | rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact Or.inl rfl
    · exact (hp.not_ac hadj).elim
    · exact (hp.not_ad hadj).elim
  · rcases hy' with rfl | rfl | rfl | rfl
    · exact Or.inl (Sym2.eq_swap)
    · exact (hne rfl).elim
    · exact Or.inr (Or.inl rfl)
    · exact (hp.not_bd hadj).elim
  · rcases hy' with rfl | rfl | rfl | rfl
    · exact (hp.not_ac hadj.symm).elim
    · exact Or.inr (Or.inl (Sym2.eq_swap))
    · exact (hne rfl).elim
    · exact Or.inr (Or.inr rfl)
  · rcases hy' with rfl | rfl | rfl | rfl
    · exact (hp.not_ad hadj.symm).elim
    · exact (hp.not_bd hadj.symm).elim
    · exact Or.inr (Or.inr (Sym2.eq_swap))
    · exact (hne rfl).elim

lemma card_p4_path_edges [DecidableEq V] {a b c d : V} (hp : InducedP4 G a b c d) :
    ({s(a, b), s(b, c), s(c, d)} : Finset (Sym2 V)).card = 3 := by
  have h1 : s(a, b) ≠ s(b, c) := by
    intro h
    have : a = c ∨ a = b ∧ b = c := by
      simpa [Sym2.eq_iff, hp.ne_ab, hp.ne_bc] using h
    rcases this with h' | ⟨_, h'⟩
    · exact hp.ne_ac h'
    · exact hp.ne_bc h'
  have h2 : s(a, b) ≠ s(c, d) := by
    intro h
    have : a = c ∧ b = d ∨ a = d ∧ b = c := by
      simpa [Sym2.eq_iff] using h
    rcases this with ⟨h', _⟩ | ⟨_, h'⟩
    · exact hp.ne_ac h'
    · exact hp.ne_bc h'
  have h3 : s(b, c) ≠ s(c, d) := by
    intro h
    have : b = c ∧ c = d ∨ b = d ∧ c = c := by
      simpa [Sym2.eq_iff] using h
    rcases this with ⟨h', _⟩ | ⟨h', _⟩
    · exact hp.ne_bc h'
    · exact hp.ne_bd h'
  simp [h1, h2, h3]

/-- Complete join of a covering partition preserves `P4`-freeness. -/
lemma isCographGraph_complete_join [DecidableEq V] {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hAB : G.IsCompleteBetween A B)
    (hA : IsCographOn G A) (hB : IsCographOn G B) : IsCographGraph G := by
  intro a b c d hp
  classical
  let S : Finset V := {a, b, c, d}
  have hScard : S.card = 4 := hp.card_four
  have hdisjAB : Disjoint A B := hAB.disjoint
  let SA := S.filter (· ∈ A)
  let SB := S.filter (· ∈ B)
  have hunion : SA ∪ SB = S := by
    ext x
    constructor
    · intro hx
      simp only [SA, SB, Finset.mem_union, Finset.mem_filter] at hx
      rcases hx with ⟨hxS, _⟩ | ⟨hxS, _⟩ <;> exact hxS
    · intro hx
      have hxAB : x ∈ A ∨ x ∈ B := by
        have : x ∈ A ∪ B := by simp [hcover]
        simpa [Set.mem_union] using this
      simp only [SA, SB, Finset.mem_union, Finset.mem_filter]
      exact hxAB.elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  have hdisjSA : Disjoint SA SB := by
    refine Finset.disjoint_left.2 ?_
    intro x hxA hxB
    exact Set.disjoint_left.1 hdisjAB
      (Finset.mem_filter.mp hxA).2 (Finset.mem_filter.mp hxB).2
  have hsum : SA.card + SB.card = 4 := by
    have hcard := Finset.card_union_of_disjoint hdisjSA
    rw [hunion, hScard] at hcard
    exact hcard.symm
  have hnotA : ¬ S ⊆ SA := by
    intro hS
    have hSA : ∀ z ∈ S, z ∈ A := fun z hz => (Finset.mem_filter.mp (hS hz)).2
    exact hA (hSA a (by simp [S])) (hSA b (by simp [S]))
      (hSA c (by simp [S])) (hSA d (by simp [S])) hp
  have hnotB : ¬ S ⊆ SB := by
    intro hS
    have hSB : ∀ z ∈ S, z ∈ B := fun z hz => (Finset.mem_filter.mp (hS hz)).2
    exact hB (hSB a (by simp [S])) (hSB b (by simp [S]))
      (hSB c (by simp [S])) (hSB d (by simp [S])) hp
  have hSA_ne : SA.card ≠ 4 := by
    intro h4
    have : SA = S := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    exact hnotA (by simp [this])
  have hSB_ne : SB.card ≠ 4 := by
    intro h4
    have : SB = S := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    exact hnotB (by simp [this])
  have hSA_pos : SA.card ≠ 0 := by
    intro h0
    have : SB.card = 4 := by omega
    exact hSB_ne this
  have hSB_pos : SB.card ≠ 0 := by
    intro h0
    have : SA.card = 4 := by omega
    exact hSA_ne this
  have hsplit : SA.card = 1 ∨ SA.card = 2 ∨ SA.card = 3 := by omega
  have hcross {x y : V} (hx : x ∈ SA) (hy : y ∈ SB) : G.Adj x y :=
    hAB (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  rcases hsplit with h1 | h2 | h3
  · obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp h1
    have hxSA : x ∈ SA := by simp [hxeq]
    have hxS : x ∈ S := (Finset.mem_filter.mp hxSA).1
    have hxquad : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [S, Finset.mem_insert, Finset.mem_singleton] using hxS
    have hother : (x ≠ a → G.Adj x a) ∧ (x ≠ b → G.Adj x b) ∧
        (x ≠ c → G.Adj x c) ∧ (x ≠ d → G.Adj x d) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hxa
        have haS : a ∈ S := by simp [S]
        have : a ∈ SA ∨ a ∈ SB := by
          have : a ∈ SA ∪ SB := by simpa [hunion] using haS
          simpa [Finset.mem_union] using this
        rcases this with haA | haB
        · have : a = x := by
            have : a ∈ ({x} : Finset V) := by simpa [hxeq] using haA
            simpa using this
          exact (hxa this.symm).elim
        · exact hcross hxSA haB
      · intro hxb
        have hbS : b ∈ S := by simp [S]
        have : b ∈ SA ∨ b ∈ SB := by
          have : b ∈ SA ∪ SB := by simpa [hunion] using hbS
          simpa [Finset.mem_union] using this
        rcases this with hbA | hbB
        · have : b = x := by
            have : b ∈ ({x} : Finset V) := by simpa [hxeq] using hbA
            simpa using this
          exact (hxb this.symm).elim
        · exact hcross hxSA hbB
      · intro hxc
        have hcS : c ∈ S := by simp [S]
        have : c ∈ SA ∨ c ∈ SB := by
          have : c ∈ SA ∪ SB := by simpa [hunion] using hcS
          simpa [Finset.mem_union] using this
        rcases this with hcA | hcB
        · have : c = x := by
            have : c ∈ ({x} : Finset V) := by simpa [hxeq] using hcA
            simpa using this
          exact (hxc this.symm).elim
        · exact hcross hxSA hcB
      · intro hxd
        have hdS : d ∈ S := by simp [S]
        have : d ∈ SA ∨ d ∈ SB := by
          have : d ∈ SA ∪ SB := by simpa [hunion] using hdS
          simpa [Finset.mem_union] using this
        rcases this with hdA | hdB
        · have : d = x := by
            have : d ∈ ({x} : Finset V) := by simpa [hxeq] using hdA
            simpa using this
          exact (hxd this.symm).elim
        · exact hcross hxSA hdB
    exact hp.not_adj_other_three hxquad hother
  · -- 2-2 split: four distinct cross edges, but an induced P4 has only three edges
    have hSB2 : SB.card = 2 := by omega
    obtain ⟨x, y, hxy, hSA2⟩ := Finset.card_eq_two.mp h2
    obtain ⟨z, w, hzw, hSB2eq⟩ := Finset.card_eq_two.mp hSB2
    have hxA : x ∈ SA := by simp [hSA2]
    have hyA : y ∈ SA := by simp [hSA2]
    have hzB : z ∈ SB := by simp [hSB2eq]
    have hwB : w ∈ SB := by simp [hSB2eq]
    have hxS : x ∈ S := (Finset.mem_filter.mp hxA).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hyA).1
    have hzS : z ∈ S := (Finset.mem_filter.mp hzB).1
    have hwS : w ∈ S := (Finset.mem_filter.mp hwB).1
    have hx_ne_z : x ≠ z := fun h =>
      Set.disjoint_left.1 hdisjAB (Finset.mem_filter.mp hxA).2
        (by simpa [h] using (Finset.mem_filter.mp hzB).2)
    have hx_ne_w : x ≠ w := fun h =>
      Set.disjoint_left.1 hdisjAB (Finset.mem_filter.mp hxA).2
        (by simpa [h] using (Finset.mem_filter.mp hwB).2)
    have hy_ne_z : y ≠ z := fun h =>
      Set.disjoint_left.1 hdisjAB (Finset.mem_filter.mp hyA).2
        (by simpa [h] using (Finset.mem_filter.mp hzB).2)
    have hy_ne_w : y ≠ w := fun h =>
      Set.disjoint_left.1 hdisjAB (Finset.mem_filter.mp hyA).2
        (by simpa [h] using (Finset.mem_filter.mp hwB).2)
    let E : Finset (Sym2 V) := {s(x, z), s(x, w), s(y, z), s(y, w)}
    have hEcard : E.card = 4 := by
      have hxz_xw : s(x, z) ≠ s(x, w) := by
        intro h
        have : z = w := by
          simpa [Sym2.eq_iff, hx_ne_z, hx_ne_w, hxy] using h
        exact hzw this
      have hxz_yz : s(x, z) ≠ s(y, z) := by
        intro h
        have : x = y := by
          simpa [Sym2.eq_iff, hx_ne_z, hy_ne_z, hzw] using h
        exact hxy this
      have hxz_yw : s(x, z) ≠ s(y, w) := by
        intro h
        have : x = y ∧ z = w ∨ x = w ∧ z = y := by
          simpa [Sym2.eq_iff] using h
        rcases this with ⟨h', _⟩ | ⟨h', _⟩
        · exact hxy h'
        · exact hx_ne_w h'
      have hxw_yz : s(x, w) ≠ s(y, z) := by
        intro h
        have : x = y ∧ w = z ∨ x = z ∧ w = y := by
          simpa [Sym2.eq_iff] using h
        rcases this with ⟨h', _⟩ | ⟨h', _⟩
        · exact hxy h'
        · exact hx_ne_z h'
      have hxw_yw : s(x, w) ≠ s(y, w) := by
        intro h
        have : x = y := by
          simpa [Sym2.eq_iff, hx_ne_w, hy_ne_w, hzw] using h
        exact hxy this
      have hyz_yw : s(y, z) ≠ s(y, w) := by
        intro h
        have : z = w := by
          simpa [Sym2.eq_iff, hy_ne_z, hy_ne_w, hxy] using h
        exact hzw this
      simp [E, hxz_xw, hxz_yz, hxz_yw, hxw_yz, hxw_yw, hyz_yw]
    have hEsub : E ⊆ ({s(a, b), s(b, c), s(c, d)} : Finset (Sym2 V)) := by
      intro e he
      have he' : e = s(x, z) ∨ e = s(x, w) ∨ e = s(y, z) ∨ e = s(y, w) := by
        simpa [E, Finset.mem_insert, Finset.mem_singleton] using he
      have hmem {p q : V} (hpq : p ∈ S) (hqp : q ∈ S) (hpqne : p ≠ q)
          (hadj : G.Adj p q) :
          s(p, q) ∈ ({s(a, b), s(b, c), s(c, d)} : Finset (Sym2 V)) := by
        have := inducedP4_adj_mem_path_edges hp hpq hqp hpqne hadj
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      rcases he' with rfl | rfl | rfl | rfl
      · exact hmem hxS hzS hx_ne_z (hcross hxA hzB)
      · exact hmem hxS hwS hx_ne_w (hcross hxA hwB)
      · exact hmem hyS hzS hy_ne_z (hcross hyA hzB)
      · exact hmem hyS hwS hy_ne_w (hcross hyA hwB)
    have : E.card ≤ ({s(a, b), s(b, c), s(c, d)} : Finset (Sym2 V)).card :=
      Finset.card_le_card hEsub
    have : 4 ≤ 3 := by simpa [hEcard, card_p4_path_edges hp] using this
    omega
  · obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp (show SB.card = 1 by omega)
    have hxSB : x ∈ SB := by simp [hxeq]
    have hxS : x ∈ S := (Finset.mem_filter.mp hxSB).1
    have hxquad : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [S, Finset.mem_insert, Finset.mem_singleton] using hxS
    have hother : (x ≠ a → G.Adj x a) ∧ (x ≠ b → G.Adj x b) ∧
        (x ≠ c → G.Adj x c) ∧ (x ≠ d → G.Adj x d) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hxa
        have haS : a ∈ S := by simp [S]
        have : a ∈ SA ∨ a ∈ SB := by
          have : a ∈ SA ∪ SB := by simpa [hunion] using haS
          simpa [Finset.mem_union] using this
        rcases this with haA | haB
        · exact (hcross haA hxSB).symm
        · have : a = x := by
            have : a ∈ ({x} : Finset V) := by simpa [hxeq] using haB
            simpa using this
          exact (hxa this.symm).elim
      · intro hxb
        have hbS : b ∈ S := by simp [S]
        have : b ∈ SA ∨ b ∈ SB := by
          have : b ∈ SA ∪ SB := by simpa [hunion] using hbS
          simpa [Finset.mem_union] using this
        rcases this with hbA | hbB
        · exact (hcross hbA hxSB).symm
        · have : b = x := by
            have : b ∈ ({x} : Finset V) := by simpa [hxeq] using hbB
            simpa using this
          exact (hxb this.symm).elim
      · intro hxc
        have hcS : c ∈ S := by simp [S]
        have : c ∈ SA ∨ c ∈ SB := by
          have : c ∈ SA ∪ SB := by simpa [hunion] using hcS
          simpa [Finset.mem_union] using this
        rcases this with hcA | hcB
        · exact (hcross hcA hxSB).symm
        · have : c = x := by
            have : c ∈ ({x} : Finset V) := by simpa [hxeq] using hcB
            simpa using this
          exact (hxc this.symm).elim
      · intro hxd
        have hdS : d ∈ S := by simp [S]
        have : d ∈ SA ∨ d ∈ SB := by
          have : d ∈ SA ∪ SB := by simpa [hunion] using hdS
          simpa [Finset.mem_union] using this
        rcases this with hdA | hdB
        · exact (hcross hdA hxSB).symm
        · have : d = x := by
            have : d ∈ ({x} : Finset V) := by simpa [hxeq] using hdB
            simpa using this
          exact (hxd this.symm).elim
    exact hp.not_adj_other_three hxquad hother

/-- Complete join of finset parts preserves `P4`-freeness. -/
lemma isCographGraph_complete_join_finset [Fintype V] [DecidableEq V] {A B : Finset V}
    (hcover : A ∪ B = Finset.univ) (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hA : IsCograph G A) (hB : IsCograph G B) : IsCographGraph G :=
  isCographGraph_complete_join (A := (A : Set V)) (B := (B : Set V))
    (by
      ext x
      constructor
      · intro; simp
      · intro
        have : x ∈ A ∪ B := by simp [hcover]
        simpa [Finset.mem_union] using this) hAB hA hB

/-- Following a `G`-edge from `A` cannot land in `B` if there are no cross edges;
if the other end already lies in `A ∪ B`, it therefore lies in `A`. -/
lemma mem_of_adj_of_no_cross_of_mem {A B : Set V} {a b : V}
    (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (ha : a ∈ A) (hbAB : b ∈ A ∨ b ∈ B) (hadj : G.Adj a b) : b ∈ A := by
  rcases hbAB with hbA | hbB
  · exact hbA
  · exact (hnocross a ha b hbB hadj).elim

lemma mem_of_adj_of_no_cross_of_mem' {A B : Set V} {a b : V}
    (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (ha : a ∈ B) (hbAB : b ∈ A ∨ b ∈ B) (hadj : G.Adj a b) : b ∈ B := by
  have hsym : ∀ x ∈ B, ∀ y ∈ A, ¬ G.Adj x y := fun x hx y hy hxy =>
    hnocross y hy x hx hxy.symm
  have hbBA : b ∈ B ∨ b ∈ A := hbAB.symm
  exact mem_of_adj_of_no_cross_of_mem (A := B) (B := A) hsym ha hbBA hadj

/-- An induced `P4` contained in `A ∪ B` cannot meet both sides of a no-cross partition. -/
lemma inducedP4_subset_of_no_cross {A B : Set V} {a b c d : V}
    (hmem : ({a, b, c, d} : Set V) ⊆ A ∪ B)
    (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (hp : InducedP4 G a b c d) :
    ({a, b, c, d} : Set V) ⊆ A ∨ ({a, b, c, d} : Set V) ⊆ B := by
  have hab : G.Adj a b := hp.adj_ab
  have hbc : G.Adj b c := hp.adj_bc
  have hcd : G.Adj c d := hp.adj_cd
  have mem4 {x : V} (hx : x ∈ ({a, b, c, d} : Set V)) : x ∈ A ∨ x ∈ B := by
    have : x ∈ A ∪ B := hmem hx
    simpa [Set.mem_union] using this
  have haAB : a ∈ A ∨ a ∈ B := mem4 (by simp)
  rcases haAB with haA | haB
  · refine Or.inl ?_
    intro x hx
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    have hbA : b ∈ A :=
      mem_of_adj_of_no_cross_of_mem hnocross haA (mem4 (by simp)) hab
    have hcA : c ∈ A :=
      mem_of_adj_of_no_cross_of_mem hnocross hbA (mem4 (by simp)) hbc
    have hdA : d ∈ A :=
      mem_of_adj_of_no_cross_of_mem hnocross hcA (mem4 (by simp)) hcd
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption
  · refine Or.inr ?_
    intro x hx
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    have hbB : b ∈ B :=
      mem_of_adj_of_no_cross_of_mem' hnocross haB (mem4 (by simp)) hab
    have hcB : c ∈ B :=
      mem_of_adj_of_no_cross_of_mem' hnocross hbB (mem4 (by simp)) hbc
    have hdB : d ∈ B :=
      mem_of_adj_of_no_cross_of_mem' hnocross hcB (mem4 (by simp)) hcd
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption

/-- Disjoint union of two `P4`-free sets remains `P4`-free on the union. -/
lemma isCographOn_union_of_no_cross {A B : Set V}
    (hnocross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (hA : IsCographOn G A) (hB : IsCographOn G B) : IsCographOn G (A ∪ B) := by
  intro a b c d ha hb hc hd hp
  have hmem : ({a, b, c, d} : Set V) ⊆ A ∪ B := by
    intro x hx
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases hx' with rfl | rfl | rfl | rfl <;> simp [ha, hb, hc, hd]
  rcases inducedP4_subset_of_no_cross hmem hnocross hp with hA' | hB'
  · exact hA (hA' (by simp)) (hA' (by simp)) (hA' (by simp)) (hA' (by simp)) hp
  · exact hB (hB' (by simp)) (hB' (by simp)) (hB' (by simp)) (hB' (by simp)) hp

lemma isCograph_union_of_no_cross [DecidableEq V] {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hA : IsCograph G A) (hB : IsCograph G B) : IsCograph G (A ∪ B) := by
  rw [← isCographOn_iff_isCograph, Finset.coe_union]
  exact isCographOn_union_of_no_cross (A := (A : Set V)) (B := (B : Set V))
    (fun a ha b hb => hnocross a ha b hb) hA hB

/-- Complete join of two `P4`-free sets remains `P4`-free on the union. -/
lemma isCographOn_union_of_complete_join [DecidableEq V] {A B : Set V}
    (hAB : G.IsCompleteBetween A B)
    (hA : IsCographOn G A) (hB : IsCographOn G B) : IsCographOn G (A ∪ B) := by
  rw [isCographOn_iff_isCographGraph_induce]
  let s : Set V := A ∪ B
  let A' : Set s := Subtype.val ⁻¹' A
  let B' : Set s := Subtype.val ⁻¹' B
  have hcover : A' ∪ B' = (Set.univ : Set s) := by
    ext x
    constructor
    · intro
      trivial
    · intro
      have hx : x.1 ∈ A ∨ x.1 ∈ B := by
        have : x.1 ∈ A ∪ B := x.property
        exact (Set.mem_union (x := x.1) (a := A) (b := B)).mp this
      refine (Set.mem_union (x := x) (a := A') (b := B')).mpr ?_
      rcases hx with hxA | hxB
      · exact Or.inl hxA
      · exact Or.inr hxB
  have hABon : (G.induce s).IsCompleteBetween A' B' := by
    intro x hx y hy
    have : G.Adj x.1 y.1 :=
      hAB (by simpa [A', Set.mem_preimage] using hx)
        (by simpa [B', Set.mem_preimage] using hy)
    simpa [induce_adj] using this
  have hA' : IsCographOn (G.induce s) A' := by
    intro a b c d ha hb hc hd hp
    exact hA (by simpa [A', Set.mem_preimage] using ha)
      (by simpa [A', Set.mem_preimage] using hb)
      (by simpa [A', Set.mem_preimage] using hc)
      (by simpa [A', Set.mem_preimage] using hd) (inducedP4_induce hp)
  have hB' : IsCographOn (G.induce s) B' := by
    intro a b c d ha hb hc hd hp
    exact hB (by simpa [B', Set.mem_preimage] using ha)
      (by simpa [B', Set.mem_preimage] using hb)
      (by simpa [B', Set.mem_preimage] using hc)
      (by simpa [B', Set.mem_preimage] using hd) (inducedP4_induce hp)
  exact isCographGraph_complete_join (A := A') (B := B') hcover hABon hA' hB'

lemma isCograph_union_of_complete_join [DecidableEq V] {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hA : IsCograph G A) (hB : IsCograph G B) : IsCograph G (A ∪ B) := by
  rw [← isCographOn_iff_isCograph, Finset.coe_union]
  exact isCographOn_union_of_complete_join (A := (A : Set V)) (B := (B : Set V)) hAB hA hB

end Cograph
end Nikoghosyan

