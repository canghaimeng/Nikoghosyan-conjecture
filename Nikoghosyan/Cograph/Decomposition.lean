/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-!
# Complete-join decomposition of connected cographs

Manuscript `cog:lem:cotree`: a finite connected cograph of order at least two is
a nontrivial complete join of two nonempty smaller induced cographs.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph

variable {V : Type u}

/-- A walk from a vertex of `T` to a vertex outside `T` has a leaving edge. -/
lemma Walk.exists_leaving_edge {G : SimpleGraph V} {u w : V} {T : Set V}
    (p : G.Walk u w) (hu : u ∈ T) (hw : w ∉ T) :
    ∃ x y, x ∈ T ∧ y ∉ T ∧ G.Adj x y := by
  induction p with
  | nil => exact (hw hu).elim
  | cons hadj p ih =>
    rename_i u v w
    by_cases hv : v ∈ T
    · exact ih hv hw
    · exact ⟨u, v, hu, hv, hadj⟩

variable [Fintype V] [DecidableEq V]

/-- Nonneighbours of `v`, excluding `v` itself. -/
def nonneighbors (G : SimpleGraph V) (v : V) : Set V := {w | w ≠ v ∧ ¬ G.Adj v w}

lemma mem_nonneighbors {G : SimpleGraph V} {v w : V} :
    w ∈ nonneighbors G v ↔ w ≠ v ∧ ¬ G.Adj v w := Iff.rfl

lemma not_mem_nonneighbors_of_adj {G : SimpleGraph V} {v a : V} (ha : G.Adj v a) :
    a ∉ nonneighbors G v := fun h => h.2 ha

/-- Neighbours of `v` that are complete to a nonneighbour-component. -/
noncomputable def completeToBlock (G : SimpleGraph V) (v : V)
    (C : (G.induce (nonneighbors G v)).ConnectedComponent) : Finset V :=
  Finset.univ.filter fun a => G.Adj v a ∧ ∀ b ∈ componentVerts C, G.Adj a b

lemma mem_completeToBlock {G : SimpleGraph V} {v a : V}
    {C : (G.induce (nonneighbors G v)).ConnectedComponent} :
    a ∈ completeToBlock G v C ↔
      G.Adj v a ∧ ∀ b ∈ componentVerts C, G.Adj a b := by
  simp [completeToBlock]

/-- If a neighbour meets a nonneighbour-component, it is complete to that
component: a boundary edge in the component would form an induced `P4`
`v-a-x-y`. -/
lemma completeToBlock_of_meets {G : SimpleGraph V} {v a : V}
    {C : (G.induce (nonneighbors G v)).ConnectedComponent}
    (hC : IsCographGraph G) (ha : G.Adj v a)
    (hmeet : ∃ b ∈ componentVerts C, G.Adj a b) :
    a ∈ completeToBlock G v C := by
  refine mem_completeToBlock.2 ⟨ha, ?_⟩
  intro b' hb'
  by_contra hnab
  obtain ⟨b, hb, hab⟩ := hmeet
  obtain ⟨hbS, hbC⟩ := (mem_componentVerts (C := C)).1 hb
  obtain ⟨hb'S, hb'C⟩ := (mem_componentVerts (C := C)).1 hb'
  let T : Set (nonneighbors G v) := {x | G.Adj a x.1}
  have hu : (⟨b, hbS⟩ : nonneighbors G v) ∈ T := hab
  have hw : (⟨b', hb'S⟩ : nonneighbors G v) ∉ T := hnab
  have hreach : (G.induce (nonneighbors G v)).Reachable ⟨b, hbS⟩ ⟨b', hb'S⟩ :=
    ConnectedComponent.exact (by
      rw [ConnectedComponent.mem_supp_iff] at hbC hb'C
      rw [hbC, hb'C])
  obtain ⟨p⟩ := hreach
  obtain ⟨x, y, hxT, hyT, hxy⟩ := Walk.exists_leaving_edge p hu hw
  have hxyG : G.Adj x.1 y.1 := by simpa [induce_adj] using hxy
  have hadj_ax : G.Adj a x.1 := hxT
  have ha_ne_x : a ≠ x.1 := hadj_ax.ne
  have ha_ne_y : a ≠ y.1 := fun h => not_mem_nonneighbors_of_adj ha (h ▸ y.2)
  have hp4 : InducedP4 G v a x.1 y.1 :=
    { ne_ab := ha.ne
      ne_ac := x.2.1.symm
      ne_ad := y.2.1.symm
      ne_bc := ha_ne_x
      ne_bd := ha_ne_y
      ne_cd := fun h => hxy.ne (Subtype.ext h)
      adj_ab := ha
      adj_bc := hxT
      adj_cd := hxyG
      not_ac := x.2.2
      not_ad := y.2.2
      not_bd := hyT }
  exact hC _ _ _ _ hp4

/-- A connected cograph of order at least two with a universal vertex is a
nontrivial complete join `{v}` against the remainder. -/
lemma exists_complete_join_of_universal {G : SimpleGraph V} {v : V}
    (_hG : G.Connected) (hcard : 2 ≤ Fintype.card V) (hv : G.IsUniversal v) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧
      G.IsCompleteBetween (A : Set V) (B : Set V) ∧
      A.card < Fintype.card V ∧ B.card < Fintype.card V := by
  have : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hcard)
  obtain ⟨w, hw⟩ := exists_ne v
  refine ⟨{v}, Finset.univ.erase v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.singleton_nonempty v
  · exact ⟨w, Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩⟩
  · exact Finset.disjoint_singleton_left.2 (Finset.notMem_erase v _)
  · ext x
    by_cases hx : x = v <;> simp [hx]
  · intro x hx y hy
    have hx' : x = v := Finset.mem_singleton.mp hx
    have hy' : y ≠ v := (Finset.mem_erase.mp hy).1
    subst hx'
    exact hv hy'.symm
  · have : ({v} : Finset V).card = 1 := Finset.card_singleton v
    omega
  · have : (Finset.univ.erase v).card = Fintype.card V - 1 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ v)]
    omega

lemma componentVerts_nonempty {G : SimpleGraph V} {s : Set V}
    (C : (G.induce s).ConnectedComponent) : (componentVerts C).Nonempty := by
  obtain ⟨x, hx⟩ := C.nonempty_supp
  exact ⟨x.1, ⟨x, hx, rfl⟩⟩

/-- A neighbour outside `completeToBlock G v C` meets no vertex of that block;
otherwise completeness would place it in the block. -/
lemma not_adj_to_block_of_not_mem_completeToBlock {G : SimpleGraph V} {v b : V}
    {C : (G.induce (nonneighbors G v)).ConnectedComponent}
    (hC : IsCographGraph G) (hbN : G.Adj v b)
    (hb : b ∉ completeToBlock G v C) {x : V} (hx : x ∈ componentVerts C) :
    ¬ G.Adj b x := by
  intro hbx
  have : b ∈ completeToBlock G v C :=
    completeToBlock_of_meets hC hbN ⟨x, hx, hbx⟩
  exact hb this

/-- A vertex of `A_i` is adjacent to every neighbour of `v` that is not in `A_i`.
Otherwise a vertex of the block, followed by `a`, `v`, and `b`, is an induced `P4`. -/
lemma adj_of_mem_completeToBlock_of_not_mem {G : SimpleGraph V} {v a b : V}
    {C : (G.induce (nonneighbors G v)).ConnectedComponent}
    (hC : IsCographGraph G) (ha : a ∈ completeToBlock G v C) (hbN : G.Adj v b)
    (hb : b ∉ completeToBlock G v C) : G.Adj a b := by
  obtain ⟨x, hx⟩ := componentVerts_nonempty C
  have haN : G.Adj v a := (mem_completeToBlock.1 ha).1
  have hax : G.Adj a x := (mem_completeToBlock.1 ha).2 x hx
  by_contra hnab
  have hxN := componentVerts_subset C hx
  have hbx : ¬ G.Adj b x :=
    not_adj_to_block_of_not_mem_completeToBlock hC hbN hb hx
  have hp4 : InducedP4 G x a v b :=
    { ne_ab := hax.ne.symm
      ne_ac := hxN.1
      ne_ad := fun h => hxN.2 (h ▸ hbN)
      ne_bc := haN.ne.symm
      ne_bd := fun h => hb (h ▸ ha)
      ne_cd := hbN.ne
      adj_ab := hax.symm
      adj_bc := haN.symm
      adj_cd := hbN
      not_ac := fun h => hxN.2 h.symm
      not_ad := fun h => hbx h.symm
      not_bd := hnab }
  exact hC _ _ _ _ hp4

/-- In a connected graph, every nonneighbour-component has a nonempty
complete-neighbour set. -/
lemma completeToBlock_nonempty {G : SimpleGraph V} {v : V}
    {C : (G.induce (nonneighbors G v)).ConnectedComponent}
    (hG : G.Connected) (hC : IsCographGraph G) :
    (completeToBlock G v C).Nonempty := by
  by_contra hempty
  have hAempty : completeToBlock G v C = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  obtain ⟨x, hx⟩ := componentVerts_nonempty C
  have hvT : v ∉ componentVerts C := fun h =>
    (componentVerts_subset C h).1 rfl
  obtain ⟨p⟩ := hG x v
  obtain ⟨y, z, hyT, hzT, hyz⟩ :=
    Walk.exists_leaving_edge (T := componentVerts C) p hx hvT
  -- Classify the outside endpoint `z`.
  have hyN := componentVerts_subset C hyT
  have hz_cases : z ∈ G.neighborSet v ∨ z = v ∨ z ∈ nonneighbors G v := by
    by_cases hzn : z = v
    · exact Or.inr (Or.inl hzn)
    · by_cases hzadj : G.Adj v z
      · exact Or.inl hzadj
      · exact Or.inr (Or.inr ⟨hzn, hzadj⟩)
  rcases hz_cases with hzN | hzv | hzB
  · -- `z` is a neighbour meeting the block, hence lies in `completeToBlock`.
    have hzA : z ∈ completeToBlock G v C :=
      completeToBlock_of_meets hC hzN ⟨y, hyT, hyz.symm⟩
    have : z ∈ (∅ : Finset V) := hAempty ▸ hzA
    exact Finset.notMem_empty z this
  · -- `z = v` but `y` is a nonneighbour, so `G.Adj y v` is impossible.
    subst hzv
    exact hyN.2 hyz.symm
  · -- `z` is another nonneighbour: then `y z` is an induce-edge, so `z` is in `C`.
    have hyS : y ∈ nonneighbors G v := hyN
    have : (G.induce (nonneighbors G v)).Adj ⟨y, hyS⟩ ⟨z, hzB⟩ := by
      simpa [induce_adj] using hyz
    have hzC : z ∈ componentVerts C := by
      refine (mem_componentVerts (C := C)).2 ⟨hzB, ?_⟩
      have hyC : (⟨y, hyS⟩ : nonneighbors G v) ∈ C.supp :=
        (mem_componentVerts (C := C)).1 hyT |>.2
      exact (C.mem_supp_congr_adj this).mp hyC
    exact hzT hzC

lemma not_isUniversal_iff {G : SimpleGraph V} {v : V} :
    ¬ G.IsUniversal v ↔ (nonneighbors G v).Nonempty := by
  constructor
  · intro hv
    unfold SimpleGraph.IsUniversal at hv
    push_neg at hv
    obtain ⟨w, hwne, hwadj⟩ := hv
    exact ⟨w, hwne.symm, hwadj⟩
  · intro ⟨w, hw⟩
    intro hU
    exact hw.2 (hU hw.1.symm)

lemma mem_nonneighbors_of_mem_componentVerts {G : SimpleGraph V} {v : V}
    {C : (G.induce (nonneighbors G v)).ConnectedComponent} {x : V}
    (hx : x ∈ componentVerts C) : x ∈ nonneighbors G v :=
  componentVerts_subset C hx

lemma not_mem_completeToBlock_self {G : SimpleGraph V} {v : V}
    {C : (G.induce (nonneighbors G v)).ConnectedComponent} :
    v ∉ completeToBlock G v C := by
  intro h
  exact (mem_completeToBlock.1 h).1.ne rfl

/-- Distinct nonneighbour-components have no original edge between them. -/
lemma not_adj_of_ne_component {G : SimpleGraph V} {s : Set V}
    {C D : (G.induce s).ConnectedComponent} (hCD : C ≠ D) {x y : V}
    (hx : x ∈ componentVerts C) (hy : y ∈ componentVerts D) : ¬ G.Adj x y := by
  obtain ⟨hxS, hxC⟩ := (mem_componentVerts (C := C)).1 hx
  have hxD : (⟨x, hxS⟩ : s) ∉ D.supp := by
    intro hmem
    apply hCD
    rw [ConnectedComponent.mem_supp_iff] at hxC hmem
    exact hxC.symm.trans hmem
  exact not_adj_of_mem_other_component hxS hxD hy

lemma connectedComponent_eq_of_mem_componentVerts {G : SimpleGraph V} {s : Set V}
    {C D : (G.induce s).ConnectedComponent} {x : V}
    (hxC : x ∈ componentVerts C) (hxD : x ∈ componentVerts D) : C = D := by
  obtain ⟨hxS, hC⟩ := (mem_componentVerts (C := C)).1 hxC
  obtain ⟨_, hD⟩ := (mem_componentVerts (C := D)).1 hxD
  rw [ConnectedComponent.mem_supp_iff] at hC hD
  exact hC.symm.trans hD

/-- The family of complete-neighbour blocks is nested. -/
lemma completeToBlock_nested {G : SimpleGraph V} {v : V}
    {C D : (G.induce (nonneighbors G v)).ConnectedComponent}
    (hCograph : IsCographGraph G) :
    completeToBlock G v C ⊆ completeToBlock G v D ∨
      completeToBlock G v D ⊆ completeToBlock G v C := by
  by_contra h
  push_neg at h
  obtain ⟨a, haC, haD⟩ := Finset.not_subset.mp h.1
  obtain ⟨b, hbD, hbC⟩ := Finset.not_subset.mp h.2
  have hCneD : C ≠ D := by
    intro hCD
    subst hCD
    exact haD haC
  have hbN : G.Adj v b := (mem_completeToBlock.1 hbD).1
  have hab : G.Adj a b :=
    adj_of_mem_completeToBlock_of_not_mem hCograph haC hbN hbC
  obtain ⟨x, hx⟩ := componentVerts_nonempty C
  obtain ⟨y, hy⟩ := componentVerts_nonempty D
  have hxN := mem_nonneighbors_of_mem_componentVerts hx
  have hyN := mem_nonneighbors_of_mem_componentVerts hy
  have hax : G.Adj a x := (mem_completeToBlock.1 haC).2 x hx
  have hby : G.Adj b y := (mem_completeToBlock.1 hbD).2 y hy
  have hbx : ¬ G.Adj b x :=
    not_adj_to_block_of_not_mem_completeToBlock hCograph hbN hbC hx
  have hay : ¬ G.Adj a y :=
    not_adj_to_block_of_not_mem_completeToBlock hCograph
      (mem_completeToBlock.1 haC).1 haD hy
  have hxy : ¬ G.Adj x y := not_adj_of_ne_component hCneD hx hy
  have hx_ne_y : x ≠ y := by
    intro hxy'
    exact hCneD (connectedComponent_eq_of_mem_componentVerts (hxy' ▸ hx) hy)
  have hp4 : InducedP4 G x a b y :=
    { ne_ab := hax.ne.symm
      ne_ac := fun h => hxN.2 (h ▸ hbN)
      ne_ad := hx_ne_y
      ne_bc := hab.ne
      ne_bd := fun h => hyN.2 (h ▸ (mem_completeToBlock.1 haC).1)
      ne_cd := hby.ne
      adj_ab := hax.symm
      adj_bc := hab
      adj_cd := hby
      not_ac := fun h => hbx h.symm
      not_ad := hxy
      not_bd := hay }
  exact hCograph _ _ _ _ hp4

lemma exists_min_completeToBlock {G : SimpleGraph V} {v : V}
    (hv : ¬ G.IsUniversal v) (hCograph : IsCographGraph G) :
    ∃ C : (G.induce (nonneighbors G v)).ConnectedComponent,
      ∀ D, completeToBlock G v C ⊆ completeToBlock G v D := by
  haveI : DecidableRel G.Adj := Classical.decRel _
  haveI : Fintype (nonneighbors G v) := inferInstance
  haveI : DecidableRel (G.induce (nonneighbors G v)).Adj := inferInstance
  haveI : Fintype (G.induce (nonneighbors G v)).ConnectedComponent := inferInstance
  haveI : Nonempty (G.induce (nonneighbors G v)).ConnectedComponent := by
    obtain ⟨w, hw⟩ := (not_isUniversal_iff (v := v)).1 hv
    exact ⟨(G.induce (nonneighbors G v)).connectedComponentMk ⟨w, hw⟩⟩
  obtain ⟨C, hmin⟩ :=
    Finite.exists_min (fun D : (G.induce (nonneighbors G v)).ConnectedComponent =>
      (completeToBlock G v D).card)
  refine ⟨C, fun D => ?_⟩
  rcases completeToBlock_nested (C := C) (D := D) hCograph with hCD | hDC
  · exact hCD
  · have hcard : (completeToBlock G v D).card = (completeToBlock G v C).card :=
      le_antisymm (Finset.card_mono hDC) (hmin D)
    have : completeToBlock G v D = completeToBlock G v C :=
      Finset.eq_of_subset_of_card_le hDC (by omega)
    simpa [this]

/-- Non-universal vertex: a smallest complete-neighbour block is a join side. -/
lemma exists_complete_join_of_not_universal {G : SimpleGraph V} {v : V}
    (hG : G.Connected) (hCograph : IsCographGraph G) (hv : ¬ G.IsUniversal v) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧
      G.IsCompleteBetween (A : Set V) (B : Set V) ∧
      A.card < Fintype.card V ∧ B.card < Fintype.card V := by
  obtain ⟨C, hmin⟩ := exists_min_completeToBlock (v := v) hv hCograph
  let A := completeToBlock G v C
  let B := Finset.univ \ A
  have hAne : A.Nonempty := completeToBlock_nonempty (C := C) hG hCograph
  have hvB : v ∈ B := by
    simp [B, A, not_mem_completeToBlock_self (C := C)]
  have hBne : B.Nonempty := ⟨v, hvB⟩
  have hdisj : Disjoint A B := Finset.disjoint_sdiff
  have hcover : A ∪ B = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ A)
  have hAB : G.IsCompleteBetween (A : Set V) (B : Set V) := by
    intro a ha b hb
    have haN : G.Adj v a := (mem_completeToBlock.1 (by simpa [A] using ha)).1
    have hbA : b ∉ A := by
      have : b ∈ B := hb
      simp [B] at this
      exact this
    by_cases hbv : b = v
    · subst hbv
      exact haN.symm
    · by_cases hbN : G.Adj v b
      · exact adj_of_mem_completeToBlock_of_not_mem hCograph
          (by simpa [A] using ha) hbN hbA
      · have hbnn : b ∈ nonneighbors G v := ⟨hbv, hbN⟩
        let D := (G.induce (nonneighbors G v)).connectedComponentMk ⟨b, hbnn⟩
        have hbD : b ∈ componentVerts D :=
          (mem_componentVerts (C := D)).2 ⟨hbnn, by
            simp [D, ConnectedComponent.mem_supp_iff]⟩
        have hsub : A ⊆ completeToBlock G v D := by
          simpa [A] using hmin D
        have haD : a ∈ completeToBlock G v D := hsub (by simpa [A] using ha)
        exact (mem_completeToBlock.1 haD).2 b hbD
  have hsum : A.card + B.card = Fintype.card V := by
    have := Finset.card_union_of_disjoint hdisj
    simpa [hcover, Finset.card_univ] using this.symm
  have hAcard : A.card < Fintype.card V := by
    have : 1 ≤ B.card := Finset.card_pos.mpr hBne
    omega
  have hBcard : B.card < Fintype.card V := by
    have : 1 ≤ A.card := Finset.card_pos.mpr hAne
    omega
  exact ⟨A, B, hAne, hBne, hdisj, hcover, hAB, hAcard, hBcard⟩

/-- A finite connected cograph of order at least two is a nontrivial complete join
of two nonempty strictly smaller induced subgraphs, using only original edges. -/
lemma exists_complete_join_of_connected_cograph {G : SimpleGraph V}
    (hG : G.Connected) (hCograph : IsCographGraph G) (hcard : 2 ≤ Fintype.card V) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧
      G.IsCompleteBetween (A : Set V) (B : Set V) ∧
      A.card < Fintype.card V ∧ B.card < Fintype.card V := by
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hcard)
  let v : V := Classical.choice ‹Nonempty V›
  by_cases hv : G.IsUniversal v
  · exact exists_complete_join_of_universal hG hcard hv
  · exact exists_complete_join_of_not_universal hG hCograph hv

/-- A nonempty disconnected graph splits as a disjoint union of a component and
its nonempty complement, with no original cross edges. -/
lemma exists_disjoint_union_of_not_connected {G : SimpleGraph V} [Nonempty V]
    (hG : ¬ G.Connected) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧
      A.card < Fintype.card V ∧ B.card < Fintype.card V := by
  have hpre : ¬ G.Preconnected := fun hp =>
    hG ((connected_iff G).2 ⟨hp, ‹Nonempty V›⟩)
  obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ G.Reachable x y := by
    unfold SimpleGraph.Preconnected at hpre
    push_neg at hpre
    exact hpre
  let u : V := Classical.choice ‹Nonempty V›
  have hz : ∃ z, ¬ G.Reachable u z := by
    by_cases hux : G.Reachable u x
    · by_cases huy : G.Reachable u y
      · exact (hxy (hux.symm.trans huy)).elim
      · exact ⟨y, huy⟩
    · exact ⟨x, hux⟩
  obtain ⟨z, huz⟩ := hz
  let C := G.connectedComponentMk u
  let A : Finset V := Finset.univ.filter (fun w => G.connectedComponentMk w = C)
  have huA : u ∈ A := by simp [A, C]
  have hAne : A.Nonempty := ⟨u, huA⟩
  let B := Finset.univ \ A
  have hzB : z ∈ B := by
    simp [B, A, C]
    intro h
    exact huz h.symm
  have hBne : B.Nonempty := ⟨z, hzB⟩
  have hdisj : Disjoint A B := Finset.disjoint_sdiff
  have hcover : A ∪ B = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ A)
  have hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a ha b hb hadj
    have hbA : b ∉ A := by
      have : b ∈ B := hb
      simp [B] at this
      exact this
    have hmk :
        G.connectedComponentMk a = G.connectedComponentMk b :=
      ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    have haC : G.connectedComponentMk a = C := (Finset.mem_filter.mp ha).2
    have hbC : G.connectedComponentMk b = C := hmk.symm.trans haC
    exact hbA (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hbC⟩)
  have hsum : A.card + B.card = Fintype.card V := by
    have := Finset.card_union_of_disjoint hdisj
    simpa [hcover, Finset.card_univ] using this.symm
  have hAcard : A.card < Fintype.card V := by
    have : 1 ≤ B.card := Finset.card_pos.mpr hBne
    omega
  have hBcard : B.card < Fintype.card V := by
    have : 1 ≤ A.card := Finset.card_pos.mpr hAne
    omega
  exact ⟨A, B, hAne, hBne, hdisj, hcover, hnocross, hAcard, hBcard⟩

/-- Push a finset of a coerced vertex set forward to the ambient type. -/
def finsetOfSubtype {s : Set V} (A : Finset s) : Finset V :=
  A.image Subtype.val

lemma card_finsetOfSubtype {s : Set V} (A : Finset s) :
    (finsetOfSubtype A).card = A.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

lemma finsetOfSubtype_univ (U : Finset V) :
    finsetOfSubtype (Finset.univ : Finset (U : Set V)) = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hx
    exact hy
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

lemma finsetOfSubtype_union {s : Set V} (A B : Finset s) :
    finsetOfSubtype (A ∪ B) = finsetOfSubtype A ∪ finsetOfSubtype B := by
  simp [finsetOfSubtype, Finset.image_union]

lemma disjoint_finsetOfSubtype {s : Set V} {A B : Finset s} (h : Disjoint A B) :
    Disjoint (finsetOfSubtype A) (finsetOfSubtype B) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxA hxB
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxA
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hxB
  have : a = b := Subtype.ext hba.symm
  subst this
  exact Finset.disjoint_left.1 h ha hb

lemma subset_finsetOfSubtype {s : Set V} (A : Finset s) :
    finsetOfSubtype A ⊆ (s.toFinset) := by
  intro x hx
  obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hx
  simpa [Set.mem_toFinset] using hy

lemma finsetOfSubtype_subset_of_coe (U : Finset V) (A : Finset (U : Set V)) :
    finsetOfSubtype A ⊆ U := by
  intro x hx
  obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hx
  exact hy

/-- Join split transported to an induced connected cograph on a finset. -/
lemma exists_complete_join_on {G : SimpleGraph V} {U : Finset V}
    (hU : IsCograph G U) (hconn : (G.induce (U : Set V)).Connected)
    (hcard : 2 ≤ U.card) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ A ∪ B = U ∧
      G.IsCompleteBetween (A : Set V) (B : Set V) ∧
      A.card < U.card ∧ B.card < U.card := by
  have hCograph : IsCographGraph (G.induce (U : Set V)) :=
    (isCographOn_iff_isCographGraph_induce (s := (U : Set V))).1 hU
  have hcard' : 2 ≤ Fintype.card (U : Set V) := by
    simpa [Fintype.card_coe] using hcard
  obtain ⟨A0, B0, hA0ne, hB0ne, hdisj0, hcover0, hAB0, hA0card, hB0card⟩ :=
    exists_complete_join_of_connected_cograph (G := G.induce (U : Set V))
      hconn hCograph hcard'
  refine ⟨finsetOfSubtype A0, finsetOfSubtype B0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finsetOfSubtype_subset_of_coe U A0
  · exact finsetOfSubtype_subset_of_coe U B0
  · obtain ⟨a, ha⟩ := hA0ne
    exact ⟨a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  · obtain ⟨b, hb⟩ := hB0ne
    exact ⟨b.1, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  · exact disjoint_finsetOfSubtype hdisj0
  · rw [← finsetOfSubtype_union]
    exact (congrArg finsetOfSubtype hcover0).trans (finsetOfSubtype_univ U)
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    have : (G.induce (U : Set V)).Adj a' b' :=
      hAB0 (by exact ha') (by exact hb')
    simpa [induce_adj] using this
  · simpa [card_finsetOfSubtype, Fintype.card_coe] using hA0card
  · simpa [card_finsetOfSubtype, Fintype.card_coe] using hB0card

/-- Disjoint-union split transported to a nonempty disconnected induced subgraph. -/
lemma exists_disjoint_union_on {G : SimpleGraph V} {U : Finset V}
    (hdisc : ¬ (G.induce (U : Set V)).Connected) (hne : U.Nonempty) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ A ∪ B = U ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧
      A.card < U.card ∧ B.card < U.card := by
  haveI : Nonempty (U : Set V) := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨A0, B0, hA0ne, hB0ne, hdisj0, hcover0, hnocross0, hA0card, hB0card⟩ :=
    exists_disjoint_union_of_not_connected (G := G.induce (U : Set V)) hdisc
  refine ⟨finsetOfSubtype A0, finsetOfSubtype B0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finsetOfSubtype_subset_of_coe U A0
  · exact finsetOfSubtype_subset_of_coe U B0
  · obtain ⟨a, ha⟩ := hA0ne
    exact ⟨a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  · obtain ⟨b, hb⟩ := hB0ne
    exact ⟨b.1, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  · exact disjoint_finsetOfSubtype hdisj0
  · rw [← finsetOfSubtype_union]
    exact (congrArg finsetOfSubtype hcover0).trans (finsetOfSubtype_univ U)
  · intro a ha b hb hadj
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    have : (G.induce (U : Set V)).Adj a' b' := by simpa [induce_adj] using hadj
    exact hnocross0 a' ha' b' hb' this
  · simpa [card_finsetOfSubtype, Fintype.card_coe] using hA0card
  · simpa [card_finsetOfSubtype, Fintype.card_coe] using hB0card

end Cograph
end Nikoghosyan
