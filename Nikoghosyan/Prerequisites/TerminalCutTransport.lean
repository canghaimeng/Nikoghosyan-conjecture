/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalNeighbor

/-!
# Original-host cut transport: `c(G-S) = 1 + z_B(K-S)`

For `AllCographSides G` and `S ⊆ K = B ∪ W`, the remainder
`univ \ S` is `A ∪ U ∪ (K \ S)`. The complete join `A–U` keeps
`A ∪ U` connected. Every `K \ S` component that meets surviving
`B \ S` joins this blob by an actual `A–B` edge. Every `B`-free
`K \ S` component lies in `W`, is anticomplete to `A ∪ U`, and
remains a component of `G-S`. This yields an actual bijection
`c(G-S) = 1 + z_B(K-S)`.

OneTough of the original `G` then gives `TerminalHypothesis` on `K`:
the empty cut has `z = 0`, and every nonempty `S ⊆ K` has
`z ≤ |S| - 1`, including the `z = 0` and one-component cases.
No induced-pair toughness or component-count monotonicity is used.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace AllCographSides

variable (P : AllCographSides G)

lemma mem_A_not_mem_K {x : V} (hx : x ∈ P.A) : x ∉ P.B ∪ P.W :=
  disjoint_left.1 P.disjoint_A_K hx

lemma mem_U_not_mem_K {x : V} (hx : x ∈ P.U) : x ∉ P.B ∪ P.W :=
  disjoint_left.1 P.disjoint_U_K hx

lemma univ_sdiff_eq {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    univ \ S = P.A ∪ P.U ∪ ((P.B ∪ P.W) \ S) := by
  ext x
  constructor
  · intro hx
    have hxuniv : x ∈ univ := (mem_sdiff.1 hx).1
    have hxS : x ∉ S := (mem_sdiff.1 hx).2
    have hxAll : x ∈ P.A ∪ P.B ∪ P.U ∪ P.W := P.hcover ▸ hxuniv
    rcases mem_union.1 hxAll with hABU | hW
    · rcases mem_union.1 hABU with hAB | hU
      · rcases mem_union.1 hAB with hA | hB
        · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl hA)))
        · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨mem_union.2 (Or.inl hB), hxS⟩))
      · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr hU)))
    · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨mem_union.2 (Or.inr hW), hxS⟩))
  · intro hx
    refine mem_sdiff.2 ⟨mem_univ x, ?_⟩
    intro hS'
    rcases mem_union.1 hx with hAU | hK
    · rcases mem_union.1 hAU with hA | hU
      · exact (disjoint_left.1 P.disjoint_A_K hA (hS hS')).elim
      · exact (disjoint_left.1 P.disjoint_U_K hU (hS hS')).elim
    · exact (mem_sdiff.1 hK).2 hS'

lemma subset_AU_union_Ksdiff {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    P.A ∪ P.U ⊆ univ \ S := by
  intro x hx
  rw [P.univ_sdiff_eq hS]
  exact mem_union.2 (Or.inl hx)

lemma connected_AU :
    (G.induce ((P.A ∪ P.U : Finset V) : Set V)).Connected :=
  Cograph.induce_connected_of_completeJoin P.A_nonempty P.hUne P.hAU

lemma reachable_AU {x y : V} (hx : x ∈ P.A ∪ P.U) (hy : y ∈ P.A ∪ P.U) :
    (G.induce ((P.A ∪ P.U : Finset V) : Set V)).Reachable
      ⟨x, hx⟩ ⟨y, hy⟩ :=
  P.connected_AU.preconnected ⟨x, hx⟩ ⟨y, hy⟩

/-- Surviving `B` vertices attach to `A` by original complete-join edges. -/
lemma adj_A_surviving_B {S : Finset V} {a b : V}
    (ha : a ∈ P.A) (hb : b ∈ P.B) (hbS : b ∉ S) : G.Adj a b :=
  P.hAB ha hb

lemma W_anti_AU {w x : V} (hw : w ∈ P.W) (hx : x ∈ P.A ∪ P.U) : ¬ G.Adj w x := by
  rcases mem_union.1 hx with hA | hU
  · exact P.hWantiA w hw x hA
  · exact fun h => P.hUantiW x hU w hw h.symm

/-- `A ∪ U` remains connected after deleting any `S ⊆ K`. -/
lemma connected_AU_in_remainder {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    (G.induce ((P.A ∪ P.U : Finset V) : Set V)).Connected :=
  P.connected_AU

def induceIncl_AU_remainder {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    G.induce ((P.A ∪ P.U : Finset V) : Set V) →g
      G.induce ((univ \ S : Finset V) : Set V) :=
  induceIncl G (P.subset_AU_union_Ksdiff hS)

def induceIncl_Ksdiff_remainder {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V) →g
      G.induce ((univ \ S : Finset V) : Set V) :=
  induceIncl G (by
    intro x hx
    rw [P.univ_sdiff_eq hS]
    exact mem_union.2 (Or.inr hx))

/-- The mixed remainder component: the component of a vertex of `A`. -/
noncomputable def mixedComponent {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    (G.induce ((univ \ S : Finset V) : Set V)).ConnectedComponent :=
  let a := P.A_nonempty.choose
  let ha : a ∈ univ \ S :=
    P.subset_AU_union_Ksdiff hS (mem_union.2 (Or.inl P.A_nonempty.choose_spec))
  (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk ⟨a, ha⟩

lemma mem_mixedComponent_of_AU {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    {x : V} (hx : x ∈ P.A ∪ P.U) :
    (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
        ⟨x, P.subset_AU_union_Ksdiff hS hx⟩ =
      P.mixedComponent hS := by
  let a := P.A_nonempty.choose
  have haAU : a ∈ P.A ∪ P.U := mem_union.2 (Or.inl P.A_nonempty.choose_spec)
  have hxEq : (P.induceIncl_AU_remainder hS) ⟨x, hx⟩ =
      ⟨x, P.subset_AU_union_Ksdiff hS hx⟩ := Subtype.ext rfl
  have haEq : (P.induceIncl_AU_remainder hS) ⟨a, haAU⟩ =
      ⟨a, P.subset_AU_union_Ksdiff hS haAU⟩ := Subtype.ext rfl
  have hR := (P.reachable_AU hx haAU).map (P.induceIncl_AU_remainder hS)
  apply ConnectedComponent.sound
  rw [← hxEq, ← haEq]
  exact hR

lemma mem_mixedComponent_of_surviving_B {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    {b : V} (hb : b ∈ P.B) (hbS : b ∉ S) :
    (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
        ⟨b, by
          rw [P.univ_sdiff_eq hS]
          exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨mem_union.2 (Or.inl hb), hbS⟩))⟩ =
      P.mixedComponent hS := by
  obtain ⟨a, ha⟩ := P.A_nonempty
  have haRem : a ∈ univ \ S :=
    P.subset_AU_union_Ksdiff hS (mem_union.2 (Or.inl ha))
  have hbRem : b ∈ univ \ S := by
    rw [P.univ_sdiff_eq hS]
    exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨mem_union.2 (Or.inl hb), hbS⟩))
  have hadj : (G.induce ((univ \ S : Finset V) : Set V)).Adj
      ⟨b, hbRem⟩ ⟨a, haRem⟩ := by
    simpa [induce_adj] using (P.hAB ha hb).symm
  have hA : (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
      ⟨a, haRem⟩ = P.mixedComponent hS :=
    P.mem_mixedComponent_of_AU hS (mem_union.2 (Or.inl ha))
  convert (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hA

lemma mem_remainder_of_Ksdiff {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    {x : V} (hx : x ∈ (P.B ∪ P.W) \ S) : x ∈ univ \ S := by
  rw [P.univ_sdiff_eq hS]
  exact mem_union.2 (Or.inr hx)

lemma not_mem_Ksdiff_of_AU {S : Finset V} {x : V}
    (hx : x ∈ P.A ∪ P.U) : x ∉ (P.B ∪ P.W) \ S := by
  intro hxK
  have hxK' : x ∈ P.B ∪ P.W := (mem_sdiff.1 hxK).1
  rcases mem_union.1 hx with hA | hU
  · exact (disjoint_left.1 P.disjoint_A_K hA hxK').elim
  · exact (disjoint_left.1 P.disjoint_U_K hU hxK').elim

/-- B-free remainder components of `K \ S` live in `W`. -/
lemma free_component_subset_W {S : Finset V}
    {C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent}
    (hC : IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C) :
    componentFinset G ((P.B ∪ P.W) \ S) C ⊆ P.W := by
  intro x hx
  have hxKS : x ∈ (P.B ∪ P.W) \ S := (mem_filter.1 hx).1
  have hxK : x ∈ P.B ∪ P.W := (mem_sdiff.1 hxKS).1
  have hxS : x ∉ S := (mem_sdiff.1 hxKS).2
  have hxB : x ∉ P.B := by
    intro hB
    have : x ∈ componentFinset G ((P.B ∪ P.W) \ S) C ∩ (P.B \ S) :=
      mem_inter.2 ⟨hx, mem_sdiff.2 ⟨hB, hxS⟩⟩
    rw [hC] at this
    exact absurd this (notMem_empty x)
  rcases mem_union.1 hxK with hB | hW
  · exact (hxB hB).elim
  · exact hW

lemma not_adj_free_AU {S : Finset V}
    {C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent}
    (hC : IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C)
    {x y : V} (hx : x ∈ componentFinset G ((P.B ∪ P.W) \ S) C)
    (hy : y ∈ P.A ∪ P.U) : ¬ G.Adj x y :=
  P.W_anti_AU (P.free_component_subset_W hC hx) hy

lemma adj_mem_componentFinset {U : Finset V}
    {C : (G.induce (U : Set V)).ConnectedComponent} {x y : V}
    (hx : x ∈ componentFinset G U C) (hy : y ∈ U) (hadj : G.Adj x y) :
    y ∈ componentFinset G U C := by
  have hxU : x ∈ U := (mem_filter.1 hx).1
  obtain ⟨_, hxC⟩ := (mem_filter.1 hx).2
  have hadj' : (G.induce (U : Set V)).Adj ⟨x, hxU⟩ ⟨y, hy⟩ := by
    simpa [induce_adj] using hadj
  have hyC :
      (G.induce (U : Set V)).connectedComponentMk ⟨y, hy⟩ = C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hadj').symm.trans hxC
  exact mem_filter.2 ⟨hy, ⟨hy, hyC⟩⟩

/-- A walk in `G-S` that starts in a B-free `K \ S` component stays there. -/
lemma free_walk_stays {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    {C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent}
    (hC : IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C)
    {x y : ((univ \ S : Finset V) : Set V)}
    (hx : x.val ∈ componentFinset G ((P.B ∪ P.W) \ S) C)
    (p : (G.induce ((univ \ S : Finset V) : Set V)).Walk x y) :
    y.val ∈ componentFinset G ((P.B ∪ P.W) \ S) C := by
  revert hx
  induction p with
  | nil =>
    intro hx
    exact hx
  | @cons u v w hadj q ih =>
    intro hx
    have hadjG : G.Adj u.val v.val := by simpa [induce_adj] using hadj
    have hv' : v.val ∈ P.A ∪ P.U ∪ ((P.B ∪ P.W) \ S) :=
      (P.univ_sdiff_eq hS) ▸ v.property
    have hvKS : v.val ∈ (P.B ∪ P.W) \ S := by
      rcases mem_union.1 hv' with hAU | hKS
      · exact (P.not_adj_free_AU hC hx hAU hadjG).elim
      · exact hKS
    have hvC :=
      adj_mem_componentFinset (G := G) (U := (P.B ∪ P.W) \ S) hx hvKS hadjG
    exact ih hvC

lemma free_reachable_stays {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    {C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent}
    (hC : IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C)
    {x y : ((univ \ S : Finset V) : Set V)}
    (hx : x.val ∈ componentFinset G ((P.B ∪ P.W) \ S) C)
    (hR : (G.induce ((univ \ S : Finset V) : Set V)).Reachable x y) :
    y.val ∈ componentFinset G ((P.B ∪ P.W) \ S) C :=
  P.free_walk_stays hS hC hx (Classical.choice hR)

lemma exists_mem_connectedComponent {U : Finset V}
    (C : (G.induce (U : Set V)).ConnectedComponent) :
    ∃ (x : V) (hx : x ∈ U),
      (G.induce (U : Set V)).connectedComponentMk ⟨x, hx⟩ = C :=
  C.ind fun z => ⟨z.1, z.2, rfl⟩

lemma mem_componentFinset_mk {U : Finset V} {x : V} (hx : x ∈ U) :
    x ∈ componentFinset G U
      ((G.induce (U : Set V)).connectedComponentMk ⟨x, hx⟩) :=
  mem_filter.2 ⟨hx, ⟨hx, rfl⟩⟩

lemma connectedComponentMk_eq_of_mem_componentFinset {U : Finset V}
    {C : (G.induce (U : Set V)).ConnectedComponent} {x : V}
    (hx : x ∈ componentFinset G U C) :
    (G.induce (U : Set V)).connectedComponentMk ⟨x, (mem_filter.1 hx).1⟩ = C := by
  obtain ⟨_, hC⟩ := (mem_filter.1 hx).2
  exact hC

/-- A non-free `K \ S` component meets surviving `B` and joins the mixed blob. -/
lemma mem_mixedComponent_of_not_free {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    {x : V} (hx : x ∈ (P.B ∪ P.W) \ S)
    (hnot : ¬ IsFreeComponent (G := G) (P.B ∪ P.W) P.B S
      ((G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).connectedComponentMk
        ⟨x, hx⟩)) :
    (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
        ⟨x, P.mem_remainder_of_Ksdiff hS hx⟩ =
      P.mixedComponent hS := by
  set C :=
    (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).connectedComponentMk
      ⟨x, hx⟩
  have hne : (componentFinset G ((P.B ∪ P.W) \ S) C ∩ (P.B \ S)).Nonempty :=
    nonempty_iff_ne_empty.2 hnot
  obtain ⟨b, hbint⟩ := hne
  have hbC : b ∈ componentFinset G ((P.B ∪ P.W) \ S) C := (mem_inter.1 hbint).1
  have hbB : b ∈ P.B \ S := (mem_inter.1 hbint).2
  have hbKS : b ∈ (P.B ∪ P.W) \ S := (mem_filter.1 hbC).1
  have hxC : C =
      (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).connectedComponentMk
        ⟨x, hx⟩ := rfl
  have hbMk := connectedComponentMk_eq_of_mem_componentFinset hbC
  have hreachKS :
      (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).Reachable
        ⟨x, hx⟩ ⟨b, hbKS⟩ :=
    ConnectedComponent.eq.mp (hxC ▸ hbMk.symm)
  have hreachRem := hreachKS.map (P.induceIncl_Ksdiff_remainder hS)
  have hbRem : b ∈ univ \ S := P.mem_remainder_of_Ksdiff hS hbKS
  have hxRem : x ∈ univ \ S := P.mem_remainder_of_Ksdiff hS hx
  have hinclx :
      (P.induceIncl_Ksdiff_remainder hS) ⟨x, hx⟩ = ⟨x, hxRem⟩ := Subtype.ext rfl
  have hinclb :
      (P.induceIncl_Ksdiff_remainder hS) ⟨b, hbKS⟩ = ⟨b, hbRem⟩ := Subtype.ext rfl
  have hmx :
      (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
          ⟨x, hxRem⟩ =
        (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
          ⟨b, hbRem⟩ := by
    apply ConnectedComponent.sound
    simpa [hinclx, hinclb] using hreachRem
  have hmb :=
    P.mem_mixedComponent_of_surviving_B hS (mem_sdiff.1 hbB).1 (mem_sdiff.1 hbB).2
  exact hmx.trans hmb

/-- Remainder components of `G-S` are the mixed blob together with the
B-free `K \ S` components. -/
noncomputable def remainderSum {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    Unit ⊕
      { C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent //
        IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C } →
      (G.induce ((univ \ S : Finset V) : Set V)).ConnectedComponent
  | .inl _ => P.mixedComponent hS
  | .inr C => C.1.map (P.induceIncl_Ksdiff_remainder hS)

lemma remainderSum_inl {S : Finset V} (hS : S ⊆ P.B ∪ P.W) (u : Unit) :
    P.remainderSum hS (.inl u) = P.mixedComponent hS :=
  rfl

lemma remainderSum_inr {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    (C : { C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent //
      IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C }) :
    P.remainderSum hS (.inr C) =
      C.1.map (P.induceIncl_Ksdiff_remainder hS) :=
  rfl

lemma map_free_eq_mk {S : Finset V} (hS : S ⊆ P.B ∪ P.W)
    {C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent}
    {x : V} (hxKS : x ∈ (P.B ∪ P.W) \ S)
    (hxC : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).connectedComponentMk
        ⟨x, hxKS⟩ = C) :
    C.map (P.induceIncl_Ksdiff_remainder hS) =
      (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
        ⟨x, P.mem_remainder_of_Ksdiff hS hxKS⟩ := by
  subst hxC
  rw [ConnectedComponent.map_mk]
  rfl

lemma mem_componentFinset_of_eq {S : Finset V}
    {C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent}
    {x : V} (hxKS : x ∈ (P.B ∪ P.W) \ S)
    (hxC : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).connectedComponentMk
        ⟨x, hxKS⟩ = C) :
    x ∈ componentFinset G ((P.B ∪ P.W) \ S) C := by
  simpa [hxC] using (mem_componentFinset_mk (G := G) hxKS)

lemma remainderSum_bijective {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    Function.Bijective (P.remainderSum hS) := by
  refine ⟨?inj, ?surj⟩
  · intro a b hab
    match a, b with
    | .inl _, .inl _ =>
      rfl
    | .inr C, .inr D =>
      have hmap : C.1.map (P.induceIncl_Ksdiff_remainder hS) =
          D.1.map (P.induceIncl_Ksdiff_remainder hS) := by
        simpa [P.remainderSum_inr hS] using hab
      obtain ⟨x, hxKS, hxC⟩ := exists_mem_connectedComponent C.1
      have hxCfin := P.mem_componentFinset_of_eq hxKS hxC
      have hmapC := P.map_free_eq_mk hS hxKS hxC
      obtain ⟨y, hyKS, hyD⟩ := exists_mem_connectedComponent D.1
      have hyCfin := P.mem_componentFinset_of_eq hyKS hyD
      have hmapD := P.map_free_eq_mk hS hyKS hyD
      have hR :
          (G.induce ((univ \ S : Finset V) : Set V)).Reachable
            ⟨x, P.mem_remainder_of_Ksdiff hS hxKS⟩
            ⟨y, P.mem_remainder_of_Ksdiff hS hyKS⟩ :=
        ConnectedComponent.eq.mp (hmapC.symm.trans (hmap.trans hmapD))
      have hyC : y ∈ componentFinset G ((P.B ∪ P.W) \ S) C.1 :=
        P.free_reachable_stays hS C.2 hxCfin hR
      have hCD : C.1 = D.1 :=
        (connectedComponentMk_eq_of_mem_componentFinset hyC).symm.trans
          (connectedComponentMk_eq_of_mem_componentFinset hyCfin)
      exact congrArg Sum.inr (Subtype.ext hCD)
    | .inl _, .inr C =>
      exfalso
      obtain ⟨x, hxKS, hxC⟩ := exists_mem_connectedComponent C.1
      have hxCfin := P.mem_componentFinset_of_eq hxKS hxC
      have hmapC := P.map_free_eq_mk hS hxKS hxC
      obtain ⟨a, ha⟩ := P.A_nonempty
      have haAU : a ∈ P.A ∪ P.U := mem_union.2 (Or.inl ha)
      have haRem : a ∈ univ \ S := P.subset_AU_union_Ksdiff hS haAU
      have hmixed :
          P.mixedComponent hS =
            (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
              ⟨a, haRem⟩ :=
        (P.mem_mixedComponent_of_AU hS haAU).symm
      have heq : P.mixedComponent hS =
          C.1.map (P.induceIncl_Ksdiff_remainder hS) := by
        simpa [P.remainderSum_inl hS, P.remainderSum_inr hS] using hab
      have hR :
          (G.induce ((univ \ S : Finset V) : Set V)).Reachable
            ⟨x, P.mem_remainder_of_Ksdiff hS hxKS⟩ ⟨a, haRem⟩ :=
        ConnectedComponent.eq.mp (hmapC.symm.trans (heq.symm.trans hmixed))
      have haC : a ∈ componentFinset G ((P.B ∪ P.W) \ S) C.1 :=
        P.free_reachable_stays hS C.2 hxCfin hR
      exact P.not_mem_Ksdiff_of_AU haAU (mem_filter.1 haC).1
    | .inr C, .inl _ =>
      exfalso
      obtain ⟨x, hxKS, hxC⟩ := exists_mem_connectedComponent C.1
      have hxCfin := P.mem_componentFinset_of_eq hxKS hxC
      have hmapC := P.map_free_eq_mk hS hxKS hxC
      obtain ⟨a, ha⟩ := P.A_nonempty
      have haAU : a ∈ P.A ∪ P.U := mem_union.2 (Or.inl ha)
      have haRem : a ∈ univ \ S := P.subset_AU_union_Ksdiff hS haAU
      have hmixed :
          P.mixedComponent hS =
            (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
              ⟨a, haRem⟩ :=
        (P.mem_mixedComponent_of_AU hS haAU).symm
      have heq : C.1.map (P.induceIncl_Ksdiff_remainder hS) =
          P.mixedComponent hS := by
        simpa [P.remainderSum_inl hS, P.remainderSum_inr hS] using hab
      have hR :
          (G.induce ((univ \ S : Finset V) : Set V)).Reachable
            ⟨x, P.mem_remainder_of_Ksdiff hS hxKS⟩ ⟨a, haRem⟩ :=
        ConnectedComponent.eq.mp (hmapC.symm.trans (heq.trans hmixed))
      have haC : a ∈ componentFinset G ((P.B ∪ P.W) \ S) C.1 :=
        P.free_reachable_stays hS C.2 hxCfin hR
      exact P.not_mem_Ksdiff_of_AU haAU (mem_filter.1 haC).1
  · intro D
    refine D.ind fun x => ?_
    have hx' : x.val ∈ P.A ∪ P.U ∪ ((P.B ∪ P.W) \ S) :=
      (P.univ_sdiff_eq hS) ▸ x.property
    rcases mem_union.1 hx' with hAU | hKS
    · refine ⟨Sum.inl (), ?_⟩
      change P.mixedComponent hS =
        (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk x
      have hxeq : x = ⟨x.val, P.subset_AU_union_Ksdiff hS hAU⟩ := Subtype.ext rfl
      exact hxeq ▸ (P.mem_mixedComponent_of_AU hS hAU).symm
    · set C :=
        (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).connectedComponentMk
          ⟨x.val, hKS⟩
      by_cases hfree : IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C
      · refine ⟨Sum.inr ⟨C, hfree⟩, ?_⟩
        change C.map (P.induceIncl_Ksdiff_remainder hS) =
          (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk x
        have hxRem : x.val ∈ univ \ S := P.mem_remainder_of_Ksdiff hS hKS
        have hxeq : x = ⟨x.val, hxRem⟩ := Subtype.ext rfl
        have hmap :
            C.map (P.induceIncl_Ksdiff_remainder hS) =
              (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk
                ⟨x.val, hxRem⟩ := by
          rw [ConnectedComponent.map_mk]
          rfl
        exact hxeq ▸ hmap
      · refine ⟨Sum.inl (), ?_⟩
        change P.mixedComponent hS =
          (G.induce ((univ \ S : Finset V) : Set V)).connectedComponentMk x
        have hxRem : x.val ∈ univ \ S := P.mem_remainder_of_Ksdiff hS hKS
        have hxeq : x = ⟨x.val, hxRem⟩ := Subtype.ext rfl
        exact hxeq ▸ (P.mem_mixedComponent_of_not_free hS hKS hfree).symm

noncomputable def remainderComponentEquiv {S : Finset V}
    (hS : S ⊆ P.B ∪ P.W) :
    (G.induce ((univ \ S : Finset V) : Set V)).ConnectedComponent ≃
      Unit ⊕
        { C : (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent //
          IsFreeComponent (G := G) (P.B ∪ P.W) P.B S C } :=
  (Equiv.ofBijective (P.remainderSum hS) (P.remainderSum_bijective hS)).symm

/-- Actual host identity: `c(G-S) = 1 + z_B(K-S)` for every `S ⊆ K`. -/
lemma componentCount_remainder_eq {S : Finset V} (hS : S ⊆ P.B ∪ P.W) :
    componentCount G (univ \ S) =
      1 + terminalComponentCount (G := G) (P.B ∪ P.W) P.B S := by
  haveI : Fintype
      (G.induce ((univ \ S : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  haveI : Fintype
      (G.induce (((P.B ∪ P.W) \ S : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  have hcard := Nat.card_congr (P.remainderComponentEquiv hS)
  have hunit : Nat.card Unit = 1 := Nat.card_unique
  simpa [componentCount, terminalComponentCount, Nat.card_sum, hunit,
    Nat.add_comm] using hcard

lemma componentCount_univ_of_connected [Nonempty V] (h : G.Connected) :
    componentCount G univ = 1 := by
  have hss : Subsingleton G.ConnectedComponent :=
    h.preconnected.subsingleton_connectedComponent
  have hne : Nonempty G.ConnectedComponent := inferInstance
  have : Nat.card G.ConnectedComponent = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨hss, hne⟩
  rw [componentCount_univ, this]

/-- Original 1-toughness of `G` yields the strict terminal cut hypothesis
on `K = B ∪ W`. The empty cut has `z = 0`. A nonempty cut with `z = 0`
is numerically trivial. Positive `z` produces at least two actual
remainder components, so the conditional tough bound applies. -/
lemma terminalHypothesis_of_oneTough (htough : OneTough G) :
    TerminalHypothesis (G := G) (P.B ∪ P.W) P.B := by
  haveI : Nonempty V := ⟨P.A_nonempty.choose⟩
  refine ⟨?empty, ?cut⟩
  · have hconn := OneTough.connected (G := G) htough
    have hc1 : componentCount G univ = 1 :=
      componentCount_univ_of_connected hconn
    have hid := P.componentCount_remainder_eq (S := ∅) (empty_subset _)
    have : 1 + terminalComponentCount (G := G) (P.B ∪ P.W) P.B ∅ = 1 := by
      rw [← hid, sdiff_empty, hc1]
    exact (Nat.add_eq_left.mp this)
  · intro S hS hSne
    have hid := P.componentCount_remainder_eq hS
    by_cases hz : terminalComponentCount (G := G) (P.B ∪ P.W) P.B S = 0
    · have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.mpr hSne)
      omega
    · have hzpos : 1 ≤ terminalComponentCount (G := G) (P.B ∪ P.W) P.B S :=
        Nat.pos_of_ne_zero hz
      have h2 : 2 ≤ componentCount G (univ \ S) := by omega
      have ht := htough S h2
      omega

lemma repairedTerminalHypothesis_of_oneTough
    (hpat : NoInducedP4UnionP1 G) (htough : OneTough G) :
    RepairedTerminalHypothesis (G := G) (P.B ∪ P.W) P.B :=
  repairedTerminalHypothesis_of_sides P hpat (P.terminalHypothesis_of_oneTough htough)

end AllCographSides

end Nikoghosyan
