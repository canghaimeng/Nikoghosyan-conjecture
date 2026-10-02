/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalFeasibility
import Nikoghosyan.Cograph.PartCuts

/-!
# Actual mixed reduction: child carrier `B ∩ D`

If `K \ B` is nonempty and `z_B(K) = 0`, a walk from a nonterminal to a
surviving terminal supplies a real `B`–`(K \ B)` edge. NeighborCondition
places every nonterminal in that one induced component `D`. The complement
`I = K \ D` lies in `B`. The child terminal set is `Bd = B ∩ D`, never
the original `B` (which is not a subset of `D` when `I` is nonempty).

Cuts of `D` transport: for `S ⊆ D`, `K \ S` is the no-cross union of
`D \ S` with the intact terminal singletons `I`, so
`z_B(K-S) = z_Bd(D-S)`, including the empty and all-`D` cuts. Strict
`TerminalHypothesis` on `(D, Bd)` is therefore inherited from `(K, B)`.

When `p(D) = 1`, the checked traceable base on `(D, Bd)` plus the
singleton cover of `I` is a real minimum `B`-ended cover of `K`, even if
`p(K) > 1` from isolated terminals.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Component support of an induced component -/

lemma componentFinset_subset {U : Finset V}
    (C : (G.induce (U : Set V)).ConnectedComponent) :
    componentFinset G U C ⊆ U :=
  filter_subset _ _

lemma mem_componentFinset_self {U : Finset V} {x : V} (hx : x ∈ U) :
    x ∈ componentFinset G U
      ((G.induce (U : Set V)).connectedComponentMk ⟨x, hx⟩) :=
  mem_filter.2 ⟨hx, ⟨hx, rfl⟩⟩

lemma componentFinset_nonempty {U : Finset V}
    (C : (G.induce (U : Set V)).ConnectedComponent) :
    (componentFinset G U C).Nonempty :=
  C.ind fun z => ⟨z.1, mem_filter.2 ⟨z.2, ⟨z.2, rfl⟩⟩⟩

lemma induce_walk_mem_componentFinset {U : Finset V}
    {C : (G.induce (U : Set V)).ConnectedComponent}
    {x y : ((U : Set V))}
    (p : (G.induce (U : Set V)).Walk x y)
    (hx : x.val ∈ componentFinset G U C) :
    y.val ∈ componentFinset G U C := by
  cases p with
  | nil => exact hx
  | cons hadj q =>
      rename_i mid
      have hadjG : G.Adj x.val mid.val := by simpa [induce_adj] using hadj
      have hmid := adj_mem_componentFinset' (G := G) hx mid.property hadjG
      exact induce_walk_mem_componentFinset q hmid

lemma induce_reachable_of_mem_componentFinset_walk {U : Finset V}
    {C : (G.induce (U : Set V)).ConnectedComponent}
    {x y : ((U : Set V))}
    (hxD : x.val ∈ componentFinset G U C)
    (hyD : y.val ∈ componentFinset G U C)
    (p : (G.induce (U : Set V)).Walk x y) :
    (G.induce (componentFinset G U C : Set V)).Reachable
      ⟨x.val, hxD⟩ ⟨y.val, hyD⟩ := by
  cases p with
  | nil => exact Reachable.rfl
  | cons hadj q =>
      rename_i mid
      have hadjG : G.Adj x.val mid.val := by simpa [induce_adj] using hadj
      have hmidD := adj_mem_componentFinset' (G := G) hxD mid.property hadjG
      have hfirst :
          (G.induce (componentFinset G U C : Set V)).Adj
            ⟨x.val, hxD⟩ ⟨mid.val, hmidD⟩ := by
        simpa [induce_adj] using hadjG
      exact (Adj.reachable hfirst).trans
        (induce_reachable_of_mem_componentFinset_walk hmidD hyD q)

lemma connected_componentFinset {U : Finset V}
    (C : (G.induce (U : Set V)).ConnectedComponent) :
    (G.induce (componentFinset G U C : Set V)).Connected := by
  let D := componentFinset G U C
  have hDne : D.Nonempty := componentFinset_nonempty (G := G) C
  have hpre : (G.induce (D : Set V)).Preconnected := by
    intro x y
    have hxU : x.val ∈ U := (componentFinset_subset (G := G) C) x.property
    have hyU : y.val ∈ U := (componentFinset_subset (G := G) C) y.property
    have hxC :=
      connectedComponentMk_eq_of_mem_componentFinset' (G := G) x.property
    have hyC :=
      connectedComponentMk_eq_of_mem_componentFinset' (G := G) y.property
    have hreach :
        (G.induce (U : Set V)).Reachable ⟨x.val, hxU⟩ ⟨y.val, hyU⟩ :=
      ConnectedComponent.exact (hxC.trans hyC.symm)
    exact induce_reachable_of_mem_componentFinset_walk
      (G := G) x.property y.property (Classical.choice hreach)
  obtain ⟨x, hx⟩ := hDne
  exact (connected_iff _).2 ⟨hpre, ⟨⟨x, hx⟩⟩⟩

/-! ### Empty-cut free count -/

lemma not_free_of_terminalComponentCount_empty {K B : Finset V}
    (hz : terminalComponentCount (G := G) K B ∅ = 0)
    (C : (G.induce ((K \ (∅ : Finset V) : Finset V) : Set V)).ConnectedComponent) :
    ¬ IsFreeComponent (G := G) K B ∅ C := by
  haveI : Fintype
      { C : (G.induce ((K \ (∅ : Finset V) : Finset V) : Set V)).ConnectedComponent //
        IsFreeComponent (G := G) K B ∅ C } := inferInstance
  have hcard : Fintype.card
      { C : (G.induce ((K \ (∅ : Finset V) : Finset V) : Set V)).ConnectedComponent //
        IsFreeComponent (G := G) K B ∅ C } = 0 := by
    simpa [terminalComponentCount, Nat.card_eq_fintype_card] using hz
  have hE : IsEmpty
      { C : (G.induce ((K \ (∅ : Finset V) : Finset V) : Set V)).ConnectedComponent //
        IsFreeComponent (G := G) K B ∅ C } :=
    Fintype.card_eq_zero_iff.1 hcard
  intro hC
  exact hE.false ⟨C, hC⟩

/-! ### A nonterminal–terminal walk supplies a `B`–`V` edge -/

lemma exists_BV_edge_of_induce_walk {K B : Finset V}
    {x y : ((K : Set V))}
    (p : (G.induce (K : Set V)).Walk x y)
    (hxB : x.val ∉ B) (hyB : y.val ∈ B) :
    ∃ b v, b ∈ B ∧ v ∈ K \ B ∧ G.Adj b v := by
  cases p with
  | nil => exact (hxB hyB).elim
  | cons hadj q =>
      rename_i mid
      by_cases hm : mid.val ∈ B
      · refine ⟨mid.val, x.val, hm, mem_sdiff.2 ⟨x.property, hxB⟩, ?_⟩
        simpa [induce_adj] using hadj.symm
      · exact exists_BV_edge_of_induce_walk q hm hyB

lemma exists_BV_edge_of_z_zero {K B : Finset V}
    (hBK : B ⊆ K) (hz : terminalComponentCount (G := G) K B ∅ = 0)
    {v : V} (hv : v ∈ K \ B) :
    ∃ b w, b ∈ B ∧ w ∈ K \ B ∧ G.Adj b w := by
  have hvK : v ∈ K := (mem_sdiff.1 hv).1
  have hvB : v ∉ B := (mem_sdiff.1 hv).2
  have hvKS : v ∈ K \ (∅ : Finset V) := by simp [hvK]
  let C := (G.induce ((K \ (∅ : Finset V) : Finset V) : Set V)).connectedComponentMk
    ⟨v, hvKS⟩
  have hnot := not_free_of_terminalComponentCount_empty hz C
  obtain ⟨b, hbint⟩ := nonempty_iff_ne_empty.2 hnot
  have hbC : b ∈ componentFinset G (K \ (∅ : Finset V)) C :=
    (mem_inter.1 hbint).1
  have hbB : b ∈ B := by
    have : b ∈ B \ (∅ : Finset V) := (mem_inter.1 hbint).2
    simpa using this
  have hbK : b ∈ K := hBK hbB
  have hbKS : b ∈ K \ (∅ : Finset V) := by simp [hbK]
  have hvMk :
      (G.induce ((K \ (∅ : Finset V) : Finset V) : Set V)).connectedComponentMk
        ⟨v, hvKS⟩ = C := rfl
  have hbMk :=
    connectedComponentMk_eq_of_mem_componentFinset' (G := G) hbC
  have hreach0 :
      (G.induce ((K \ (∅ : Finset V) : Finset V) : Set V)).Reachable
        ⟨v, hvKS⟩ ⟨b, hbKS⟩ :=
    ConnectedComponent.exact (hvMk.trans hbMk.symm)
  have hsub : K \ (∅ : Finset V) ⊆ K := sdiff_subset
  have hreach :
      (G.induce (K : Set V)).Reachable ⟨v, hvK⟩ ⟨b, hbK⟩ :=
    hreach0.map (induceIncl G hsub)
  exact exists_BV_edge_of_induce_walk (Classical.choice hreach) hvB hbB

/-! ### Mixed split data -/

/-- The unique mixed component of a `B`–`(K \ B)` edge, together with the
terminal-singleton complement. Child terminals are `B ∩ D`. -/
structure MixedSplit (K B : Finset V) where
  D : Finset V
  I : Finset V
  hDU : D ∪ I = K
  hdisj : Disjoint D I
  hI : I ⊆ B
  hV : K \ B ⊆ D
  hDsub : D ⊆ K
  hnonterm : (D \ B).Nonempty
  hBd : (B ∩ D).Nonempty
  hconn : (G.induce (D : Set V)).Connected
  hnocross : ∀ a ∈ D, ∀ b ∈ I, ¬ G.Adj a b

namespace MixedSplit

variable {K B : Finset V} (s : MixedSplit (G := G) K B)

lemma I_eq : s.I = K \ s.D := by
  ext x
  constructor
  · intro hx
    have hxK : x ∈ K := by
      have : x ∈ s.D ∪ s.I := mem_union.2 (Or.inr hx)
      rwa [s.hDU] at this
    exact mem_sdiff.2 ⟨hxK, fun hD => Finset.disjoint_left.1 s.hdisj hD hx⟩
  · intro hx
    have hxK : x ∈ K := (mem_sdiff.1 hx).1
    have hxD : x ∉ s.D := (mem_sdiff.1 hx).2
    have hxDI : x ∈ s.D ∪ s.I := by
      rw [s.hDU]
      exact hxK
    rcases mem_union.1 hxDI with hD | hI
    · exact (hxD hD).elim
    · exact hI

lemma D_sdiff_Bd : s.D \ (B ∩ s.D) = s.D \ B := by
  ext x
  constructor
  · intro hx
    have hxD := (mem_sdiff.1 hx).1
    have hxBd := (mem_sdiff.1 hx).2
    exact mem_sdiff.2 ⟨hxD, fun hB => hxBd (mem_inter.2 ⟨hB, hxD⟩)⟩
  · intro hx
    have hxD := (mem_sdiff.1 hx).1
    have hxB := (mem_sdiff.1 hx).2
    exact mem_sdiff.2 ⟨hxD, fun hBd => hxB (mem_inter.1 hBd).1⟩

lemma two_le_card_D : 2 ≤ s.D.card := by
  obtain ⟨b, hb⟩ := s.hBd
  obtain ⟨v, hv⟩ := s.hnonterm
  have hbD : b ∈ s.D := (mem_inter.1 hb).2
  have hbB : b ∈ B := (mem_inter.1 hb).1
  have hvD : v ∈ s.D := (mem_sdiff.1 hv).1
  have hvB : v ∉ B := (mem_sdiff.1 hv).2
  have hne : b ≠ v := fun h => hvB (h ▸ hbB)
  have hpair : ({b, v} : Finset V) ⊆ s.D :=
    insert_subset hbD (singleton_subset_iff.2 hvD)
  have hcard2 : ({b, v} : Finset V).card = 2 := by
    rw [card_insert_of_notMem, card_singleton]
    simp [mem_singleton, hne]
  exact hcard2.symm.le.trans (card_le_card hpair)

end MixedSplit

lemma exists_mixedSplit {K B : Finset V}
    (hBK : B ⊆ K) (hN : NeighborCondition (G := G) K B)
    (hz : terminalComponentCount (G := G) K B ∅ = 0)
    (hVne : (K \ B).Nonempty) :
    Nonempty (MixedSplit (G := G) K B) := by
  obtain ⟨v0, hv0⟩ := hVne
  obtain ⟨b, w, hb, hw, hadj⟩ :=
    exists_BV_edge_of_z_zero (G := G) hBK hz hv0
  have hwK : w ∈ K := (mem_sdiff.1 hw).1
  let C := (G.induce (K : Set V)).connectedComponentMk ⟨w, hwK⟩
  let D := componentFinset G K C
  let I := K \ D
  have hDsub : D ⊆ K := componentFinset_subset (G := G) C
  have hDU : D ∪ I = K := union_sdiff_of_subset hDsub
  have hdisj : Disjoint D I := disjoint_sdiff
  have hV : K \ B ⊆ D := sdiff_subset_mixed_component hN hBK hb hw hadj
  have hI : I ⊆ B := sdiff_mixed_component_subset_B hN hBK hb hw hadj
  have hbD : b ∈ D :=
    mem_componentFinset_of_adj_B (G := G) (hBK hb) hwK hadj
  have hBd : (B ∩ D).Nonempty := ⟨b, mem_inter.2 ⟨hb, hbD⟩⟩
  have hwD : w ∈ D := mem_componentFinset_self (G := G) hwK
  have hnonterm : (D \ B).Nonempty :=
    ⟨w, mem_sdiff.2 ⟨hwD, (mem_sdiff.1 hw).2⟩⟩
  have hconn : (G.induce (D : Set V)).Connected :=
    connected_componentFinset (G := G) C
  have hnocross : ∀ a ∈ D, ∀ i ∈ I, ¬ G.Adj a i := by
    intro a ha i hi
    have hiK : i ∈ K := (mem_sdiff.1 hi).1
    have hiD : i ∉ D := (mem_sdiff.1 hi).2
    exact no_cross_mixed_component (G := G) ha hiK hiD
  exact ⟨⟨D, I, hDU, hdisj, hI, hV, hDsub, hnonterm, hBd, hconn, hnocross⟩⟩

/-! ### NeighborCondition and independence restrict to `(D, B ∩ D)` -/

lemma NeighborCondition.restrict_inter {K B D : Finset V}
    (hN : NeighborCondition (G := G) K B) (hD : D ⊆ K) :
    NeighborCondition (G := G) D (B ∩ D) := by
  intro b v w hb hv hw hbv hbw
  have hbB : b ∈ B := (mem_inter.1 hb).1
  have hvK : v ∈ K \ B := by
    have hvD := (mem_sdiff.1 hv).1
    have hvBd := (mem_sdiff.1 hv).2
    have hvB : v ∉ B := fun hB => hvBd (mem_inter.2 ⟨hB, hvD⟩)
    exact mem_sdiff.2 ⟨hD hvD, hvB⟩
  have hwK : w ∈ K \ B := by
    have hwD := (mem_sdiff.1 hw).1
    have hwBd := (mem_sdiff.1 hw).2
    have hwB : w ∉ B := fun hB => hwBd (mem_inter.2 ⟨hB, hwD⟩)
    exact mem_sdiff.2 ⟨hD hwD, hwB⟩
  exact hN hbB hvK hwK hbv hbw

lemma sdiff_eq_sdiff_union_compl {K D S : Finset V}
    (hD : D ⊆ K) (hS : S ⊆ D) :
    K \ S = (D \ S) ∪ (K \ D) := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hx
    by_cases hDx : x ∈ D
    · exact Or.inl ⟨hDx, hx.2⟩
    · exact Or.inr ⟨hx.1, hDx⟩
  · intro hx
    rcases hx with h | h
    · exact ⟨hD h.1, h.2⟩
    · exact ⟨h.1, fun hS' => h.2 (hS hS')⟩

lemma B_sdiff_eq_inter_union_compl {K D B S : Finset V}
    (hBK : B ⊆ K) (hD : D ⊆ K) (hS : S ⊆ D) (hI : K \ D ⊆ B) :
    B \ S = (B ∩ D) \ S ∪ (K \ D) := by
  ext x
  simp only [mem_sdiff, mem_union, mem_inter]
  constructor
  · intro hx
    have hxK : x ∈ K := hBK hx.1
    by_cases hDx : x ∈ D
    · exact Or.inl ⟨⟨hx.1, hDx⟩, hx.2⟩
    · exact Or.inr ⟨hxK, hDx⟩
  · intro hx
    rcases hx with h | h
    · exact ⟨h.1.1, h.2⟩
    · exact ⟨hI (mem_sdiff.2 h), fun hS' => h.2 (hS hS')⟩

lemma no_cross_sdiff_compl {K D S : Finset V}
    (hnocross : ∀ a ∈ D, ∀ b ∈ K \ D, ¬ G.Adj a b)
    (hS : S ⊆ D) :
    ∀ a ∈ D \ S, ∀ b ∈ K \ D, ¬ G.Adj a b :=
  fun a ha b hb => hnocross a (mem_sdiff.1 ha).1 b hb

/-! ### Mapped components of a no-cross union -/

lemma induceIncl_union_left_apply {A J : Finset V} {x : V}
    (hxA : x ∈ A) :
    induceIncl G (subset_union_left (s₁ := A) (s₂ := J)) ⟨x, hxA⟩ =
      ⟨x, mem_union.2 (Or.inl hxA)⟩ :=
  rfl

lemma mixMap_eq_mk {A J : Finset V} {x : V} (hxA : x ∈ A) :
    ((G.induce (A : Set V)).connectedComponentMk ⟨x, hxA⟩).map
        (induceIncl G (subset_union_left (s₁ := A) (s₂ := J))) =
      (G.induce ((A ∪ J : Finset V) : Set V)).connectedComponentMk
        ⟨x, mem_union.2 (Or.inl hxA)⟩ := by
  rw [ConnectedComponent.map_mk, induceIncl_union_left_apply]

lemma mixMap_injective {A J : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ J, ¬ G.Adj a b) :
    Function.Injective
      (fun C : (G.induce (A : Set V)).ConnectedComponent =>
        C.map (induceIncl G (subset_union_left (s₁ := A) (s₂ := J)))) := by
  intro C D hCD
  revert hCD
  refine C.ind fun u => ?_
  refine D.ind fun v => ?_
  intro hCD
  have hCD' :
      (G.induce ((A ∪ J : Finset V) : Set V)).connectedComponentMk
          (induceIncl G (subset_union_left (s₁ := A) (s₂ := J)) u) =
        (G.induce ((A ∪ J : Finset V) : Set V)).connectedComponentMk
          (induceIncl G (subset_union_left (s₁ := A) (s₂ := J)) v) := by
    simpa [ConnectedComponent.map_mk] using hCD
  have hreach := ConnectedComponent.eq.mp hCD'
  exact ConnectedComponent.sound
    (Cograph.induce_reachable_of_mem_left (G := G) hnocross
      u.property v.property hreach)

lemma mem_componentFinset_map_iff {A J : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ J, ¬ G.Adj a b)
    (C : (G.induce (A : Set V)).ConnectedComponent) {x : V}
    (hxA : x ∈ A) :
    x ∈ componentFinset G (A ∪ J)
        (C.map (induceIncl G (subset_union_left (s₁ := A) (s₂ := J)))) ↔
      x ∈ componentFinset G A C := by
  constructor
  · intro hx
    obtain ⟨hxU0, hxC⟩ := (mem_filter.1 hx).2
    have hL :
        ((G.induce (A : Set V)).connectedComponentMk ⟨x, hxA⟩).map
            (induceIncl G (subset_union_left (s₁ := A) (s₂ := J))) =
          C.map (induceIncl G (subset_union_left (s₁ := A) (s₂ := J))) := by
      rw [mixMap_eq_mk]
      have : (⟨x, mem_union.2 (Or.inl hxA)⟩ :
          ((A ∪ J : Finset V) : Set V)) = ⟨x, hxU0⟩ := Subtype.ext rfl
      simpa [this] using hxC
    exact mem_filter.2 ⟨hxA, ⟨hxA, mixMap_injective (G := G) hnocross hL⟩⟩
  · intro hx
    obtain ⟨_, hxC⟩ := (mem_filter.1 hx).2
    have hxU : x ∈ A ∪ J := mem_union.2 (Or.inl hxA)
    refine mem_filter.2 ⟨hxU, ⟨hxU, ?_⟩⟩
    have hmap := mixMap_eq_mk (G := G) (J := J) hxA
    rw [hxC] at hmap
    have : (⟨x, hxU⟩ : ((A ∪ J : Finset V) : Set V)) =
        ⟨x, mem_union.2 (Or.inl hxA)⟩ := Subtype.ext rfl
    exact this ▸ hmap.symm

lemma componentFinset_map_subset_left {A J : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ J, ¬ G.Adj a b)
    (C : (G.induce (A : Set V)).ConnectedComponent) :
    componentFinset G (A ∪ J)
        (C.map (induceIncl G (subset_union_left (s₁ := A)))) ⊆ A := by
  intro x hx
  have hxU : x ∈ A ∪ J := (mem_filter.1 hx).1
  obtain ⟨z, hzA, hzC⟩ :
      ∃ (z : V) (hzA : z ∈ A),
        (G.induce (A : Set V)).connectedComponentMk ⟨z, hzA⟩ = C :=
    C.ind fun t => ⟨t.1, t.2, rfl⟩
  have hzU : z ∈ A ∪ J := mem_union.2 (Or.inl hzA)
  obtain ⟨_, hxC⟩ := (mem_filter.1 hx).2
  have hzMk :
      (G.induce ((A ∪ J : Finset V) : Set V)).connectedComponentMk ⟨z, hzU⟩ =
        C.map (induceIncl G (subset_union_left (s₁ := A) (s₂ := J))) := by
    have hmap := mixMap_eq_mk (G := G) (J := J) hzA
    rw [hzC] at hmap
    have : (⟨z, hzU⟩ : ((A ∪ J : Finset V) : Set V)) =
        ⟨z, mem_union.2 (Or.inl hzA)⟩ := Subtype.ext rfl
    exact this ▸ hmap.symm
  have hreach :
      (G.induce ((A ∪ J : Finset V) : Set V)).Reachable ⟨z, hzU⟩ ⟨x, hxU⟩ :=
    ConnectedComponent.exact (hzMk.trans hxC.symm)
  exact Cograph.mem_left_of_induce_reachable (G := G) hnocross hzA hreach

lemma componentFinset_map_inter_left {A J T : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ J, ¬ G.Adj a b)
    (C : (G.induce (A : Set V)).ConnectedComponent) :
    componentFinset G (A ∪ J)
        (C.map (induceIncl G (subset_union_left (s₁ := A)))) ∩ T =
      componentFinset G A C ∩ T := by
  ext x
  constructor
  · intro hx
    have hxC := (mem_inter.1 hx).1
    have hxT := (mem_inter.1 hx).2
    have hxA : x ∈ A := componentFinset_map_subset_left (G := G) hnocross C hxC
    have hxCA : x ∈ componentFinset G A C :=
      (mem_componentFinset_map_iff (G := G) hnocross C hxA).1 hxC
    exact mem_inter.2 ⟨hxCA, hxT⟩
  · intro hx
    have hxCA := (mem_inter.1 hx).1
    have hxT := (mem_inter.1 hx).2
    have hxA : x ∈ A := (mem_filter.1 hxCA).1
    have hxC : x ∈ componentFinset G (A ∪ J)
        (C.map (induceIncl G (subset_union_left (s₁ := A)))) :=
      (mem_componentFinset_map_iff (G := G) hnocross C hxA).2 hxCA
    exact mem_inter.2 ⟨hxC, hxT⟩

lemma exists_mem_A_of_free_union {A J T : Finset V}
    (hJ : J ⊆ T)
    (C' : (G.induce ((A ∪ J : Finset V) : Set V)).ConnectedComponent)
    (hfree : componentFinset G (A ∪ J) C' ∩ T = ∅) :
    ∃ (x : V) (hxA : x ∈ A),
      (G.induce ((A ∪ J : Finset V) : Set V)).connectedComponentMk
        ⟨x, mem_union.2 (Or.inl hxA)⟩ = C' := by
  obtain ⟨x, hxU, hxMk⟩ :
      ∃ (x : V) (hxU : x ∈ A ∪ J),
        (G.induce ((A ∪ J : Finset V) : Set V)).connectedComponentMk
          ⟨x, hxU⟩ = C' :=
    C'.ind fun t => ⟨t.1, t.2, rfl⟩
  have hxT : x ∉ T := by
    intro hxT
    have : x ∈ componentFinset G (A ∪ J) C' ∩ T :=
      mem_inter.2 ⟨mem_filter.2 ⟨hxU, ⟨hxU, hxMk⟩⟩, hxT⟩
    exact (notMem_empty x (hfree ▸ this))
  have hxJ : x ∉ J := fun hJ' => hxT (hJ hJ')
  have hxA : x ∈ A := (mem_union.1 hxU).resolve_right hxJ
  refine ⟨x, hxA, ?_⟩
  have : (⟨x, hxU⟩ : ((A ∪ J : Finset V) : Set V)) =
      ⟨x, mem_union.2 (Or.inl hxA)⟩ := Subtype.ext rfl
  simpa [this] using hxMk

lemma ncard_free_union_isolates {A J T : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ J, ¬ G.Adj a b)
    (hJ : J ⊆ T) :
    Nat.card { C : (G.induce ((A ∪ J : Finset V) : Set V)).ConnectedComponent //
        componentFinset G (A ∪ J) C ∩ T = ∅ } =
      Nat.card { C : (G.induce (A : Set V)).ConnectedComponent //
        componentFinset G A C ∩ T = ∅ } := by
  let f : { C : (G.induce (A : Set V)).ConnectedComponent //
        componentFinset G A C ∩ T = ∅ } →
      { C : (G.induce ((A ∪ J : Finset V) : Set V)).ConnectedComponent //
        componentFinset G (A ∪ J) C ∩ T = ∅ } :=
    fun C =>
      ⟨C.1.map (induceIncl G (subset_union_left (s₁ := A))), by
        have h := componentFinset_map_inter_left (G := G) (T := T) hnocross C.1
        simpa [h] using C.2⟩
  have hinj : Function.Injective f := by
    intro C D hCD
    apply Subtype.ext
    exact mixMap_injective (G := G) hnocross (Subtype.ext_iff.1 hCD)
  have hsurj : Function.Surjective f := by
    intro C'
    obtain ⟨x, hxA, hxMk⟩ :=
      exists_mem_A_of_free_union (G := G) hJ C'.1 C'.2
    let C : (G.induce (A : Set V)).ConnectedComponent :=
      (G.induce (A : Set V)).connectedComponentMk ⟨x, hxA⟩
    have hmapEq :
        C.map (induceIncl G (subset_union_left (s₁ := A) (s₂ := J))) = C'.1 :=
      (mixMap_eq_mk (G := G) (J := J) hxA).trans hxMk
    have hfree : componentFinset G A C ∩ T = ∅ := by
      apply eq_empty_of_forall_notMem
      intro y hy
      have hyA := (mem_filter.1 (mem_inter.1 hy).1).1
      have hyT := (mem_inter.1 hy).2
      have hyMap :
          y ∈ componentFinset G (A ∪ J)
            (C.map (induceIncl G (subset_union_left (s₁ := A) (s₂ := J)))) :=
        (mem_componentFinset_map_iff (G := G) hnocross C hyA).2
          (mem_inter.1 hy).1
      have : y ∈ componentFinset G (A ∪ J) C'.1 ∩ T := by
        rw [hmapEq] at hyMap
        exact mem_inter.2 ⟨hyMap, hyT⟩
      exact (notMem_empty y (C'.2 ▸ this))
    refine ⟨⟨C, hfree⟩, Subtype.ext hmapEq⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm

lemma T_inter_A_of_sdiff {D B S : Finset V} :
    ((B \ S) ∩ (D \ S)) = (B ∩ D) \ S := by
  ext x
  simp [mem_sdiff, mem_inter]
  tauto

/-- Cut transport: `z_B(K-S) = z_{B ∩ D}(D-S)` for `S ⊆ D`. -/
lemma terminalComponentCount_mixed {K D B S : Finset V}
    (hBK : B ⊆ K) (hD : D ⊆ K) (hS : S ⊆ D)
    (hI : K \ D ⊆ B)
    (hnocross : ∀ a ∈ D, ∀ b ∈ K \ D, ¬ G.Adj a b) :
    terminalComponentCount (G := G) K B S =
      terminalComponentCount (G := G) D (B ∩ D) S := by
  have hEq : K \ S = (D \ S) ∪ (K \ D) := sdiff_eq_sdiff_union_compl hD hS
  have hnc := no_cross_sdiff_compl hnocross hS
  have hJ : K \ D ⊆ B \ S := by
    intro x hx
    have hxKD := mem_sdiff.1 hx
    exact mem_sdiff.2 ⟨hI hx, fun hSx => hxKD.2 (hS hSx)⟩
  unfold terminalComponentCount IsFreeComponent
  -- Rewrite remainder carriers.
  have h1 :
      Nat.card { C : (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent //
          componentFinset G (K \ S) C ∩ (B \ S) = ∅ } =
        Nat.card
          { C : (G.induce (((D \ S) ∪ (K \ D) : Finset V) : Set V)).ConnectedComponent //
            componentFinset G ((D \ S) ∪ (K \ D)) C ∩ (B \ S) = ∅ } := by
    rw [hEq]
  have h2 :=
    ncard_free_union_isolates (G := G) (A := D \ S) (J := K \ D)
      (T := B \ S) hnc hJ
  have h3 :
      Nat.card { C : (G.induce ((D \ S : Finset V) : Set V)).ConnectedComponent //
          componentFinset G (D \ S) C ∩ (B \ S) = ∅ } =
        Nat.card { C : (G.induce ((D \ S : Finset V) : Set V)).ConnectedComponent //
          componentFinset G (D \ S) C ∩ ((B ∩ D) \ S) = ∅ } := by
    have hinter : ∀ C,
        componentFinset G (D \ S) C ∩ (B \ S) =
          componentFinset G (D \ S) C ∩ ((B ∩ D) \ S) := by
      intro C
      have hsub : componentFinset G (D \ S) C ⊆ D \ S :=
        componentFinset_subset (G := G) C
      ext x
      simp only [mem_inter]
      constructor
      · intro hx
        have hxC := hx.1
        have hxB := hx.2
        have hxDS : x ∈ D \ S := hsub hxC
        have hxBd : x ∈ (B ∩ D) \ S := by
          have : x ∈ (B \ S) ∩ (D \ S) := mem_inter.2 ⟨hxB, hxDS⟩
          simpa [T_inter_A_of_sdiff] using this
        exact ⟨hxC, hxBd⟩
      · intro hx
        have hxC := hx.1
        have hxBd := hx.2
        have hxB : x ∈ B \ S :=
          mem_sdiff.2 ⟨(mem_inter.1 (mem_sdiff.1 hxBd).1).1, (mem_sdiff.1 hxBd).2⟩
        exact ⟨hxC, hxB⟩
    refine Nat.card_congr ?_
    refine Equiv.subtypeEquiv (Equiv.refl _) ?_
    intro C
    simp [hinter C]
  exact h1.trans (h2.trans h3)

lemma TerminalHypothesis.restrict_mixed {K D B : Finset V}
    (hBK : B ⊆ K) (hD : D ⊆ K) (hI : K \ D ⊆ B)
    (hnocross : ∀ a ∈ D, ∀ b ∈ K \ D, ¬ G.Adj a b)
    (hTH : TerminalHypothesis (G := G) K B) :
    TerminalHypothesis (G := G) D (B ∩ D) := by
  constructor
  · have h := hTH.1
    simpa [terminalComponentCount_mixed (S := (∅ : Finset V)) hBK hD
      (empty_subset D) hI hnocross] using h
  · intro S hS hSne
    have hz := hTH.2 S (hS.trans hD) hSne
    simpa [terminalComponentCount_mixed hBK hD hS hI hnocross] using hz

lemma repairedTerminalHypothesis_mixed {K D B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hD : D ⊆ K) (hI : K \ D ⊆ B)
    (hnocross : ∀ a ∈ D, ∀ b ∈ K \ D, ¬ G.Adj a b)
    (hconn : (G.induce (D : Set V)).Connected)
    (hBd : (B ∩ D).Nonempty) :
    RepairedTerminalHypothesis (G := G) D (B ∩ D) := by
  rcases hrep with ⟨hcog, hBK, hInd, hTH, hN⟩
  refine ⟨fun a b c d ha hb hc hd => hcog (hD ha) (hD hb) (hD hc) (hD hd),
    inter_subset_right, hInd.mono inter_subset_left,
    TerminalHypothesis.restrict_mixed hBK hD hI hnocross hTH,
    NeighborCondition.restrict_inter hN hD⟩

lemma exists_min_terminalCover_of_mixed_traceable {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (s : MixedSplit (G := G) K B)
    (hpD : pathCoverNumber G s.D = 1) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc := by
  rcases hrep with ⟨hcog, hBK, hInd, hTH, hN⟩
  have hIeq : s.I = K \ s.D := s.I_eq
  have hI : K \ s.D ⊆ B := by simpa [hIeq] using s.hI
  have hrepD :
      RepairedTerminalHypothesis (G := G) s.D (B ∩ s.D) :=
    repairedTerminalHypothesis_mixed ⟨hcog, hBK, hInd, hTH, hN⟩
      s.hDsub hI (by simpa [hIeq] using s.hnocross) s.hconn s.hBd
  have h2 : 2 ≤ s.D.card := s.two_le_card_D
  have hDcover :
      ∃ pc : PathCover G s.D,
        pc.card = pathCoverNumber G s.D ∧
          IsTerminalCover (G := G) (B ∩ s.D) pc :=
    exists_min_terminalCover_of_pathCoverNumber_eq_one
      h2 hrepD.1 s.hconn hpD inter_subset_right s.hBd hrepD.2.2.2.1
  have hDcoverB :
      ∃ pc : PathCover G s.D,
        pc.card = pathCoverNumber G s.D ∧ IsTerminalCover (G := G) B pc := by
    obtain ⟨pc, hcard, hterm⟩ := hDcover
    exact ⟨pc, hcard, IsTerminalCover.of_subset hterm inter_subset_left⟩
  have hunion : s.D ∪ s.I = K := s.hDU
  obtain ⟨pc, hcard, hterm⟩ :=
    exists_min_terminalCover_mixed_union_isolates s.hdisj s.hI hInd
      s.hnocross hDcoverB
  refine ⟨pc.cast hunion, ?_, ?_⟩
  · rw [PathCover.cast_card, hcard, hunion]
  · intro p hp
    rw [PathCover.cast_paths pc hunion] at hp
    exact hterm p hp

/-- Host: a mixed (possibly disconnected) `K = B ∪ W` whose mixed component
is traceable has a real minimum `B`-ended cover, even if isolated terminals
make `p(K) > 1`. -/
theorem exists_min_terminalCover_of_sides_of_mixed_component_traceable
    (P : AllCographSides G) (hpat : NoInducedP4UnionP1 G) (htough : OneTough G)
    (hpD : ∀ s : MixedSplit (G := G) (P.B ∪ P.W) P.B,
      pathCoverNumber G s.D = 1) :
    ∃ pc : PathCover G (P.B ∪ P.W),
      pc.card = pathCoverNumber G (P.B ∪ P.W) ∧
        IsTerminalCover (G := G) P.B pc := by
  have hrep := P.repairedTerminalHypothesis_of_oneTough hpat htough
  have hV : ((P.B ∪ P.W) \ P.B).Nonempty := by
    obtain ⟨w, hw⟩ := P.hWne
    exact ⟨w, (P.mem_W_iff_mem_K_sdiff_B).1 hw⟩
  have hz : terminalComponentCount (G := G) (P.B ∪ P.W) P.B ∅ = 0 :=
    hrep.2.2.2.1.1
  obtain ⟨s⟩ :=
    exists_mixedSplit (G := G) P.B_subset_K hrep.2.2.2.2 hz hV
  exact exists_min_terminalCover_of_mixed_traceable hrep s (hpD s)

/-! ### Attained minimum endpoint deficit of ordinary min covers -/

noncomputable def minEndpointDeficit (K B : Finset V) : ℕ :=
  sInf {n | ∃ pc : PathCover G K,
    pc.card = pathCoverNumber G K ∧ pc.endpointDeficit B = n}

lemma minEndpointDeficit_mem (K B : Finset V) :
    minEndpointDeficit (G := G) K B ∈
      {n | ∃ pc : PathCover G K,
        pc.card = pathCoverNumber G K ∧ pc.endpointDeficit B = n} := by
  refine Nat.sInf_mem ?_
  obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) K
  exact ⟨pc.endpointDeficit B, pc, hpc, rfl⟩

lemma exists_min_pathCover_min_deficit (K B : Finset V) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧
        pc.endpointDeficit B = minEndpointDeficit (G := G) K B :=
  minEndpointDeficit_mem (G := G) K B

lemma minEndpointDeficit_eq_zero_iff (K B : Finset V) :
    minEndpointDeficit (G := G) K B = 0 ↔
      ∃ pc : PathCover G K,
        pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc := by
  constructor
  · intro h
    obtain ⟨pc, hcard, hdef⟩ := exists_min_pathCover_min_deficit (G := G) K B
    exact ⟨pc, hcard, PathCover.terminalCover_of_deficit_eq_zero pc (h ▸ hdef)⟩
  · intro ⟨pc, hcard, hterm⟩
    have h0 := PathCover.deficit_eq_zero_of_terminal pc hterm
    have hle : minEndpointDeficit (G := G) K B ≤ 0 :=
      Nat.sInf_le ⟨pc, hcard, h0⟩
    omega

/-! ### Part-cut obstruction for `p ≥ 2` when `B ⊆ F ∪ P_x` -/

lemma terminalHypothesis_not_swallowed_class {K B : Finset V}
    (hcog : IsCograph G K)
    (hTH : TerminalHypothesis (G := G) K B)
    (hp : 2 ≤ pathCoverNumber G K)
    {x : V} (hx : x ∈ eligibleSet G K)
    (hBsub : B ⊆ ineligibleSet G K ∪ Cograph.dNonadjClass (G := G) K x) :
    False := by
  obtain ⟨S, hSsub, hScut, hScomp⟩ :=
    Cograph.exists_partCut_of_canonical (G := G) hcog hx
  have hBrem :
      B \ S ⊆
        (ineligibleSet G K ∪ Cograph.dNonadjClass (G := G) K x) \ S :=
    fun z hz => mem_sdiff.2 ⟨hBsub (mem_sdiff.1 hz).1, (mem_sdiff.1 hz).2⟩
  have hSsubK : S ⊆ K := hSsub.trans (ineligibleSet_subset (G := G) K)
  have hzge :=
    terminalComponentCount_ge_pred_of_inOne (G := G) (K := K) (B := B)
      (S := S) hScomp hBrem
  have hc : componentCount G (K \ S) = S.card + pathCoverNumber G K := hScut
  have hge : S.card + pathCoverNumber G K - 1 ≤
      terminalComponentCount (G := G) K B S := by
    simpa [hc] using hzge
  by_cases hSne : S.Nonempty
  · have hle := hTH.2 S hSsubK hSne
    omega
  · have hS0 : S = ∅ := not_nonempty_iff_eq_empty.1 hSne
    have hz0 := hTH.1
    subst hS0
    simp at hge hz0 hc
    omega

/-- If `K ⊆ B`, the singleton cover is already a minimum `B`-ended cover.
Combined with mixed reduction this is the no-nonterminal base. -/
lemma exists_min_terminalCover_of_repaired {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hKB : K ⊆ B) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc :=
  exists_min_terminalCover_subset_B hKB hrep.2.2.1

/-- Complete-join case in which the mixed child is filled by terminals:
`X ⊆ B`, so the singleton cover of `X` splices through the B-free side. -/
lemma exists_min_terminalCover_join_terminals_in_child {X Y B : Finset V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hKcog : IsCograph G (X ∪ Y))
    (hB : B ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B)
    (hInd : Independent (G := G) B)
    (hpK : 2 ≤ pathCoverNumber G (X ∪ Y))
    (hXB : X ⊆ B) :
    ∃ pc : PathCover G (X ∪ Y),
      pc.card = pathCoverNumber G (X ∪ Y) ∧
        IsTerminalCover (G := G) B pc := by
  have hdom : Y.card < pathCoverNumber G X :=
    dominant_mixed_child_of_slack_zero hXne hYne hAB hKcog hB hTH hpK
  have hXcover :=
    exists_min_terminalCover_subset_B (K := X) (B := B) hXB hInd
  exact exists_min_terminalCover_complete_join hXne hYne hAB hB hdom hXcover

/-- A connected mixed component with `p ≥ 2` is a complete join whose
independent terminals occupy the unique dominant child. -/
lemma exists_join_split_of_mixed_p_ge_two {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (s : MixedSplit (G := G) K B)
    (hp : 2 ≤ pathCoverNumber G s.D) :
    ∃ X Y : Finset V,
      X ∪ Y = s.D ∧ Disjoint X Y ∧ X.Nonempty ∧ Y.Nonempty ∧
        G.IsCompleteBetween (X : Set V) (Y : Set V) ∧
          B ∩ s.D ⊆ X ∧ Y.card < pathCoverNumber G X := by
  have hcogD : IsCograph G s.D :=
    fun a b c d ha hb hc hd => hrep.1 (s.hDsub ha) (s.hDsub hb) (s.hDsub hc) (s.hDsub hd)
  have h2 : 2 ≤ s.D.card := s.two_le_card_D
  obtain ⟨X0, Y0, hX0sub, hY0sub, hX0ne, hY0ne, hdisj0, hcover0, hAB0, -, -⟩ :=
    Cograph.exists_complete_join_on (G := G) (Cograph.isCograph_iff.2 hcogD)
      s.hconn h2
  have hBd : B ∩ s.D ⊆ X0 ∪ Y0 := by
    intro x hx
    have : x ∈ s.D := (mem_inter.1 hx).2
    rwa [← hcover0] at this
  have hside :=
    Independent.subset_join_side (G := G) hAB0
      (hrep.2.2.1.mono inter_subset_left) hBd
  have hIeq : s.I = K \ s.D := s.I_eq
  have hTHD : TerminalHypothesis (G := G) s.D (B ∩ s.D) :=
    (repairedTerminalHypothesis_mixed hrep s.hDsub
      (by simpa [hIeq] using s.hI)
      (by simpa [hIeq] using s.hnocross) s.hconn s.hBd).2.2.2.1
  rcases hside with hX | hY
  · refine ⟨X0, Y0, hcover0, hdisj0, hX0ne, hY0ne, hAB0, hX, ?_⟩
    have hunion : X0 ∪ Y0 = s.D := hcover0
    simpa [hunion] using
      dominant_mixed_child_of_slack_zero (G := G) hX0ne hY0ne hAB0
        (by simpa [hunion] using hcogD) hX (by simpa [hunion] using hTHD)
        (by simpa [hunion] using hp)
  · have hBA : G.IsCompleteBetween (Y0 : Set V) (X0 : Set V) :=
      fun {a} ha {b} hb => (hAB0 hb ha).symm
    have hcover1 : Y0 ∪ X0 = s.D := by
      rw [union_comm, hcover0]
    refine ⟨Y0, X0, hcover1, hdisj0.symm, hY0ne, hX0ne, hBA, hY, ?_⟩
    simpa [hcover1] using
      dominant_mixed_child_of_slack_zero (G := G) hY0ne hX0ne hBA
        (by simpa [hcover1] using hcogD) hY (by simpa [hcover1] using hTHD)
        (by simpa [hcover1] using hp)

end Nikoghosyan

