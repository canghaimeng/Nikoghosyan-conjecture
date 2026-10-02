/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.SaturatedJoin
import Nikoghosyan.Cograph.Cotree
import Nikoghosyan.Cograph.PathCoverUnion
import Nikoghosyan.Cograph.Compatibility

/-!
# Cograph F-cut identity

Binary `CotreeOn` induction yields
`c(U \ F(U)) = |F(U)| + p(U)`
on every constructible carrier, including empty and singleton sets.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma pathCoverNumber_singleton (v : V) : pathCoverNumber G {v} = 1 := by
  have hle := pathCoverNumber_le_card (G := G) {v}
  have hge := one_le_pathCoverNumber_of_nonempty (G := G) (singleton_nonempty v)
  simpa [card_singleton] using (le_antisymm hle hge)

lemma eligible_singleton (v : V) : Eligible G {v} v := by
  let p := GraphPath.singleton (G := G) v
  have hp : p.support = {v} := GraphPath.support_singleton v
  let pc : PathCover G {v} := (PathCover.ofPath p).cast hp
  have hcard : pc.card = 1 := by
    rw [PathCover.cast_card, PathCover.ofPath_card]
  have hmin : pc.card = pathCoverNumber G {v} := by
    rw [hcard, pathCoverNumber_singleton]
  have hmem : p ∈ pc.paths := by
    rw [PathCover.cast_paths, PathCover.ofPath]
    exact List.mem_singleton.2 rfl
  exact ⟨pc, hmin, p, hmem, Or.inl rfl⟩

lemma eligibleSet_singleton (v : V) : eligibleSet G {v} = {v} := by
  ext x
  constructor
  · intro hx
    exact (eligibleSet_subset (G := G) {v}) hx
  · intro hx
    have hx' : x = v := mem_singleton.1 hx
    rw [hx']
    exact (mem_eligibleSet_iff (G := G)).2 ⟨mem_singleton_self v, eligible_singleton v⟩

lemma ineligibleSet_empty : ineligibleSet G (∅ : Finset V) = ∅ := by
  simp [ineligibleSet]

lemma ineligibleSet_singleton (v : V) : ineligibleSet G {v} = ∅ := by
  ext x
  constructor
  · intro hx
    rw [mem_ineligibleSet_iff] at hx
    have hx' : x = v := mem_singleton.1 hx.1
    rw [hx'] at hx
    exact (hx.2 (eligible_singleton v)).elim
  · intro hx
    exact (notMem_empty x hx).elim

lemma componentCount_eq_one_of_connected {U : Finset V}
    (hU : U.Nonempty) (hc : (G.induce (U : Set V)).Connected) :
    componentCount G U = 1 := by
  have hneU : Nonempty (U : Set V) := hU.to_subtype
  have hne : Nonempty (G.induce (U : Set V)).ConnectedComponent :=
    ⟨(G.induce (U : Set V)).connectedComponentMk ⟨hU.choose, hU.choose_spec⟩⟩
  have hss : Subsingleton (G.induce (U : Set V)).ConnectedComponent :=
    hc.preconnected.subsingleton_connectedComponent
  exact Nat.card_eq_one_iff_unique.2 ⟨hss, hne⟩

lemma induce_connected_of_completeJoin {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    (G.induce ((A ∪ B : Finset V) : Set V)).Connected := by
  haveI : Nonempty ((A ∪ B : Finset V) : Set V) :=
    (hAne.mono subset_union_left).to_subtype
  refine (connected_iff _).2 ⟨?_, inferInstance⟩
  intro x y
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨a, ha⟩ := hAne
  have hbU : b ∈ A ∪ B := mem_union.2 (Or.inr hb)
  have haU : a ∈ A ∪ B := mem_union.2 (Or.inl ha)
  let b' : ((A ∪ B : Finset V) : Set V) := ⟨b, hbU⟩
  let a' : ((A ∪ B : Finset V) : Set V) := ⟨a, haU⟩
  have reach (z : ((A ∪ B : Finset V) : Set V)) :
      (G.induce ((A ∪ B : Finset V) : Set V)).Reachable z b' := by
    rcases mem_union.1 z.property with hzA | hzB
    · exact Adj.reachable <| by simpa [induce_adj] using hAB hzA hb
    · by_cases hzb : z.val = b
      · have : z = b' := Subtype.ext hzb
        simpa [this] using
          Reachable.rfl (G := G.induce ((A ∪ B : Finset V) : Set V)) (x := z)
      · have hz_to_a : (G.induce ((A ∪ B : Finset V) : Set V)).Adj z a' := by
          simpa [induce_adj] using (hAB ha hzB).symm
        have ha_to_b : (G.induce ((A ∪ B : Finset V) : Set V)).Adj a' b' := by
          simpa [induce_adj] using hAB ha hb
        exact (Adj.reachable hz_to_a).trans ha_to_b.reachable
  exact (reach x).trans (reach y).symm

lemma componentCount_complete_join {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    componentCount G (A ∪ B) = 1 :=
  componentCount_eq_one_of_connected (hAne.mono subset_union_left)
    (induce_connected_of_completeJoin hAne hBne hAB)

lemma mem_left_of_induce_walk {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ A) :
    (G.induce ((A ∪ B : Finset V) : Set V)).Walk x y → y.val ∈ A
  | .nil => hx
  | .cons (v := mid) hadj p => by
      have hadjG : G.Adj x.val mid.val := by simpa [induce_adj] using hadj
      have hvA : mid.val ∈ A := by
        rcases mem_union.1 mid.property with hA | hB
        · exact hA
        · exact (hnocross x.val hx mid.val hB hadjG).elim
      exact mem_left_of_induce_walk hnocross hvA p

lemma mem_left_of_induce_reachable {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ A)
    (hreach : (G.induce ((A ∪ B : Finset V) : Set V)).Reachable x y) :
    y.val ∈ A :=
  mem_left_of_induce_walk hnocross hx (Classical.choice hreach)

lemma induce_reachable_of_mem_left_walk {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ A) (hy : y.val ∈ A)
    (p : (G.induce ((A ∪ B : Finset V) : Set V)).Walk x y) :
    (G.induce (A : Set V)).Reachable ⟨x.val, hx⟩ ⟨y.val, hy⟩ := by
  cases p with
  | nil => exact Reachable.rfl
  | cons hadj q =>
      rename_i mid
      have hadjG : G.Adj x.val mid.val := by simpa [induce_adj] using hadj
      have hvA : mid.val ∈ A := by
        rcases mem_union.1 mid.property with hA | hB
        · exact hA
        · exact (hnocross x.val hx mid.val hB hadjG).elim
      have hfirst : (G.induce (A : Set V)).Reachable ⟨x.val, hx⟩ ⟨mid.val, hvA⟩ :=
        Adj.reachable (by simpa [induce_adj] using hadjG)
      have hrest := induce_reachable_of_mem_left_walk hnocross hvA hy q
      exact hfirst.trans hrest

lemma induce_reachable_of_mem_left {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hreach : (G.induce ((A ∪ B : Finset V) : Set V)).Reachable x y) :
    (G.induce (A : Set V)).Reachable ⟨x.val, hx⟩ ⟨y.val, hy⟩ :=
  induce_reachable_of_mem_left_walk hnocross hx hy (Classical.choice hreach)

lemma mem_right_of_induce_walk {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ B) :
    (G.induce ((A ∪ B : Finset V) : Set V)).Walk x y → y.val ∈ B
  | .nil => hx
  | .cons (v := mid) hadj p => by
      have hadjG : G.Adj x.val mid.val := by simpa [induce_adj] using hadj
      have hvB : mid.val ∈ B := by
        rcases mem_union.1 mid.property with hA | hB
        · exact (hnocross mid.val hA x.val hx hadjG.symm).elim
        · exact hB
      exact mem_right_of_induce_walk hnocross hvB p

lemma mem_right_of_induce_reachable {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ B)
    (hreach : (G.induce ((A ∪ B : Finset V) : Set V)).Reachable x y) :
    y.val ∈ B :=
  mem_right_of_induce_walk hnocross hx (Classical.choice hreach)

lemma induce_reachable_of_mem_right_walk {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ B) (hy : y.val ∈ B)
    (p : (G.induce ((A ∪ B : Finset V) : Set V)).Walk x y) :
    (G.induce (B : Set V)).Reachable ⟨x.val, hx⟩ ⟨y.val, hy⟩ := by
  cases p with
  | nil => exact Reachable.rfl
  | cons hadj q =>
      rename_i mid
      have hadjG : G.Adj x.val mid.val := by simpa [induce_adj] using hadj
      have hvB : mid.val ∈ B := by
        rcases mem_union.1 mid.property with hA | hB
        · exact (hnocross mid.val hA x.val hx hadjG.symm).elim
        · exact hB
      have hfirst : (G.induce (B : Set V)).Reachable ⟨x.val, hx⟩ ⟨mid.val, hvB⟩ :=
        Adj.reachable (by simpa [induce_adj] using hadjG)
      have hrest := induce_reachable_of_mem_right_walk hnocross hvB hy q
      exact hfirst.trans hrest

lemma induce_reachable_of_mem_right {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : ((A ∪ B : Finset V) : Set V)} (hx : x.val ∈ B) (hy : y.val ∈ B)
    (hreach : (G.induce ((A ∪ B : Finset V) : Set V)).Reachable x y) :
    (G.induce (B : Set V)).Reachable ⟨x.val, hx⟩ ⟨y.val, hy⟩ :=
  induce_reachable_of_mem_right_walk hnocross hx hy (Classical.choice hreach)

lemma componentCount_union_of_no_cross {A B : Finset V}
    (_hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    componentCount G (A ∪ B) = componentCount G A + componentCount G B := by
  have hle := componentCount_union_le (G := G) A B
  let g : (G.induce (A : Set V)).ConnectedComponent ⊕
        (G.induce (B : Set V)).ConnectedComponent →
      (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent
    | .inl C => C.map (induceIncl G (subset_union_left (s₁ := A)))
    | .inr C => C.map (induceIncl G (subset_union_right (s₁ := A)))
  have hg : Function.Injective g := by
    intro x y hxy
    match x, y with
    | .inl C, .inl D =>
      apply congrArg Sum.inl
      revert hxy
      refine C.ind fun u => ?_
      refine D.ind fun v => ?_
      intro hxy
      have hreach := ConnectedComponent.eq.mp (by
        simpa [g, ConnectedComponent.map_mk] using hxy)
      exact ConnectedComponent.sound
        (induce_reachable_of_mem_left hnocross
          (by exact u.property) (by exact v.property) hreach)
    | .inr C, .inr D =>
      apply congrArg Sum.inr
      revert hxy
      refine C.ind fun u => ?_
      refine D.ind fun v => ?_
      intro hxy
      have hreach := ConnectedComponent.eq.mp (by
        simpa [g, ConnectedComponent.map_mk] using hxy)
      exact ConnectedComponent.sound
        (induce_reachable_of_mem_right hnocross
          (by exact u.property) (by exact v.property) hreach)
    | .inl C, .inr D =>
      exfalso
      revert hxy
      refine C.ind fun u => ?_
      refine D.ind fun v => ?_
      intro hxy
      have hreach := ConnectedComponent.eq.mp (by
        simpa [g, ConnectedComponent.map_mk] using hxy)
      have hvA := mem_left_of_induce_reachable hnocross
        (by exact u.property) hreach
      exact Finset.disjoint_left.1 _hdisj hvA v.property
    | .inr C, .inl D =>
      exfalso
      revert hxy
      refine C.ind fun u => ?_
      refine D.ind fun v => ?_
      intro hxy
      have hreach := ConnectedComponent.eq.mp (by
        simpa [g, ConnectedComponent.map_mk] using hxy)
      have hvA := mem_left_of_induce_reachable hnocross
        (by exact v.property) hreach.symm
      exact Finset.disjoint_left.1 _hdisj hvA u.property
  haveI : Fintype (G.induce (A : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce (B : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  have hge : componentCount G A + componentCount G B ≤ componentCount G (A ∪ B) := by
    simpa [componentCount, Nat.card_sum, Nat.card_eq_fintype_card] using
      Nat.card_le_card_of_injective g hg
  omega

lemma exists_spanning_path_start_of_internal {U : Finset V} {x : V}
    (r : GraphPath G) (hr : r.support = U)
    (hadj : G.Adj r.finish r.start)
    (hx : x ∈ U) (hs : x ≠ r.start) (hf : x ≠ r.finish) :
    ∃ p : GraphPath G, p.support = U ∧ p.start = x := by
  have hx' : x ∈ r.support := by simpa [hr] using hx
  have hnilT : ¬ (r.takeUntil hx').walk.Nil := by
    intro hnil
    exact hs ((GraphPath.takeUntil_nil_iff r hx').1 hnil)
  let left := r.dropUntil hx'
  let right := (r.takeUntil hx').trimFinish hnilT
  have hdisj : Disjoint left.support right.support := by
    rw [disjoint_iff_inter_eq_empty]
    ext y
    constructor
    · intro hy
      have hyL : y ∈ (r.dropUntil hx').support := (mem_inter.1 hy).1
      have hyR : y ∈ right.support := (mem_inter.1 hy).2
      have hyR' : y ∈ (r.takeUntil hx').support.erase (r.takeUntil hx').finish := by
        simpa [right, GraphPath.support_trimFinish] using hyR
      have hinter := GraphPath.inter_support_takeUntil_dropUntil_subset r hx'
      have hyx : y ∈ ({x} : Finset V) := by
        have : y ∈ (r.takeUntil hx').support ∩ (r.dropUntil hx').support :=
          mem_inter.2 ⟨(mem_erase.1 hyR').2, hyL⟩
        simpa [GraphPath.takeUntil] using hinter this
      have hyne : y ≠ x := by
        have : y ≠ (r.takeUntil hx').finish := (mem_erase.1 hyR').1
        simpa [GraphPath.takeUntil] using this
      exact (hyne (mem_singleton.1 hyx)).elim
    · intro hy
      exact (notMem_empty y hy).elim
  have hadj' : G.Adj left.finish right.start := by
    have : right.start = r.start := by
      simp [right, GraphPath.trimFinish_start, GraphPath.takeUntil]
    have : left.finish = r.finish := by
      simp [left, GraphPath.dropUntil]
    simpa [left, right, GraphPath.trimFinish_start, GraphPath.takeUntil,
      GraphPath.dropUntil] using hadj
  let p := left.splice right hadj' hdisj
  have hstart : p.start = x := by
    change left.start = x
    simp [left, GraphPath.dropUntil]
  refine ⟨p, ?_, hstart⟩
  have hxD : x ∈ left.support := by
    have : left.start = x := by simp [left, GraphPath.dropUntil]
    simpa [this] using left.start_mem_support
  have hR : right.support = (r.takeUntil hx').support.erase x := by
    simp [right, GraphPath.support_trimFinish, GraphPath.takeUntil]
  have hTD := GraphPath.support_takeUntil_union_dropUntil r hx'
  have hunion : left.support ∪ right.support = r.support := by
    rw [hR]
    ext y
    constructor
    · intro hy
      rcases mem_union.1 hy with hyL | hyR
      · have : y ∈ (r.takeUntil hx').support ∪ (r.dropUntil hx').support :=
          mem_union.2 (Or.inr (by simpa [left] using hyL))
        rwa [hTD] at this
      · have hyT : y ∈ (r.takeUntil hx').support := (mem_erase.1 hyR).2
        have : y ∈ (r.takeUntil hx').support ∪ (r.dropUntil hx').support :=
          mem_union.2 (Or.inl hyT)
        rwa [hTD] at this
    · intro hy
      have hy' : y ∈ (r.takeUntil hx').support ∪ (r.dropUntil hx').support := by
        rw [hTD]
        simpa [hr] using hy
      rcases mem_union.1 hy' with hyT | hyD
      · by_cases hyx : y = x
        · exact mem_union.2 (Or.inl (by simpa [hyx] using hxD))
        · exact mem_union.2 (Or.inr (mem_erase.2 ⟨hyx, hyT⟩))
      · exact mem_union.2 (Or.inl (by simpa [left] using hyD))
  simpa [p, GraphPath.support_splice, hr] using hunion

lemma eligible_of_complete_join_balanced {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ B.card)
    (hpB : pathCoverNumber G B ≤ A.card)
    (hx : x ∈ A ∪ B) : Eligible G (A ∪ B) x := by
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_complete_join_spanning_path hAne hBne hAB hpA hpB
  have hmin_of (p : GraphPath G) (hp : p.support = A ∪ B) :
      Eligible G (A ∪ B) p.start ∧ Eligible G (A ∪ B) p.finish := by
    let pc : PathCover G (A ∪ B) := (PathCover.ofPath p).cast hp
    have hcard : pc.card = 1 := by
      rw [PathCover.cast_card, PathCover.ofPath_card]
    have hpc : pc.card = pathCoverNumber G (A ∪ B) := by
      have hle := pathCoverNumber_le (G := G) pc
      have hge := one_le_pathCoverNumber_of_nonempty (G := G) (U := A ∪ B)
        (hAne.mono (subset_union_left (s₂ := B)))
      omega
    have hmem : p ∈ pc.paths := by
      rw [PathCover.cast_paths, PathCover.ofPath]
      exact List.mem_singleton.2 rfl
    exact Eligible.of_min_cover_endpoint pc hpc hmem
  by_cases hxs : x = r.start
  · simpa [hxs] using (hmin_of r hr).1
  by_cases hxf : x = r.finish
  · simpa [hxf] using (hmin_of r hr).2
  have hadj : G.Adj r.finish r.start := (hAB hs hf).symm
  obtain ⟨p, hp, hstart⟩ :=
    exists_spanning_path_start_of_internal (U := A ∪ B) r hr hadj hx hxs hxf
  simpa [hstart] using (hmin_of p hp).1

lemma eligibleSet_complete_join_balanced {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ B.card)
    (hpB : pathCoverNumber G B ≤ A.card) :
    eligibleSet G (A ∪ B) = A ∪ B := by
  ext x
  constructor
  · intro hx
    exact (eligibleSet_subset (G := G) (A ∪ B)) hx
  · intro hx
    exact (mem_eligibleSet_iff (G := G)).2
      ⟨hx, eligible_of_complete_join_balanced hAne hBne hAB hpA hpB hx⟩

lemma ineligibleSet_complete_join_balanced {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ B.card)
    (hpB : pathCoverNumber G B ≤ A.card) :
    ineligibleSet G (A ∪ B) = ∅ := by
  ext x
  constructor
  · intro hx
    rw [mem_ineligibleSet_iff] at hx
    exact (hx.2 (eligible_of_complete_join_balanced hAne hBne hAB hpA hpB hx.1)).elim
  · intro hx
    exact (notMem_empty x hx).elim

lemma card_ineligibleSet_complete_join_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    (ineligibleSet G (A ∪ B)).card =
      B.card + (ineligibleSet G A).card := by
  have hF := ineligibleSet_complete_join_dominant hAne hBne hAB hdom
  have hdisj := disjoint_of_completeBetween hAB
  have hdisjF : Disjoint B (ineligibleSet G A) := by
    rw [disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      exact (Finset.disjoint_left.1 hdisj
        (ineligibleSet_subset (G := G) A (mem_inter.1 hx).2)
        (mem_inter.1 hx).1).elim
    · intro hx
      exact (notMem_empty x hx).elim
  rw [hF, card_union_of_disjoint hdisjF]

lemma sdiff_ineligible_disjoint_union {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    (A ∪ B) \ ineligibleSet G (A ∪ B) =
      (A \ ineligibleSet G A) ∪ (B \ ineligibleSet G B) := by
  have hF := ineligibleSet_disjoint_union (G := G) hdisj hnocross
  ext x
  constructor
  · intro hx
    have hxU : x ∈ A ∪ B := (mem_sdiff.1 hx).1
    have hnot : x ∉ ineligibleSet G (A ∪ B) := (mem_sdiff.1 hx).2
    have hnot' : x ∉ ineligibleSet G A ∪ ineligibleSet G B := by rwa [hF] at hnot
    rcases mem_union.1 hxU with hxA | hxB
    · refine mem_union.2 (Or.inl (mem_sdiff.2 ⟨hxA, ?_⟩))
      intro hFA
      exact hnot' (mem_union.2 (Or.inl hFA))
    · refine mem_union.2 (Or.inr (mem_sdiff.2 ⟨hxB, ?_⟩))
      intro hFB
      exact hnot' (mem_union.2 (Or.inr hFB))
  · intro hx
    rcases mem_union.1 hx with hxA | hxB
    · have hxA' : x ∈ A := (mem_sdiff.1 hxA).1
      have hxFA : x ∉ ineligibleSet G A := (mem_sdiff.1 hxA).2
      refine mem_sdiff.2 ⟨mem_union.2 (Or.inl hxA'), ?_⟩
      intro hF
      have hF' : x ∈ ineligibleSet G A ∪ ineligibleSet G B := by rwa
        [ineligibleSet_disjoint_union (G := G) hdisj hnocross] at hF
      rcases mem_union.1 hF' with hA | hB
      · exact hxFA hA
      · exact Finset.disjoint_left.1 hdisj hxA'
          (ineligibleSet_subset (G := G) B hB)
    · have hxB' : x ∈ B := (mem_sdiff.1 hxB).1
      have hxFB : x ∉ ineligibleSet G B := (mem_sdiff.1 hxB).2
      refine mem_sdiff.2 ⟨mem_union.2 (Or.inr hxB'), ?_⟩
      intro hF
      have hF' : x ∈ ineligibleSet G A ∪ ineligibleSet G B := by rwa
        [ineligibleSet_disjoint_union (G := G) hdisj hnocross] at hF
      rcases mem_union.1 hF' with hA | hB
      · exact Finset.disjoint_left.1 hdisj
          (ineligibleSet_subset (G := G) A hA) hxB'
      · exact hxFB hB

/-- Numerical F-cut identity on every cotree carrier. -/
lemma componentCount_sdiff_ineligibleSet_eq {U : Finset V}
    (h : CotreeOn G U) :
    componentCount G (U \ ineligibleSet G U) =
      (ineligibleSet G U).card + pathCoverNumber G U := by
  induction h with
  | empty =>
    simp [ineligibleSet_empty, pathCoverNumber_empty, componentCount_empty]
  | singleton v =>
    simp [ineligibleSet_singleton, pathCoverNumber_singleton,
      componentCount_singleton]
  | disjointUnion hdisj hnocross hA hB ihA ihB =>
    rename_i A B
    have hF := ineligibleSet_disjoint_union (G := G) hdisj hnocross
    have hp := pathCoverNumber_disjoint_union (G := G) hdisj hnocross
    have hrem := sdiff_ineligible_disjoint_union hdisj hnocross
    have hdisjRem :
        Disjoint (A \ ineligibleSet G A) (B \ ineligibleSet G B) :=
      disjoint_of_subset_left sdiff_subset
        (disjoint_of_subset_right sdiff_subset hdisj)
    have hnocrossRem :
        ∀ a ∈ A \ ineligibleSet G A, ∀ b ∈ B \ ineligibleSet G B, ¬ G.Adj a b :=
      fun a ha b hb =>
        hnocross a (mem_sdiff.1 ha).1 b (mem_sdiff.1 hb).1
    have hadd :=
      componentCount_union_of_no_cross hdisjRem hnocrossRem
    have hcardF :
        (ineligibleSet G (A ∪ B)).card =
          (ineligibleSet G A).card + (ineligibleSet G B).card := by
      have hdisjF :
          Disjoint (ineligibleSet G A) (ineligibleSet G B) :=
        disjoint_of_subset_left (ineligibleSet_subset (G := G) A)
          (disjoint_of_subset_right (ineligibleSet_subset (G := G) B) hdisj)
      rw [hF, card_union_of_disjoint hdisjF]
    rw [hrem, hadd, ihA, ihB, hcardF, hp]
    omega
  | completeJoin hAne hBne hAB hA hB ihA ihB =>
    rename_i A B
    by_cases hAdom : B.card < pathCoverNumber G A
    · have hrem := sdiff_ineligibleSet_complete_join_dominant hAne hBne hAB hAdom
      have hcard :=
        card_ineligibleSet_complete_join_dominant hAne hBne hAB hAdom
      have hp := pathCoverNumber_add_card_of_dominant hAne hBne hAB hAdom
      rw [hrem, ihA, hcard, hp]
      omega
    · by_cases hBdom : A.card < pathCoverNumber G B
      · have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
          fun {b} hb {a} ha => (hAB ha hb).symm
        have hrem : (A ∪ B) \ ineligibleSet G (A ∪ B) =
            B \ ineligibleSet G B := by
          simpa [union_comm] using
            sdiff_ineligibleSet_complete_join_dominant hBne hAne hBA hBdom
        have hcard : (ineligibleSet G (A ∪ B)).card =
            A.card + (ineligibleSet G B).card := by
          simpa [union_comm] using
            card_ineligibleSet_complete_join_dominant hBne hAne hBA hBdom
        have hp : pathCoverNumber G B =
            pathCoverNumber G (A ∪ B) + A.card := by
          simpa [union_comm] using
            pathCoverNumber_add_card_of_dominant hBne hAne hBA hBdom
        rw [hrem, ihB, hcard, hp]
        omega
      · have hpA : pathCoverNumber G A ≤ B.card := Nat.le_of_not_gt hAdom
        have hpB : pathCoverNumber G B ≤ A.card := Nat.le_of_not_gt hBdom
        have hF := ineligibleSet_complete_join_balanced hAne hBne hAB hpA hpB
        have hp := pathCoverNumber_complete_join hAne hBne hAB
        have hmax :
            max 1 (max (pathCoverNumber G A - B.card)
              (pathCoverNumber G B - A.card)) = 1 := by
          simp [Nat.sub_eq_zero_of_le hpA, Nat.sub_eq_zero_of_le hpB]
        have hp1 : pathCoverNumber G (A ∪ B) = 1 := hp.trans hmax
        rw [hF, sdiff_empty, hp1, card_empty,
          componentCount_complete_join hAne hBne hAB]

lemma ineligibleSet_is_largest_attaining_cut {U : Finset V}
    (h : CotreeOn G U) :
    componentCount G (U \ ineligibleSet G U) =
      pathCoverNumber G U + (ineligibleSet G U).card ∧
    (∀ X, X ⊆ U →
      componentCount G (U \ X) = pathCoverNumber G U + X.card →
        X ⊆ ineligibleSet G U) ∧
    (∀ X, X ⊆ U →
      componentCount G (U \ X) = pathCoverNumber G U + X.card →
        X.card ≤ (ineligibleSet G U).card) := by
  have hid := componentCount_sdiff_ineligibleSet_eq h
  refine ⟨by rw [hid, add_comm], ?_, ?_⟩
  · intro X hX heq
    exact eq_cut_bound_imp_subset_ineligible hX heq
  · intro X hX heq
    exact card_le_card (eq_cut_bound_imp_subset_ineligible hX heq)

lemma fcut_int_eq_zero {U : Finset V} (h : CotreeOn G U) :
    (componentCount G (U \ ineligibleSet G U) : ℤ) -
      (ineligibleSet G U).card - pathCoverNumber G U = 0 := by
  have h' := componentCount_sdiff_ineligibleSet_eq h
  omega

lemma componentCount_sdiff_ineligibleSet_eq_of_isCograph {U : Finset V}
    (h : IsCograph G U) :
    componentCount G (U \ ineligibleSet G U) =
      (ineligibleSet G U).card + pathCoverNumber G U :=
  componentCount_sdiff_ineligibleSet_eq (cotreeOn_of_isCograph h)

/-- Canonical flattened `Nikoghosyan.IsCograph` wrapper. The numerical identity
is already proved on the structured predicate; this is API transport via
`isCograph_iff.2`. -/
lemma componentCount_sdiff_ineligibleSet_eq_of_canonical {U : Finset V}
    (h : Nikoghosyan.IsCograph G U) :
    componentCount G (U \ ineligibleSet G U) =
      (ineligibleSet G U).card + pathCoverNumber G U :=
  componentCount_sdiff_ineligibleSet_eq_of_isCograph (isCograph_iff.2 h)

lemma ineligibleSet_is_largest_attaining_cut_of_isCograph {U : Finset V}
    (h : IsCograph G U) :
    componentCount G (U \ ineligibleSet G U) =
      pathCoverNumber G U + (ineligibleSet G U).card ∧
    (∀ X, X ⊆ U →
      componentCount G (U \ X) = pathCoverNumber G U + X.card →
        X ⊆ ineligibleSet G U) ∧
    (∀ X, X ⊆ U →
      componentCount G (U \ X) = pathCoverNumber G U + X.card →
        X.card ≤ (ineligibleSet G U).card) :=
  ineligibleSet_is_largest_attaining_cut (cotreeOn_of_isCograph h)

lemma ineligibleSet_is_largest_attaining_cut_of_canonical {U : Finset V}
    (h : Nikoghosyan.IsCograph G U) :
    componentCount G (U \ ineligibleSet G U) =
      pathCoverNumber G U + (ineligibleSet G U).card ∧
    (∀ X, X ⊆ U →
      componentCount G (U \ X) = pathCoverNumber G U + X.card →
        X ⊆ ineligibleSet G U) ∧
    (∀ X, X ⊆ U →
      componentCount G (U \ X) = pathCoverNumber G U + X.card →
        X.card ≤ (ineligibleSet G U).card) :=
  ineligibleSet_is_largest_attaining_cut_of_isCograph (isCograph_iff.2 h)

end Cograph
end Nikoghosyan
