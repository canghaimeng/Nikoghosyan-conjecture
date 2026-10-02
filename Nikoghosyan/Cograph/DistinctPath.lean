/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.IneligibleDeletion

/-!
# Distinct-path certificates

`D` is defined by endpoints of distinct paths of one common minimum cover.
On a saturated complete join `U = A ∪ B` with excess `q = p(U) ≥ 2`,
`D(U) = D(A)`: the marked `x`-chain is always merged with an unmarked third
path, leaving the `y`-path untouched; reverse deletion retains distinct
descendants in disjoint parent supports. No `D` identity is claimed for `q = 1`.

On a no-cross disjoint union, independently witnessed child covers concatenate,
so every eligible cross pair is `D`-adjacent.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma endpoint_mem_support {p : GraphPath G} {x : V}
    (hx : x = p.start ∨ x = p.finish) : x ∈ p.support := by
  rcases hx with hx | hx
  · rw [hx]; exact p.start_mem_support
  · rw [hx]; exact p.finish_mem_support

lemma exists_third_path {U : Finset V} (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths)
    (hne : p ≠ q) (h3 : 3 ≤ pc.card) :
    ∃ r, r ∈ pc.paths ∧ r ≠ p ∧ r ≠ q := by
  have hlen :=
    PathCover.length_filter_ne_two (a := p) (b := q) hp hq hne pc.nodup_paths
  have hpos :
      0 < ((pc.paths.filter fun x => decide (x ≠ p)).filter
        fun x => decide (x ≠ q)).length := by
    have : 3 ≤ pc.paths.length := by simpa [PathCover.card] using h3
    omega
  rw [List.length_pos_iff_exists_mem] at hpos
  obtain ⟨r, hr⟩ := hpos
  have hr1 := List.mem_filter.1 hr
  have hr0 := List.mem_filter.1 hr1.1
  exact ⟨r, hr0.1, of_decide_eq_true hr0.2, of_decide_eq_true hr1.2⟩

lemma exists_deleteVertex_keepDistinct {U : Finset V}
    (pc : PathCover G U) {x y f : V} {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hx : x = p.start ∨ x = p.finish)
    (hy : y = q.start ∨ y = q.finish)
    (hxf : x ≠ f) (hyf : y ≠ f) :
    ∃ p' q', p' ∈ (pc.deleteVertex f).paths ∧ q' ∈ (pc.deleteVertex f).paths ∧
      p' ≠ q' ∧ (x = p'.start ∨ x = p'.finish) ∧
        (y = q'.start ∨ y = q'.finish) := by
  obtain ⟨p', hp', hxp'⟩ := GraphPath.exists_mem_deleteVertex_endpoint p hx hxf
  obtain ⟨q', hq', hyq'⟩ := GraphPath.exists_mem_deleteVertex_endpoint q hy hyf
  refine ⟨p', q', List.mem_flatMap.2 ⟨p, hp, hp'⟩,
    List.mem_flatMap.2 ⟨q, hq, hq'⟩, ?_, hxp', hyq'⟩
  intro heq
  have hps : p'.support ⊆ p.support :=
    GraphPath.support_subset_of_mem_deleteVertex hp'
  have hxsup : x ∈ p'.support := endpoint_mem_support hxp'
  have hysup : y ∈ q'.support := endpoint_mem_support hyq'
  have hyP : y ∈ p.support := by
    have : y ∈ p'.support := by rwa [heq]
    exact hps this
  have hyQ : y ∈ q.support := endpoint_mem_support hy
  exact Finset.disjoint_left.1
    (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne) hyP hyQ

lemma exists_deleteFinset_keepDistinct {U S : Finset V}
    (pc : PathCover G U) (hS : S ⊆ U) {x y : V} {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hx : x = p.start ∨ x = p.finish)
    (hy : y = q.start ∨ y = q.finish)
    (hxS : x ∉ S) (hyS : y ∉ S) :
    ∃ (pc' : PathCover G (U \ S)) (p' q' : GraphPath G),
      pc'.card ≤ pc.card + S.card ∧
        p' ∈ pc'.paths ∧ q' ∈ pc'.paths ∧ p' ≠ q' ∧
          (x = p'.start ∨ x = p'.finish) ∧
            (y = q'.start ∨ y = q'.finish) := by
  induction S using Finset.induction generalizing U pc p q with
  | empty =>
    refine ⟨pc.cast (by simp), p, q, ?_, ?_, ?_, hne, hx, hy⟩
    · simp [PathCover.cast_card]
    · rw [PathCover.cast_paths]; exact hp
    · rw [PathCover.cast_paths]; exact hq
  | insert b S hb ih =>
    have hbU : b ∈ U := hS (mem_insert_self b S)
    have hSsub : S ⊆ U.erase b := by
      intro z hz
      exact mem_erase.2 ⟨fun hzb => hb (hzb ▸ hz), hS (mem_insert_of_mem hz)⟩
    have hxb : x ≠ b := fun h => hxS (by simp [h])
    have hyb : y ≠ b := fun h => hyS (by simp [h])
    obtain ⟨p1, q1, hp1, hq1, hne1, hx1, hy1⟩ :=
      exists_deleteVertex_keepDistinct pc hp hq hne hx hy hxb hyb
    have hxS' : x ∉ S := fun h => hxS (mem_insert_of_mem h)
    have hyS' : y ∉ S := fun h => hyS (mem_insert_of_mem h)
    obtain ⟨pc1, p2, q2, hcard1, hp2, hq2, hne2, hx2, hy2⟩ :=
      ih (U := U.erase b) (pc.deleteVertex b) hSsub hp1 hq1 hne1 hx1 hy1 hxS' hyS'
    have hEq : U.erase b \ S = U \ insert b S := by
      rw [sdiff_insert, erase_sdiff_comm]
    refine ⟨pc1.cast hEq, p2, q2, ?_, ?_, ?_, hne2, hx2, hy2⟩
    · have hdv := pc.card_deleteVertex_le b
      have hcard := card_insert_of_notMem (s := S) hb
      rw [PathCover.cast_card]
      omega
    · rw [PathCover.cast_paths]; exact hp2
    · rw [PathCover.cast_paths]; exact hq2

/-- Reverse `D` inheritance on a dominant complete join: deleting `B` never
merges old cover paths. -/
lemma DistinctPathCompatible_of_dominant {A B : Finset V} {x y : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hD : DistinctPathCompatible (G := G) (A ∪ B) x y) :
    DistinctPathCompatible (G := G) A x y := by
  obtain ⟨hne, pcU, hU, p, hp, q, hq, hpq, hx, hy⟩ := hD
  have hxE : Eligible G (A ∪ B) x := ⟨pcU, hU, p, hp, hx⟩
  have hyE : Eligible G (A ∪ B) y := ⟨pcU, hU, q, hq, hy⟩
  have hxA := eligible_mem_left_of_dominant hAne hBne hAB hdom hxE
  have hyA := eligible_mem_left_of_dominant hAne hBne hAB hdom hyE
  have hdisj := disjoint_of_completeBetween hAB
  have hxB : x ∉ B := fun h => Finset.disjoint_left.1 hdisj hxA h
  have hyB : y ∉ B := fun h => Finset.disjoint_left.1 hdisj hyA h
  obtain ⟨pc1, p', q', hcard1, hp', hq', hne', hx', hy'⟩ :=
    exists_deleteFinset_keepDistinct (U := A ∪ B) (S := B)
      pcU subset_union_right hp hq hpq hx hy hxB hyB
  have hEq : (A ∪ B) \ B = A := union_sdiff_eq_left_of_disjoint hdisj
  let pcA : PathCover G A := pc1.cast hEq
  have hsat := pathCoverNumber_add_card_of_dominant hAne hBne hAB hdom
  have hmin : pcA.card = pathCoverNumber G A := by
    have hle := pathCoverNumber_le (G := G) pcA
    have hcard : pcA.card ≤ pathCoverNumber G A := by
      rw [PathCover.cast_card]; omega
    omega
  refine ⟨hne, pcA, hmin, p', ?_, q', ?_, hne', hx', hy'⟩
  · rw [PathCover.cast_paths]; exact hp'
  · rw [PathCover.cast_paths]; exact hq'

lemma exists_orientStart_marked_keepOther {A U : Finset V} {x y : V}
    (pc : PathCover G U) {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hx : x = p.start ∨ x = p.finish)
    (hy : y = q.start ∨ y = q.finish)
    (hend : ∀ s ∈ pc.paths, s.start ∈ A ∧ s.finish ∈ A) :
    ∃ (pc' : PathCover G U) (p' q' : GraphPath G),
      pc'.card = pc.card ∧
        p' ∈ pc'.paths ∧ q' ∈ pc'.paths ∧ p' ≠ q' ∧
          p'.start = x ∧ (y = q'.start ∨ y = q'.finish) ∧
            (∀ s ∈ pc'.paths, s.start ∈ A ∧ s.finish ∈ A) := by
  by_cases hs : x = p.start
  · exact ⟨pc, p, q, rfl, hp, hq, hne, hs.symm, hy, hend⟩
  · have hf : x = p.finish := hx.resolve_left hs
    let r := p.reverse
    have hr : r.support = p.support := GraphPath.support_reverse p
    have hrne : r ≠ q := by
      intro heq
      have hxsup : x ∈ p.support := endpoint_mem_support hx
      have hxq : x ∈ q.support := by
        have : x ∈ r.support := by rwa [hr]
        rwa [heq] at this
      exact Finset.disjoint_left.1
        (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne) hxsup hxq
    have hq' : q ∈ (pc.replacePath_sat hp r hr).paths := by
      refine List.mem_append.mpr (Or.inl (List.mem_filter.2 ⟨hq, ?_⟩))
      exact decide_eq_true hne.symm
    refine ⟨pc.replacePath_sat hp r hr, r, q,
      pc.replacePath_sat_card hp r hr,
      pc.replacePath_sat_self_mem hp r hr, hq', hrne, ?_, hy, ?_⟩
    · simp [r, PathCover.GraphPath.start_reverse, hf]
    · intro s hs'
      rcases pc.replacePath_sat_mem_paths hp r hr hs' with hsr | ⟨hspc, _⟩
      · subst hsr
        rw [PathCover.GraphPath.start_reverse, PathCover.GraphPath.finish_reverse]
        exact ⟨(hend p hp).2, (hend p hp).1⟩
      · exact hend s hspc

lemma exists_marked_splice_two_through_avoid {A B U : Finset V} {b x y : V}
    {p qy : GraphPath G}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (pc : PathCover G U) (hp : p ∈ pc.paths) (hqy : qy ∈ pc.paths)
    (hne : p ≠ qy) (hstart : p.start = x)
    (hy : y = qy.start ∨ y = qy.finish)
    (h3 : 3 ≤ pc.card)
    (hend : ∀ s ∈ pc.paths, s.start ∈ A ∧ s.finish ∈ A)
    (hb : b ∈ B) (hbU : b ∉ U) :
    ∃ (pc' : PathCover G (insert b U)) (p' qy' : GraphPath G),
      pc'.card = pc.card - 1 ∧
        p' ∈ pc'.paths ∧ qy' ∈ pc'.paths ∧ p' ≠ qy' ∧
          p'.start = x ∧ (y = qy'.start ∨ y = qy'.finish) ∧
            (∀ s ∈ pc'.paths, s.start ∈ A ∧ s.finish ∈ A) := by
  obtain ⟨r, hr, hrp, hrq⟩ := exists_third_path pc hp hqy hne h3
  have hpb : b ∉ p.support := fun h => hbU (pc.support_subset hp h)
  have hrb : b ∉ r.support := fun h => hbU (pc.support_subset hr h)
  obtain ⟨s, hs, hss, hsf⟩ :=
    exists_spliceABA hAB p b r (hend p hp).2 hb (hend r hr).1 hpb hrb
      (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hr hrp.symm)
  have hqyKeep : qy ∈
      (pc.spliceTwoInsert hp hr hrp.symm b hbU s hs).paths := by
    refine List.mem_append.mpr (Or.inl ?_)
    exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hqy, decide_eq_true hne.symm⟩,
      decide_eq_true hrq.symm⟩
  have hsne : s ≠ qy := by
    intro heq
    have hbq : b ∈ qy.support := by
      have : b ∈ s.support := by
        rw [hs]
        exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_singleton_self b))))
      rwa [heq] at this
    exact hbU (pc.support_subset hqy hbq)
  refine ⟨pc.spliceTwoInsert hp hr hrp.symm b hbU s hs, s, qy,
    pc.spliceTwoInsert_card hp hr hrp.symm b hbU s hs,
    List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)),
    hqyKeep, hsne, hss.trans hstart, hy, ?_⟩
  intro t ht
  rcases pc.spliceTwoInsert_mem_paths hp hr hrp.symm b hbU s hs ht with hts | ⟨htpc, _, _⟩
  · subst hts
    rw [hss, hsf]
    exact ⟨(hend p hp).1, (hend r hr).2⟩
  · exact hend t htpc

/-- Dominant-child construction preserving two distinct marks: the `x`-chain
is always the left splice operand, the `y`-path is never the merge partner,
and before each insertion the cover has at least three paths. -/
lemma exists_pathCover_complete_join_dominant_twoMarked {A B : Finset V}
    {x y : V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hq : 2 ≤ pathCoverNumber G A - B.card)
    (hD : DistinctPathCompatible (G := G) A x y) :
    ∃ (pc : PathCover G (A ∪ B)) (p q : GraphPath G),
      pc.card = pathCoverNumber G A - B.card ∧
        p ∈ pc.paths ∧ q ∈ pc.paths ∧ p ≠ q ∧
          (x = p.start ∨ x = p.finish) ∧
            (y = q.start ∨ y = q.finish) := by
  obtain ⟨hne, pc0, h0, p0, hp0, q0, hq0, hpq0, hxend, hyend⟩ := hD
  have hend0 : ∀ s ∈ pc0.paths, s.start ∈ A ∧ s.finish ∈ A := by
    intro s hs
    exact ⟨pc0.support_subset hs s.start_mem_support,
      pc0.support_subset hs s.finish_mem_support⟩
  obtain ⟨pc0o, p0o, q0o, hcard0o, hp0o, hq0o, hne0o, hstart0, hy0, hend0o⟩ :=
    exists_orientStart_marked_keepOther (A := A) pc0 hp0 hq0 hpq0 hxend hyend hend0
  have aux :
      ∀ (k : ℕ) (S : Finset V) (pc : PathCover G (A ∪ S))
        (p qy : GraphPath G),
        S ⊆ B → (B \ S).card = k →
          pc.card = pathCoverNumber G A - S.card →
            p ∈ pc.paths → qy ∈ pc.paths → p ≠ qy →
              p.start = x → (y = qy.start ∨ y = qy.finish) →
                (∀ s ∈ pc.paths, s.start ∈ A ∧ s.finish ∈ A) →
                  ∃ (pc' : PathCover G (A ∪ B)) (p' q' : GraphPath G),
                    pc'.card = pathCoverNumber G A - B.card ∧
                      p' ∈ pc'.paths ∧ q' ∈ pc'.paths ∧ p' ≠ q' ∧
                        (x = p'.start ∨ x = p'.finish) ∧
                          (y = q'.start ∨ y = q'.finish) := by
    intro k
    induction k with
    | zero =>
      intro S pc p qy hS hk hcard hp hqy hne pqstart hyend' hend
      have hBS : B \ S = ∅ := Finset.card_eq_zero.mp hk
      have hBeq : S = B :=
        subset_antisymm hS (sdiff_eq_empty_iff_subset.mp hBS)
      subst hBeq
      exact ⟨pc, p, qy, hcard, hp, hqy, hne, Or.inl pqstart.symm, hyend'⟩
    | succ k ih =>
      intro S pc p qy hS hk hcard hp hqy hne pqstart hyend' hend
      have hneS : (B \ S).Nonempty :=
        card_pos.mp (by omega : 0 < (B \ S).card)
      obtain ⟨b, hb⟩ := hneS
      have hbB : b ∈ B := (mem_sdiff.1 hb).1
      have hbS : b ∉ S := (mem_sdiff.1 hb).2
      have hdisjAB := disjoint_of_completeBetween hAB
      have hbU : b ∉ A ∪ S := by
        intro h
        rcases mem_union.1 h with hA | hS'
        · exact Finset.disjoint_left.1 hdisjAB hA hbB
        · exact hbS hS'
      have hsum : S.card + (B \ S).card = B.card := by
        rw [← card_union_of_disjoint, union_sdiff_of_subset hS]
        exact disjoint_sdiff
      have h3 : 3 ≤ pc.card := by omega
      obtain ⟨pc1, p1, q1, hcard1, hp1, hq1, hne1, hstart1, hy1, hend1⟩ :=
        exists_marked_splice_two_through_avoid (x := x) (y := y) (p := p)
          (qy := qy) hAB pc hp hqy hne pqstart hyend' h3 hend hbB hbU
      have hU : insert b (A ∪ S) = A ∪ insert b S := by
        ext z
        simp [mem_insert, mem_union]
      let pc1' : PathCover G (A ∪ insert b S) := pc1.cast hU
      have hS' : insert b S ⊆ B := insert_subset hbB hS
      have hrem : B \ insert b S = (B \ S).erase b := sdiff_insert B S b
      have hk' : (B \ insert b S).card = k := by
        rw [hrem, card_erase_of_mem hb, hk]
        omega
      have hcard' : pc1'.card = pathCoverNumber G A - (insert b S).card := by
        rw [PathCover.cast_card, hcard1, hcard, card_insert_of_notMem hbS]
        omega
      have hp1' : p1 ∈ pc1'.paths := by
        rw [PathCover.cast_paths pc1 hU]; exact hp1
      have hq1' : q1 ∈ pc1'.paths := by
        rw [PathCover.cast_paths pc1 hU]; exact hq1
      have hend1' : ∀ s ∈ pc1'.paths, s.start ∈ A ∧ s.finish ∈ A := by
        intro s hs
        rw [PathCover.cast_paths pc1 hU] at hs
        exact hend1 s hs
      exact ih (insert b S) pc1' p1 q1 hS' hk' hcard' hp1' hq1' hne1
        hstart1 hy1 hend1'
  have hA : A ∪ (∅ : Finset V) = A := union_empty A
  let pc0' : PathCover G (A ∪ ∅) := pc0o.cast hA.symm
  have hcard0 : pc0'.card = pathCoverNumber G A - (∅ : Finset V).card := by
    rw [PathCover.cast_card, hcard0o, h0, card_empty, Nat.sub_zero]
  have hp0' : p0o ∈ pc0'.paths := by
    rw [PathCover.cast_paths pc0o hA.symm]; exact hp0o
  have hq0' : q0o ∈ pc0'.paths := by
    rw [PathCover.cast_paths pc0o hA.symm]; exact hq0o
  have hend0' : ∀ s ∈ pc0'.paths, s.start ∈ A ∧ s.finish ∈ A := by
    intro s hs
    rw [PathCover.cast_paths pc0o hA.symm] at hs
    exact hend0o s hs
  exact aux B.card ∅ pc0' p0o q0o (empty_subset B) (by simp) hcard0
    hp0' hq0' hne0o hstart0 hy0 hend0'

lemma DistinctPathCompatible_of_dominant_left {A B : Finset V} {x y : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hq : 2 ≤ pathCoverNumber G (A ∪ B))
    (hD : DistinctPathCompatible (G := G) A x y) :
    DistinctPathCompatible (G := G) (A ∪ B) x y := by
  have hq' : 2 ≤ pathCoverNumber G A - B.card := by
    have h := pathCoverNumber_eq_sub_of_dominant hAne hBne hAB hdom
    omega
  obtain ⟨pc, p, q, hpc, hp, hqP, hne, hx, hy⟩ :=
    exists_pathCover_complete_join_dominant_twoMarked hAB hdom hq' hD
  have hmin : pc.card = pathCoverNumber G (A ∪ B) := by
    have hj := pathCoverNumber_eq_sub_of_dominant hAne hBne hAB hdom
    omega
  exact ⟨hD.1, pc, hmin, p, hp, q, hqP, hne, hx, hy⟩

/-- Saturated complete join with excess `q ≥ 2`: `D(U) = D(A)` as relations. -/
lemma DistinctPathCompatible_complete_join_dominant_iff {A B : Finset V}
    {x y : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hq : 2 ≤ pathCoverNumber G (A ∪ B)) :
    DistinctPathCompatible (G := G) (A ∪ B) x y ↔
      DistinctPathCompatible (G := G) A x y :=
  ⟨DistinctPathCompatible_of_dominant hAne hBne hAB hdom,
    DistinctPathCompatible_of_dominant_left hAne hBne hAB hdom hq⟩

lemma distinctPathGraph_complete_join_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hq : 2 ≤ pathCoverNumber G (A ∪ B)) :
    distinctPathGraph (G := G) (A ∪ B) = distinctPathGraph (G := G) A := by
  ext x y
  exact DistinctPathCompatible_complete_join_dominant_iff
    hAne hBne hAB hdom hq

/-! Disjoint-union `D` completeness. -/

lemma DistinctPathCompatible_union_left {A B : Finset V} {x y : V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hD : DistinctPathCompatible (G := G) A x y) :
    DistinctPathCompatible (G := G) (A ∪ B) x y := by
  obtain ⟨hne, pcA, hA, p, hp, q, hq, hpq, hx, hy⟩ := hD
  obtain ⟨pcB, hB⟩ := exists_min_pathCover (G := G) B
  let pc := PathCover.unionDisjoint hdisj pcA pcB
  have hmin : pc.card = pathCoverNumber G (A ∪ B) := by
    rw [PathCover.unionDisjoint_card hdisj, hA, hB,
      pathCoverNumber_disjoint_union (G := G) hdisj hnocross]
  refine ⟨hne, pc, hmin, p, List.mem_append.mpr (Or.inl hp),
    q, List.mem_append.mpr (Or.inl hq), hpq, hx, hy⟩

lemma DistinctPathCompatible_union_right {A B : Finset V} {x y : V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hD : DistinctPathCompatible (G := G) B x y) :
    DistinctPathCompatible (G := G) (A ∪ B) x y := by
  obtain ⟨hne, pcB, hB, p, hp, q, hq, hpq, hx, hy⟩ := hD
  obtain ⟨pcA, hA⟩ := exists_min_pathCover (G := G) A
  let pc := PathCover.unionDisjoint hdisj pcA pcB
  have hmin : pc.card = pathCoverNumber G (A ∪ B) := by
    rw [PathCover.unionDisjoint_card hdisj, hA, hB,
      pathCoverNumber_disjoint_union (G := G) hdisj hnocross]
  refine ⟨hne, pc, hmin, p, List.mem_append.mpr (Or.inr hp),
    q, List.mem_append.mpr (Or.inr hq), hpq, hx, hy⟩

lemma DistinctPathCompatible_union_cross {A B : Finset V} {x y : V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hx : Eligible G A x) (hy : Eligible G B y) :
    DistinctPathCompatible (G := G) (A ∪ B) x y := by
  have hxA : x ∈ A := Eligible.mem (G := G) hx
  have hyB : y ∈ B := Eligible.mem (G := G) hy
  have hne : x ≠ y := fun hxy =>
    Finset.disjoint_left.1 hdisj hxA (hxy ▸ hyB)
  obtain ⟨pcA, hA, p, hp, hxend⟩ := hx
  obtain ⟨pcB, hB, q, hq, hyend⟩ := hy
  have hpq : p ≠ q := by
    intro heq
    have hxP : x ∈ p.support := endpoint_mem_support hxend
    have hyQ : y ∈ q.support := endpoint_mem_support hyend
    have hxA : x ∈ A := pcA.support_subset hp hxP
    have hyB : y ∈ B := pcB.support_subset hq hyQ
    have : x ∈ q.support := by rwa [heq] at hxP
    have hxB : x ∈ B := pcB.support_subset hq this
    exact Finset.disjoint_left.1 hdisj hxA hxB
  let pc := PathCover.unionDisjoint hdisj pcA pcB
  have hmin : pc.card = pathCoverNumber G (A ∪ B) := by
    rw [PathCover.unionDisjoint_card hdisj, hA, hB,
      pathCoverNumber_disjoint_union (G := G) hdisj hnocross]
  exact ⟨hne, pc, hmin, p, List.mem_append.mpr (Or.inl hp),
    q, List.mem_append.mpr (Or.inr hq), hpq, hxend, hyend⟩

lemma DistinctPathCompatible_union_of_left {A B : Finset V} {x y : V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hD : DistinctPathCompatible (G := G) (A ∪ B) x y) :
    DistinctPathCompatible (G := G) A x y := by
  obtain ⟨hne, pc, hpc, p, hp, q, hq, hpq, hx, hy⟩ := hD
  have hminA := splitLeft_card_eq_of_min hdisj hnocross pc hpc
  have hpL : p ∈ (PathCover.splitLeft hdisj hnocross pc).paths := by
    have hstartA : p.start ∈ A := by
      have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp
      have hxP : x ∈ p.support := endpoint_mem_support hx
      have : p.support ⊆ A := by
        have hstartAB : p.start ∈ A ∨ p.start ∈ B := by
          simpa [mem_union] using hsupp p.start_mem_support
        rcases hstartAB with hA | hB
        · exact GraphPath.support_subset_of_no_cross hnocross p hA hsupp
        · have hBsup := GraphPath.support_subset_of_no_cross' hnocross p hB hsupp
          exact (Finset.disjoint_left.1 hdisj hxA (hBsup hxP)).elim
      exact this p.start_mem_support
    exact List.mem_filter.2 ⟨hp, decide_eq_true hstartA⟩
  have hqL : q ∈ (PathCover.splitLeft hdisj hnocross pc).paths := by
    have hstartA : q.start ∈ A := by
      have hsupp : q.support ⊆ A ∪ B := pc.support_subset hq
      have hyQ : y ∈ q.support := endpoint_mem_support hy
      have : q.support ⊆ A := by
        have hstartAB : q.start ∈ A ∨ q.start ∈ B := by
          simpa [mem_union] using hsupp q.start_mem_support
        rcases hstartAB with hA | hB
        · exact GraphPath.support_subset_of_no_cross hnocross q hA hsupp
        · have hBsup := GraphPath.support_subset_of_no_cross' hnocross q hB hsupp
          exact (Finset.disjoint_left.1 hdisj hyA (hBsup hyQ)).elim
      exact this q.start_mem_support
    exact List.mem_filter.2 ⟨hq, decide_eq_true hstartA⟩
  exact ⟨hne, PathCover.splitLeft hdisj hnocross pc, hminA, p, hpL, q, hqL,
    hpq, hx, hy⟩

lemma DistinctPathCompatible.symm {U : Finset V} {x y : V}
    (h : DistinctPathCompatible (G := G) U x y) :
    DistinctPathCompatible (G := G) U y x := by
  obtain ⟨hne, pc, hpc, p, hp, q, hq, hpq, hx, hy⟩ := h
  exact ⟨hne.symm, pc, hpc, q, hq, p, hp, hpq.symm, hy, hx⟩

lemma not_DistinctPathCompatible_of_le_one {U : Finset V} {x y : V}
    (h : pathCoverNumber G U ≤ 1) :
    ¬ DistinctPathCompatible (G := G) U x y := by
  intro hD
  have hadj : (distinctPathGraph (G := G) U).Adj x y := hD
  have hbot := distinctPathGraph_eq_bot_of_pathCoverNumber_le_one (G := G) h
  rw [hbot] at hadj
  exact hadj.elim

lemma eligible_mem_of_mem_eligibleSet {U : Finset V} {x : V}
    (hx : x ∈ eligibleSet G U) : Eligible G U x :=
  (mem_eligibleSet_iff (G := G)).1 hx |>.2

/-- On a cotree carrier, D-nonadjacency is transitive on eligible vertices.
Thus the complementary relation of D on E(U) is a complete multipartite
graph whose parts are the D-nonadjacent classes. -/
lemma not_DistinctPathCompatible_trans_of_cotreeOn {U : Finset V}
    (hU : CotreeOn G U) {x y z : V}
    (hx : x ∈ eligibleSet G U) (hy : y ∈ eligibleSet G U)
    (hz : z ∈ eligibleSet G U)
    (hxy : ¬ DistinctPathCompatible (G := G) U x y)
    (hyz : ¬ DistinctPathCompatible (G := G) U y z) :
    ¬ DistinctPathCompatible (G := G) U x z := by
  induction hU generalizing x y z with
  | empty =>
    exact (notMem_empty x ((eligibleSet_subset (G := G) ∅) hx)).elim
  | singleton v =>
    have hx' : x = v := mem_singleton.1 ((eligibleSet_subset (G := G) {v}) hx)
    have hz' : z = v := mem_singleton.1 ((eligibleSet_subset (G := G) {v}) hz)
    intro hD
    exact hD.1 (hx'.trans hz'.symm)
  | disjointUnion hdisj hnocross hA hB ihA ihB =>
    rename_i A B
    have hEU := eligibleSet_disjoint_union (G := G) hdisj hnocross
    have hxU : x ∈ A ∪ B := eligibleSet_subset (G := G) (A ∪ B) hx
    have hyU : y ∈ A ∪ B := eligibleSet_subset (G := G) (A ∪ B) hy
    have hzU : z ∈ A ∪ B := eligibleSet_subset (G := G) (A ∪ B) hz
    have side (w : V) (hw : w ∈ eligibleSet G (A ∪ B)) :
        w ∈ eligibleSet G A ∨ w ∈ eligibleSet G B := by
      rw [hEU] at hw
      exact mem_union.1 hw
    have crossD {u w : V}
        (huA : u ∈ eligibleSet G A) (hwB : w ∈ eligibleSet G B) :
        DistinctPathCompatible (G := G) (A ∪ B) u w :=
      DistinctPathCompatible_union_cross hdisj hnocross
        (eligible_mem_of_mem_eligibleSet huA)
        (eligible_mem_of_mem_eligibleSet hwB)
    rcases side x hx with hxA | hxB
    · rcases side y hy with hyA | hyB
      · rcases side z hz with hzA | hzB
        · have hxyA : ¬ DistinctPathCompatible (G := G) A x y := by
            intro hD
            exact hxy (DistinctPathCompatible_union_left hdisj hnocross hD)
          have hyzA : ¬ DistinctPathCompatible (G := G) A y z := by
            intro hD
            exact hyz (DistinctPathCompatible_union_left hdisj hnocross hD)
          have hxzA := ihA hxA hyA hzA hxyA hyzA
          intro hD
          exact hxzA (DistinctPathCompatible_union_of_left hdisj hnocross
            (eligibleSet_subset (G := G) A hxA)
            (eligibleSet_subset (G := G) A hzA) hD)
        · exact (hyz (crossD hyA hzB)).elim
      · exact (hxy (crossD hxA hyB)).elim
    · rcases side y hy with hyA | hyB
      · exact (hxy (DistinctPathCompatible.symm (crossD hyA hxB))).elim
      · rcases side z hz with hzA | hzB
        · exact (hyz (DistinctPathCompatible.symm (crossD hzA hyB))).elim
        · have hxyB : ¬ DistinctPathCompatible (G := G) B x y := by
            intro hD
            exact hxy (DistinctPathCompatible_union_right hdisj hnocross hD)
          have hyzB : ¬ DistinctPathCompatible (G := G) B y z := by
            intro hD
            exact hyz (DistinctPathCompatible_union_right hdisj hnocross hD)
          have hxzB := ihB hxB hyB hzB hxyB hyzB
          intro hD
          have hxB' : x ∈ B := eligibleSet_subset (G := G) B hxB
          have hzB' : z ∈ B := eligibleSet_subset (G := G) B hzB
          have hdisj' : Disjoint B A := hdisj.symm
          have hnocross' : ∀ b ∈ B, ∀ a ∈ A, ¬ G.Adj b a := fun b hb a ha hab =>
            hnocross a ha b hb hab.symm
          have hD' : DistinctPathCompatible (G := G) (B ∪ A) x z := by
            simpa [union_comm] using hD
          exact hxzB (DistinctPathCompatible_union_of_left hdisj' hnocross'
            hxB' hzB' hD')
  | completeJoin hAne hBne hAB hA hB ihA ihB =>
    rename_i A B
    by_cases hAdom : B.card < pathCoverNumber G A
    · have hpU := pathCoverNumber_eq_sub_of_dominant hAne hBne hAB hAdom
      by_cases hq : 2 ≤ pathCoverNumber G (A ∪ B)
      · have hE := eligibleSet_complete_join_dominant hAne hBne hAB hAdom
        have hxA : x ∈ eligibleSet G A := by rwa [← hE]
        have hyA : y ∈ eligibleSet G A := by rwa [← hE]
        have hzA : z ∈ eligibleSet G A := by rwa [← hE]
        have hiff :=
          DistinctPathCompatible_complete_join_dominant_iff
            (x := x) (y := y) hAne hBne hAB hAdom hq
        have hiffyz :=
          DistinctPathCompatible_complete_join_dominant_iff
            (x := y) (y := z) hAne hBne hAB hAdom hq
        have hiffxz :=
          DistinctPathCompatible_complete_join_dominant_iff
            (x := x) (y := z) hAne hBne hAB hAdom hq
        have hxyA : ¬ DistinctPathCompatible (G := G) A x y := by
          intro hD; exact hxy (hiff.2 hD)
        have hyzA : ¬ DistinctPathCompatible (G := G) A y z := by
          intro hD; exact hyz (hiffyz.2 hD)
        have hxzA := ihA hxA hyA hzA hxyA hyzA
        intro hD
        exact hxzA (hiffxz.1 hD)
      · have hq1 : pathCoverNumber G (A ∪ B) ≤ 1 := by omega
        exact not_DistinctPathCompatible_of_le_one hq1
    · by_cases hBdom : A.card < pathCoverNumber G B
      · have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
          fun {b} hb {a} ha => (hAB ha hb).symm
        have hpU := pathCoverNumber_eq_sub_of_dominant hBne hAne hBA hBdom
        by_cases hq : 2 ≤ pathCoverNumber G (A ∪ B)
        · have hqB : 2 ≤ pathCoverNumber G (B ∪ A) := by simpa [union_comm] using hq
          have hE : eligibleSet G (A ∪ B) = eligibleSet G B := by
            simpa [union_comm] using
              eligibleSet_complete_join_dominant hBne hAne hBA hBdom
          have hxB : x ∈ eligibleSet G B := by rwa [← hE]
          have hyB : y ∈ eligibleSet G B := by rwa [← hE]
          have hzB : z ∈ eligibleSet G B := by rwa [← hE]
          have hiff :=
            DistinctPathCompatible_complete_join_dominant_iff
              (x := x) (y := y) hBne hAne hBA hBdom hqB
          have hiffyz :=
            DistinctPathCompatible_complete_join_dominant_iff
              (x := y) (y := z) hBne hAne hBA hBdom hqB
          have hiffxz :=
            DistinctPathCompatible_complete_join_dominant_iff
              (x := x) (y := z) hBne hAne hBA hBdom hqB
          have hxyB : ¬ DistinctPathCompatible (G := G) B x y := by
            intro hD
            have hD' : DistinctPathCompatible (G := G) (B ∪ A) x y := hiff.2 hD
            exact hxy (by simpa [union_comm] using hD')
          have hyzB : ¬ DistinctPathCompatible (G := G) B y z := by
            intro hD
            have hD' : DistinctPathCompatible (G := G) (B ∪ A) y z := hiffyz.2 hD
            exact hyz (by simpa [union_comm] using hD')
          have hxzB := ihB hxB hyB hzB hxyB hyzB
          intro hD
          have hD' : DistinctPathCompatible (G := G) (B ∪ A) x z := by
            simpa [union_comm] using hD
          exact hxzB (hiffxz.1 hD')
        · have hq1 : pathCoverNumber G (A ∪ B) ≤ 1 := by omega
          exact not_DistinctPathCompatible_of_le_one hq1
      · have hpA : pathCoverNumber G A ≤ B.card := Nat.le_of_not_gt hAdom
        have hpB : pathCoverNumber G B ≤ A.card := Nat.le_of_not_gt hBdom
        have hp := pathCoverNumber_complete_join hAne hBne hAB
        have hmax :
            max 1 (max (pathCoverNumber G A - B.card)
              (pathCoverNumber G B - A.card)) = 1 := by
          simp [Nat.sub_eq_zero_of_le hpA, Nat.sub_eq_zero_of_le hpB]
        have hp1 : pathCoverNumber G (A ∪ B) = 1 := hp.trans hmax
        exact not_DistinctPathCompatible_of_le_one (by omega)

lemma not_DistinctPathCompatible_trans_of_isCograph {U : Finset V}
    (hU : IsCograph G U) {x y z : V}
    (hx : x ∈ eligibleSet G U) (hy : y ∈ eligibleSet G U)
    (hz : z ∈ eligibleSet G U)
    (hxy : ¬ DistinctPathCompatible (G := G) U x y)
    (hyz : ¬ DistinctPathCompatible (G := G) U y z) :
    ¬ DistinctPathCompatible (G := G) U x z :=
  not_DistinctPathCompatible_trans_of_cotreeOn (cotreeOn_of_isCograph hU)
    hx hy hz hxy hyz

lemma not_DistinctPathCompatible_trans_of_canonical {U : Finset V}
    (hU : Nikoghosyan.IsCograph G U) {x y z : V}
    (hx : x ∈ eligibleSet G U) (hy : y ∈ eligibleSet G U)
    (hz : z ∈ eligibleSet G U)
    (hxy : ¬ DistinctPathCompatible (G := G) U x y)
    (hyz : ¬ DistinctPathCompatible (G := G) U y z) :
    ¬ DistinctPathCompatible (G := G) U x z :=
  not_DistinctPathCompatible_trans_of_isCograph (isCograph_iff.2 hU)
    hx hy hz hxy hyz

end Cograph
end Nikoghosyan
