/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.PartCuts
import Nikoghosyan.Cograph.MultiJoin

/-!
# Spanning-path endpoint classes on a critical complete join

Manuscript `cog:prop:hamilton-endpoints`, critical child: if `H = X ∨ Y`
is a complete original join with `r = |Y| ≥ 1` and `p(X) = r+1`, then
`p(H)=1`, `E(H)=E(X)`, `F(H)=Y ∪ F(X)`, and the spanning-path relation
satisfies `R(H)=D(X)`. The old `q ≥ 2` distinct-path identity is not this
`q=1` spanning-path identity.

Forward: one minimum `X`-cover carrying the two marks on distinct paths is
oriented at opposite exterior ends and chained through the `r` original
`Y`-singletons. Reverse: the first internal `Y` deletion of a spanning
`H`-path splits the two exterior ends onto distinct pieces; iterated
`exists_deleteFinset_keepDistinct` then yields a minimum `X`-cover.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma pathCoverNumber_eq_one_of_critical {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1) :
    pathCoverNumber G (A ∪ B) = 1 := by
  have hdom : B.card < pathCoverNumber G A := by omega
  have h := pathCoverNumber_eq_sub_of_dominant hAne hBne hAB hdom
  omega

lemma eligibleSet_complete_join_critical {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1) :
    eligibleSet G (A ∪ B) = eligibleSet G A :=
  eligibleSet_complete_join_dominant hAne hBne hAB (by omega)

lemma ineligibleSet_complete_join_critical {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1) :
    ineligibleSet G (A ∪ B) = B ∪ ineligibleSet G A :=
  ineligibleSet_complete_join_dominant hAne hBne hAB (by omega)

lemma exists_orientFinish_keepStart {A U : Finset V} {x y : V}
    (pc : PathCover G U) {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hstart : p.start = x)
    (hy : y = q.start ∨ y = q.finish)
    (hend : ∀ s ∈ pc.paths, s.start ∈ A ∧ s.finish ∈ A) :
    ∃ (pc' : PathCover G U) (p' q' : GraphPath G),
      pc'.card = pc.card ∧
        p' ∈ pc'.paths ∧ q' ∈ pc'.paths ∧ p' ≠ q' ∧
          p'.start = x ∧ q'.finish = y ∧
            (∀ s ∈ pc'.paths, s.start ∈ A ∧ s.finish ∈ A) := by
  by_cases hf : y = q.finish
  · exact ⟨pc, p, q, rfl, hp, hq, hne, hstart, hf.symm, hend⟩
  · have hs : y = q.start := hy.resolve_right hf
    let r := q.reverse
    have hr : r.support = q.support := GraphPath.support_reverse q
    have hrne : p ≠ r := by
      intro heq
      have hsup : p.support = q.support := by
        simpa [r, hr] using congrArg GraphPath.support heq
      obtain ⟨z, hz⟩ := p.support_nonempty
      exact Finset.disjoint_left.1
        (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne) hz
        (hsup ▸ hz)
    have hp' : p ∈ (pc.replacePath_sat hq r hr).paths := by
      refine List.mem_append.mpr (Or.inl (List.mem_filter.2 ⟨hp, ?_⟩))
      exact decide_eq_true hne
    refine ⟨pc.replacePath_sat hq r hr, p, r,
      pc.replacePath_sat_card hq r hr, hp',
      pc.replacePath_sat_self_mem hq r hr, hrne, hstart, ?_, ?_⟩
    · simp [r, PathCover.GraphPath.finish_reverse, hs]
    · intro s hs'
      rcases pc.replacePath_sat_mem_paths hq r hr hs' with hsr | ⟨hspc, _⟩
      · subst hsr
        rw [PathCover.GraphPath.start_reverse, PathCover.GraphPath.finish_reverse]
        exact ⟨(hend q hq).2, (hend q hq).1⟩
      · exact hend s hspc

lemma insert_eq_of_sdiff_singleton {S B : Finset V} {b : V}
    (hS : S ⊆ B) (hb : b ∈ B \ S) (hcard : (B \ S).card = 1) :
    insert b S = B := by
  ext z
  constructor
  · intro hz
    rcases mem_insert.1 hz with rfl | hzS
    · exact (mem_sdiff.1 hb).1
    · exact hS hzS
  · intro hzB
    by_cases hzS : z ∈ S
    · exact mem_insert_of_mem hzS
    · have hzBS : z ∈ B \ S := mem_sdiff.2 ⟨hzB, hzS⟩
      have huniq := (card_eq_one.1 hcard)
      obtain ⟨w, hw⟩ := huniq
      have hb' : b = w := mem_singleton.1 (hw ▸ hb)
      have hz' : z = w := mem_singleton.1 (hw ▸ hzBS)
      simpa [hz'.trans hb'.symm] using mem_insert_self b S

lemma support_union_of_two {U : Finset V} (pc : PathCover G U)
    {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hcard : pc.card = 2) :
    p.support ∪ q.support = U := by
  have hlen : pc.paths.length = 2 := by simpa [PathCover.card] using hcard
  match hps : pc.paths with
  | [] =>
    simp [hps] at hlen
  | [_] =>
    simp [hps] at hlen
  | a :: b :: rest =>
    have hrest : rest = [] := by
      have : rest.length + 2 = 2 := by
        simpa [hps, List.length_cons] using hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    have hp' : p = a ∨ p = b := by simpa [hps] using hp
    have hq' : q = a ∨ q = b := by simpa [hps] using hq
    have hpair : (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
      rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
      · exact (hne (hp'.trans hq'.symm)).elim
      · exact Or.inl ⟨hp', hq'⟩
      · exact Or.inr ⟨hp', hq'⟩
      · exact (hne (hp'.trans hq'.symm)).elim
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzp | hzq
      · exact pc.support_subset hp hzp
      · exact pc.support_subset hq hzq
    · intro hzU
      obtain ⟨s, hs, hzs⟩ := (pc.mem_iff z).1 hzU
      have hs' : s = a ∨ s = b := by simpa [hps] using hs
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hs' with rfl | rfl
        · exact mem_union.2 (Or.inl hzs)
        · exact mem_union.2 (Or.inr hzs)
      · rcases hs' with rfl | rfl
        · exact mem_union.2 (Or.inr hzs)
        · exact mem_union.2 (Or.inl hzs)

lemma exists_last_splice_through {A B U : Finset V} {b x y : V}
    {p q : GraphPath G}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (pc : PathCover G U)
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hstart : p.start = x) (hfinish : q.finish = y)
    (hend : ∀ s ∈ pc.paths, s.start ∈ A ∧ s.finish ∈ A)
    (hb : b ∈ B) (hbU : b ∉ U) :
    ∃ r : GraphPath G,
      r.support = p.support ∪ {b} ∪ q.support ∧
        r.start = x ∧ r.finish = y := by
  have hpb : b ∉ p.support := fun h => hbU (pc.support_subset hp h)
  have hqb : b ∉ q.support := fun h => hbU (pc.support_subset hq h)
  obtain ⟨s, hs, hss, hsf⟩ :=
    exists_spliceABA hAB p b q (hend p hp).2 hb (hend q hq).1 hpb hqb
      (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne)
  exact ⟨s, hs, hss.trans hstart, hsf.trans hfinish⟩

/-- Forward assembly: a `D(A)` pair becomes a spanning `x`-`y` path of
the critical join `A ∪ B`. -/
lemma exists_spanning_path_of_critical_D {A B : Finset V} {x y : V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1)
    (hD : DistinctPathCompatible (G := G) A x y) :
    ∃ r : GraphPath G, r.support = A ∪ B ∧ r.start = x ∧ r.finish = y := by
  obtain ⟨hne0, pc0, h0, p0, hp0, q0, hq0, hpq0, hxend, hyend⟩ := hD
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
                  ∃ r : GraphPath G,
                    r.support = A ∪ B ∧ r.start = x ∧ r.finish = y := by
    intro k
    induction k with
    | zero =>
      intro S pc p qy hS hk hcard hp hqy hne pqstart hyend' hend
      have hBS : B \ S = ∅ := Finset.card_eq_zero.mp hk
      have hBeq : S = B := subset_antisymm hS (sdiff_eq_empty_iff_subset.mp hBS)
      subst hBeq
      have hcard1 : pc.card = 1 := by
        simpa [hcrit] using hcard
      exact (hne (by
        have := PathCover.exists_singleton_of_card_one pc hcard1
        obtain ⟨r, hr⟩ := this
        have hp' : p = r := by simpa [hr] using hp
        have hq' : qy = r := by simpa [hr] using hqy
        exact hp'.trans hq'.symm)).elim
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
      by_cases hk0 : k = 0
      · subst hk0
        have hcard2 : pc.card = 2 := by omega
        obtain ⟨pc1, p1, q1, hcard1, hp1, hq1, hne1, hstart1, hfin1, hend1⟩ :=
          exists_orientFinish_keepStart (A := A) pc hp hqy hne pqstart hyend' hend
        have hcard2' : pc1.card = 2 := by omega
        obtain ⟨r, hr, hs, hf⟩ :=
          exists_last_splice_through (x := x) (y := y) hAB pc1 hp1 hq1 hne1
            hstart1 hfin1 hend1 hbB hbU
        have hBeq : insert b S = B :=
          insert_eq_of_sdiff_singleton hS hb (by omega)
        have hcov : p1.support ∪ q1.support = A ∪ S :=
          support_union_of_two pc1 hp1 hq1 hne1 hcard2'
        have hsupp : r.support = A ∪ B := by
          calc
            r.support = p1.support ∪ {b} ∪ q1.support := hr
            _ = (p1.support ∪ q1.support) ∪ {b} := by
              ext z; simp [mem_union, or_assoc]
            _ = (A ∪ S) ∪ {b} := by rw [hcov]
            _ = A ∪ insert b S := by
              ext z; simp [mem_union, mem_insert, or_left_comm]
            _ = A ∪ B := by rw [hBeq]
        exact ⟨r, hsupp, hs, hf⟩
      · have h3 : 3 ≤ pc.card := by omega
        obtain ⟨pc1, p1, q1, hcard1, hp1, hq1, hne1, hstart1, hy1, hend1⟩ :=
          exists_marked_splice_two_through_avoid (x := x) (y := y) (p := p)
            (qy := qy) hAB pc hp hqy hne pqstart hyend' h3 hend hbB hbU
        have hU : insert b (A ∪ S) = A ∪ insert b S := by
          ext z; simp [mem_insert, mem_union]
        let pc1' : PathCover G (A ∪ insert b S) := pc1.cast hU
        have hS' : insert b S ⊆ B := insert_subset hbB hS
        have hrem : B \ insert b S = (B \ S).erase b := sdiff_insert B S b
        have hk' : (B \ insert b S).card = k := by
          rw [hrem, card_erase_of_mem hb, hk]; omega
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

lemma erase_union_sdiff_erase {A B : Finset V} {b : V}
    (hdisj : Disjoint A B) (hb : b ∈ B) :
    (A ∪ B).erase b \ B.erase b = A := by
  ext z
  simp only [mem_sdiff, mem_erase, mem_union]
  constructor
  · intro ⟨⟨hzne, hzAB⟩, hnot⟩
    rcases hzAB with hzA | hzB
    · exact hzA
    · exact (hnot ⟨hzne, hzB⟩).elim
  · intro hzA
    refine ⟨⟨fun hzb => Finset.disjoint_left.1 hdisj hzA (hzb ▸ hb), Or.inl hzA⟩, ?_⟩
    intro hBe
    exact Finset.disjoint_left.1 hdisj hzA hBe.2

/-- Reverse: a spanning `x`-`y` path of the critical join yields `D(A)`. -/
lemma DistinctPathCompatible_of_critical_spanning {A B : Finset V} {x y : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1)
    (hR : SpanningPathCompatible (G := G) (A ∪ B) x y) :
    DistinctPathCompatible (G := G) A x y := by
  obtain ⟨hne, p0, hpU, hends⟩ := hR
  have hdisj := disjoint_of_completeBetween hAB
  let p : GraphPath G :=
    if h : p0.start = x ∧ p0.finish = y then p0 else p0.reverse
  have hpU' : p.support = A ∪ B := by
    by_cases h : p0.start = x ∧ p0.finish = y
    · simpa [p, h] using hpU
    · simpa [p, h, GraphPath.support_reverse] using hpU
  have hxy : p.start = x ∧ p.finish = y := by
    by_cases h : p0.start = x ∧ p0.finish = y
    · simpa [p, h]
    · have h' : p0.start = y ∧ p0.finish = x := by
        rcases hends with h1 | h2
        · exact (h h1).elim
        · exact h2
      have hp : p = p0.reverse := dif_neg h
      refine ⟨?_, ?_⟩
      · simpa [hp, PathCover.GraphPath.start_reverse] using h'.2
      · simpa [hp, PathCover.GraphPath.finish_reverse] using h'.1
  have ⟨b, hbB⟩ := hBne
  have hbU : b ∈ p.support := by simpa [hpU'] using mem_union.2 (Or.inr hbB)
  have hp1 : pathCoverNumber G (A ∪ B) = 1 :=
    pathCoverNumber_eq_one_of_critical hAne hBne hAB hcrit
  let pcU : PathCover G (A ∪ B) := (PathCover.ofPath p).cast hpU'
  have hminU : pcU.card = pathCoverNumber G (A ∪ B) := by
    rw [PathCover.cast_card, PathCover.ofPath_card, hp1]
  have hxE : Eligible G (A ∪ B) x :=
    ⟨pcU, hminU, p, by rw [PathCover.cast_paths]; exact List.mem_singleton.2 rfl,
      Or.inl hxy.1.symm⟩
  have hyE : Eligible G (A ∪ B) y :=
    ⟨pcU, hminU, p, by rw [PathCover.cast_paths]; exact List.mem_singleton.2 rfl,
      Or.inr hxy.2.symm⟩
  have hxA : x ∈ A := eligible_mem_left_of_dominant hAne hBne hAB (by omega) hxE
  have hyA : y ∈ A := eligible_mem_left_of_dominant hAne hBne hAB (by omega) hyE
  have hxb : x ≠ b := fun h => Finset.disjoint_left.1 hdisj hxA (h ▸ hbB)
  have hyb : y ≠ b := fun h => Finset.disjoint_left.1 hdisj hyA (h ▸ hbB)
  have hs : b ≠ p.start := fun h => hxb (hxy.1 ▸ h.symm)
  have hf : b ≠ p.finish := fun h => hyb (hxy.2 ▸ h.symm)
  have hnil : ¬ p.walk.Nil := GraphPath.not_nil_of_internal hbU hs
  let left := (p.takeUntil hbU).trimFinish
    (fun hnil' => hs ((GraphPath.takeUntil_nil_iff p hbU).1 hnil'))
  let right := (p.dropUntil hbU).trimStart
    (fun hnil' => hf ((GraphPath.dropUntil_nil_iff p hbU).1 hnil'))
  have hdel : p.deleteVertex b = [left, right] := by
    unfold GraphPath.deleteVertex
    rw [dif_pos hbU, dif_neg hnil, dif_neg hs, dif_neg hf]
  have hpc1paths : (pcU.deleteVertex b).paths = [left, right] := by
    change ((pcU.paths).flatMap fun q => q.deleteVertex b) = [left, right]
    have hpaths : pcU.paths = [p] := by
      simp [pcU, PathCover.cast_paths, PathCover.ofPath]
    simp [hpaths, hdel]
  have hL : left ∈ (pcU.deleteVertex b).paths := by simp [hpc1paths]
  have hR : right ∈ (pcU.deleteVertex b).paths := by simp [hpc1paths]
  have hneLR : left ≠ right := by
    intro heq
    have hd := GraphPath.disjoint_internal_pieces p hbU hs hf
    have hxL : x ∈ left.support := by
      have : left.start = p.start := by
        simp [left, GraphPath.trimFinish_start, GraphPath.takeUntil]
      simpa [this, hxy.1] using left.start_mem_support
    have hyR : y ∈ right.support := by
      have : right.finish = p.finish := by
        simp [right, GraphPath.trimStart_finish, GraphPath.dropUntil]
      simpa [this, hxy.2] using right.finish_mem_support
    have hxR : x ∈ right.support := by
      have hsup : left.support = right.support := congrArg GraphPath.support heq
      rwa [← hsup]
    exact Finset.disjoint_left.1 hd hxL hxR
  have hxLend : x = left.start ∨ x = left.finish := by
    have : left.start = p.start := by
      simp [left, GraphPath.trimFinish_start, GraphPath.takeUntil]
    exact Or.inl (hxy.1.symm.trans this.symm)
  have hyRend : y = right.start ∨ y = right.finish := by
    have : right.finish = p.finish := by
      simp [right, GraphPath.trimStart_finish, GraphPath.dropUntil]
    exact Or.inr (hxy.2.symm.trans this.symm)
  have hBsub : B.erase b ⊆ (A ∪ B).erase b := by
    intro z hz
    exact mem_erase.2 ⟨(mem_erase.1 hz).1, mem_union.2 (Or.inr (mem_erase.1 hz).2)⟩
  have hxS : x ∉ B.erase b := fun h =>
    Finset.disjoint_left.1 hdisj hxA (mem_of_mem_erase h)
  have hyS : y ∉ B.erase b := fun h =>
    Finset.disjoint_left.1 hdisj hyA (mem_of_mem_erase h)
  obtain ⟨pcA0, p', q', hcardA, hp', hq', hne', hx', hy'⟩ :=
    exists_deleteFinset_keepDistinct (pcU.deleteVertex b) hBsub hL hR hneLR
      hxLend hyRend hxS hyS
  have hEq : (A ∪ B).erase b \ B.erase b = A :=
    erase_union_sdiff_erase hdisj hbB
  let pcA : PathCover G A := pcA0.cast hEq
  have hmin : pcA.card = pathCoverNumber G A := by
    have hle := pathCoverNumber_le (G := G) pcA
    have hdv : (pcU.deleteVertex b).card = pcU.card + 1 := by
      refine PathCover.card_deleteVertex_eq_add_one_of_internal pcU
        (mem_union.2 (Or.inr hbB)) ?_
      intro q hq
      have : q = p := by
        have hpaths : pcU.paths = [p] := by
          simp [pcU, PathCover.cast_paths, PathCover.ofPath]
        have hq' : q ∈ pcU.paths := hq
        rw [hpaths] at hq'
        exact List.mem_singleton.1 hq'
      subst this
      exact ⟨hs, hf⟩
    have hcard0 : pcA0.card ≤ (pcU.deleteVertex b).card + (B.erase b).card := hcardA
    have : pcA.card ≤ B.card + 1 := by
      rw [PathCover.cast_card]
      have : (B.erase b).card = B.card - 1 := card_erase_of_mem hbB
      have : 1 ≤ B.card := Nat.succ_le_of_lt (card_pos.2 hBne)
      omega
    omega
  refine ⟨hne, pcA, hmin, p', ?_, q', ?_, hne', hx', hy'⟩
  · rw [PathCover.cast_paths]; exact hp'
  · rw [PathCover.cast_paths]; exact hq'

lemma SpanningPathCompatible_critical_iff {A B : Finset V} {x y : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1) :
    SpanningPathCompatible (G := G) (A ∪ B) x y ↔
      DistinctPathCompatible (G := G) A x y := by
  constructor
  · exact DistinctPathCompatible_of_critical_spanning hAne hBne hAB hcrit
  · intro hD
    obtain ⟨r, hr, hs, hf⟩ :=
      exists_spanning_path_of_critical_D hAB hcrit hD
    exact ⟨hD.1, r, hr, Or.inl ⟨hs, hf⟩⟩

/-- Extend a D-part cut of the dominant child by the opposite side. -/
lemma exists_critical_partCut {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1)
    (hA : IsCograph G A) (hx : x ∈ eligibleSet G A) :
    ∃ S, S ⊆ ineligibleSet G (A ∪ B) ∧ S.Nonempty ∧
      componentCount G ((A ∪ B) \ S) = S.card + 1 ∧
      InOneComponent (G := G) ((A ∪ B) \ S)
        ((ineligibleSet G (A ∪ B) ∪ dNonadjClass (G := G) A x) \ S) := by
  obtain ⟨SX, hSX, hcut, hcomp⟩ := exists_partCut_of_isCograph hA hx
  let S := B ∪ SX
  have hdisj := disjoint_of_completeBetween hAB
  have hFU := ineligibleSet_complete_join_critical hAne hBne hAB hcrit
  have hSsub : S ⊆ ineligibleSet G (A ∪ B) := by
    intro z hz
    rw [hFU]
    rcases mem_union.1 hz with hzB | hzX
    · exact mem_union.2 (Or.inl hzB)
    · exact mem_union.2 (Or.inr (hSX hzX))
  have hSne : S.Nonempty := hBne.mono subset_union_left
  have hrem : (A ∪ B) \ S = A \ SX := by
    ext z
    simp only [mem_sdiff, mem_union, S]
    constructor
    · intro ⟨hzAB, hzS⟩
      rcases hzAB with hzA | hzB
      · exact ⟨hzA, fun hX => hzS (Or.inr hX)⟩
      · exact (hzS (Or.inl hzB)).elim
    · intro ⟨hzA, hzX⟩
      exact ⟨Or.inl hzA, fun h => h.elim
        (fun hzB => Finset.disjoint_left.1 hdisj hzA hzB) hzX⟩
  have hpA : pathCoverNumber G A = B.card + 1 := hcrit
  have hcut' : componentCount G ((A ∪ B) \ S) = S.card + 1 := by
    have hdisjS : Disjoint B SX := by
      refine disjoint_left.2 ?_
      intro z hzB hzX
      exact Finset.disjoint_left.1 hdisj
        (ineligibleSet_subset (G := G) A (hSX hzX)) hzB
    have hScard : S.card = B.card + SX.card :=
      card_union_of_disjoint hdisjS
    simpa [hrem, hScard, hpA, add_comm, add_left_comm, add_assoc] using hcut
  have hW :
      (ineligibleSet G (A ∪ B) ∪ dNonadjClass (G := G) A x) \ S =
        (ineligibleSet G A ∪ dNonadjClass (G := G) A x) \ SX := by
    ext z
    simp only [mem_sdiff, mem_union, hFU, S]
    constructor
    · intro ⟨hz, hzS⟩
      rcases hz with (hzB | hzF) | hzP
      · exact (hzS (Or.inl hzB)).elim
      · exact ⟨Or.inl hzF, fun hX => hzS (Or.inr hX)⟩
      · exact ⟨Or.inr hzP, fun hX => hzS (Or.inr hX)⟩
    · intro ⟨hz, hzX⟩
      rcases hz with hzF | hzP
      · exact ⟨Or.inl (Or.inr hzF), fun h => h.elim
          (fun hzB => Finset.disjoint_left.1 hdisj
            (ineligibleSet_subset (G := G) A hzF) hzB) hzX⟩
      · exact ⟨Or.inr hzP, fun h => h.elim
          (fun hzB => Finset.disjoint_left.1 hdisj
            (eligibleSet_subset (G := G) A
              ((dNonadjClass_subset_eligible (G := G) A x) hzP)) hzB) hzX⟩
  have hmono := inOneComponent_mono (A := A \ SX) (B := (A ∪ B) \ S)
    (by simp [hrem]) hcomp
  refine ⟨S, hSsub, hSne, hcut', ?_⟩
  simpa [hW, hrem] using hmono

lemma exists_critical_partCut_of_canonical {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1)
    (hA : Nikoghosyan.IsCograph G A) (hx : x ∈ eligibleSet G A) :
    ∃ S, S ⊆ ineligibleSet G (A ∪ B) ∧ S.Nonempty ∧
      componentCount G ((A ∪ B) \ S) = S.card + 1 ∧
      InOneComponent (G := G) ((A ∪ B) \ S)
        ((ineligibleSet G (A ∪ B) ∪ dNonadjClass (G := G) A x) \ S) :=
  exists_critical_partCut hAne hBne hAB hcrit (isCograph_iff.2 hA) hx

end Cograph
end Nikoghosyan
