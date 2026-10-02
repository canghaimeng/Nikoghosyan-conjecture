/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.PathCoverRefinement
import Nikoghosyan.PathCoverCuts

/-!
# Complete-join path-cover constructions

Binary complete-join recurrence
`p(A ∪ B) = max 1 (max (p(A) - |B|) (p(B) - |A|))`
for nonempty disjoint blocks with every original `A`–`B` edge present,
together with the balanced original-edge spanning path / cycle.
The numerical lower bound uses the public generic deletion lemma
`pathCoverNumber_sdiff_le`. The matching upper bound is constructive:
dominant-child ABA splicing, or refined alternating `spliceJoin`.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma adj_of_completeBetween {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) : G.Adj a b :=
  hAB ha hb

lemma disjoint_of_completeBetween {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) : Disjoint A B := by
  rw [disjoint_iff_inter_eq_empty]
  ext x
  simp
  intro hxA hxB
  exact (hAB hxA hxB).ne rfl

lemma splice_of_completeBetween {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p q : GraphPath G) (hp : p.support ⊆ A) (hq : q.support ⊆ B)
    (_hd : Disjoint p.support q.support) :
    G.Adj p.finish q.start :=
  hAB (hp p.finish_mem_support) (hq q.start_mem_support)

/-- Join an `A`-path to a `B`-path by an original complete-join edge. -/
def spliceJoin {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p q : GraphPath G) (hp : p.support ⊆ A) (hq : q.support ⊆ B)
    (hd : Disjoint p.support q.support) : GraphPath G :=
  p.splice q (splice_of_completeBetween hAB p q hp hq hd) hd

lemma support_spliceJoin {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p q : GraphPath G) (hp : p.support ⊆ A) (hq : q.support ⊆ B)
    (hd : Disjoint p.support q.support) :
    (spliceJoin hAB p q hp hq hd).support = p.support ∪ q.support :=
  GraphPath.support_splice _ _ _ _

lemma start_spliceJoin {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p q : GraphPath G) (hp : p.support ⊆ A) (hq : q.support ⊆ B)
    (hd : Disjoint p.support q.support) :
    (spliceJoin hAB p q hp hq hd).start = p.start :=
  rfl

lemma finish_spliceJoin {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p q : GraphPath G) (hp : p.support ⊆ A) (hq : q.support ⊆ B)
    (hd : Disjoint p.support q.support) :
    (spliceJoin hAB p q hp hq hd).finish = q.finish :=
  rfl

lemma singleton_support_subset {b : V} {B : Finset V} (hb : b ∈ B) :
    (GraphPath.singleton (G := G) b).support ⊆ B := by
  simp [GraphPath.support_singleton, hb]

lemma disjoint_support_of_subset_disjoint {A B : Finset V} {p q : GraphPath G}
    (hdisj : Disjoint A B) (hp : p.support ⊆ A) (hq : q.support ⊆ B) :
    Disjoint p.support q.support :=
  disjoint_of_subset_left hp (disjoint_of_subset_right hq hdisj)

/-- Splice an `A`-ended path, a `B`-vertex, and another `A`-started path along
original join edges. Interior vertices of the input paths may already lie in
`A ∪ B`; only the outer endpoints are required to lie in `A`. -/
lemma exists_spliceABA {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p : GraphPath G) (b : V) (q : GraphPath G)
    (hp : p.finish ∈ A) (hb : b ∈ B) (hq : q.start ∈ A)
    (hpb : b ∉ p.support) (hqB : b ∉ q.support)
    (hd : Disjoint p.support q.support) :
    ∃ r : GraphPath G,
      r.support = p.support ∪ {b} ∪ q.support ∧
        r.start = p.start ∧ r.finish = q.finish := by
  let sb := GraphPath.singleton (G := G) b
  have hps : Disjoint p.support sb.support := by
    rw [GraphPath.support_singleton]
    exact disjoint_singleton_right.2 hpb
  have hadj1 : G.Adj p.finish sb.start := hAB hp hb
  let mid := p.splice sb hadj1 hps
  have hqs : Disjoint mid.support q.support := by
    unfold mid
    rw [GraphPath.support_splice, GraphPath.support_singleton, disjoint_union_left]
    exact ⟨hd, disjoint_singleton_left.2 hqB⟩
  have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
    fun {b} hb {a} ha => (hAB ha hb).symm
  have hadj2 : G.Adj mid.finish q.start := hBA hb hq
  refine ⟨mid.splice q hadj2 hqs, ?_, rfl, rfl⟩
  ext x
  simp [mid, GraphPath.support_splice, sb, GraphPath.support_singleton]

lemma PathCover.exists_singleton_of_card_one {U : Finset V}
    (pc : PathCover G U) (h : pc.card = 1) : ∃ p, pc.paths = [p] := by
  match hps : pc.paths with
  | [] =>
    simp [PathCover.card, hps] at h
  | [p] =>
    exact ⟨p, rfl⟩
  | _ :: _ :: _ =>
    simp [PathCover.card, hps] at h

lemma pathCoverNumber_complete_join_le_one {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ 1) (hpB : pathCoverNumber G B ≤ 1) :
    pathCoverNumber G (A ∪ B) ≤ 1 := by
  obtain ⟨pcA, hAcard⟩ := exists_min_pathCover (G := G) A
  obtain ⟨pcB, hBcard⟩ := exists_min_pathCover (G := G) B
  have hA0 : pathCoverNumber G A ≠ 0 := by
    intro h
    exact hAne.ne_empty ((pathCoverNumber_eq_zero_iff_refinement (G := G) A).mp h)
  have hB0 : pathCoverNumber G B ≠ 0 := by
    intro h
    exact hBne.ne_empty ((pathCoverNumber_eq_zero_iff_refinement (G := G) B).mp h)
  have hA1 : pcA.card = 1 := by omega
  have hB1 : pcB.card = 1 := by omega
  obtain ⟨p, hpApaths⟩ := PathCover.exists_singleton_of_card_one pcA hA1
  obtain ⟨q, hqBpaths⟩ := PathCover.exists_singleton_of_card_one pcB hB1
  have hp : p ∈ pcA.paths := by simp [hpApaths]
  have hq : q ∈ pcB.paths := by simp [hqBpaths]
  have hpAsupp : p.support ⊆ A := pcA.support_subset hp
  have hqBsupp : q.support ⊆ B := pcB.support_subset hq
  have hd := disjoint_support_of_subset_disjoint
    (disjoint_of_completeBetween hAB) hpAsupp hqBsupp
  let r := spliceJoin hAB p q hpAsupp hqBsupp hd
  have hr : r.support = p.support ∪ q.support :=
    support_spliceJoin hAB p q hpAsupp hqBsupp hd
  let pc : PathCover G (A ∪ B) :=
    { paths := [r]
      disjoint := List.pairwise_singleton _ _
      mem_iff := by
        intro x
        constructor
        · intro hx
          rcases mem_union.1 hx with hxA | hxB
          · obtain ⟨t, ht, hxt⟩ := (pcA.mem_iff x).1 hxA
            have : t = p := by simpa [hpApaths] using ht
            subst this
            refine ⟨r, List.mem_singleton.2 rfl, ?_⟩
            rw [hr]
            exact mem_union.2 (Or.inl hxt)
          · obtain ⟨t, ht, hxt⟩ := (pcB.mem_iff x).1 hxB
            have : t = q := by simpa [hqBpaths] using ht
            subst this
            refine ⟨r, List.mem_singleton.2 rfl, ?_⟩
            rw [hr]
            exact mem_union.2 (Or.inr hxt)
        · intro ⟨t, ht, hxt⟩
          have : t = r := List.mem_singleton.1 ht
          subst this
          have hxt' : x ∈ p.support ∪ q.support := by
            rwa [hr] at hxt
          rcases mem_union.1 hxt' with hxP | hxQ
          · exact mem_union.2 (Or.inl ((pcA.mem_iff x).2 ⟨p, hp, hxP⟩))
          · exact mem_union.2 (Or.inr ((pcB.mem_iff x).2 ⟨q, hq, hxQ⟩)) }
  have hpc1 : pc.card = 1 := rfl
  exact (pathCoverNumber_le (G := G) pc).trans_eq hpc1

namespace PathCover

/-- Transport a cover along an equality of vertex sets. -/
def cast {U W : Finset V} (pc : PathCover G U) (h : U = W) : PathCover G W :=
  h ▸ pc

@[simp]
lemma cast_card {U W : Finset V} (pc : PathCover G U) (h : U = W) :
    (pc.cast h).card = pc.card := by
  subst h
  rfl

@[simp]
lemma cast_paths {U W : Finset V} (pc : PathCover G U) (h : U = W) :
    (pc.cast h).paths = pc.paths := by
  subst h
  rfl

lemma exists_two_distinct {U : Finset V} (pc : PathCover G U)
    (h : 2 ≤ pc.card) :
    ∃ p q, p ∈ pc.paths ∧ q ∈ pc.paths ∧ p ≠ q := by
  match hps : pc.paths with
  | [] =>
    simp [PathCover.card, hps] at h
  | [_] =>
    simp [PathCover.card, hps] at h
  | p :: q :: rest =>
    refine ⟨p, q, by simp, by simp, ?_⟩
    have hn := pc.nodup_paths
    rw [hps] at hn
    intro hpq
    subst hpq
    exact (List.nodup_cons.1 hn).1 (List.mem_cons.2 (Or.inl rfl))

lemma length_filter_ne_two {α : Type*} [DecidableEq α] {a b : α} {l : List α}
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) (hn : l.Nodup) :
    ((l.filter fun x => decide (x ≠ a)).filter fun x => decide (x ≠ b)).length
      = l.length - 2 := by
  have h1 := length_filter_ne_of_mem_nodup (a := a) (l := l) ha hn
  have hb' : b ∈ l.filter fun x => decide (x ≠ a) :=
    List.mem_filter.2 ⟨hb, decide_eq_true hne.symm⟩
  have hn' : (l.filter fun x => decide (x ≠ a)).Nodup := List.Nodup.filter _ hn
  have h2 := length_filter_ne_of_mem_nodup (a := b)
    (l := l.filter fun x => decide (x ≠ a)) hb' hn'
  omega

/-- Drop one cover path; the remainder covers the leftover vertices. -/
noncomputable def erasePath {U : Finset V} (pc : PathCover G U)
    {p : GraphPath G} (hp : p ∈ pc.paths) : PathCover G (U \ p.support) where
  paths := pc.paths.filter fun q => decide (q ≠ p)
  disjoint := List.Pairwise.filter _ pc.disjoint
  mem_iff := by
    intro x
    constructor
    · intro hx
      have hxU : x ∈ U := (mem_sdiff.1 hx).1
      have hxp : x ∉ p.support := (mem_sdiff.1 hx).2
      obtain ⟨q, hq, hxq⟩ := (pc.mem_iff x).1 hxU
      have hqp : q ≠ p := fun h => hxp (h ▸ hxq)
      exact ⟨q, List.mem_filter.2 ⟨hq, decide_eq_true hqp⟩, hxq⟩
    · intro ⟨q, hq, hxq⟩
      have hqpc := (List.mem_filter.1 hq).1
      have hqp : q ≠ p := of_decide_eq_true (List.mem_filter.1 hq).2
      have hxU := (pc.mem_iff x).2 ⟨q, hqpc, hxq⟩
      have hxp : x ∉ p.support := by
        intro hxp
        have : Disjoint q.support p.support :=
          pairwise_disjoint_of_mem pc.disjoint hqpc hp hqp
        exact Finset.disjoint_left.1 this hxq hxp
      exact mem_sdiff.2 ⟨hxU, hxp⟩

lemma erasePath_card {U : Finset V} (pc : PathCover G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) :
    (pc.erasePath hp).card = pc.card - 1 := by
  simpa [erasePath, PathCover.card] using
    length_filter_ne_of_mem_nodup (a := p) (l := pc.paths) hp pc.nodup_paths

/-- Replace two distinct cover paths by a single path whose support is those
two supports together with a fresh vertex. -/
noncomputable def spliceTwoInsert {U : Finset V} (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (b : V) (hb : b ∉ U) (r : GraphPath G)
    (hr : r.support = p.support ∪ {b} ∪ q.support) :
    PathCover G (insert b U) where
  paths :=
    (pc.paths.filter fun s => decide (s ≠ p)).filter (fun s => decide (s ≠ q))
      ++ [r]
  disjoint := by
    refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · exact List.Pairwise.filter _ (List.Pairwise.filter _ pc.disjoint)
    · intro s hs t ht
      have ht' : t = r := List.mem_singleton.1 ht
      subst ht'
      have hs1 := List.mem_filter.1 hs
      have hs0 := List.mem_filter.1 hs1.1
      have hspc : s ∈ pc.paths := hs0.1
      have hsp : s ≠ p := of_decide_eq_true hs0.2
      have hsq : s ≠ q := of_decide_eq_true hs1.2
      have hdisjp : Disjoint s.support p.support :=
        pairwise_disjoint_of_mem pc.disjoint hspc hp hsp
      have hdisjq : Disjoint s.support q.support :=
        pairwise_disjoint_of_mem pc.disjoint hspc hq hsq
      have hsb : b ∉ s.support := fun hbs =>
        hb (pc.support_subset hspc hbs)
      refine Finset.disjoint_left.2 ?_
      intro x hxs hxr
      have hxrs : x ∈ p.support ∪ {b} ∪ q.support := by rwa [hr] at hxr
      have hx1 : x = b ∨ x ∈ p.support ∨ x ∈ q.support := by
        simpa [mem_union, mem_singleton] using hxrs
      rcases hx1 with rfl | hxp | hxq
      · exact hsb hxs
      · exact Finset.disjoint_left.1 hdisjp hxs hxp
      · exact Finset.disjoint_left.1 hdisjq hxs hxq
  mem_iff := by
    intro x
    constructor
    · intro hx
      rcases mem_insert.1 hx with rfl | hxU
      · refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
        rw [hr]
        exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_singleton.2 rfl))))
      · obtain ⟨s, hs, hxs⟩ := (pc.mem_iff x).1 hxU
        by_cases hsp : s = p
        · subst hsp
          refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
          rw [hr]
          exact mem_union.2 (Or.inl (mem_union.2 (Or.inl hxs)))
        · by_cases hsq : s = q
          · subst hsq
            refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
            rw [hr]
            exact mem_union.2 (Or.inr hxs)
          · refine ⟨s, List.mem_append.mpr (Or.inl ?_), hxs⟩
            exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hs, decide_eq_true hsp⟩,
              decide_eq_true hsq⟩
    · intro ⟨s, hs, hxs⟩
      rcases List.mem_append.1 hs with hsL | hsR
      · have hs1 := List.mem_filter.1 hsL
        have hs0 := List.mem_filter.1 hs1.1
        exact mem_insert.2 (Or.inr ((pc.mem_iff x).2 ⟨s, hs0.1, hxs⟩))
      · have : s = r := List.mem_singleton.1 hsR
        subst this
        have hx' : x ∈ p.support ∪ {b} ∪ q.support := by rwa [hr] at hxs
        have hx1 : x = b ∨ x ∈ p.support ∨ x ∈ q.support := by
          simpa [mem_union, mem_singleton] using hx'
        rcases hx1 with rfl | hxp | hxq
        · exact mem_insert_self _ _
        · exact mem_insert.2 (Or.inr ((pc.mem_iff x).2 ⟨p, hp, hxp⟩))
        · exact mem_insert.2 (Or.inr ((pc.mem_iff x).2 ⟨q, hq, hxq⟩))

lemma spliceTwoInsert_card {U : Finset V} (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (b : V) (hb : b ∉ U) (r : GraphPath G)
    (hr : r.support = p.support ∪ {b} ∪ q.support) :
    (pc.spliceTwoInsert hp hq hne b hb r hr).card = pc.card - 1 := by
  have hlen := length_filter_ne_two (a := p) (b := q) hp hq hne pc.nodup_paths
  have hfilt :=
    length_filter_ne_of_mem_nodup (a := p) (l := pc.paths) hp pc.nodup_paths
  have hb' : q ∈ pc.paths.filter fun x => decide (x ≠ p) :=
    List.mem_filter.2 ⟨hq, decide_eq_true hne.symm⟩
  have hpos : 2 ≤ pc.paths.length := by
    have : 1 ≤ (pc.paths.filter fun x => decide (x ≠ p)).length :=
      Nat.succ_le_of_lt (List.length_pos_of_mem hb')
    omega
  simp only [spliceTwoInsert, PathCover.card, List.length_append, List.length_cons,
    List.length_nil]
  rw [hlen]
  omega

lemma spliceTwoInsert_mem_paths {U : Finset V} (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (b : V) (hb : b ∉ U) (r : GraphPath G)
    (hr : r.support = p.support ∪ {b} ∪ q.support)
    {s : GraphPath G}
    (hs : s ∈ (pc.spliceTwoInsert hp hq hne b hb r hr).paths) :
    s = r ∨
      s ∈ pc.paths ∧ s ≠ p ∧ s ≠ q := by
  have hs' := List.mem_append.1 hs
  rcases hs' with hsL | hsR
  · have hs1 := List.mem_filter.1 hsL
    have hs0 := List.mem_filter.1 hs1.1
    exact Or.inr ⟨hs0.1, of_decide_eq_true hs0.2, of_decide_eq_true hs1.2⟩
  · exact Or.inl (List.mem_singleton.1 hsR)

end PathCover

lemma exists_splice_two_through {A B U : Finset V} {b : V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (pc : PathCover G U) (h2 : 2 ≤ pc.card)
    (hend : ∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A)
    (hb : b ∈ B) (hbU : b ∉ U) :
    ∃ pc' : PathCover G (insert b U),
      pc'.card = pc.card - 1 ∧
        (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) := by
  obtain ⟨p, q, hp, hq, hne⟩ := pc.exists_two_distinct h2
  have hpb : b ∉ p.support := fun h => hbU (pc.support_subset hp h)
  have hqb : b ∉ q.support := fun h => hbU (pc.support_subset hq h)
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_spliceABA hAB p b q (hend p hp).2 hb (hend q hq).1 hpb hqb
      (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne)
  refine ⟨pc.spliceTwoInsert hp hq hne b hbU r hr, pc.spliceTwoInsert_card hp hq hne b hbU r hr, ?_⟩
  intro s hsmem
  rcases pc.spliceTwoInsert_mem_paths hp hq hne b hbU r hr hsmem with hseq | ⟨hspc, _, _⟩
  · subst hseq
    rw [hs, hf]
    exact ⟨(hend p hp).1, (hend q hq).2⟩
  · exact hend s hspc

/-- If `p(A) > |B|`, successively splice unused `B`-vertices between pairs of
`A`-ended cover paths. The result is a cover of `A ∪ B` with
`p(A) - |B|` paths, all still `A`-ended. -/
lemma exists_pathCover_complete_join_dominant {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    ∃ pc : PathCover G (A ∪ B),
      pc.card = pathCoverNumber G A - B.card ∧
        (∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A) := by
  obtain ⟨pc0, h0⟩ := exists_min_pathCover (G := G) A
  have hend0 : ∀ p ∈ pc0.paths, p.start ∈ A ∧ p.finish ∈ A := by
    intro p hp
    exact ⟨pc0.support_subset hp p.start_mem_support,
      pc0.support_subset hp p.finish_mem_support⟩
  have aux :
      ∀ (k : ℕ) (S : Finset V) (pc : PathCover G (A ∪ S)),
        S ⊆ B → (B \ S).card = k →
          pc.card = pathCoverNumber G A - S.card →
            (∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A) →
              ∃ pc' : PathCover G (A ∪ B),
                pc'.card = pathCoverNumber G A - B.card ∧
                  (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) := by
    intro k
    induction k with
    | zero =>
      intro S pc hS hk hcard hend
      have hBS : B \ S = ∅ := Finset.card_eq_zero.mp hk
      have hBeq : S = B :=
        subset_antisymm hS (sdiff_eq_empty_iff_subset.mp hBS)
      subst hBeq
      exact ⟨pc, hcard, hend⟩
    | succ k ih =>
      intro S pc hS hk hcard hend
      have hne : (B \ S).Nonempty :=
        card_pos.mp (by omega : 0 < (B \ S).card)
      obtain ⟨b, hb⟩ := hne
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
      have h2 : 2 ≤ pc.card := by omega
      obtain ⟨pc1, hcard1, hend1⟩ :=
        exists_splice_two_through hAB pc h2 hend hbB hbU
      have hU : insert b (A ∪ S) = A ∪ insert b S := by
        ext x
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
      have hend1' : ∀ p ∈ pc1'.paths, p.start ∈ A ∧ p.finish ∈ A := by
        intro p hp
        rw [PathCover.cast_paths pc1 hU] at hp
        exact hend1 p hp
      exact ih (insert b S) pc1' hS' hk' hcard' hend1'
  have hA : A ∪ (∅ : Finset V) = A := union_empty A
  let pc0' : PathCover G (A ∪ ∅) := pc0.cast hA.symm
  have hcard0 : pc0'.card = pathCoverNumber G A - (∅ : Finset V).card := by
    rw [PathCover.cast_card, h0, card_empty, Nat.sub_zero]
  have hend0' : ∀ p ∈ pc0'.paths, p.start ∈ A ∧ p.finish ∈ A := by
    intro p hp
    rw [PathCover.cast_paths pc0 hA.symm] at hp
    exact hend0 p hp
  exact aux B.card ∅ pc0' (empty_subset B) (by simp) hcard0 hend0'

lemma exists_alternating_path :
    ∀ (n : ℕ) (A B : Finset V)
      (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
      (pcA : PathCover G A) (pcB : PathCover G B),
      pcA.card = n → pcB.card = n → 1 ≤ n →
        ∃ r : GraphPath G, r.support = A ∪ B ∧ r.start ∈ A ∧ r.finish ∈ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A B hAB pcA pcB hAn hBn hpos
    match hA : pcA.paths, hB : pcB.paths with
    | [], _ =>
      simp [PathCover.card, hA] at hAn
      omega
    | _, [] =>
      simp [PathCover.card, hB] at hBn
      omega
    | p :: _ps, q :: _qs =>
      have hp : p ∈ pcA.paths := by simp [hA]
      have hq : q ∈ pcB.paths := by simp [hB]
      have hpAsupp : p.support ⊆ A := pcA.support_subset hp
      have hqBsupp : q.support ⊆ B := pcB.support_subset hq
      have hd :=
        disjoint_support_of_subset_disjoint
          (disjoint_of_completeBetween hAB) hpAsupp hqBsupp
      by_cases h1 : n = 1
      · have hps : pcA.paths = [p] := by
          have hlen : pcA.paths.length = 1 := by
            simpa [PathCover.card, hA] using hAn.trans h1
          simpa [hA] using List.length_eq_one_iff.mp hlen
        have hqs : pcB.paths = [q] := by
          have hlen : pcB.paths.length = 1 := by
            simpa [PathCover.card, hB] using hBn.trans h1
          simpa [hB] using List.length_eq_one_iff.mp hlen
        have hAeq : p.support = A := by
          ext x
          constructor
          · intro hx
            exact hpAsupp hx
          · intro hx
            obtain ⟨t, ht, hxt⟩ := (pcA.mem_iff x).1 hx
            have : t = p := by simpa [hps] using ht
            subst this
            exact hxt
        have hBeq : q.support = B := by
          ext x
          constructor
          · intro hx
            exact hqBsupp hx
          · intro hx
            obtain ⟨t, ht, hxt⟩ := (pcB.mem_iff x).1 hx
            have : t = q := by simpa [hqs] using ht
            subst this
            exact hxt
        refine ⟨spliceJoin hAB p q hpAsupp hqBsupp hd, ?_, ?_, ?_⟩
        · rw [support_spliceJoin, hAeq, hBeq]
        · simpa [start_spliceJoin] using hpAsupp p.start_mem_support
        · simpa [finish_spliceJoin] using hqBsupp q.finish_mem_support
      · have hn2 : 2 ≤ n := by omega
        let pcA' := pcA.erasePath hp
        let pcB' := pcB.erasePath hq
        have hAcard : pcA'.card = n - 1 := by
          rw [PathCover.erasePath_card, hAn]
        have hBcard : pcB'.card = n - 1 := by
          rw [PathCover.erasePath_card, hBn]
        have hpos' : 1 ≤ n - 1 := by omega
        have hAB' :
            G.IsCompleteBetween (↑(A \ p.support) : Set V)
              (↑(B \ q.support) : Set V) := by
          intro a ha b hb
          have haF : a ∈ A \ p.support := by exact_mod_cast ha
          have hbF : b ∈ B \ q.support := by exact_mod_cast hb
          exact hAB (mem_sdiff.1 haF).1 (mem_sdiff.1 hbF).1
        obtain ⟨r', hr', hs', hf'⟩ :=
          ih (n - 1) (Nat.sub_lt (Nat.succ_le_iff.mp hpos) Nat.zero_lt_one)
            (A \ p.support) (B \ q.support) hAB' pcA' pcB' hAcard hBcard hpos'
        let r0 := spliceJoin hAB p q hpAsupp hqBsupp hd
        have hr0 : r0.support = p.support ∪ q.support :=
          support_spliceJoin hAB p q hpAsupp hqBsupp hd
        have hf0 : r0.finish = q.finish :=
          finish_spliceJoin hAB p q hpAsupp hqBsupp hd
        have hadj : G.Adj r0.finish r'.start := by
          have hfinB : r0.finish ∈ B := by
            simpa [hf0] using hqBsupp q.finish_mem_support
          have hstA : r'.start ∈ A := (mem_sdiff.1 hs').1
          exact (hAB hstA hfinB).symm
        have hd' : Disjoint r0.support r'.support := by
          rw [hr0, hr']
          refine disjoint_union_left.2 ⟨?_, ?_⟩
          · refine disjoint_union_right.2 ⟨disjoint_sdiff, ?_⟩
            exact disjoint_of_subset_left hpAsupp
              (disjoint_of_subset_right sdiff_subset
                (disjoint_of_completeBetween hAB))
          · refine disjoint_union_right.2 ⟨?_, disjoint_sdiff⟩
            exact disjoint_of_subset_left hqBsupp
              (disjoint_of_subset_right sdiff_subset
                (disjoint_of_completeBetween hAB).symm)
        let r := r0.splice r' hadj hd'
        refine ⟨r, ?_, ?_, ?_⟩
        · rw [GraphPath.support_splice, hr0, hr']
          have hAeq : p.support ∪ (A \ p.support) = A :=
            union_sdiff_of_subset hpAsupp
          have hBeq : q.support ∪ (B \ q.support) = B :=
            union_sdiff_of_subset hqBsupp
          have hrearr :
              p.support ∪ q.support ∪ ((A \ p.support) ∪ (B \ q.support)) =
                (p.support ∪ (A \ p.support)) ∪
                  (q.support ∪ (B \ q.support)) := by
            ext x
            simp only [Finset.mem_union]
            tauto
          rw [hrearr, hAeq, hBeq]
        · change r0.start ∈ A
          rw [start_spliceJoin]
          exact hpAsupp p.start_mem_support
        · change r'.finish ∈ B
          exact sdiff_subset hf'

/-- Balanced complete join: `p(A) ≤ |B|` and `p(B) ≤ |A|` yield a spanning
original-edge path of `A ∪ B` (including the order-two `K2` case). -/
lemma exists_complete_join_spanning_path {A B : Finset V}
    (hAne : A.Nonempty) (_hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ B.card)
    (hpB : pathCoverNumber G B ≤ A.card) :
    ∃ r : GraphPath G, r.support = A ∪ B ∧ r.start ∈ A ∧ r.finish ∈ B := by
  let M := max (pathCoverNumber G A) (pathCoverNumber G B)
  have hMpos : 1 ≤ M := by
    have : 1 ≤ pathCoverNumber G A :=
      one_le_pathCoverNumber_of_nonempty (G := G) hAne
    omega
  have hMA : pathCoverNumber G A ≤ M := Nat.le_max_left _ _
  have hMB : pathCoverNumber G B ≤ M := Nat.le_max_right _ _
  have hMAcard : M ≤ A.card := by
    have := pathCoverNumber_le_card (G := G) A
    omega
  have hMBcard : M ≤ B.card := by
    have := pathCoverNumber_le_card (G := G) B
    omega
  obtain ⟨pcA, hA⟩ := exists_pathCover_card (G := G) A hMA hMAcard
  obtain ⟨pcB, hB⟩ := exists_pathCover_card (G := G) B hMB hMBcard
  exact exists_alternating_path M A B hAB pcA pcB hA hB hMpos

lemma pathCoverNumber_complete_join_le_of_balanced {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ B.card)
    (hpB : pathCoverNumber G B ≤ A.card) :
    pathCoverNumber G (A ∪ B) ≤ 1 := by
  obtain ⟨r, hr, _, _⟩ :=
    exists_complete_join_spanning_path hAne hBne hAB hpA hpB
  let pc : PathCover G (A ∪ B) := (PathCover.ofPath r).cast hr
  have hpc : pc.card = 1 := by
    rw [PathCover.cast_card, PathCover.ofPath_card]
  exact (pathCoverNumber_le (G := G) pc).trans_eq hpc

/-- Close the balanced spanning path to a genuine original-edge cycle when
the union has order at least three. The order-two complete join (`K2`) is
excluded: it has a spanning path and no 3-cycle on those vertices. -/
lemma exists_complete_join_cycle {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ B.card)
    (hpB : pathCoverNumber G B ≤ A.card)
    (h3 : 3 ≤ (A ∪ B).card) :
    ∃ c : GraphCycle G, c.support = A ∪ B := by
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_complete_join_spanning_path hAne hBne hAB hpA hpB
  have hadj : G.Adj r.finish r.start := (hAB hs hf).symm
  have h3' : 3 ≤ r.support.card := by simpa [hr]
  refine ⟨r.toCycle hadj h3', ?_⟩
  simpa [GraphPath.support_toCycle] using hr

lemma pathCoverNumber_complete_join_ge_sub {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    pathCoverNumber G A ≤ pathCoverNumber G (A ∪ B) + B.card := by
  have hdisj := disjoint_of_completeBetween hAB
  have hsub : B ⊆ A ∪ B := subset_union_right
  have h := pathCoverNumber_sdiff_le (G := G) (A ∪ B) B hsub
  have hEq : (A ∪ B) \ B = A := by
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · intro hx
      rcases hx with ⟨hA | hB, hnB⟩
      · exact hA
      · exact (hnB hB).elim
    · intro hxA
      exact ⟨Or.inl hxA, fun hxB => Finset.disjoint_left.1 hdisj hxA hxB⟩
  simpa [hEq] using h

lemma pathCoverNumber_complete_join_ge_sub_symm {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    pathCoverNumber G B ≤ pathCoverNumber G (A ∪ B) + A.card := by
  have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
    fun {b} hb {a} ha => (hAB ha hb).symm
  simpa [union_comm] using pathCoverNumber_complete_join_ge_sub hBA

lemma not_both_dominant {A B : Finset V}
    (hAdom : B.card < pathCoverNumber G A)
    (hBdom : A.card < pathCoverNumber G B) : False := by
  have hpA := pathCoverNumber_le_card (G := G) A
  have hpB := pathCoverNumber_le_card (G := G) B
  omega

/-- Exact binary complete-join recurrence. Natural truncation of the child
excesses is faithful inside this `max` with one; no traceability assumption
is imposed on either child. -/
lemma pathCoverNumber_complete_join {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    pathCoverNumber G (A ∪ B) =
      max 1 (max (pathCoverNumber G A - B.card)
        (pathCoverNumber G B - A.card)) := by
  apply le_antisymm
  · by_cases hAdom : B.card < pathCoverNumber G A
    · obtain ⟨pc, hpc, _⟩ :=
        exists_pathCover_complete_join_dominant hAB hAdom
      have hle := pathCoverNumber_le (G := G) pc
      have hpB := pathCoverNumber_le_card (G := G) B
      have hpA := pathCoverNumber_le_card (G := G) A
      have hBnot : pathCoverNumber G B ≤ A.card := by
        by_contra h
        exact not_both_dominant hAdom (Nat.lt_of_not_ge h)
      have hq : 1 ≤ pathCoverNumber G A - B.card := by omega
      have hmax :
          max 1 (max (pathCoverNumber G A - B.card)
            (pathCoverNumber G B - A.card)) =
          pathCoverNumber G A - B.card := by
        simp [Nat.sub_eq_zero_of_le hBnot, max_eq_right hq]
      exact hle.trans_eq (hpc.trans hmax.symm)
    · by_cases hBdom : A.card < pathCoverNumber G B
      · have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
          fun {b} hb {a} ha => (hAB ha hb).symm
        obtain ⟨pc, hpc, _⟩ :=
          exists_pathCover_complete_join_dominant hBA hBdom
        have hle := pathCoverNumber_le (G := G) pc
        have hAnot : pathCoverNumber G A ≤ B.card := Nat.le_of_not_gt hAdom
        have hq : 1 ≤ pathCoverNumber G B - A.card := by omega
        have hmax :
            max 1 (max (pathCoverNumber G A - B.card)
              (pathCoverNumber G B - A.card)) =
            pathCoverNumber G B - A.card := by
          simp [Nat.sub_eq_zero_of_le hAnot, max_eq_right hq]
        have : pc.card = pathCoverNumber G B - A.card := by
          simpa [union_comm] using hpc
        have hle' : pathCoverNumber G (A ∪ B) ≤ pc.card := by
          simpa [union_comm] using hle
        exact hle'.trans_eq (this.trans hmax.symm)
      · have hpA : pathCoverNumber G A ≤ B.card := Nat.le_of_not_gt hAdom
        have hpB : pathCoverNumber G B ≤ A.card := Nat.le_of_not_gt hBdom
        have hle :=
          pathCoverNumber_complete_join_le_of_balanced hAne hBne hAB hpA hpB
        have hmax :
            max 1 (max (pathCoverNumber G A - B.card)
              (pathCoverNumber G B - A.card)) = 1 := by
          simp [Nat.sub_eq_zero_of_le hpA, Nat.sub_eq_zero_of_le hpB]
        exact hle.trans_eq hmax.symm
  · have h1 : 1 ≤ pathCoverNumber G (A ∪ B) :=
      one_le_pathCoverNumber_of_nonempty (G := G) (hAne.mono subset_union_left)
    have hA := pathCoverNumber_complete_join_ge_sub hAB
    have hB := pathCoverNumber_complete_join_ge_sub_symm hAB
    exact max_le h1
      (max_le (Nat.sub_le_iff_le_add.2 hA) (Nat.sub_le_iff_le_add.2 hB))

lemma Eligible.of_min_cover_endpoint {U : Finset V} (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) :
    Eligible G U p.start ∧ Eligible G U p.finish :=
  ⟨⟨pc, hpc, p, hp, Or.inl rfl⟩, ⟨pc, hpc, p, hp, Or.inr rfl⟩⟩

/-- Balanced complete join: some vertex of A and some vertex of B are
eligible in A ∪ B, namely the ends of the spanning original-edge path. -/
lemma exists_eligible_complete_join_of_balanced {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hpA : pathCoverNumber G A ≤ B.card)
    (hpB : pathCoverNumber G B ≤ A.card) :
    ∃ x y, x ∈ A ∧ y ∈ B ∧ Eligible G (A ∪ B) x ∧ Eligible G (A ∪ B) y := by
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_complete_join_spanning_path hAne hBne hAB hpA hpB
  let pc : PathCover G (A ∪ B) := (PathCover.ofPath r).cast hr
  have hcard : pc.card = 1 := by
    rw [PathCover.cast_card, PathCover.ofPath_card]
  have hmin : pc.card = pathCoverNumber G (A ∪ B) := by
    have hle := pathCoverNumber_le (G := G) pc
    obtain ⟨a, ha⟩ := hAne
    have hU : (A ∪ B).Nonempty := ⟨a, mem_union.2 (Or.inl ha)⟩
    have hge := one_le_pathCoverNumber_of_nonempty (G := G) hU
    omega
  have hp : r ∈ pc.paths := by
    rw [PathCover.cast_paths, PathCover.ofPath]
    exact List.mem_singleton.2 rfl
  have hends := Eligible.of_min_cover_endpoint pc hmin hp
  exact ⟨r.start, r.finish, hs, hf, hends.1, hends.2⟩

/-- Dominant A-child: the constructed cover of A ∪ B is minimum and entirely
A-ended. This is the numerical input to saturated-join eligibility on A. -/
lemma exists_A_ended_min_cover_of_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    ∃ pc : PathCover G (A ∪ B),
      pc.card = pathCoverNumber G (A ∪ B) ∧
        (∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A) := by
  obtain ⟨pc, hpc, hend⟩ := exists_pathCover_complete_join_dominant hAB hdom
  have heq : pc.card = pathCoverNumber G (A ∪ B) := by
    have hle := pathCoverNumber_le (G := G) pc
    have hj := pathCoverNumber_complete_join hAne hBne hAB
    have hBnot : pathCoverNumber G B ≤ A.card := by
      by_contra h
      exact not_both_dominant hdom (Nat.lt_of_not_ge h)
    have hq : 1 ≤ pathCoverNumber G A - B.card := by omega
    have hmax :
        max 1 (max (pathCoverNumber G A - B.card)
          (pathCoverNumber G B - A.card)) =
        pathCoverNumber G A - B.card := by
      simp [Nat.sub_eq_zero_of_le hBnot, max_eq_right hq]
    omega
  exact ⟨pc, heq, hend⟩

end Nikoghosyan

