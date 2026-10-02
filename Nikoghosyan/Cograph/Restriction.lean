/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.PartCuts

/-!
# Restriction of a minimum path cover to a selected subcollection

Manuscript `cog:prop:restriction`: given one actual minimum `U`-cover and a
selected subcollection of `m` of its paths, if `L` is the union of those
supports then `p(L)=m` and `E(L)=E(U) ∩ L`. The global F-cut forces the
remaining pieces after deleting `F(U)` to be whole components, so
`F(L)=F(U) ∩ L`. Arbitrary eligible tuples are not assumed to be
simultaneously realized.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def supportUnion (l : List (GraphPath G)) : Finset V :=
  (l.map GraphPath.support).foldr (· ∪ ·) ∅

lemma mem_supportUnion_iff {l : List (GraphPath G)} {x : V} :
    x ∈ supportUnion l ↔ ∃ p ∈ l, x ∈ p.support := by
  induction l with
  | nil => simp [supportUnion]
  | cons p ps ih =>
    have hfold :
        supportUnion (p :: ps) = p.support ∪ supportUnion ps := by
      simp [supportUnion]
    rw [hfold, mem_union, ih]
    simp [List.mem_cons, or_comm, or_left_comm]

lemma supportUnion_subset_of_covers {U : Finset V} (pc : PathCover G U)
    (l : List (GraphPath G)) (hl : ∀ p ∈ l, p ∈ pc.paths) :
    supportUnion l ⊆ U := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := (mem_supportUnion_iff).1 hx
  exact pc.support_subset (hl p hp) hxp

lemma pairwise_filter {l : List (GraphPath G)} (P : GraphPath G → Bool)
    (h : l.Pairwise fun p q => Disjoint p.support q.support) :
    (l.filter P).Pairwise fun p q => Disjoint p.support q.support :=
  List.Pairwise.filter _ h

noncomputable def ofPathList {U : Finset V} (l : List (GraphPath G))
    (hdisj : l.Pairwise fun p q => Disjoint p.support q.support)
    (hU : ∀ x, x ∈ U ↔ ∃ p ∈ l, x ∈ p.support) : PathCover G U where
  paths := l
  disjoint := hdisj
  mem_iff := hU

lemma ofPathList_card {U : Finset V} (l : List (GraphPath G))
    (hdisj : l.Pairwise fun p q => Disjoint p.support q.support)
    (hU : ∀ x, x ∈ U ↔ ∃ p ∈ l, x ∈ p.support) :
    (ofPathList l hdisj hU).card = l.length := rfl

noncomputable def selCover {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) : PathCover G (supportUnion (pc.paths.filter P)) :=
  ofPathList (pc.paths.filter P)
    (pairwise_filter P pc.disjoint)
    (fun x => (mem_supportUnion_iff (l := pc.paths.filter P) (x := x)))

lemma selCover_card {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) :
    (selCover pc P).card = (pc.paths.filter P).length := rfl

lemma supportUnion_filter_union {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) :
    supportUnion (pc.paths.filter P) ∪
      supportUnion (pc.paths.filter fun p => !P p) = U := by
  ext x
  constructor
  · intro hx
    rcases mem_union.1 hx with hL | hR
    · obtain ⟨p, hp, hxp⟩ := mem_supportUnion_iff.1 hL
      exact pc.support_subset (List.mem_of_mem_filter hp) hxp
    · obtain ⟨p, hp, hxp⟩ := mem_supportUnion_iff.1 hR
      exact pc.support_subset (List.mem_of_mem_filter hp) hxp
  · intro hx
    obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hx
    by_cases hP : P p = true
    · exact mem_union.2 (Or.inl (mem_supportUnion_iff.2
        ⟨p, List.mem_filter.2 ⟨hp, hP⟩, hxp⟩))
    · have hP' : (!P p) = true := by
        cases hpP : P p <;> simp_all
      exact mem_union.2 (Or.inr (mem_supportUnion_iff.2
        ⟨p, List.mem_filter.2 ⟨hp, hP'⟩, hxp⟩))

lemma supportUnion_filter_disjoint {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) :
    Disjoint (supportUnion (pc.paths.filter P))
      (supportUnion (pc.paths.filter fun p => !P p)) := by
  rw [disjoint_iff_inter_eq_empty]
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := mem_supportUnion_iff.1 (mem_inter.1 hx).1
    obtain ⟨q, hq, hxq⟩ := mem_supportUnion_iff.1 (mem_inter.1 hx).2
    have hp' := List.mem_filter.1 hp
    have hq' := List.mem_filter.1 hq
    have hPp : P p = true := hp'.2
    have hPq : P q = false := by
      have : (!P q) = true := hq'.2
      simp at this
      exact this
    have hne : p ≠ q := fun heq => by
      subst heq
      simp [hPp] at hPq
    exact (Finset.disjoint_left.1
      (PathCover.pairwise_disjoint_of_mem pc.disjoint hp'.1 hq'.1 hne) hxp hxq).elim
  · intro hx
    exact (notMem_empty x hx).elim

lemma supportUnion_filter_sdiff {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) :
    supportUnion (pc.paths.filter fun p => !P p) =
      U \ supportUnion (pc.paths.filter P) := by
  have hU := supportUnion_filter_union pc P
  have hdisj := supportUnion_filter_disjoint pc P
  ext x
  constructor
  · intro hx
    exact mem_sdiff.2 ⟨(hU ▸ mem_union.2 (Or.inr hx)), fun hL =>
      Finset.disjoint_left.1 hdisj hL hx⟩
  · intro hx
    have hxU : x ∈ U := (mem_sdiff.1 hx).1
    have hxL : x ∉ supportUnion (pc.paths.filter P) := (mem_sdiff.1 hx).2
    have : x ∈ supportUnion (pc.paths.filter P) ∪
        supportUnion (pc.paths.filter fun p => !P p) := by
      rwa [hU]
    exact (mem_union.1 this).resolve_left hxL

noncomputable def replaceSel {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) (pcL : PathCover G (supportUnion (pc.paths.filter P))) :
    PathCover G U :=
  ofPathList
    ((pc.paths.filter fun p => !P p) ++ pcL.paths)
    (by
      refine List.pairwise_append.mpr
        ⟨pairwise_filter (fun p => !P p) pc.disjoint, pcL.disjoint, ?_⟩
      intro p hp q hq
      have hpU : p.support ⊆ U \ supportUnion (pc.paths.filter P) := by
        intro x hx
        have : x ∈ supportUnion (pc.paths.filter fun r => !P r) :=
          mem_supportUnion_iff.2 ⟨p, hp, hx⟩
        rwa [supportUnion_filter_sdiff pc P] at this
      have hqL : q.support ⊆ supportUnion (pc.paths.filter P) :=
        pcL.support_subset hq
      have hdisjUL :
          Disjoint (U \ supportUnion (pc.paths.filter P))
            (supportUnion (pc.paths.filter P)) :=
        disjoint_sdiff.symm
      exact Finset.disjoint_of_subset_left hpU
        (Finset.disjoint_of_subset_right hqL hdisjUL))
    (by
      intro x
      constructor
      · intro hx
        have hU := supportUnion_filter_union pc P
        have hx' : x ∈ supportUnion (pc.paths.filter P) ∪
            supportUnion (pc.paths.filter fun p => !P p) := by rwa [hU]
        rcases mem_union.1 hx' with hL | hR
        · obtain ⟨q, hq, hxq⟩ := (pcL.mem_iff x).1 hL
          exact ⟨q, List.mem_append.mpr (Or.inr hq), hxq⟩
        · obtain ⟨p, hp, hxp⟩ := mem_supportUnion_iff.1 hR
          exact ⟨p, List.mem_append.mpr (Or.inl hp), hxp⟩
      · intro ⟨p, hp, hxp⟩
        rcases List.mem_append.1 hp with hpR | hpL
        · exact pc.support_subset (List.mem_of_mem_filter hpR) hxp
        · exact supportUnion_subset_of_covers pc (pc.paths.filter P)
            (fun q hq => List.mem_of_mem_filter hq)
            ((pcL.mem_iff x).2 ⟨p, hpL, hxp⟩))

lemma replaceSel_paths {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) (pcL : PathCover G (supportUnion (pc.paths.filter P))) :
    (replaceSel pc P pcL).paths =
      (pc.paths.filter fun p => !P p) ++ pcL.paths :=
  rfl

lemma replaceSel_card {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) (pcL : PathCover G (supportUnion (pc.paths.filter P))) :
    (replaceSel pc P pcL).card =
      (pc.paths.filter fun p => !P p).length + pcL.card := by
  rw [PathCover.card, replaceSel_paths, List.length_append]
  rfl

/-- Cover replacement: a cheaper cover of the selected supports would
cheapen the original minimum cover. -/
lemma pathCoverNumber_selected {U : Finset V} (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) (P : GraphPath G → Bool) :
    pathCoverNumber G (supportUnion (pc.paths.filter P)) =
      (pc.paths.filter P).length := by
  have hle : pathCoverNumber G (supportUnion (pc.paths.filter P)) ≤
      (pc.paths.filter P).length := by
    simpa [selCover_card] using
      pathCoverNumber_le (G := G) (selCover pc P)
  refine le_antisymm hle ?_
  by_contra hlt
  obtain ⟨pcL, hL⟩ :=
    exists_min_pathCover (G := G) (supportUnion (pc.paths.filter P))
  have hsum := length_filter_add_not P pc.paths
  have hrep := replaceSel_card pc P pcL
  have hlen : pc.card = pc.paths.length := rfl
  have hpc' : (replaceSel pc P pcL).card < pc.card := by omega
  have : pathCoverNumber G U ≤ (replaceSel pc P pcL).card :=
    pathCoverNumber_le (G := G) (replaceSel pc P pcL)
  omega

lemma eligibleSet_selected_subset {U : Finset V} (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) (P : GraphPath G → Bool) :
    eligibleSet G (supportUnion (pc.paths.filter P)) ⊆
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) := by
  intro x hx
  have hxL : x ∈ supportUnion (pc.paths.filter P) :=
    eligibleSet_subset (G := G) _ hx
  have hxE := (mem_eligibleSet_iff (G := G)).1 hx
  obtain ⟨pcL, hL, p, hp, hxend⟩ := hxE.2
  have hm := pathCoverNumber_selected pc hpc P
  have hrep := replaceSel_card pc P pcL
  have hsum := length_filter_add_not P pc.paths
  have hlen : pc.card = pc.paths.length := rfl
  have hcard : (replaceSel pc P pcL).card = pathCoverNumber G U := by omega
  have hp' : p ∈ (replaceSel pc P pcL).paths := by
    rw [replaceSel_paths]
    exact List.mem_append.mpr (Or.inr hp)
  have hEl : Eligible G U x := ⟨replaceSel pc P pcL, hcard, p, hp', hxend⟩
  exact mem_inter.2 ⟨(mem_eligibleSet_iff (G := G)).2 ⟨hEl.mem, hEl⟩, hxL⟩

lemma ineligibleSet_selected_supset {U : Finset V} (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) (P : GraphPath G → Bool) :
    ineligibleSet G U ∩ supportUnion (pc.paths.filter P) ⊆
      ineligibleSet G (supportUnion (pc.paths.filter P)) := by
  intro x hx
  have hxF := (mem_ineligibleSet_iff (G := G)).1 (mem_inter.1 hx).1
  have hxL : x ∈ supportUnion (pc.paths.filter P) := (mem_inter.1 hx).2
  refine (mem_ineligibleSet_iff (G := G)).2 ⟨hxL, ?_⟩
  intro hE
  have hxE : x ∈ eligibleSet G (supportUnion (pc.paths.filter P)) :=
    (mem_eligibleSet_iff (G := G)).2 ⟨hxL, hE⟩
  have hxU := eligibleSet_selected_subset pc hpc P hxE
  exact hxF.2 ((mem_eligibleSet_iff (G := G)).1 (mem_inter.1 hxU).1).2

lemma exists_pathCover_sdiff {U S : Finset V} (pc : PathCover G U)
    (hS : S ⊆ U) :
    ∃ pc' : PathCover G (U \ S),
      pc'.card ≤ pc.card + S.card ∧
      ∀ q ∈ pc'.paths, ∃ p ∈ pc.paths, q.support ⊆ p.support := by
  induction S using Finset.induction generalizing U pc with
  | empty =>
    refine ⟨pc.cast (by simp), ?_, ?_⟩
    · simp [PathCover.cast_card]
    · intro q hq
      rw [PathCover.cast_paths] at hq
      exact ⟨q, hq, subset_rfl⟩
  | insert b S hb ih =>
    have hSsub : S ⊆ U.erase b := by
      intro y hy
      exact mem_erase.2 ⟨fun hby => hb (hby ▸ hy), hS (mem_insert_of_mem hy)⟩
    obtain ⟨pc1, hcard1, hsup1⟩ :=
      ih (U := U.erase b) (pc.deleteVertex b) hSsub
    have hEq : U.erase b \ S = U \ insert b S := by
      rw [sdiff_insert, erase_sdiff_distrib, erase_eq_of_notMem hb]
    refine ⟨pc1.cast hEq, ?_, ?_⟩
    · have hdv := pc.card_deleteVertex_le b
      have hins : (insert b S).card = S.card + 1 := card_insert_of_notMem hb
      rw [PathCover.cast_card]
      omega
    · intro q hq
      rw [PathCover.cast_paths] at hq
      obtain ⟨r, hr, hqr⟩ := hsup1 q hq
      obtain ⟨p, hp, hr'⟩ := List.mem_flatMap.1 (show r ∈
          (pc.paths.flatMap fun t => GraphPath.deleteVertex t b) from by
        simpa [PathCover.deleteVertex] using hr)
      exact ⟨p, hp, hqr.trans (GraphPath.support_subset_of_mem_deleteVertex hr')⟩

lemma mem_filter_bool_or {α : Type*} (P : α → Bool) {a : α} {l : List α}
    (ha : a ∈ l) : a ∈ l.filter P ∨ a ∈ l.filter fun x => !P x := by
  cases hP : P a
  · exact Or.inr (List.mem_filter.2 ⟨ha, by simp [hP]⟩)
  · exact Or.inl (List.mem_filter.2 ⟨ha, hP⟩)

lemma L_sdiff_F0_eq_eligible_inter {U : Finset V} (pc : PathCover G U)
    (P : GraphPath G → Bool) :
    supportUnion (pc.paths.filter P) \
        (ineligibleSet G U ∩ supportUnion (pc.paths.filter P)) =
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) := by
  ext z
  constructor
  · intro hz
    have hzL : z ∈ supportUnion (pc.paths.filter P) := (mem_sdiff.1 hz).1
    have hzF : z ∉ ineligibleSet G U ∩ supportUnion (pc.paths.filter P) :=
      (mem_sdiff.1 hz).2
    have hzU : z ∈ U := supportUnion_subset_of_covers pc (pc.paths.filter P)
      (fun p hp => List.mem_of_mem_filter hp) hzL
    have hzE : z ∈ eligibleSet G U := by
      by_contra hnot
      have : z ∈ ineligibleSet G U :=
        (mem_ineligibleSet_iff (G := G)).2 ⟨hzU, fun hE =>
          hnot ((mem_eligibleSet_iff (G := G)).2 ⟨hzU, hE⟩)⟩
      exact hzF (mem_inter.2 ⟨this, hzL⟩)
    exact mem_inter.2 ⟨hzE, hzL⟩
  · intro hz
    refine mem_sdiff.2 ⟨(mem_inter.1 hz).2, ?_⟩
    intro hF
    exact (disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) U)
      (mem_inter.1 hz).1) (mem_inter.1 hF).1

lemma eligible_sdiff_eq_unselected_remainder {U : Finset V}
    (pc : PathCover G U) (P : GraphPath G → Bool) :
    eligibleSet G U \ supportUnion (pc.paths.filter P) =
      (U \ supportUnion (pc.paths.filter P)) \
        (ineligibleSet G U \ supportUnion (pc.paths.filter P)) := by
  ext z
  constructor
  · intro hz
    have hzE := (mem_eligibleSet_iff (G := G)).1 (mem_sdiff.1 hz).1
    have hzL : z ∉ supportUnion (pc.paths.filter P) := (mem_sdiff.1 hz).2
    refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hzE.1, hzL⟩, ?_⟩
    intro hF
    exact ((mem_ineligibleSet_iff (G := G)).1 (mem_sdiff.1 hF).1).2 hzE.2
  · intro hz
    have hzUL := mem_sdiff.1 (mem_sdiff.1 hz).1
    have hzF : z ∉ ineligibleSet G U \ supportUnion (pc.paths.filter P) :=
      (mem_sdiff.1 hz).2
    have hnotF : z ∉ ineligibleSet G U := fun h =>
      hzF (mem_sdiff.2 ⟨h, hzUL.2⟩)
    have hE : Eligible G U z := by
      have h := (mem_ineligibleSet_iff (G := G) (U := U) (x := z)).not
      simp only [not_and, Classical.not_not] at h
      exact h.mp hnotF hzUL.1
    exact mem_sdiff.2 ⟨(mem_eligibleSet_iff (G := G)).2 ⟨hzUL.1, hE⟩, hzUL.2⟩

lemma exists_remainder_cover_of_ineligible {U : Finset V}
    (hU : CotreeOn G U) (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) :
    ∃ pc' : PathCover G (eligibleSet G U),
      pc'.card = componentCount G (eligibleSet G U) ∧
      pc'.card = pathCoverNumber G U + (ineligibleSet G U).card ∧
      ∀ q ∈ pc'.paths, ∃ p ∈ pc.paths, q.support ⊆ p.support := by
  have hFsub : ineligibleSet G U ⊆ U := ineligibleSet_subset (G := G) U
  obtain ⟨pc1, hcard1, hsup1⟩ := exists_pathCover_sdiff pc hFsub
  have hE : U \ ineligibleSet G U = eligibleSet G U :=
    (eligibleSet_eq_sdiff_ineligible (G := G) U).symm
  let pc' : PathCover G (eligibleSet G U) := pc1.cast hE
  have hcut := componentCount_sdiff_ineligibleSet_eq hU
  have hCE : componentCount G (eligibleSet G U) =
      (ineligibleSet G U).card + pathCoverNumber G U := by
    simpa [eligibleSet_eq_sdiff_ineligible (G := G) U] using hcut
  have hple := pathCoverNumber_le (G := G) pc'
  have hcle := componentCount_le_pathCoverNumber (G := G) (eligibleSet G U)
  have hcard' : pc'.card ≤ pathCoverNumber G U + (ineligibleSet G U).card := by
    rw [PathCover.cast_card]; omega
  have hpcard : pc'.card = pathCoverNumber G U + (ineligibleSet G U).card := by
    omega
  refine ⟨pc', ?_, hpcard, ?_⟩
  · omega
  · intro q hq
    rw [PathCover.cast_paths] at hq
    exact hsup1 q hq

lemma componentCount_lt_of_adj_between_paths {W : Finset V}
    (pc : PathCover G W) {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    {a b : V} (ha : a ∈ p.support) (hb : b ∈ q.support)
    (hadj : G.Adj a b) :
    componentCount G W < pc.card := by
  let f : Fin pc.paths.length → (G.induce (W : Set V)).ConnectedComponent :=
    fun i =>
      (G.induce (W : Set V)).connectedComponentMk
        ⟨(pc.paths.get i).start,
          pc.support_subset (List.mem_iff_get.2 ⟨i, rfl⟩)
            (pc.paths.get i).start_mem_support⟩
  have hf : Function.Surjective f := by
    intro C
    refine C.ind fun x => ?_
    obtain ⟨r, hr, hxr⟩ := (pc.mem_iff x.1).1 x.2
    obtain ⟨k, hk⟩ := List.mem_iff_get.1 hr
    refine ⟨k, ConnectedComponent.sound ?_⟩
    have hsub : r.support ⊆ W := pc.support_subset hr
    have hR :=
      reachable_of_mem_graphPath (U := W) r hsub r.start_mem_support hxr
    have heq :
        (⟨(pc.paths.get k).start,
            pc.support_subset (List.mem_iff_get.2 ⟨k, rfl⟩)
              (pc.paths.get k).start_mem_support⟩ : (W : Set V)) =
          ⟨r.start, hsub r.start_mem_support⟩ :=
      Subtype.ext (congrArg GraphPath.start hk)
    rw [heq]; exact hR
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 hp
  obtain ⟨j, hj⟩ := List.mem_iff_get.1 hq
  have hij : i ≠ j := fun heq => hne (hi.symm.trans (heq ▸ hj))
  have hsubp : p.support ⊆ W := pc.support_subset hp
  have hsubq : q.support ⊆ W := pc.support_subset hq
  have hsame : f i = f j := by
    apply ConnectedComponent.sound
    have hpa :=
      reachable_of_mem_graphPath (U := W) p hsubp p.start_mem_support ha
    have hqb :=
      reachable_of_mem_graphPath (U := W) q hsubq hb q.start_mem_support
    have hab : (G.induce (W : Set V)).Reachable
        ⟨a, hsubp ha⟩ ⟨b, hsubq hb⟩ :=
      Adj.reachable (by simpa [induce_adj] using hadj)
    have hi' :
        (⟨(pc.paths.get i).start,
            pc.support_subset (List.mem_iff_get.2 ⟨i, rfl⟩)
              (pc.paths.get i).start_mem_support⟩ : (W : Set V)) =
          ⟨p.start, hsubp p.start_mem_support⟩ :=
      Subtype.ext (congrArg GraphPath.start hi)
    have hj' :
        (⟨(pc.paths.get j).start,
            pc.support_subset (List.mem_iff_get.2 ⟨j, rfl⟩)
              (pc.paths.get j).start_mem_support⟩ : (W : Set V)) =
          ⟨q.start, hsubq q.start_mem_support⟩ :=
      Subtype.ext (congrArg GraphPath.start hj)
    rw [hi', hj']
    exact hpa.trans (hab.trans hqb)
  have hnInj : ¬ Function.Injective f := fun hinj => hij (hinj hsame)
  haveI : Fintype (G.induce (W : Set V)).ConnectedComponent := inferInstance
  have hlt : Fintype.card (G.induce (W : Set V)).ConnectedComponent <
      Fintype.card (Fin pc.paths.length) :=
    Fintype.card_lt_of_surjective_not_injective f hf hnInj
  simpa [componentCount, PathCover.card, Nat.card_eq_fintype_card,
    Fintype.card_fin] using hlt

lemma no_adj_of_card_eq_componentCount {W : Finset V}
    (pc : PathCover G W) (heq : pc.card = componentCount G W)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths)
    (hne : p ≠ q) {a b : V}
    (ha : a ∈ p.support) (hb : b ∈ q.support) : ¬ G.Adj a b := by
  intro hadj
  have := componentCount_lt_of_adj_between_paths pc hp hq hne ha hb hadj
  omega

lemma no_cross_selected_remainder {U : Finset V} (hU : CotreeOn G U)
    (pc : PathCover G U) (hpc : pc.card = pathCoverNumber G U)
    (P : GraphPath G → Bool) {a b : V}
    (ha : a ∈ eligibleSet G U ∩ supportUnion (pc.paths.filter P))
    (hb : b ∈ eligibleSet G U \ supportUnion (pc.paths.filter P)) :
    ¬ G.Adj a b := by
  obtain ⟨pc', hcomp, _, hsup⟩ :=
    exists_remainder_cover_of_ineligible hU pc hpc
  have haE : a ∈ eligibleSet G U := (mem_inter.1 ha).1
  have haL : a ∈ supportUnion (pc.paths.filter P) := (mem_inter.1 ha).2
  have hbE : b ∈ eligibleSet G U := (mem_sdiff.1 hb).1
  have hbL : b ∉ supportUnion (pc.paths.filter P) := (mem_sdiff.1 hb).2
  obtain ⟨qa, hqa, haq⟩ := (pc'.mem_iff a).1 haE
  obtain ⟨qb, hqb, hbq⟩ := (pc'.mem_iff b).1 hbE
  obtain ⟨pa, hpa, hqaP⟩ := hsup qa hqa
  have hne : qa ≠ qb := by
    intro heq
    have hbqa : b ∈ qa.support := by
      have : b ∈ qb.support := hbq
      rwa [heq]
    rcases mem_filter_bool_or P hpa with hP | hR
    · exact hbL (mem_supportUnion_iff.2 ⟨pa, hP, hqaP hbqa⟩)
    · have haR : a ∈ supportUnion (pc.paths.filter fun r => !P r) :=
        mem_supportUnion_iff.2 ⟨pa, hR, hqaP haq⟩
      have : a ∈ U \ supportUnion (pc.paths.filter P) := by
        rwa [supportUnion_filter_sdiff pc P] at haR
      exact (mem_sdiff.1 this).2 haL
  exact no_adj_of_card_eq_componentCount pc' hcomp hqa hqb hne haq hbq

lemma componentCount_eligible_split {U : Finset V} (hU : CotreeOn G U)
    (pc : PathCover G U) (hpc : pc.card = pathCoverNumber G U)
    (P : GraphPath G → Bool) :
    componentCount G (eligibleSet G U) =
      componentCount G (eligibleSet G U ∩ supportUnion (pc.paths.filter P)) +
        componentCount G (eligibleSet G U \ supportUnion (pc.paths.filter P)) := by
  have hsplit : eligibleSet G U =
      (eligibleSet G U ∩ supportUnion (pc.paths.filter P)) ∪
        (eligibleSet G U \ supportUnion (pc.paths.filter P)) := by
    ext z
    constructor
    · intro hz
      by_cases hL : z ∈ supportUnion (pc.paths.filter P)
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hL⟩))
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hz, hL⟩))
    · intro hz
      rcases mem_union.1 hz with h | h
      · exact (mem_inter.1 h).1
      · exact (mem_sdiff.1 h).1
  have hdisj :
      Disjoint (eligibleSet G U ∩ supportUnion (pc.paths.filter P))
        (eligibleSet G U \ supportUnion (pc.paths.filter P)) := by
    rw [disjoint_iff_inter_eq_empty]
    ext z
    constructor
    · intro hz
      exact ((mem_sdiff.1 (mem_inter.1 hz).2).2 (mem_inter.1 (mem_inter.1 hz).1).2).elim
    · intro hz
      exact (notMem_empty z hz).elim
  have hnocross :
      ∀ a ∈ eligibleSet G U ∩ supportUnion (pc.paths.filter P),
        ∀ b ∈ eligibleSet G U \ supportUnion (pc.paths.filter P), ¬ G.Adj a b :=
    fun a ha b hb => no_cross_selected_remainder hU pc hpc P ha hb
  have h := componentCount_union_of_no_cross hdisj hnocross
  rwa [← hsplit] at h

lemma componentCount_selected_remainder {U : Finset V} (hU : CotreeOn G U)
    (pc : PathCover G U) (hpc : pc.card = pathCoverNumber G U)
    (P : GraphPath G → Bool) :
    componentCount G
        (eligibleSet G U ∩ supportUnion (pc.paths.filter P)) =
      (ineligibleSet G U ∩ supportUnion (pc.paths.filter P)).card +
        (pc.paths.filter P).length := by
  have hsplit := componentCount_eligible_split hU pc hpc P
  have hCE : componentCount G (eligibleSet G U) =
      (ineligibleSet G U).card + pathCoverNumber G U := by
    simpa [eligibleSet_eq_sdiff_ineligible (G := G) U] using
      componentCount_sdiff_ineligibleSet_eq hU
  have hrest := eligible_sdiff_eq_unselected_remainder pc P
  have hsub :
      ineligibleSet G U \ supportUnion (pc.paths.filter P) ⊆
        U \ supportUnion (pc.paths.filter P) :=
    sdiff_subset_sdiff (ineligibleSet_subset (G := G) U) subset_rfl
  have hcle :
      componentCount G (eligibleSet G U \ supportUnion (pc.paths.filter P)) ≤
        pathCoverNumber G (U \ supportUnion (pc.paths.filter P)) +
          (ineligibleSet G U \ supportUnion (pc.paths.filter P)).card := by
    simpa [hrest] using
      componentCount_sdiff_le (G := G)
        (U \ supportUnion (pc.paths.filter P))
        (ineligibleSet G U \ supportUnion (pc.paths.filter P)) hsub
  have hcov :
      pathCoverNumber G (U \ supportUnion (pc.paths.filter P)) ≤
        (pc.paths.filter fun p => !P p).length := by
    have hrem := supportUnion_filter_sdiff pc P
    simpa [selCover_card, PathCover.cast_card] using
      pathCoverNumber_le (G := G)
        ((selCover pc (fun p => !P p)).cast hrem)
  have hsum := length_filter_add_not P pc.paths
  have hlen : pc.card = pc.paths.length := rfl
  have hFsplit :
      (ineligibleSet G U ∩ supportUnion (pc.paths.filter P)).card +
        (ineligibleSet G U \ supportUnion (pc.paths.filter P)).card =
      (ineligibleSet G U).card := by
    have hun : ineligibleSet G U ∩ supportUnion (pc.paths.filter P) ∪
        ineligibleSet G U \ supportUnion (pc.paths.filter P) =
        ineligibleSet G U := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with h | h
        · exact (mem_inter.1 h).1
        · exact (mem_sdiff.1 h).1
      · intro hz
        by_cases hL : z ∈ supportUnion (pc.paths.filter P)
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hL⟩))
        · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hz, hL⟩))
    have hdisj :
        Disjoint (ineligibleSet G U ∩ supportUnion (pc.paths.filter P))
          (ineligibleSet G U \ supportUnion (pc.paths.filter P)) := by
      rw [disjoint_iff_inter_eq_empty]
      ext z
      constructor
      · intro hz
        exact ((mem_sdiff.1 (mem_inter.1 hz).2).2 (mem_inter.1 (mem_inter.1 hz).1).2).elim
      · intro hz
        exact (notMem_empty z hz).elim
    rw [← card_union_of_disjoint hdisj, hun]
  have hm := pathCoverNumber_selected pc hpc P
  have hLF0 := L_sdiff_F0_eq_eligible_inter pc P
  have hle :
      componentCount G (eligibleSet G U ∩ supportUnion (pc.paths.filter P)) ≤
        pathCoverNumber G (supportUnion (pc.paths.filter P)) +
          (ineligibleSet G U ∩ supportUnion (pc.paths.filter P)).card := by
    have hsubL : ineligibleSet G U ∩ supportUnion (pc.paths.filter P) ⊆
        supportUnion (pc.paths.filter P) := inter_subset_right
    have := componentCount_sdiff_le (G := G)
      (supportUnion (pc.paths.filter P))
      (ineligibleSet G U ∩ supportUnion (pc.paths.filter P)) hsubL
    simpa [hLF0] using this
  omega

lemma restriction_of_min_cover {U : Finset V} (hU : CotreeOn G U)
    (pc : PathCover G U) (hpc : pc.card = pathCoverNumber G U)
    (P : GraphPath G → Bool) :
    pathCoverNumber G (supportUnion (pc.paths.filter P)) =
      (pc.paths.filter P).length ∧
    eligibleSet G (supportUnion (pc.paths.filter P)) ⊆
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) ∧
    ineligibleSet G U ∩ supportUnion (pc.paths.filter P) ⊆
      ineligibleSet G (supportUnion (pc.paths.filter P)) :=
  ⟨pathCoverNumber_selected pc hpc P,
    eligibleSet_selected_subset pc hpc P,
    ineligibleSet_selected_supset pc hpc P⟩

lemma ineligibleSet_selected_eq {U : Finset V} (hU : CotreeOn G U)
    (pc : PathCover G U) (hpc : pc.card = pathCoverNumber G U)
    (P : GraphPath G → Bool) :
    ineligibleSet G (supportUnion (pc.paths.filter P)) =
      ineligibleSet G U ∩ supportUnion (pc.paths.filter P) := by
  set L := supportUnion (pc.paths.filter P)
  set m := (pc.paths.filter P).length
  set F := ineligibleSet G U
  set F0 := F ∩ L
  set FL := ineligibleSet G L
  have hm := pathCoverNumber_selected pc hpc P
  have hF0sub := ineligibleSet_selected_supset pc hpc P
  have hLsub : L ⊆ U := supportUnion_subset_of_covers pc (pc.paths.filter P)
    (fun p hp => List.mem_of_mem_filter hp)
  have hLc : IsCograph G L :=
    isCograph_mono (isCograph_of_cotreeOn hU) hLsub
  have hcutL :=
    componentCount_sdiff_ineligibleSet_eq (cotreeOn_of_isCograph hLc)
  have hEsub := eligibleSet_selected_subset pc hpc P
  refine subset_antisymm ?_ hF0sub
  intro v hvFL
  by_contra hvF0
  have hvL : v ∈ L := ineligibleSet_subset (G := G) L hvFL
  have hvnotF : v ∉ F := fun h => hvF0 (mem_inter.2 ⟨h, hvL⟩)
  let S := (F \ L) ∪ FL
  have hFLsub : FL ⊆ L := ineligibleSet_subset (G := G) L
  have hdisjS : Disjoint (F \ L) FL := by
    rw [disjoint_iff_inter_eq_empty]
    ext z
    constructor
    · intro hz
      exact ((mem_sdiff.1 (mem_inter.1 hz).1).2 (hFLsub (mem_inter.1 hz).2)).elim
    · intro hz
      exact (notMem_empty z hz).elim
  have hSsub : S ⊆ U := by
    intro z hz
    rcases mem_union.1 hz with h | h
    · exact ineligibleSet_subset (G := G) U (mem_sdiff.1 h).1
    · exact hLsub (hFLsub h)
  have hUrem : U \ S = (eligibleSet G U \ L) ∪ (L \ FL) := by
    ext z
    constructor
    · intro hz
      have hzU : z ∈ U := (mem_sdiff.1 hz).1
      have hzN : z ∉ S := (mem_sdiff.1 hz).2
      by_cases hzL : z ∈ L
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hzL, fun hFL =>
          hzN (mem_union.2 (Or.inr hFL))⟩))
      · have hzE : z ∈ eligibleSet G U := by
          have hnotF : z ∉ F := fun h =>
            hzN (mem_union.2 (Or.inl (mem_sdiff.2 ⟨h, hzL⟩)))
          have h := (mem_ineligibleSet_iff (G := G) (U := U) (x := z)).not
          simp only [not_and, Classical.not_not] at h
          exact (mem_eligibleSet_iff (G := G)).2 ⟨hzU, h.mp hnotF hzU⟩
        exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzE, hzL⟩))
    · intro hz
      rcases mem_union.1 hz with hE | hL
      · have hzE := (mem_eligibleSet_iff (G := G)).1 (mem_sdiff.1 hE).1
        have hzL : z ∉ L := (mem_sdiff.1 hE).2
        refine mem_sdiff.2 ⟨hzE.1, ?_⟩
        intro hS
        rcases mem_union.1 hS with hzF | hzFL
        · exact ((mem_ineligibleSet_iff (G := G)).1 (mem_sdiff.1 hzF).1).2 hzE.2
        · exact hzL (hFLsub hzFL)
      · have hzL : z ∈ L := (mem_sdiff.1 hL).1
        have hzFL : z ∉ FL := (mem_sdiff.1 hL).2
        refine mem_sdiff.2 ⟨hLsub hzL, ?_⟩
        intro hS
        rcases mem_union.1 hS with hzF | hzFL'
        · exact (mem_sdiff.1 hzF).2 hzL
        · exact hzFL hzFL'
  have hdisjRem : Disjoint (eligibleSet G U \ L) (L \ FL) := by
    rw [disjoint_iff_inter_eq_empty]
    ext z
    constructor
    · intro hz
      exact ((mem_sdiff.1 (mem_inter.1 hz).1).2 (mem_sdiff.1 (mem_inter.1 hz).2).1).elim
    · intro hz
      exact (notMem_empty z hz).elim
  have hnocross :
      ∀ a ∈ eligibleSet G U \ L, ∀ b ∈ L \ FL, ¬ G.Adj a b := by
    intro a ha b hb hadj
    have hbL : b ∈ L := (mem_sdiff.1 hb).1
    have hbnotFL : b ∉ FL := (mem_sdiff.1 hb).2
    have hbEL : Eligible G L b := by
      have h := (mem_ineligibleSet_iff (G := G) (U := L) (x := b)).not
      simp only [not_and, Classical.not_not] at h
      exact h.mp hbnotFL hbL
    have hbE := hEsub ((mem_eligibleSet_iff (G := G)).2 ⟨hbL, hbEL⟩)
    exact no_cross_selected_remainder hU pc hpc P hbE ha hadj.symm
  have hadd := componentCount_union_of_no_cross hdisjRem hnocross
  have hUS : componentCount G (U \ S) =
      componentCount G (eligibleSet G U \ L) + componentCount G (L \ FL) := by
    have h := hadd
    rwa [← hUrem] at h
  have hCFL : componentCount G (L \ FL) = FL.card + m := by
    have h := hcutL
    rw [hm] at h
    exact h
  have hsplit := componentCount_eligible_split hU pc hpc P
  have hCE : componentCount G (eligibleSet G U) =
      F.card + pathCoverNumber G U := by
    simpa [eligibleSet_eq_sdiff_ineligible (G := G) U] using
      componentCount_sdiff_ineligibleSet_eq hU
  have hCEL := componentCount_selected_remainder hU pc hpc P
  have hCun :
      componentCount G (eligibleSet G U ∩ L) +
        componentCount G (eligibleSet G U \ L) =
      F.card + pathCoverNumber G U := by
    have h1 : componentCount G (eligibleSet G U) =
        componentCount G (eligibleSet G U ∩ L) +
          componentCount G (eligibleSet G U \ L) := by
      convert hsplit
    exact h1.symm.trans hCE
  have hFsplit :
      F0.card + (F \ L).card = F.card := by
    have hun : F0 ∪ (F \ L) = F := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with h | h
        · exact (mem_inter.1 h).1
        · exact (mem_sdiff.1 h).1
      · intro hz
        by_cases hL : z ∈ L
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hL⟩))
        · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hz, hL⟩))
    have hdisj : Disjoint F0 (F \ L) := by
      rw [disjoint_iff_inter_eq_empty]
      ext z
      constructor
      · intro hz
        exact ((mem_sdiff.1 (mem_inter.1 hz).2).2 (mem_inter.1 (mem_inter.1 hz).1).2).elim
      · intro hz
        exact (notMem_empty z hz).elim
    rw [← card_union_of_disjoint hdisj, hun]
  have hScard : S.card = (F \ L).card + FL.card :=
    card_union_of_disjoint hdisjS
  have hatt : componentCount G (U \ S) = pathCoverNumber G U + S.card := by
    have h1 := hUS
    have h2 := hCFL
    have h3 := hCun
    have h4 := hCEL
    have h5 := hFsplit
    have h6 := hScard
    have h7 := hpc
    have h8 := hm
    dsimp [L, m, F, F0, FL, S] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    omega
  have hSinc := eq_cut_bound_imp_subset_ineligible hSsub hatt
  have hvS : v ∈ S := mem_union.2 (Or.inr hvFL)
  have hvF : v ∈ F := hSinc hvS
  exact hvnotF hvF

lemma eligibleSet_selected_eq {U : Finset V} (hU : CotreeOn G U)
    (pc : PathCover G U) (hpc : pc.card = pathCoverNumber G U)
    (P : GraphPath G → Bool) :
    eligibleSet G (supportUnion (pc.paths.filter P)) =
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) := by
  refine subset_antisymm (eligibleSet_selected_subset pc hpc P) ?_
  intro x hx
  have hxU : x ∈ eligibleSet G U := (mem_inter.1 hx).1
  have hxL : x ∈ supportUnion (pc.paths.filter P) := (mem_inter.1 hx).2
  have hFeq := ineligibleSet_selected_eq hU pc hpc P
  have hxnotF : x ∉ ineligibleSet G (supportUnion (pc.paths.filter P)) := by
    intro hxF
    have : x ∈ ineligibleSet G U ∩ supportUnion (pc.paths.filter P) := by
      rwa [← hFeq]
    exact (disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) U)
      hxU) (mem_inter.1 this).1
  have hE : Eligible G (supportUnion (pc.paths.filter P)) x := by
    have h := (mem_ineligibleSet_iff (G := G)
      (U := supportUnion (pc.paths.filter P)) (x := x)).not
    simp only [not_and, Classical.not_not] at h
    exact h.mp hxnotF hxL
  exact (mem_eligibleSet_iff (G := G)).2 ⟨hxL, hE⟩

lemma restriction_eq_of_min_cover {U : Finset V} (hU : CotreeOn G U)
    (pc : PathCover G U) (hpc : pc.card = pathCoverNumber G U)
    (P : GraphPath G → Bool) :
    pathCoverNumber G (supportUnion (pc.paths.filter P)) =
      (pc.paths.filter P).length ∧
    eligibleSet G (supportUnion (pc.paths.filter P)) =
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) ∧
    ineligibleSet G (supportUnion (pc.paths.filter P)) =
      ineligibleSet G U ∩ supportUnion (pc.paths.filter P) :=
  ⟨pathCoverNumber_selected pc hpc P,
    eligibleSet_selected_eq hU pc hpc P,
    ineligibleSet_selected_eq hU pc hpc P⟩

lemma restriction_eq_of_min_cover_of_isCograph {U : Finset V}
    (hU : IsCograph G U) (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) (P : GraphPath G → Bool) :
    pathCoverNumber G (supportUnion (pc.paths.filter P)) =
      (pc.paths.filter P).length ∧
    eligibleSet G (supportUnion (pc.paths.filter P)) =
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) ∧
    ineligibleSet G (supportUnion (pc.paths.filter P)) =
      ineligibleSet G U ∩ supportUnion (pc.paths.filter P) :=
  restriction_eq_of_min_cover (cotreeOn_of_isCograph hU) pc hpc P

lemma restriction_eq_of_min_cover_of_canonical {U : Finset V}
    (hU : Nikoghosyan.IsCograph G U) (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) (P : GraphPath G → Bool) :
    pathCoverNumber G (supportUnion (pc.paths.filter P)) =
      (pc.paths.filter P).length ∧
    eligibleSet G (supportUnion (pc.paths.filter P)) =
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) ∧
    ineligibleSet G (supportUnion (pc.paths.filter P)) =
      ineligibleSet G U ∩ supportUnion (pc.paths.filter P) :=
  restriction_eq_of_min_cover_of_isCograph (isCograph_iff.2 hU) pc hpc P

lemma restriction_of_min_cover_of_isCograph {U : Finset V}
    (hU : IsCograph G U) (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) (P : GraphPath G → Bool) :
    pathCoverNumber G (supportUnion (pc.paths.filter P)) =
      (pc.paths.filter P).length ∧
    eligibleSet G (supportUnion (pc.paths.filter P)) ⊆
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) ∧
    ineligibleSet G U ∩ supportUnion (pc.paths.filter P) ⊆
      ineligibleSet G (supportUnion (pc.paths.filter P)) :=
  restriction_of_min_cover (cotreeOn_of_isCograph hU) pc hpc P

lemma restriction_of_min_cover_of_canonical {U : Finset V}
    (hU : Nikoghosyan.IsCograph G U) (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) (P : GraphPath G → Bool) :
    pathCoverNumber G (supportUnion (pc.paths.filter P)) =
      (pc.paths.filter P).length ∧
    eligibleSet G (supportUnion (pc.paths.filter P)) ⊆
      eligibleSet G U ∩ supportUnion (pc.paths.filter P) ∧
    ineligibleSet G U ∩ supportUnion (pc.paths.filter P) ⊆
      ineligibleSet G (supportUnion (pc.paths.filter P)) :=
  restriction_of_min_cover_of_isCograph (isCograph_iff.2 hU) pc hpc P

end Cograph
end Nikoghosyan

