/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.PathCover

/-!
# Path-cover refinement by splitting original-edge paths

Any count between `pathCoverNumber G U` and `U.card` is realized by an actual
`PathCover`: a non-singleton cover path splits along its first original edge
into two nonempty disjoint pieces and the cover cardinality increases by one.
This module does not redefine covers or assume a cover of a given size exists.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GraphPath

private lemma nodup_support (p : GraphPath G) : p.walk.support.Nodup :=
  (Walk.isPath_def _).1 p.isPath

private lemma path_support_card (p : GraphPath G) :
    p.support.card = p.walk.length + 1 := by
  simp [support, List.toFinset_card_of_nodup p.nodup_support, Walk.length_support]

lemma not_nil_of_two_le_card (p : GraphPath G) (h : 2 ≤ p.support.card) :
    ¬ p.walk.Nil := by
  intro hn
  have hlen : p.walk.length = 0 := Walk.length_eq_zero_iff.2 hn
  have hcard : p.support.card = 1 := by rw [path_support_card p, hlen]
  omega

/-- Tail of a non-nil original-edge path, itself an original-edge path. -/
def tailOfWalk : ∀ {u v : V} (p : G.Walk u v), p.IsPath → ¬ p.Nil → GraphPath G
  | _, _, .nil, _, h => absurd Walk.nil_nil h
  | _, v, .cons hadj q, hp, _ =>
    ⟨_, v, q, ((Walk.cons_isPath_iff hadj q).1 hp).1⟩

def tail (p : GraphPath G) (h : ¬ p.walk.Nil) : GraphPath G :=
  tailOfWalk p.walk p.isPath h

lemma support_eq_insert_start_tail (p : GraphPath G) (h : ¬ p.walk.Nil) :
    p.support = insert p.start (p.tail h).support := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q =>
    simp [tail, tailOfWalk, support]

lemma start_not_mem_tail_support (p : GraphPath G) (h : ¬ p.walk.Nil) :
    p.start ∉ (p.tail h).support := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q =>
    have hq : u ∉ q.support := ((Walk.cons_isPath_iff hadj q).1 isPath).2
    simpa [tail, tailOfWalk, support] using hq

lemma disjoint_singleton_start_tail (p : GraphPath G) (h : ¬ p.walk.Nil) :
    Disjoint (GraphPath.singleton (G := G) p.start).support (p.tail h).support := by
  rw [support_singleton, disjoint_singleton_left]
  exact start_not_mem_tail_support p h

lemma tail_support_subset (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.tail h).support ⊆ p.support := by
  rw [support_eq_insert_start_tail p h]
  exact subset_insert _ _

lemma singleton_start_support_subset (p : GraphPath G) :
    (GraphPath.singleton (G := G) p.start).support ⊆ p.support := by
  simp [support_singleton, start_mem_support]

lemma mem_support_iff_start_or_tail (p : GraphPath G) (h : ¬ p.walk.Nil) {x : V} :
    x ∈ p.support ↔ x = p.start ∨ x ∈ (p.tail h).support := by
  rw [support_eq_insert_start_tail p h, mem_insert]

end GraphPath

namespace PathCover

lemma nodup_paths {U : Finset V} (pc : PathCover G U) : pc.paths.Nodup := by
  refine List.Pairwise.imp ?_ pc.disjoint
  intro a b hdisj hab
  subst hab
  have : a.support ∩ a.support = ∅ := disjoint_iff_inter_eq_empty.1 hdisj
  simp only [inter_self] at this
  exact (nonempty_iff_ne_empty.1 a.support_nonempty) this

lemma pairwise_disjoint_of_mem_refinement {l : List (GraphPath G)}
    (h : l.Pairwise fun a b => Disjoint a.support b.support)
    {a b : GraphPath G} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    Disjoint a.support b.support := by
  induction l generalizing a b with
  | nil => cases ha
  | cons x xs ih =>
    have h' := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact (hne rfl).elim
    · exact h'.1 b hb'
    · exact (h'.1 a ha').symm
    · exact ih h'.2 ha' hb' hne

lemma length_filter_add_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter fun x => !p x).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases ha : p a
    · simp [ha]; omega
    · simp [ha]; omega

lemma filter_eq_singleton_of_nodup {α : Type*} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ l → l.Nodup → l.filter (fun x => decide (x = a)) = [a]
  | [], h, _ => by cases h
  | b :: l, h, hn => by
    have hn' := List.nodup_cons.1 hn
    rcases List.mem_cons.1 h with rfl | ha
    · have hnone : l.filter (fun x => decide (x = a)) = [] := by
        refine List.filter_eq_nil_iff.2 ?_
        intro x hx hxeq
        have : x = a := of_decide_eq_true hxeq
        exact hn'.1 (this ▸ hx)
      simp [hnone]
    · have hne : b ≠ a := fun hba => hn'.1 (hba ▸ ha)
      simp [hne, filter_eq_singleton_of_nodup ha hn'.2]

lemma length_filter_ne_of_mem_nodup {α : Type*} [DecidableEq α] {a : α} {l : List α}
    (ha : a ∈ l) (hn : l.Nodup) :
    (l.filter fun x => decide (x ≠ a)).length = l.length - 1 := by
  have hsum := length_filter_add_not (fun x : α => decide (x = a)) l
  have heq : l.filter (fun x => decide (x = a)) = [a] :=
    filter_eq_singleton_of_nodup ha hn
  have hne :
      l.filter (fun x => !decide (x = a)) =
        l.filter (fun x => decide (x ≠ a)) := by
    apply List.filter_congr
    intro x _
    by_cases hx : x = a <;> simp [hx]
  have hpos : 1 ≤ l.length := Nat.succ_le_of_lt (List.length_pos_of_mem ha)
  simp [heq, hne] at hsum
  omega

/-- Replace a non-singleton cover path by its first vertex and its original-edge
tail. The resulting object is still a path cover of the same vertex set, with
cardinality increased by one. -/
noncomputable def splitOne {U : Finset V} (pc : PathCover G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) (h2 : 2 ≤ p.support.card) : PathCover G U where
  paths :=
    pc.paths.filter (fun q => decide (q ≠ p)) ++
      [GraphPath.singleton p.start,
        p.tail (GraphPath.not_nil_of_two_le_card p h2)]
  disjoint := by
    set hnil := GraphPath.not_nil_of_two_le_card p h2
    refine List.pairwise_append.mpr ⟨List.Pairwise.filter _ pc.disjoint, ?_, ?_⟩
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
      intro q hq
      have hq' : q = p.tail hnil := by simpa [hnil] using hq
      subst hq'
      exact GraphPath.disjoint_singleton_start_tail p hnil
    · intro q hq r hr
      have hqpc : q ∈ pc.paths := (List.mem_filter.1 hq).1
      have hqpne : q ≠ p := of_decide_eq_true (List.mem_filter.1 hq).2
      have hdisjqp : Disjoint q.support p.support :=
        pairwise_disjoint_of_mem_refinement pc.disjoint hqpc hp hqpne
      have hr' : r = GraphPath.singleton p.start ∨ r = p.tail hnil := by
        simpa [hnil] using hr
      rcases hr' with rfl | rfl
      · exact disjoint_of_subset_right
          (GraphPath.singleton_start_support_subset p) hdisjqp
      · exact disjoint_of_subset_right
          (GraphPath.tail_support_subset p hnil) hdisjqp
  mem_iff := by
    set hnil := GraphPath.not_nil_of_two_le_card p h2
    intro x
    constructor
    · intro hx
      obtain ⟨q, hq, hxq⟩ := (pc.mem_iff x).1 hx
      by_cases hqp : q = p
      · have hxq' : x ∈ p.support := by simpa [hqp] using hxq
        rcases (GraphPath.mem_support_iff_start_or_tail p hnil).1 hxq' with hx0 | hxt
        · refine ⟨GraphPath.singleton p.start,
            List.mem_append.mpr (Or.inr (by simp)), ?_⟩
          simp [GraphPath.support_singleton, hx0]
        · exact ⟨p.tail hnil, List.mem_append.mpr (Or.inr (by simp)), hxt⟩
      · refine ⟨q, List.mem_append.mpr (Or.inl ?_), hxq⟩
        exact List.mem_filter.mpr ⟨hq, decide_eq_true hqp⟩
    · intro ⟨q, hq, hxq⟩
      rcases List.mem_append.1 hq with hqL | hqR
      · exact (pc.mem_iff x).2 ⟨q, (List.mem_filter.1 hqL).1, hxq⟩
      · have : q = GraphPath.singleton p.start ∨ q = p.tail hnil := by
          simpa [hnil] using hqR
        rcases this with rfl | rfl
        · have hx0 : x = p.start := by simpa [GraphPath.support_singleton] using hxq
          exact (pc.mem_iff x).2 ⟨p, hp, by simpa [hx0] using p.start_mem_support⟩
        · exact (pc.mem_iff x).2
            ⟨p, hp, GraphPath.tail_support_subset p hnil hxq⟩

lemma splitOne_card {U : Finset V} (pc : PathCover G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) (h2 : 2 ≤ p.support.card) :
    (pc.splitOne hp h2).card = pc.card + 1 := by
  have hlen :=
    length_filter_ne_of_mem_nodup (a := p) (l := pc.paths) hp pc.nodup_paths
  have hfilter :
      pc.paths.filter (fun q => decide (q ≠ p)) =
        pc.paths.filter (fun q => !decide (q = p)) := by
    apply List.filter_congr
    intro q _
    by_cases hq : q = p <;> simp [hq]
  have hpos : 1 ≤ pc.paths.length := Nat.succ_le_of_lt (List.length_pos_of_mem hp)
  simp [splitOne, PathCover.card, List.length_append]
  rw [← hfilter, hlen]
  omega

lemma card_eq_of_all_singleton {U : Finset V} (pc : PathCover G U)
    (h : ∀ p ∈ pc.paths, p.support.card = 1) : pc.card = U.card := by
  let rec
    go : ∀ (l : List (GraphPath G)),
        l.Pairwise (fun a b => Disjoint a.support b.support) →
        (∀ p ∈ l, p.support.card = 1) →
        ∀ (W : Finset V), (∀ x, x ∈ W ↔ ∃ p ∈ l, x ∈ p.support) →
          l.length = W.card
    | [], _, _, W, hW => by
      have : W = ∅ := by
        ext x
        simp [hW]
      simp [this]
    | p :: l, hdisj, hcard, W, hW => by
      have hdisj' := List.pairwise_cons.1 hdisj
      have hp1 : p.support.card = 1 :=
        hcard p (List.mem_cons.2 (Or.inl rfl))
      let W' : Finset V := W \ p.support
      have hW' : ∀ x, x ∈ W' ↔ ∃ q ∈ l, x ∈ q.support := by
        intro x
        constructor
        · intro hx
          have hxW : x ∈ W := (mem_sdiff.1 hx).1
          have hxP : x ∉ p.support := (mem_sdiff.1 hx).2
          obtain ⟨q, hq, hxq⟩ := (hW x).1 hxW
          rcases List.mem_cons.1 hq with rfl | hql
          · exact (hxP hxq).elim
          · exact ⟨q, hql, hxq⟩
        · intro ⟨q, hq, hxq⟩
          have hxW : x ∈ W :=
            (hW x).2 ⟨q, List.mem_cons.2 (Or.inr hq), hxq⟩
          have hxP : x ∉ p.support := by
            intro hxp
            have : Disjoint p.support q.support := hdisj'.1 q hq
            exact Finset.disjoint_left.1 this hxp hxq
          exact mem_sdiff.2 ⟨hxW, hxP⟩
      have hrest :=
        go l hdisj'.2 (fun q hq => hcard q (List.mem_cons.2 (Or.inr hq))) W' hW'
      have hcover : W = p.support ∪ W' := by
        ext x
        constructor
        · intro hx
          by_cases hxp : x ∈ p.support
          · exact mem_union.2 (Or.inl hxp)
          · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hx, hxp⟩))
        · intro hx
          rcases mem_union.1 hx with hxp | hx'
          · exact (hW x).2 ⟨p, List.mem_cons.2 (Or.inl rfl), hxp⟩
          · exact (mem_sdiff.1 hx').1
      have hdisjW : Disjoint p.support W' := by
        rw [disjoint_iff_inter_eq_empty]
        exact inter_sdiff_self _ _
      have hWcard : W.card = p.support.card + W'.card := by
        rw [hcover, card_union_of_disjoint hdisjW]
      rw [List.length_cons, hWcard, hp1, hrest]
      omega
  simpa [PathCover.card] using go pc.paths pc.disjoint h U pc.mem_iff

lemma exists_two_le_support_of_card_lt {U : Finset V} (pc : PathCover G U)
    (h : pc.card < U.card) : ∃ p ∈ pc.paths, 2 ≤ p.support.card := by
  by_contra hnone
  have hall : ∀ p ∈ pc.paths, p.support.card = 1 := by
    intro p hp
    have : ¬ 2 ≤ p.support.card := fun h2 => hnone ⟨p, hp, h2⟩
    have hlt : p.support.card < 2 := Nat.not_le.1 this
    have hpos : 1 ≤ p.support.card :=
      Nat.succ_le_of_lt (card_pos.2 p.support_nonempty)
    omega
  have := pc.card_eq_of_all_singleton hall
  omega

lemma exists_succ_of_card_lt {U : Finset V} (pc : PathCover G U)
    (h : pc.card < U.card) : ∃ pc' : PathCover G U, pc'.card = pc.card + 1 := by
  obtain ⟨p, hp, h2⟩ := pc.exists_two_le_support_of_card_lt h
  exact ⟨pc.splitOne hp h2, pc.splitOne_card hp h2⟩

end PathCover

/-- Every integer between the minimum path-cover number and the order is
realized by an actual original-edge path cover, obtained by repeatedly splitting
a non-singleton cover path along an original edge. -/
lemma exists_pathCover_card (U : Finset V) {n : ℕ}
    (hlo : pathCoverNumber G U ≤ n) (hhi : n ≤ U.card) :
    ∃ pc : PathCover G U, pc.card = n := by
  obtain ⟨pc0, h0⟩ := exists_min_pathCover (G := G) U
  have hge : pc0.card ≤ n := by omega
  have : ∀ k, k ≤ n - pc0.card → ∃ pc : PathCover G U, pc.card = pc0.card + k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨pc0, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨pc, hpc⟩ := ih (Nat.le_of_succ_le hk)
      have hlt : pc.card < U.card := by omega
      obtain ⟨pc', hpc'⟩ := pc.exists_succ_of_card_lt hlt
      refine ⟨pc', ?_⟩
      omega
  have hn : pc0.card + (n - pc0.card) = n := Nat.add_sub_of_le hge
  obtain ⟨pc, hpc⟩ := this (n - pc0.card) le_rfl
  exact ⟨pc, hpc.trans hn⟩

lemma pathCoverNumber_eq_zero_iff_refinement (U : Finset V) :
    pathCoverNumber G U = 0 ↔ U = ∅ := by
  constructor
  · intro h
    obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
    have hlen : pc.paths.length = 0 := by
      simpa [PathCover.card, h] using hpc
    have : pc.paths = [] := List.length_eq_zero_iff.mp hlen
    ext x
    simp [pc.mem_iff, this]
  · intro h
    subst h
    exact pathCoverNumber_empty (G := G)

end Nikoghosyan
