/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.Basic
import Nikoghosyan.PathCover

/-!
# Path-cover number of a disjoint union

Manuscript `cog:prop:join`, union half: a cover path cannot leave a block of a
no-cross partition, so minimum covers add. Join recurrence is separate and
needs an original-edge path splice.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma walk_support_subset_of_no_cross {A B : Set V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {u w : V} (p : G.Walk u w) (hu : u ∈ A)
    (hsupp : ∀ x ∈ p.support, x ∈ A ∨ x ∈ B) :
    ∀ x ∈ p.support, x ∈ A := by
  suffices ∀ {u w : V} (p : G.Walk u w),
      u ∈ A → (∀ x ∈ p.support, x ∈ A ∨ x ∈ B) → ∀ x ∈ p.support, x ∈ A from
    this p hu hsupp
  intro u w p
  induction p with
  | nil =>
    intro hu hsupp x hx
    simp [Walk.support_nil] at hx
    cases hx
    exact hu
  | cons hadj p ih =>
    intro hu hsupp x hx
    rename_i u v w
    have hvAB : v ∈ A ∨ v ∈ B :=
      hsupp v (by simp [Walk.support_cons])
    have hvA : v ∈ A := by
      rcases hvAB with hvA | hvB
      · exact hvA
      · exact (hnocross u hu v hvB hadj).elim
    have hsupp' : ∀ y ∈ p.support, y ∈ A ∨ y ∈ B := by
      intro y hy
      exact hsupp y (by simp [Walk.support_cons, hy])
    have hx' : x = u ∨ x ∈ p.support := by
      simpa [Walk.support_cons] using hx
    rcases hx' with rfl | hxP
    · exact hu
    · exact ih hvA hsupp' x hxP

lemma walk_support_subset_of_no_cross' {A B : Set V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {u w : V} (p : G.Walk u w) (hu : u ∈ B)
    (hsupp : ∀ x ∈ p.support, x ∈ A ∨ x ∈ B) :
    ∀ x ∈ p.support, x ∈ B := by
  have hsym : ∀ a ∈ B, ∀ b ∈ A, ¬ G.Adj a b := fun a ha b hb hab =>
    hnocross b hb a ha hab.symm
  simpa [Or.comm] using
    walk_support_subset_of_no_cross (A := B) (B := A) hsym p hu
      (fun x hx => (hsupp x hx).symm)

lemma GraphPath.support_subset_of_no_cross {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (p : GraphPath G) (hstart : p.start ∈ A)
    (hsupp : p.support ⊆ A ∪ B) : p.support ⊆ A := by
  intro x hx
  have hxL : x ∈ p.walk.support := by
    simpa [GraphPath.support] using hx
  have hwalk : ∀ y ∈ p.walk.support, y ∈ (A : Set V) ∨ y ∈ (B : Set V) := by
    intro y hy
    have : y ∈ p.support := by simpa [GraphPath.support] using hy
    have hyU : y ∈ A ∪ B := hsupp this
    simpa [Finset.mem_union] using hyU
  exact walk_support_subset_of_no_cross
    (A := (A : Set V)) (B := (B : Set V))
    (fun a ha b hb => hnocross a ha b hb) p.walk hstart hwalk x hxL

lemma GraphPath.support_subset_of_no_cross' {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (p : GraphPath G) (hstart : p.start ∈ B)
    (hsupp : p.support ⊆ A ∪ B) : p.support ⊆ B := by
  have hsym : ∀ a ∈ B, ∀ b ∈ A, ¬ G.Adj a b := fun a ha b hb hab =>
    hnocross b hb a ha hab.symm
  simpa [Finset.union_comm] using
    GraphPath.support_subset_of_no_cross (A := B) (B := A) hsym p hstart
      (by simpa [Finset.union_comm] using hsupp)

/-- Concatenate path covers of the two sides of a disjoint partition. -/
noncomputable def PathCover.unionDisjoint {A B : Finset V}
    (hdisj : Disjoint A B)
    (pcA : PathCover G A) (pcB : PathCover G B) : PathCover G (A ∪ B) where
  paths := pcA.paths ++ pcB.paths
  disjoint := by
    refine List.pairwise_append.mpr ⟨pcA.disjoint, pcB.disjoint, ?_⟩
    intro p hp q hq
    have hpA : p.support ⊆ A := pcA.support_subset hp
    have hqB : q.support ⊆ B := pcB.support_subset hq
    exact Finset.disjoint_of_subset_left hpA
      (Finset.disjoint_of_subset_right hqB hdisj)
  mem_iff := by
    intro x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · obtain ⟨p, hp, hxp⟩ := (pcA.mem_iff x).1 hxA
        exact ⟨p, List.mem_append.mpr (Or.inl hp), hxp⟩
      · obtain ⟨p, hp, hxp⟩ := (pcB.mem_iff x).1 hxB
        exact ⟨p, List.mem_append.mpr (Or.inr hp), hxp⟩
    · intro ⟨p, hp, hxp⟩
      rcases List.mem_append.mp hp with hpA | hpB
      · exact Finset.mem_union.mpr (Or.inl ((pcA.mem_iff x).2 ⟨p, hpA, hxp⟩))
      · exact Finset.mem_union.mpr (Or.inr ((pcB.mem_iff x).2 ⟨p, hpB, hxp⟩))

lemma PathCover.unionDisjoint_card {A B : Finset V} (hdisj : Disjoint A B)
    (pcA : PathCover G A) (pcB : PathCover G B) :
    (PathCover.unionDisjoint hdisj pcA pcB).card = pcA.card + pcB.card := by
  simp [PathCover.unionDisjoint, PathCover.card, List.length_append]

/-- Split a cover of a no-cross union into covers of the two sides. -/
noncomputable def PathCover.splitLeft {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (pc : PathCover G (A ∪ B)) : PathCover G A where
  paths := pc.paths.filter (fun p => p.start ∈ A)
  disjoint := List.Pairwise.filter _ pc.disjoint
  mem_iff := by
    intro x
    constructor
    · intro hxA
      have hxU : x ∈ A ∪ B := Finset.mem_union.mpr (Or.inl hxA)
      obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hxU
      have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp
      have hstartAB : p.start ∈ A ∨ p.start ∈ B := by
        have : p.start ∈ A ∪ B := hsupp p.start_mem_support
        simpa [Finset.mem_union] using this
      have hstartA : p.start ∈ A := by
        rcases hstartAB with hA | hB
        · exact hA
        · have : p.support ⊆ B :=
            GraphPath.support_subset_of_no_cross' hnocross p hB hsupp
          have hxB : x ∈ B := this hxp
          exact (Finset.disjoint_left.1 hdisj hxA hxB).elim
      refine ⟨p, ?_, hxp⟩
      exact List.mem_filter.mpr ⟨hp, decide_eq_true hstartA⟩
    · intro ⟨p, hp, hxp⟩
      obtain ⟨hp', hstartA'⟩ := List.mem_filter.mp hp
      have hstartA : p.start ∈ A := of_decide_eq_true hstartA'
      have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp'
      exact GraphPath.support_subset_of_no_cross hnocross p hstartA hsupp hxp

noncomputable def PathCover.splitRight {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (pc : PathCover G (A ∪ B)) : PathCover G B where
  paths := pc.paths.filter (fun p => p.start ∈ B)
  disjoint := List.Pairwise.filter _ pc.disjoint
  mem_iff := by
    intro x
    constructor
    · intro hxB
      have hxU : x ∈ A ∪ B := Finset.mem_union.mpr (Or.inr hxB)
      obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hxU
      have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp
      have hstartAB : p.start ∈ A ∨ p.start ∈ B := by
        have : p.start ∈ A ∪ B := hsupp p.start_mem_support
        simpa [Finset.mem_union] using this
      have hstartB : p.start ∈ B := by
        rcases hstartAB with hA | hB
        · have : p.support ⊆ A :=
            GraphPath.support_subset_of_no_cross hnocross p hA hsupp
          have hxA : x ∈ A := this hxp
          exact (Finset.disjoint_left.1 hdisj hxA hxB).elim
        · exact hB
      refine ⟨p, ?_, hxp⟩
      exact List.mem_filter.mpr ⟨hp, decide_eq_true hstartB⟩
    · intro ⟨p, hp, hxp⟩
      obtain ⟨hp', hstartB'⟩ := List.mem_filter.mp hp
      have hstartB : p.start ∈ B := of_decide_eq_true hstartB'
      have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp'
      exact GraphPath.support_subset_of_no_cross' hnocross p hstartB hsupp hxp

lemma length_filter_add_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter fun x => !p x).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases ha : p a
    · simp [ha]; omega
    · simp [ha]; omega

lemma PathCover.card_split_add {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (pc : PathCover G (A ∪ B)) :
    (PathCover.splitLeft hdisj hnocross pc).card +
      (PathCover.splitRight hdisj hnocross pc).card = pc.card := by
  unfold PathCover.splitLeft PathCover.splitRight PathCover.card
  have hB : pc.paths.filter (fun p => decide (p.start ∈ B)) =
      pc.paths.filter (fun p => !decide (p.start ∈ A)) := by
    apply List.filter_congr
    intro p hp
    have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp
    have hAB : p.start ∈ A ∨ p.start ∈ B := by
      have : p.start ∈ A ∪ B := hsupp p.start_mem_support
      simpa [Finset.mem_union] using this
    cases hA : decide (p.start ∈ A) <;> cases hB : decide (p.start ∈ B) <;> simp
    · have : p.start ∉ A := of_decide_eq_false hA
      have : p.start ∉ B := of_decide_eq_false hB
      rcases hAB with h | h <;> contradiction
    · have hA' : p.start ∈ A := of_decide_eq_true hA
      have hB' : p.start ∈ B := of_decide_eq_true hB
      exact (Finset.disjoint_left.1 hdisj hA' hB').elim
  have hlen := length_filter_add_not (fun p : GraphPath G => decide (p.start ∈ A)) pc.paths
  simpa [hB] using hlen

/-- Path-cover numbers add over a disjoint union with no original cross edges. -/
lemma pathCoverNumber_disjoint_union {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    pathCoverNumber G (A ∪ B) = pathCoverNumber G A + pathCoverNumber G B := by
  apply Nat.le_antisymm
  · obtain ⟨pcA, hA⟩ := exists_min_pathCover (G := G) A
    obtain ⟨pcB, hB⟩ := exists_min_pathCover (G := G) B
    have hle := pathCoverNumber_le (G := G)
      (PathCover.unionDisjoint hdisj pcA pcB)
    have hcard := PathCover.unionDisjoint_card hdisj pcA pcB
    omega
  · obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) (A ∪ B)
    have hleA := pathCoverNumber_le (G := G) (PathCover.splitLeft hdisj hnocross pc)
    have hleB := pathCoverNumber_le (G := G) (PathCover.splitRight hdisj hnocross pc)
    have hadd := PathCover.card_split_add hdisj hnocross pc
    omega

lemma splitLeft_card_eq_of_min {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (pc : PathCover G (A ∪ B))
    (hpc : pc.card = pathCoverNumber G (A ∪ B)) :
    (PathCover.splitLeft hdisj hnocross pc).card = pathCoverNumber G A := by
  have hleA := pathCoverNumber_le (G := G) (PathCover.splitLeft hdisj hnocross pc)
  have hleB := pathCoverNumber_le (G := G) (PathCover.splitRight hdisj hnocross pc)
  have hadd := PathCover.card_split_add hdisj hnocross pc
  have hsum := pathCoverNumber_disjoint_union hdisj hnocross
  omega

lemma splitRight_card_eq_of_min {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (pc : PathCover G (A ∪ B))
    (hpc : pc.card = pathCoverNumber G (A ∪ B)) :
    (PathCover.splitRight hdisj hnocross pc).card = pathCoverNumber G B := by
  have hleA := pathCoverNumber_le (G := G) (PathCover.splitLeft hdisj hnocross pc)
  have hleB := pathCoverNumber_le (G := G) (PathCover.splitRight hdisj hnocross pc)
  have hadd := PathCover.card_split_add hdisj hnocross pc
  have hsum := pathCoverNumber_disjoint_union hdisj hnocross
  omega

/-- Eligibility is componentwise on a no-cross partition: a vertex is eligible
in the union if and only if it is eligible in the unique side that contains it. -/
lemma eligible_disjoint_union_iff {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) {x : V} :
    Eligible G (A ∪ B) x ↔ Eligible G A x ∨ Eligible G B x := by
  constructor
  · intro hx
    obtain ⟨pc, hpc, p, hp, hxend⟩ := hx
    have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp
    have hstartAB : p.start ∈ A ∨ p.start ∈ B := by
      have : p.start ∈ A ∪ B := hsupp p.start_mem_support
      simpa [Finset.mem_union] using this
    rcases hstartAB with hA | hB
    · have hpA : p ∈ (PathCover.splitLeft hdisj hnocross pc).paths :=
        List.mem_filter.mpr ⟨hp, decide_eq_true hA⟩
      have hcard := splitLeft_card_eq_of_min hdisj hnocross pc hpc
      refine Or.inl ⟨PathCover.splitLeft hdisj hnocross pc, hcard, p, hpA, hxend⟩
    · have hpB : p ∈ (PathCover.splitRight hdisj hnocross pc).paths :=
        List.mem_filter.mpr ⟨hp, decide_eq_true hB⟩
      have hcard := splitRight_card_eq_of_min hdisj hnocross pc hpc
      refine Or.inr ⟨PathCover.splitRight hdisj hnocross pc, hcard, p, hpB, hxend⟩
  · intro hx
    rcases hx with hA | hB
    · obtain ⟨pcA, hAcard, p, hp, hxend⟩ := hA
      obtain ⟨pcB, hBcard⟩ := exists_min_pathCover (G := G) B
      refine ⟨PathCover.unionDisjoint hdisj pcA pcB, ?_, p, ?_, hxend⟩
      · rw [PathCover.unionDisjoint_card, hAcard, hBcard,
          pathCoverNumber_disjoint_union hdisj hnocross]
      · exact List.mem_append.mpr (Or.inl hp)
    · obtain ⟨pcB, hBcard, p, hp, hxend⟩ := hB
      obtain ⟨pcA, hAcard⟩ := exists_min_pathCover (G := G) A
      refine ⟨PathCover.unionDisjoint hdisj pcA pcB, ?_, p, ?_, hxend⟩
      · rw [PathCover.unionDisjoint_card, hAcard, hBcard,
          pathCoverNumber_disjoint_union hdisj hnocross]
      · exact List.mem_append.mpr (Or.inr hp)

lemma eligibleSet_disjoint_union {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    eligibleSet G (A ∪ B) = eligibleSet G A ∪ eligibleSet G B := by
  ext x
  constructor
  · intro hx
    have hxE : Eligible G (A ∪ B) x := by
      have := (eligibleSet_subset (G := G) (A ∪ B)) hx
      rw [mem_eligibleSet_iff] at hx
      exact hx.2
    rcases (eligible_disjoint_union_iff (G := G) hdisj hnocross).mp hxE with hA | hB
    · exact mem_union.2 (Or.inl (by
        rw [mem_eligibleSet_iff]; exact ⟨hA.mem, hA⟩))
    · exact mem_union.2 (Or.inr (by
        rw [mem_eligibleSet_iff]; exact ⟨hB.mem, hB⟩))
  · intro hx
    rcases mem_union.1 hx with hxA | hxB
    · rw [mem_eligibleSet_iff] at hxA
      rw [mem_eligibleSet_iff]
      exact ⟨mem_union.2 (Or.inl hxA.1),
        (eligible_disjoint_union_iff (G := G) hdisj hnocross).mpr (Or.inl hxA.2)⟩
    · rw [mem_eligibleSet_iff] at hxB
      rw [mem_eligibleSet_iff]
      exact ⟨mem_union.2 (Or.inr hxB.1),
        (eligible_disjoint_union_iff (G := G) hdisj hnocross).mpr (Or.inr hxB.2)⟩

lemma ineligibleSet_disjoint_union {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    ineligibleSet G (A ∪ B) = ineligibleSet G A ∪ ineligibleSet G B := by
  ext x
  constructor
  · intro hx
    rw [mem_ineligibleSet_iff] at hx
    have hnot' : ¬ (Eligible G A x ∨ Eligible G B x) := by
      intro h
      exact hx.2 ((eligible_disjoint_union_iff (G := G) hdisj hnocross).mpr h)
    rcases mem_union.1 hx.1 with hxA | hxB
    · exact mem_union.2 (Or.inl (by
        rw [mem_ineligibleSet_iff]; exact ⟨hxA, fun hA => hnot' (Or.inl hA)⟩))
    · exact mem_union.2 (Or.inr (by
        rw [mem_ineligibleSet_iff]; exact ⟨hxB, fun hB => hnot' (Or.inr hB)⟩))
  · intro hx
    rcases mem_union.1 hx with hxA | hxB
    · rw [mem_ineligibleSet_iff] at hxA
      rw [mem_ineligibleSet_iff]
      refine ⟨mem_union.2 (Or.inl hxA.1), ?_⟩
      intro hEl
      rcases (eligible_disjoint_union_iff (G := G) hdisj hnocross).mp hEl with hA | hB
      · exact hxA.2 hA
      · exact (Finset.disjoint_left.1 hdisj hxA.1 hB.mem).elim
    · rw [mem_ineligibleSet_iff] at hxB
      rw [mem_ineligibleSet_iff]
      refine ⟨mem_union.2 (Or.inr hxB.1), ?_⟩
      intro hEl
      rcases (eligible_disjoint_union_iff (G := G) hdisj hnocross).mp hEl with hA | hB
      · exact (Finset.disjoint_left.1 hdisj hA.mem hxB.1).elim
      · exact hxB.2 hB

end Cograph
end Nikoghosyan
