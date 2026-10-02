/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalFeasibility

/-!
Specified two-path connector merges with endpoint-deficit control.

Given an actual path cover of `U` whose outside ends all lie in a carrier
`P`, and a fresh vertex `u` originally complete to `P`, join two specified
distinct cover paths through the original singleton `u` after specified
orientations. The new cover of `insert u U` has cardinality `old.card - 1`,
keeps every remaining path, and its unused ends remain in `P`.

`GraphPath.endpointDeficit` / `PathCover.endpointDeficit` are imported from
`TerminalFeasibility` and not redeclared. Deficit never increases, and it
drops by the number of selected bad ends (0, 1 or 2). The budget-decrement
and connector-iteration lemmas supply the generic parent operation needed
by positive-slack induction; they do not prove a cograph cut bound.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Specified orientations -/

/-- Face a chosen end of `p` toward a later splice at the finish. -/
def GraphPath.faceFinish (p : GraphPath G) (selectStart : Bool) : GraphPath G :=
  if selectStart then p.reverse else p

/-- Face a chosen end of `p` toward a later splice at the start. -/
def GraphPath.faceStart (p : GraphPath G) (selectStart : Bool) : GraphPath G :=
  if selectStart then p else p.reverse

lemma GraphPath.faceFinish_support (p : GraphPath G) (b : Bool) :
    (p.faceFinish b).support = p.support := by
  unfold GraphPath.faceFinish
  cases b <;> simp

lemma GraphPath.faceStart_support (p : GraphPath G) (b : Bool) :
    (p.faceStart b).support = p.support := by
  unfold GraphPath.faceStart
  cases b <;> simp

lemma GraphPath.faceFinish_deficit (B : Finset V) (p : GraphPath G) (b : Bool) :
    (p.faceFinish b).endpointDeficit B = p.endpointDeficit B := by
  unfold GraphPath.faceFinish
  cases b <;> simp [GraphPath.endpointDeficit_reverse]

lemma GraphPath.faceStart_deficit (B : Finset V) (p : GraphPath G) (b : Bool) :
    (p.faceStart b).endpointDeficit B = p.endpointDeficit B := by
  unfold GraphPath.faceStart
  cases b <;> simp [GraphPath.endpointDeficit_reverse]

lemma GraphPath.faceFinish_ends_mem {P : Finset V} (p : GraphPath G) (b : Bool)
    (hs : p.start ∈ P) (hf : p.finish ∈ P) :
    (p.faceFinish b).start ∈ P ∧ (p.faceFinish b).finish ∈ P := by
  unfold GraphPath.faceFinish
  cases b <;> simp [GraphPath.reverse, hs, hf]

lemma GraphPath.faceStart_ends_mem {P : Finset V} (p : GraphPath G) (b : Bool)
    (hs : p.start ∈ P) (hf : p.finish ∈ P) :
    (p.faceStart b).start ∈ P ∧ (p.faceStart b).finish ∈ P := by
  unfold GraphPath.faceStart
  cases b <;> simp [GraphPath.reverse, hs, hf]

/-- Deficit of the single selected end (0 or 1). -/
def GraphPath.selectedDeficit (B : Finset V) (p : GraphPath G)
    (selectStart : Bool) : ℕ :=
  if (if selectStart then p.start else p.finish) ∈ B then 0 else 1

lemma GraphPath.selectedDeficit_le (B : Finset V) (p : GraphPath G)
    (b : Bool) :
    p.selectedDeficit B b ≤ p.endpointDeficit B := by
  unfold GraphPath.selectedDeficit GraphPath.endpointDeficit
  cases b <;> split_ifs <;> simp

lemma GraphPath.faceFinish_finish_selected (B : Finset V) (p : GraphPath G)
    (b : Bool) :
    (if (p.faceFinish b).finish ∈ B then 0 else 1) = p.selectedDeficit B b := by
  unfold GraphPath.faceFinish GraphPath.selectedDeficit
  cases b <;> simp [GraphPath.reverse]

lemma GraphPath.faceStart_start_selected (B : Finset V) (p : GraphPath G)
    (b : Bool) :
    (if (p.faceStart b).start ∈ B then 0 else 1) = p.selectedDeficit B b := by
  unfold GraphPath.faceStart GraphPath.selectedDeficit
  cases b <;> simp [GraphPath.reverse]

lemma GraphPath.faceFinish_start_unused (B : Finset V) (p : GraphPath G)
    (b : Bool) :
    (if (p.faceFinish b).start ∈ B then 0 else 1) + p.selectedDeficit B b =
      p.endpointDeficit B := by
  unfold GraphPath.faceFinish GraphPath.selectedDeficit GraphPath.endpointDeficit
  cases b <;> simp [GraphPath.reverse, Nat.add_comm]

lemma GraphPath.faceStart_finish_unused (B : Finset V) (p : GraphPath G)
    (b : Bool) :
    p.selectedDeficit B b + (if (p.faceStart b).finish ∈ B then 0 else 1) =
      p.endpointDeficit B := by
  unfold GraphPath.faceStart GraphPath.selectedDeficit GraphPath.endpointDeficit
  cases b <;> simp [GraphPath.reverse, Nat.add_comm]

lemma isCompleteBetween_singleton {P : Finset V} {u : V}
    (h : ∀ x ∈ P, G.Adj x u) :
    G.IsCompleteBetween (P : Set V) (({u} : Finset V) : Set V) := by
  intro a ha b hb
  have hb' : b = u := by simpa using hb
  subst hb'
  exact h a (by simpa using ha)

/-! ### List-sum identities for cover deficit -/

lemma filter_decide_ne {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    l.filter (fun x => decide (x ≠ a)) = l.filter (fun x => !decide (x = a)) := by
  refine List.filter_congr ?_
  intro x _
  by_cases hx : x = a <;> simp [hx]

lemma sum_map_filter_ne {α : Type*} [DecidableEq α] (f : α → ℕ) {a : α}
    {l : List α} (ha : a ∈ l) (hn : l.Nodup) :
    ((l.filter fun x => decide (x ≠ a)).map f).sum + f a = (l.map f).sum := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have hn' := List.nodup_cons.1 hn
    rcases List.mem_cons.1 ha with hxa | haxs
    · subst hxa
      have hnotin : a ∉ xs := hn'.1
      have hxs : xs.filter (fun y => decide (y ≠ a)) = xs := by
        refine List.filter_eq_self.2 ?_
        intro y hy
        exact decide_eq_true (fun hya => hnotin (hya ▸ hy))
      rw [filter_decide_ne, List.filter]
      simp
      rw [← filter_decide_ne, hxs]
      simp [List.map_cons, List.sum_cons, Nat.add_comm]
    · have hne : x ≠ a := fun heq => hn'.1 (heq ▸ haxs)
      have hdec : decide (x = a) = false := decide_eq_false hne
      rw [filter_decide_ne, List.filter]
      simp [hdec, ← filter_decide_ne, List.map_cons, List.sum_cons]
      have ih' := ih haxs hn'.2
      omega

lemma sum_map_filter_ne_two {α : Type*} [DecidableEq α] (f : α → ℕ) {a b : α}
    {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) (hn : l.Nodup) :
    (((l.filter fun x => decide (x ≠ a)).filter fun x => decide (x ≠ b)).map f).sum
        + f a + f b =
      (l.map f).sum := by
  have h1 := sum_map_filter_ne f ha hn
  have hb' : b ∈ l.filter fun x => decide (x ≠ a) :=
    List.mem_filter.2 ⟨hb, decide_eq_true hne.symm⟩
  have hn' : (l.filter fun x => decide (x ≠ a)).Nodup := List.Nodup.filter _ hn
  have h2 := sum_map_filter_ne (a := b) f hb' hn'
  omega

lemma sum_map_eq_sum_filter_pos {α : Type*} (f : α → ℕ) :
    ∀ l : List α,
      (l.map f).sum = ((l.filter fun x => decide (1 ≤ f x)).map f).sum
  | [] => rfl
  | x :: xs => by
    cases h : decide (1 ≤ f x)
    · have : ¬ 1 ≤ f x := of_decide_eq_false h
      have h0 : f x = 0 := by omega
      simpa [List.filter, h, h0] using sum_map_eq_sum_filter_pos f xs
    · simpa [List.filter, h] using sum_map_eq_sum_filter_pos f xs

lemma sum_map_deficit_le_two_mul_length (B : Finset V) :
    ∀ l : List (GraphPath G),
      (l.map (fun p => p.endpointDeficit B)).sum ≤ 2 * l.length
  | [] => by simp
  | p :: ps => by
    have hp := GraphPath.endpointDeficit_le_two B p
    have ih := sum_map_deficit_le_two_mul_length B ps
    have hmul : 2 + 2 * ps.length = 2 * (ps.length + 1) := by omega
    simpa [List.map_cons, List.sum_cons, hmul] using Nat.add_le_add hp ih

lemma exists_two_mem_nodup {α : Type*} {l : List α}
    (hn : l.Nodup) (h : 2 ≤ l.length) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  match hl : l with
  | [] =>
    simp at h
  | [_] =>
    simp at h
  | a :: b :: rest =>
    refine ⟨a, b, by simp, by simp, ?_⟩
    intro heq
    subst heq
    have hn2 : (a :: a :: rest).Nodup := by simpa [hl] using hn
    exact (List.nodup_cons.1 hn2).1 (List.mem_cons.2 (Or.inl rfl))

lemma PathCover.exists_ne_of_two_le {U : Finset V} (pc : PathCover G U)
    {p : GraphPath G} (hp : p ∈ pc.paths) (h2 : 2 ≤ pc.card) :
    ∃ q, q ∈ pc.paths ∧ q ≠ p := by
  obtain ⟨a, b, ha, hb, hne⟩ := pc.exists_two_distinct h2
  by_cases h : a = p
  · subst h
    exact ⟨b, hb, hne.symm⟩
  · exact ⟨a, ha, h⟩

lemma PathCover.endpointDeficit_eq_sum_bad {U : Finset V} (pc : PathCover G U)
    (B : Finset V) :
    pc.endpointDeficit B =
      ((pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)).map
        (fun p => p.endpointDeficit B)).sum := by
  simpa [PathCover.endpointDeficit] using
    sum_map_eq_sum_filter_pos (fun p : GraphPath G => p.endpointDeficit B) pc.paths

lemma PathCover.two_le_bad_of_deficit_ge_three {U : Finset V}
    (pc : PathCover G U) (B : Finset V)
    (h : 3 ≤ pc.endpointDeficit B) :
    2 ≤ (pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)).length := by
  set bad := pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)
  have hsum : pc.endpointDeficit B = (bad.map (fun p => p.endpointDeficit B)).sum :=
    pc.endpointDeficit_eq_sum_bad B
  have hle := sum_map_deficit_le_two_mul_length B bad
  by_contra hlt
  have : bad.length ≤ 1 := by omega
  have : (bad.map (fun p => p.endpointDeficit B)).sum ≤ 2 := by omega
  omega

lemma PathCover.exists_two_bad {U : Finset V} (pc : PathCover G U) (B : Finset V)
    (h : 2 ≤ (pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)).length) :
    ∃ p q, p ∈ pc.paths ∧ q ∈ pc.paths ∧ p ≠ q ∧
      1 ≤ p.endpointDeficit B ∧ 1 ≤ q.endpointDeficit B := by
  set bad := pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)
  have hn : bad.Nodup := List.Nodup.filter _ pc.nodup_paths
  obtain ⟨p, q, hp, hq, hne⟩ := exists_two_mem_nodup hn h
  have hpB := List.mem_filter.1 hp
  have hqB := List.mem_filter.1 hq
  exact ⟨p, q, hpB.1, hqB.1, hne, of_decide_eq_true hpB.2, of_decide_eq_true hqB.2⟩

lemma PathCover.exists_one_bad {U : Finset V} (pc : PathCover G U) (B : Finset V)
    (h2 : 2 ≤ pc.card)
    (h : (pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)).length = 1) :
    ∃ p q, p ∈ pc.paths ∧ q ∈ pc.paths ∧ p ≠ q ∧ 1 ≤ p.endpointDeficit B := by
  set bad := pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)
  have hpos : 0 < bad.length := by omega
  obtain ⟨p, hp⟩ := List.length_pos_iff_exists_mem.mp hpos
  have hp' := List.mem_filter.1 hp
  obtain ⟨q, hq, hne⟩ := pc.exists_ne_of_two_le hp'.1 h2
  exact ⟨p, q, hp'.1, hq, hne.symm, of_decide_eq_true hp'.2⟩

lemma GraphPath.orientFinishOpen_selected_iff (B : Finset V) (p : GraphPath G) :
    (p.orientFinishOpen B).finish ∉ B ↔ 1 ≤ p.endpointDeficit B := by
  constructor
  · intro h
    have hnot : ¬ (p.start ∈ B ∧ p.finish ∈ B) := by
      intro hboth
      unfold GraphPath.orientFinishOpen at h
      split_ifs at h with hf
      · simp [GraphPath.reverse] at h
        exact h hboth.1
      · exact hf hboth.2
    have : p.endpointDeficit B ≠ 0 :=
      (GraphPath.endpointDeficit_eq_zero_iff B p).not.mpr hnot
    omega
  · intro h
    have hne0 : p.endpointDeficit B ≠ 0 := by omega
    have hnot : ¬ (p.start ∈ B ∧ p.finish ∈ B) :=
      (GraphPath.endpointDeficit_eq_zero_iff B p).not.mp hne0
    rcases not_and_or.mp hnot with hs | hf
    · exact GraphPath.orientFinishOpen_finish_not_mem B p (Or.inl hs)
    · exact GraphPath.orientFinishOpen_finish_not_mem B p (Or.inr hf)

lemma GraphPath.orientStartOpen_selected_iff (B : Finset V) (p : GraphPath G) :
    (p.orientStartOpen B).start ∉ B ↔ 1 ≤ p.endpointDeficit B := by
  constructor
  · intro h
    have hnot : ¬ (p.start ∈ B ∧ p.finish ∈ B) := by
      intro hboth
      unfold GraphPath.orientStartOpen at h
      split_ifs at h with hs
      · simp [GraphPath.reverse] at h
        exact h hboth.2
      · exact hs hboth.1
    have : p.endpointDeficit B ≠ 0 :=
      (GraphPath.endpointDeficit_eq_zero_iff B p).not.mpr hnot
    omega
  · intro h
    have hne0 : p.endpointDeficit B ≠ 0 := by omega
    have hnot : ¬ (p.start ∈ B ∧ p.finish ∈ B) :=
      (GraphPath.endpointDeficit_eq_zero_iff B p).not.mp hne0
    rcases not_and_or.mp hnot with hs | hf
    · exact GraphPath.orientStartOpen_start_not_mem B p (Or.inl hs)
    · exact GraphPath.orientStartOpen_start_not_mem B p (Or.inr hf)

lemma GraphPath.ite_end_eq_selected (B : Finset V) {x : V} :
    (if x ∈ B then (0 : ℕ) else 1) = if x ∉ B then 1 else 0 := by
  split_ifs <;> simp_all

/-! ### Oriented two-path merge through a singleton connector -/

/-- Join two already-oriented disjoint cover paths through an original
singleton `u` complete to the carrier `P` of their outside ends. -/
lemma exists_mergeOriented {P U : Finset V} {u : V} (B : Finset V)
    (pc : PathCover G U)
    {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (p' q' : GraphPath G)
    (hp'supp : p'.support = p.support) (hq'supp : q'.support = q.support)
    (hp'def : p'.endpointDeficit B = p.endpointDeficit B)
    (hq'def : q'.endpointDeficit B = q.endpointDeficit B)
    (hp's : p'.start ∈ P) (hp'f : p'.finish ∈ P)
    (hq's : q'.start ∈ P) (hq'f : q'.finish ∈ P)
    (hend : ∀ r ∈ pc.paths, r.start ∈ P ∧ r.finish ∈ P)
    (hu : u ∉ U) (hAdj : ∀ x ∈ P, G.Adj x u) :
    ∃ pc' : PathCover G (insert u U),
      pc'.card = pc.card - 1 ∧
        (∀ r ∈ pc'.paths, r.start ∈ P ∧ r.finish ∈ P) ∧
          pc.endpointDeficit B =
            pc'.endpointDeficit B
              + (if p'.finish ∈ B then 0 else 1)
              + (if q'.start ∈ B then 0 else 1) := by
  have hpb : u ∉ p'.support := by
    intro h
    exact hu (pc.support_subset hp (hp'supp ▸ h))
  have hqb : u ∉ q'.support := by
    intro h
    exact hu (pc.support_subset hq (hq'supp ▸ h))
  have hd : Disjoint p'.support q'.support := by
    rw [hp'supp, hq'supp]
    exact PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne
  have hAB := isCompleteBetween_singleton (P := P) (u := u) hAdj
  obtain ⟨r, hr, hst, hfn⟩ :=
    exists_spliceABA hAB p' u q' hp'f (mem_singleton_self u) hq's hpb hqb hd
  have hr' : r.support = p.support ∪ {u} ∪ q.support := by
    simpa [hp'supp, hq'supp] using hr
  refine ⟨pc.spliceTwoInsert hp hq hne u hu r hr',
    pc.spliceTwoInsert_card hp hq hne u hu r hr', ?_, ?_⟩
  · intro s hs
    rcases pc.spliceTwoInsert_mem_paths hp hq hne u hu r hr' hs with hseq | ⟨hspc, _, _⟩
    · subst hseq
      rw [hst, hfn]
      exact ⟨hp's, hq'f⟩
    · exact hend s hspc
  · have hn := pc.nodup_paths
    have hsum :=
      sum_map_filter_ne_two (fun t : GraphPath G => t.endpointDeficit B)
        hp hq hne hn
    have hrdef :
        r.endpointDeficit B =
          (if p'.start ∈ B then 0 else 1) + (if q'.finish ∈ B then 0 else 1) := by
      unfold GraphPath.endpointDeficit
      simp [hst, hfn]
    have hp'id :
        p'.endpointDeficit B =
          (if p'.start ∈ B then 0 else 1) + (if p'.finish ∈ B then 0 else 1) :=
      rfl
    have hq'id :
        q'.endpointDeficit B =
          (if q'.start ∈ B then 0 else 1) + (if q'.finish ∈ B then 0 else 1) :=
      rfl
    have hpc' :
        (pc.spliceTwoInsert hp hq hne u hu r hr').endpointDeficit B =
          (((pc.paths.filter fun s => decide (s ≠ p)).filter
              fun s => decide (s ≠ q)).map
            (fun t => t.endpointDeficit B)).sum + r.endpointDeficit B := by
      simp [PathCover.endpointDeficit, PathCover.spliceTwoInsert,
        List.map_append, List.sum_append]
    have hends :
        p.endpointDeficit B + q.endpointDeficit B =
          r.endpointDeficit B + (if p'.finish ∈ B then 0 else 1)
            + (if q'.start ∈ B then 0 else 1) := by
      rw [← hp'def, ← hq'def, hrdef]
      unfold GraphPath.endpointDeficit
      omega
    rw [hpc']
    unfold PathCover.endpointDeficit
    omega

/-- Specified orientations: reverse the chosen ends toward `u`, splice the
original singleton, drop exactly those two old paths, keep the others. -/
lemma exists_mergeThroughSpecified {P U : Finset V} {u : V} (B : Finset V)
    (pc : PathCover G U)
    {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hend : ∀ r ∈ pc.paths, r.start ∈ P ∧ r.finish ∈ P)
    (hu : u ∉ U) (hAdj : ∀ x ∈ P, G.Adj x u)
    (selectP selectQ : Bool) :
    ∃ pc' : PathCover G (insert u U),
      pc'.card = pc.card - 1 ∧
        (∀ r ∈ pc'.paths, r.start ∈ P ∧ r.finish ∈ P) ∧
          pc.endpointDeficit B =
            pc'.endpointDeficit B
              + p.selectedDeficit B selectP
              + q.selectedDeficit B selectQ := by
  let p' := p.faceFinish selectP
  let q' := q.faceStart selectQ
  have hpP := hend p hp
  have hqP := hend q hq
  have hp'ends := GraphPath.faceFinish_ends_mem (P := P) p selectP hpP.1 hpP.2
  have hq'ends := GraphPath.faceStart_ends_mem (P := P) q selectQ hqP.1 hqP.2
  obtain ⟨pc', hcard, hend', hdef⟩ :=
    exists_mergeOriented (B := B) pc hp hq hne p' q'
      (p.faceFinish_support selectP) (q.faceStart_support selectQ)
      (p.faceFinish_deficit B selectP) (q.faceStart_deficit B selectQ)
      hp'ends.1 hp'ends.2 hq'ends.1 hq'ends.2 hend hu hAdj
  refine ⟨pc', hcard, hend', ?_⟩
  have hpSel := p.faceFinish_finish_selected (B := B) selectP
  have hqSel := q.faceStart_start_selected (B := B) selectQ
  simp only [p', q'] at hdef
  rw [hpSel, hqSel] at hdef
  exact hdef

lemma exists_mergeThroughSpecified_le {P U : Finset V} {u : V} (B : Finset V)
    (pc : PathCover G U)
    {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hend : ∀ r ∈ pc.paths, r.start ∈ P ∧ r.finish ∈ P)
    (hu : u ∉ U) (hAdj : ∀ x ∈ P, G.Adj x u)
    (selectP selectQ : Bool) :
    ∃ pc' : PathCover G (insert u U),
      pc'.card = pc.card - 1 ∧
        (∀ r ∈ pc'.paths, r.start ∈ P ∧ r.finish ∈ P) ∧
          pc'.endpointDeficit B ≤ pc.endpointDeficit B := by
  obtain ⟨pc', hcard, hend', hdef⟩ :=
    exists_mergeThroughSpecified (B := B) pc hp hq hne hend hu hAdj
      selectP selectQ
  refine ⟨pc', hcard, hend', ?_⟩
  omega

/-- Orient any open ends toward `u` and merge. The deficit drops by 1 for
each selected parent that currently has a bad end. -/
lemma exists_mergeOpenToward {P U : Finset V} {u : V} (B : Finset V)
    (pc : PathCover G U)
    {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hend : ∀ r ∈ pc.paths, r.start ∈ P ∧ r.finish ∈ P)
    (hu : u ∉ U) (hAdj : ∀ x ∈ P, G.Adj x u) :
    ∃ pc' : PathCover G (insert u U),
      pc'.card = pc.card - 1 ∧
        (∀ r ∈ pc'.paths, r.start ∈ P ∧ r.finish ∈ P) ∧
          pc.endpointDeficit B =
            pc'.endpointDeficit B
              + (if 1 ≤ p.endpointDeficit B then 1 else 0)
              + (if 1 ≤ q.endpointDeficit B then 1 else 0) := by
  let p' := p.orientFinishOpen B
  let q' := q.orientStartOpen B
  have hpP := hend p hp
  have hqP := hend q hq
  have hp'ends := GraphPath.orientFinishOpen_mem_X (X := P) (B := B) p hpP.1 hpP.2
  have hq'ends := GraphPath.orientStartOpen_mem_X (X := P) (B := B) q hqP.1 hqP.2
  obtain ⟨pc', hcard, hend', hdef⟩ :=
    exists_mergeOriented (B := B) pc hp hq hne p' q'
      (p.orientFinishOpen_support B) (q.orientStartOpen_support B)
      (by
        dsimp [p']
        unfold GraphPath.orientFinishOpen
        split_ifs
        · exact GraphPath.endpointDeficit_reverse B p
        · rfl)
      (by
        dsimp [q']
        unfold GraphPath.orientStartOpen
        split_ifs
        · exact GraphPath.endpointDeficit_reverse B q
        · rfl)
      hp'ends.1 hp'ends.2 hq'ends.1 hq'ends.2 hend hu hAdj
  refine ⟨pc', hcard, hend', ?_⟩
  have hpdrop :
      (if p'.finish ∈ B then 0 else 1) =
        if 1 ≤ p.endpointDeficit B then 1 else 0 := by
    by_cases h : 1 ≤ p.endpointDeficit B
    · have : p'.finish ∉ B := (p.orientFinishOpen_selected_iff B).mpr h
      simp [h, this]
    · have : p'.finish ∈ B := by
        by_contra hn
        exact h ((p.orientFinishOpen_selected_iff B).mp hn)
      simp [h, this]
  have hqdrop :
      (if q'.start ∈ B then 0 else 1) =
        if 1 ≤ q.endpointDeficit B then 1 else 0 := by
    by_cases h : 1 ≤ q.endpointDeficit B
    · have : q'.start ∉ B := (q.orientStartOpen_selected_iff B).mpr h
      simp [h, this]
    · have : q'.start ∈ B := by
        by_contra hn
        exact h ((q.orientStartOpen_selected_iff B).mp hn)
      simp [h, this]
  rw [hpdrop, hqdrop] at hdef
  exact hdef

/-! ### Budget decrement -/

/-- One actual merge: if `delta ≤ 2 * s - 1` and `s ≥ 2`, some specified
parent choice yields `deltaNew ≤ 2 * (s - 1) - 1`. -/
lemma exists_budget_decrement {P U : Finset V} {u : V} (B : Finset V)
    (pc : PathCover G U) (s : ℕ)
    (h2 : 2 ≤ pc.card) (hs : 2 ≤ s)
    (hdelta : pc.endpointDeficit B ≤ 2 * s - 1)
    (hend : ∀ r ∈ pc.paths, r.start ∈ P ∧ r.finish ∈ P)
    (hu : u ∉ U) (hAdj : ∀ x ∈ P, G.Adj x u) :
    ∃ pc' : PathCover G (insert u U),
      pc'.card = pc.card - 1 ∧
        (∀ r ∈ pc'.paths, r.start ∈ P ∧ r.finish ∈ P) ∧
          pc'.endpointDeficit B ≤ 2 * (s - 1) - 1 := by
  set bad := pc.paths.filter fun p => decide (1 ≤ p.endpointDeficit B)
  have hbound : 2 * (s - 1) - 1 = 2 * s - 3 := by omega
  have htarget : 1 ≤ 2 * (s - 1) - 1 := by omega
  by_cases hbad2 : 2 ≤ bad.length
  · obtain ⟨p, q, hp, hq, hne, hpB, hqB⟩ := pc.exists_two_bad (B := B) hbad2
    obtain ⟨pc', hcard, hend', hdef⟩ :=
      exists_mergeOpenToward (B := B) pc hp hq hne hend hu hAdj
    refine ⟨pc', hcard, hend', ?_⟩
    have hp1 : (if 1 ≤ p.endpointDeficit B then 1 else 0) = 1 := ite_eq_left hpB
    have hq1 : (if 1 ≤ q.endpointDeficit B then 1 else 0) = 1 := ite_eq_left hqB
    omega
  · by_cases hbad1 : bad.length = 1
    · obtain ⟨p, q, hp, hq, hne, hpB⟩ :=
        pc.exists_one_bad (B := B) h2 hbad1
      obtain ⟨pc', hcard, hend', hdef⟩ :=
        exists_mergeOpenToward (B := B) pc hp hq hne hend hu hAdj
      refine ⟨pc', hcard, hend', ?_⟩
      have hp1 : (if 1 ≤ p.endpointDeficit B then 1 else 0) = 1 := ite_eq_left hpB
      have hdelta2 : pc.endpointDeficit B ≤ 2 := by
        have hsum := pc.endpointDeficit_eq_sum_bad B
        have hle' := sum_map_deficit_le_two_mul_length B bad
        rw [hsum]
        change (bad.map (fun r => r.endpointDeficit B)).sum ≤ 2
        omega
      omega
    · have hbad0 : bad.length = 0 := by omega
      obtain ⟨p, q, hp, hq, hne⟩ := pc.exists_two_distinct h2
      obtain ⟨pc', hcard, hend', hdef⟩ :=
        exists_mergeOpenToward (B := B) pc hp hq hne hend hu hAdj
      refine ⟨pc', hcard, hend', ?_⟩
      have hdelta0 : pc.endpointDeficit B = 0 := by
        have hsum := pc.endpointDeficit_eq_sum_bad B
        have hnil : bad = [] := List.eq_nil_of_length_eq_zero hbad0
        rw [hsum]
        change (bad.map (fun r => r.endpointDeficit B)).sum = 0
        simp [hnil]
      omega

/-! ### Iteration through a finite set of original connectors -/

lemma insert_union_eq (u : V) (U S : Finset V) :
    insert u (U ∪ S) = U ∪ insert u S := by
  ext x
  simp only [mem_insert, mem_union]
  constructor
  · rintro (h | h | h) <;> simp [h]
  · rintro (h | h | h) <;> simp [h]

lemma PathCover.cast_endpointDeficit {U W : Finset V} (pc : PathCover G U)
    (h : U = W) (B : Finset V) :
    (pc.cast h).endpointDeficit B = pc.endpointDeficit B := by
  simp [PathCover.endpointDeficit, PathCover.cast_paths]

/-- Consume every connector in `C`. The input deficit bound is an operation
hypothesis (G3 derives it by cograph induction); this helper only iterates
the budget-decrement merge. -/
lemma exists_endpoint_budget_iteration {P U C : Finset V} (B : Finset V)
    (pc : PathCover G U) (t : ℕ)
    (ht : 1 ≤ t)
    (hend : ∀ r ∈ pc.paths, r.start ∈ P ∧ r.finish ∈ P)
    (hCU : Disjoint C U)
    (hAdj : ∀ u ∈ C, ∀ x ∈ P, G.Adj x u)
    (hcard : C.card + 2 ≤ pc.card)
    (hdef : pc.endpointDeficit B ≤ 2 * (t + C.card) - 1) :
    ∃ pc' : PathCover G (U ∪ C),
      pc'.card = pc.card - C.card ∧
        (∀ r ∈ pc'.paths, r.start ∈ P ∧ r.finish ∈ P) ∧
          pc'.endpointDeficit B ≤ 2 * t - 1 := by
  have aux :
      ∀ (k : ℕ) (S : Finset V) (pcS : PathCover G (U ∪ S)),
        S ⊆ C → (C \ S).card = k →
          pcS.card = pc.card - S.card →
            (∀ r ∈ pcS.paths, r.start ∈ P ∧ r.finish ∈ P) →
              pcS.endpointDeficit B ≤ 2 * (t + (C \ S).card) - 1 →
                ∃ pc' : PathCover G (U ∪ C),
                  pc'.card = pc.card - C.card ∧
                    (∀ r ∈ pc'.paths, r.start ∈ P ∧ r.finish ∈ P) ∧
                      pc'.endpointDeficit B ≤ 2 * t - 1 := by
    intro k
    induction k with
    | zero =>
      intro S pcS hS hk hcardS hendS hdefS
      have hCS : C \ S = ∅ := Finset.card_eq_zero.mp hk
      have hBeq : S = C := subset_antisymm hS (sdiff_eq_empty_iff_subset.mp hCS)
      subst hBeq
      exact ⟨pcS, hcardS, hendS, by simpa using hdefS⟩
    | succ k ih =>
      intro S pcS hS hk hcardS hendS hdefS
      have hne : (C \ S).Nonempty := card_pos.mp (by omega : 0 < (C \ S).card)
      obtain ⟨u, hu⟩ := hne
      have huC : u ∈ C := (mem_sdiff.1 hu).1
      have huS : u ∉ S := (mem_sdiff.1 hu).2
      have huU : u ∉ U ∪ S := by
        intro h
        rcases mem_union.1 h with hU | hS'
        · exact Finset.disjoint_left.1 hCU huC hU
        · exact huS hS'
      have hs : 2 ≤ t + (C \ S).card := by omega
      have h2 : 2 ≤ pcS.card := by
        have hsum : S.card + (C \ S).card = C.card := by
          rw [← card_union_of_disjoint, union_sdiff_of_subset hS]
          exact disjoint_sdiff
        omega
      obtain ⟨pc1, hcard1, hend1, hdef1⟩ :=
        exists_budget_decrement (P := P) (U := U ∪ S) (u := u) B pcS
          (t + (C \ S).card) h2 hs hdefS hendS huU (fun x hx => hAdj u huC x hx)
      have hUeq : insert u (U ∪ S) = U ∪ insert u S := insert_union_eq u U S
      let pc1' : PathCover G (U ∪ insert u S) := pc1.cast hUeq
      have hS' : insert u S ⊆ C := insert_subset huC hS
      have hrem : C \ insert u S = (C \ S).erase u := sdiff_insert C S u
      have hk' : (C \ insert u S).card = k := by
        rw [hrem, card_erase_of_mem hu, hk]
        omega
      have hcard' : pc1'.card = pc.card - (insert u S).card := by
        rw [PathCover.cast_card, hcard1, hcardS, card_insert_of_notMem huS]
        omega
      have hend1' : ∀ r ∈ pc1'.paths, r.start ∈ P ∧ r.finish ∈ P := by
        intro r hr
        rw [PathCover.cast_paths pc1 hUeq] at hr
        exact hend1 r hr
      have hdef' : pc1'.endpointDeficit B ≤ 2 * (t + (C \ insert u S).card) - 1 := by
        have hcast : pc1'.endpointDeficit B = pc1.endpointDeficit B :=
          pc1.cast_endpointDeficit hUeq B
        have hkrem : (C \ insert u S).card = (C \ S).card - 1 := by
          rw [hrem, card_erase_of_mem hu]
        omega
      exact ih (insert u S) pc1' hS' hk' hcard' hend1' hdef'
  have hU : U ∪ (∅ : Finset V) = U := union_empty U
  let pc0 : PathCover G (U ∪ ∅) := pc.cast hU.symm
  have hcard0 : pc0.card = pc.card - (∅ : Finset V).card := by
    rw [PathCover.cast_card, card_empty, Nat.sub_zero]
  have hend0 : ∀ r ∈ pc0.paths, r.start ∈ P ∧ r.finish ∈ P := by
    intro r hr
    rw [PathCover.cast_paths pc hU.symm] at hr
    exact hend r hr
  have hdef0 : pc0.endpointDeficit B ≤ 2 * (t + (C \ ∅).card) - 1 := by
    have hcast : pc0.endpointDeficit B = pc.endpointDeficit B :=
      pc.cast_endpointDeficit hU.symm B
    simpa [sdiff_empty, hcast] using hdef
  exact aux C.card ∅ pc0 (empty_subset C) (by simp) hcard0 hend0 hdef0

end Nikoghosyan
