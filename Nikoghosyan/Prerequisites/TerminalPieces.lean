/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalNeighbor

/-!
# Leftover ordinary path covers after deleting an independent terminal set

From any actual `B`-terminal original-edge cover of `K`, with `B ⊆ K`
independent, deleting the vertices of `B` from each cover path retains
every nonempty original-edge run. Independence forbids a `B`–`B` path
edge, and every path starts and ends in `B`, so the path `p` contributes
exactly `|p.support ∩ B| - 1` nonempty leftover pieces.

The resulting object is an ordinary `PathCover` of `K \ B` whose
cardinality `r` satisfies the additive identity `r + q = |B|`. Combined
with the already checked sum `∑ (|p.support ∩ B| - 1) + q = |B|`, this
yields the necessary bound `q + p(K \ B) ≤ |B|`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GraphPath

lemma start_mem_takeUntil (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    p.start ∈ (p.takeUntil hx).support :=
  start_mem_support (p.takeUntil hx)

lemma start_not_mem_dropUntil (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hne : x ≠ p.start) :
    p.start ∉ (p.dropUntil hx).support := by
  intro hst
  have hinter := inter_support_takeUntil_dropUntil_subset p hx
  have : p.start ∈ ({x} : Finset V) :=
    hinter (mem_inter.2 ⟨start_mem_takeUntil p hx, hst⟩)
  exact hne (mem_singleton.1 this).symm

lemma dropUntil_support_card_lt (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hne : x ≠ p.start) :
    (p.dropUntil hx).support.card < p.support.card := by
  have hsub : (p.dropUntil hx).support ⊆ p.support :=
    dropUntil_support_subset p hx
  have hne' : (p.dropUntil hx).support ≠ p.support := by
    intro heq
    exact start_not_mem_dropUntil p hx hne (heq ▸ p.start_mem_support)
  exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)

def inB (B : Finset V) : V → Bool := fun x => decide (x ∈ B)

lemma mem_find?_B {B : Finset V} {p : GraphPath G} {b : V}
    (h : p.walk.support.find? (inB B) = some b) :
    b ∈ p.support ∧ b ∈ B := by
  have hmem : b ∈ p.walk.support := List.mem_of_find?_eq_some h
  have hb : b ∈ B := of_decide_eq_true (List.find?_some (p := inB B) h)
  exact ⟨(mem_walk_support (p := p)).2 hmem, hb⟩

lemma find?_B_ne_start {B : Finset V} {p : GraphPath G} {b : V}
    (hs : p.start ∉ B)
    (h : p.walk.support.find? (inB B) = some b) :
    b ≠ p.start :=
  fun hbs => hs (hbs ▸ (mem_find?_B (B := B) h).2)

lemma find?_B_of_mem {B : Finset V} {p : GraphPath G} {x : V}
    (hx : x ∈ p.support) (hxB : x ∈ B) :
    ∃ b, p.walk.support.find? (inB B) = some b := by
  have hxW : x ∈ p.walk.support := (mem_walk_support (p := p)).1 hx
  have hne : p.walk.support.find? (inB B) ≠ none := by
    intro hnone
    have hnot : ¬ inB B x := (List.find?_eq_none (p := inB B)).1 hnone x hxW
    exact hnot (decide_eq_true hxB)
  exact Option.ne_none_iff_exists'.1 hne

noncomputable def firstB
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (B : Finset V) (p : GraphPath G)
    (h : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none) : V :=
  Classical.choose (Option.ne_none_iff_exists'.1 h)

lemma firstB_spec
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {B : Finset V} {p : GraphPath G}
    (h : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none) :
    p.walk.support.find? (fun x => decide (x ∈ B)) = some (firstB B p h) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.1 h)

/-- Nonempty leftover runs of a single original-edge path after deleting `B`. -/
noncomputable def leftoverPieces
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (B : Finset V) (p : GraphPath G) : List (GraphPath G) :=
  if hsB : p.start ∈ B then
    if hnil : p.walk.Nil then
      []
    else
      leftoverPieces B (p.trimStart hnil)
  else if hnone : p.walk.support.find? (fun x => decide (x ∈ B)) = none then
    [p]
  else
    let b := firstB B p hnone
    have hfind := firstB_spec (B := B) (p := p) hnone
    have hx : b ∈ p.support := (mem_find?_B (B := B) hfind).1
    have hne : b ≠ p.start := find?_B_ne_start (B := B) hsB hfind
    have hnn : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
      hne ((takeUntil_nil_iff p hx).1 hn)
    (p.takeUntil hx).trimFinish hnn :: leftoverPieces B (p.dropUntil hx)
termination_by p.support.card
decreasing_by
  · have hnod : p.walk.support.Nodup := (Walk.isPath_def _).1 p.isPath
    have hnod' : (p.trimStart hnil).walk.support.Nodup :=
      (Walk.isPath_def _).1 (p.trimStart hnil).isPath
    have hcard : p.support.card = p.walk.length + 1 := by
      simp [GraphPath.support, List.toFinset_card_of_nodup hnod, Walk.length_support]
    have hcard' : (p.trimStart hnil).support.card =
        (p.trimStart hnil).walk.length + 1 := by
      simp [GraphPath.support, List.toFinset_card_of_nodup hnod', Walk.length_support]
    have hlen : (p.trimStart hnil).walk.length + 1 = p.walk.length := by
      simpa [trimStart] using Walk.length_tail_add_one hnil
    omega
  · have hfind := firstB_spec (B := B) (p := p) hnone
    have hx' : b ∈ p.walk.support := List.mem_of_find?_eq_some hfind
    have hnod : p.walk.support.Nodup := (Walk.isPath_def _).1 p.isPath
    have hnod' : (p.dropUntil hx).walk.support.Nodup :=
      (Walk.isPath_def _).1 (p.dropUntil hx).isPath
    have hcard : p.support.card = p.walk.length + 1 := by
      simp [GraphPath.support, List.toFinset_card_of_nodup hnod, Walk.length_support]
    have hcard' : (p.dropUntil hx).support.card =
        (p.dropUntil hx).walk.length + 1 := by
      simp [GraphPath.support, List.toFinset_card_of_nodup hnod', Walk.length_support]
    have hlen : p.walk.length =
        (p.walk.takeUntil b hx').length + (p.walk.dropUntil b hx').length := by
      rw [← Walk.length_append, Walk.take_spec]
    have hdrop : (p.dropUntil hx).walk.length = (p.walk.dropUntil b hx').length := by
      simp [dropUntil]
    have htake_pos : 1 ≤ (p.walk.takeUntil b hx').length := by
      have hnn : ¬ (p.walk.takeUntil b hx').Nil := fun hn =>
        hne ((Walk.nil_takeUntil p.walk hx').1 hn).symm
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (mt Walk.length_eq_zero_iff.1 hnn))
    omega

lemma leftoverPieces_of_start_mem_nil {B : Finset V} {p : GraphPath G}
    (hsB : p.start ∈ B) (hnil : p.walk.Nil) :
    leftoverPieces B p = [] := by
  rw [leftoverPieces.eq_def]
  simp [hsB, hnil]

lemma leftoverPieces_of_start_mem_cons {B : Finset V} {p : GraphPath G}
    (hsB : p.start ∈ B) (hnil : ¬ p.walk.Nil) :
    leftoverPieces B p = leftoverPieces B (p.trimStart hnil) := by
  rw [leftoverPieces.eq_def]
  simp [hsB, hnil]

lemma leftoverPieces_of_not_mem_start_none {B : Finset V} {p : GraphPath G}
    (hs : p.start ∉ B)
    (h : p.walk.support.find? (fun x => decide (x ∈ B)) = none) :
    leftoverPieces B p = [p] := by
  rw [leftoverPieces.eq_def]
  simp [hs, h]

lemma leftoverPieces_support_subset {B : Finset V} (p : GraphPath G) :
    ∀ q ∈ leftoverPieces B p, q.support ⊆ p.support := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        ∀ q ∈ leftoverPieces B p, q.support ⊆ p.support)
    p.support.card ?_ p rfl
  intro n ih p hn q hq
  by_cases hsB : p.start ∈ B
  · by_cases hnil : p.walk.Nil
    · simp [leftoverPieces_of_start_mem_nil hsB hnil] at hq
    · rw [leftoverPieces_of_start_mem_cons hsB hnil] at hq
      have hlt : (p.trimStart hnil).support.card < n := by
        simpa [hn] using trimStart_support_card_lt p hnil
      have hsub := ih _ hlt (p.trimStart hnil) rfl q hq
      exact hsub.trans (by
        rw [support_trimStart]
        exact erase_subset _ _)
  · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
    | none =>
      rw [leftoverPieces_of_not_mem_start_none hsB hfind] at hq
      simp at hq
      subst hq
      exact subset_rfl
    | some _ =>
      have hnone : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
        simp [hfind]
      rw [leftoverPieces.eq_def] at hq
      simp [hsB, hnone] at hq
      have hfind' := firstB_spec (B := B) (p := p) hnone
      have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
      have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind'
      rcases hq with hq | hq
      · subst hq
        have hnn : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
          hne ((takeUntil_nil_iff p hx).1 hn)
        rw [support_trimFinish (p.takeUntil hx) hnn]
        exact (erase_subset _ _).trans (takeUntil_support_subset p hx)
      · have hlt : (p.dropUntil hx).support.card < n := by
          simpa [hn] using dropUntil_support_card_lt p hx hne
        have hsub := ih _ hlt (p.dropUntil hx) rfl q hq
        exact hsub.trans (dropUntil_support_subset p hx)

lemma takeUntil_ne_first_not_mem_B {B : Finset V} {p : GraphPath G} {b y : V}
    (h : p.walk.support.find? (fun x => decide (x ∈ B)) = some b)
    (hx : b ∈ p.support) (hy : y ∈ (p.takeUntil hx).support) (hne : y ≠ b) :
    y ∉ B := by
  obtain ⟨hbB, as, bs, happ, hpre⟩ :=
    (List.find?_eq_some_iff_append (p := fun x : V => decide (x ∈ B))).1 h
  have hx' := (mem_walk_support (p := p)).1 hx
  obtain ⟨t, ht⟩ := Walk.support_takeUntil_prefix_support p.walk hx'
  have hnn : ¬ (p.takeUntil hx).walk.Nil := by
    intro hn
    have hsing := support_eq_singleton_of_nil (p.takeUntil hx) hn
    have hyb : y = b := by
      have hsf : (p.takeUntil hx).start = b :=
        (nil_iff_start_eq_finish (p.takeUntil hx)).1 hn
      simpa [hsing, hsf] using hy
    exact hne hyb
  have hcat :=
    Walk.support_dropLast_concat (p := p.walk.takeUntil b hx')
      (by simpa [takeUntil] using hnn)
  have hyL : y ∈ (p.walk.takeUntil b hx').support := by
    simpa [takeUntil, support, List.mem_toFinset] using hy
  have hyDL : y ∈ (p.walk.takeUntil b hx').dropLast.support := by
    have : y ∈ (p.walk.takeUntil b hx').dropLast.support ++ [b] := by
      simpa [hcat] using hyL
    exact (List.mem_append.1 this).resolve_right (by simp [hne])
  have hb_as : b ∉ as := by
    intro hba
    have hfalse : decide (b ∈ B) = false := by simpa using hpre b hba
    exact Bool.false_ne_true (hfalse.symm.trans hbB)
  have hdrop_not : b ∉ (p.walk.takeUntil b hx').dropLast.support := by
    intro hbdl
    have hnodT : (p.walk.takeUntil b hx').support.Nodup :=
      (p.takeUntil hx).support_nodup
    rw [← hcat] at hnodT
    have hcnt : ((p.walk.takeUntil b hx').dropLast.support ++ [b]).count b = 1 :=
      List.count_eq_one_of_mem hnodT (by simp)
    have : 2 ≤ ((p.walk.takeUntil b hx').dropLast.support ++ [b]).count b := by
      have h1 : 1 ≤ (p.walk.takeUntil b hx').dropLast.support.count b :=
        List.count_pos_iff.mpr hbdl
      simp [List.count_append, h1]
    omega
  have hsplit2 : p.walk.support =
      (p.walk.takeUntil b hx').dropLast.support ++ b :: t := by
    calc p.walk.support
        = (p.walk.takeUntil b hx').support ++ t := ht.symm
      _ = ((p.walk.takeUntil b hx').dropLast.support ++ [b]) ++ t := by rw [hcat]
      _ = (p.walk.takeUntil b hx').dropLast.support ++ b :: t := by simp
  have hidx1 : p.walk.support.idxOf b = as.length := by
    rw [happ, List.idxOf_append]
    simp [hb_as, List.idxOf_cons_self]
  have hidx2 : p.walk.support.idxOf b =
      (p.walk.takeUntil b hx').dropLast.support.length := by
    rw [hsplit2, List.idxOf_append]
    simp [hdrop_not, List.idxOf_cons_self]
  have hlen : as.length = (p.walk.takeUntil b hx').dropLast.support.length := by
    omega
  have has_eq : as = (p.walk.takeUntil b hx').dropLast.support :=
    List.append_inj_left (t₁ := b :: bs) (t₂ := b :: t)
      (by rw [← happ, hsplit2]) hlen
  have hy_as : y ∈ as := by simpa [has_eq] using hyDL
  intro hyB
  have hfalse : decide (y ∈ B) = false := by simpa using hpre y hy_as
  exact Bool.false_ne_true (hfalse.symm.trans (decide_eq_true hyB))

lemma leftoverPieces_disjoint_B {B : Finset V} (p : GraphPath G) :
    ∀ q ∈ leftoverPieces B p, Disjoint q.support B := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        ∀ q ∈ leftoverPieces B p, Disjoint q.support B)
    p.support.card ?_ p rfl
  intro n ih p hn q hq
  by_cases hsB : p.start ∈ B
  · by_cases hnil : p.walk.Nil
    · simp [leftoverPieces_of_start_mem_nil hsB hnil] at hq
    · rw [leftoverPieces_of_start_mem_cons hsB hnil] at hq
      have hlt : (p.trimStart hnil).support.card < n := by
        simpa [hn] using trimStart_support_card_lt p hnil
      exact ih _ hlt (p.trimStart hnil) rfl q hq
  · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
    | none =>
      have hlist : leftoverPieces B p = [p] :=
        leftoverPieces_of_not_mem_start_none hsB hfind
      have hq' : q = p := List.mem_singleton.1 (hlist ▸ hq)
      cases hq'
      refine disjoint_left.2 ?_
      intro y hy hyB
      have hyW : y ∈ p.walk.support := (mem_walk_support (p := p)).1 hy
      have hnot : ¬ decide (y ∈ B) :=
        (List.find?_eq_none (p := fun x : V => decide (x ∈ B))).1 hfind y hyW
      exact hnot (decide_eq_true hyB)
    | some _ =>
      have hnone : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
        simp [hfind]
      rw [leftoverPieces.eq_def] at hq
      simp [hsB, hnone] at hq
      have hfind' := firstB_spec (B := B) (p := p) hnone
      have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
      have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind'
      rcases hq with hq | hq
      · subst hq
        have hnn : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
          hne ((takeUntil_nil_iff p hx).1 hn)
        rw [disjoint_iff_inter_eq_empty, support_trimFinish (p.takeUntil hx) hnn]
        rw [eq_empty_iff_forall_notMem]
        intro y hy
        have hyE := mem_inter.1 hy
        have hyT : y ∈ (p.takeUntil hx).support := (mem_erase.1 hyE.1).2
        have hyne : y ≠ firstB B p hnone := (mem_erase.1 hyE.1).1
        exact takeUntil_ne_first_not_mem_B (B := B) hfind' hx hyT hyne hyE.2
      · have hlt : (p.dropUntil hx).support.card < n := by
          simpa [hn] using dropUntil_support_card_lt p hx hne
        exact ih _ hlt (p.dropUntil hx) rfl q hq

lemma leftoverPieces_exists_of_mem {B : Finset V} (p : GraphPath G) {y : V}
    (hy : y ∈ p.support) (hyB : y ∉ B) :
    ∃ q ∈ leftoverPieces B p, y ∈ q.support := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n → y ∈ p.support → y ∉ B →
        ∃ q ∈ leftoverPieces B p, y ∈ q.support)
    p.support.card ?_ p rfl hy hyB
  intro n ih p hn hy hyB
  by_cases hsB : p.start ∈ B
  · by_cases hnil : p.walk.Nil
    · have : p.support = {p.start} := support_eq_singleton_of_nil p hnil
      have : y = p.start := by simpa [this] using hy
      exact (hyB (this ▸ hsB)).elim
    · rw [leftoverPieces_of_start_mem_cons hsB hnil]
      have hlt : (p.trimStart hnil).support.card < n := by
        simpa [hn] using trimStart_support_card_lt p hnil
      have hy' : y ∈ (p.trimStart hnil).support := by
        rw [support_trimStart, mem_erase]
        exact ⟨fun hys => hyB (hys ▸ hsB), hy⟩
      exact ih _ hlt (p.trimStart hnil) rfl hy' hyB
  · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
    | none =>
      rw [leftoverPieces_of_not_mem_start_none hsB hfind]
      exact ⟨p, by simp, hy⟩
    | some _ =>
      have hnone : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
        simp [hfind]
      have hfind' := firstB_spec (B := B) (p := p) hnone
      have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
      have hneS : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind'
      have hneY : y ≠ firstB B p hnone := fun h => hyB (h ▸ (mem_find?_B (B := B) hfind').2)
      rw [leftoverPieces.eq_def]
      simp [hsB, hnone]
      have hnn : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
        hneS ((takeUntil_nil_iff p hx).1 hn)
      have hyU : y ∈ (p.takeUntil hx).support ∪ (p.dropUntil hx).support := by
        simpa [support_takeUntil_union_dropUntil] using hy
      rcases mem_union.1 hyU with hyT | hyD
      · refine Or.inl ?_
        rw [support_trimFinish (p.takeUntil hx) hnn, mem_erase]
        exact ⟨hneY, hyT⟩
      · have hlt : (p.dropUntil hx).support.card < n := by
          simpa [hn] using dropUntil_support_card_lt p hx hneS
        obtain ⟨q, hq, hyq⟩ := ih _ hlt (p.dropUntil hx) rfl hyD hyB
        exact Or.inr ⟨q, hq, hyq⟩

lemma leftoverPieces_mem_iff {B : Finset V} (p : GraphPath G) (y : V) :
    (∃ q ∈ leftoverPieces B p, y ∈ q.support) ↔ y ∈ p.support ∧ y ∉ B := by
  constructor
  · intro ⟨q, hq, hy⟩
    exact ⟨leftoverPieces_support_subset p q hq hy,
      disjoint_left.1 (leftoverPieces_disjoint_B p q hq) hy⟩
  · intro ⟨hy, hyB⟩
    exact leftoverPieces_exists_of_mem p hy hyB

lemma leftoverPieces_pairwise {B : Finset V} (p : GraphPath G) :
    (leftoverPieces B p).Pairwise fun q r => Disjoint q.support r.support := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        (leftoverPieces B p).Pairwise fun q r => Disjoint q.support r.support)
    p.support.card ?_ p rfl
  intro n ih p hn
  by_cases hsB : p.start ∈ B
  · by_cases hnil : p.walk.Nil
    · simp [leftoverPieces_of_start_mem_nil hsB hnil]
    · rw [leftoverPieces_of_start_mem_cons hsB hnil]
      have hlt : (p.trimStart hnil).support.card < n := by
        simpa [hn] using trimStart_support_card_lt p hnil
      exact ih _ hlt (p.trimStart hnil) rfl
  · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
    | none =>
      simp [leftoverPieces_of_not_mem_start_none hsB hfind]
    | some _ =>
      have hnone : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
        simp [hfind]
      rw [leftoverPieces.eq_def]
      simp [hsB, hnone]
      have hfind' := firstB_spec (B := B) (p := p) hnone
      have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
      have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind'
      have hnn : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
        hne ((takeUntil_nil_iff p hx).1 hn)
      have hlt : (p.dropUntil hx).support.card < n := by
        simpa [hn] using dropUntil_support_card_lt p hx hne
      refine ⟨?_, ih _ hlt (p.dropUntil hx) rfl⟩
      intro r hr
      have hrsub : r.support ⊆ (p.dropUntil hx).support :=
        leftoverPieces_support_subset (p.dropUntil hx) r hr
      rw [support_trimFinish (p.takeUntil hx) hnn]
      refine disjoint_of_subset_right hrsub ?_
      rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
      intro y hy
      have hyE := mem_inter.1 hy
      have hyne : y ≠ firstB B p hnone := (mem_erase.1 hyE.1).1
      have hyT : y ∈ (p.takeUntil hx).support := (mem_erase.1 hyE.1).2
      have hinter := inter_support_takeUntil_dropUntil_subset p hx
      have : y ∈ ({firstB B p hnone} : Finset V) :=
        hinter (mem_inter.2 ⟨hyT, hyE.2⟩)
      exact hyne (mem_singleton.1 this)

lemma leftoverPieces_length_of_terminal {B : Finset V} {p : GraphPath G}
    (hInd : Independent (G := G) B)
    (hs : p.start ∈ B) (hf : p.finish ∈ B) :
    (leftoverPieces B p).length = (p.support ∩ B).card - 1 := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n → p.start ∈ B → p.finish ∈ B →
        (leftoverPieces B p).length = (p.support ∩ B).card - 1)
    p.support.card ?_ p rfl hs hf
  intro n ih p hn hs hf
  by_cases hnil : p.walk.Nil
  · have hsing : p.support = {p.start} := support_eq_singleton_of_nil p hnil
    have hfin : p.finish = p.start := ((nil_iff_start_eq_finish p).1 hnil).symm
    simp [leftoverPieces_of_start_mem_nil hs hnil, hsing, hs]
  · rw [leftoverPieces_of_start_mem_cons hs hnil]
    have hstart' : (p.trimStart hnil).start ∉ B :=
      trimStart_start_not_mem hInd p hnil hs
    have hfin' : (p.trimStart hnil).finish ∈ B := by
      simpa [trimStart_finish] using hf
    have hlt : (p.trimStart hnil).support.card < n := by
      simpa [hn] using trimStart_support_card_lt p hnil
    have hfind_some : ∃ b, (p.trimStart hnil).walk.support.find?
        (fun x => decide (x ∈ B)) = some b :=
      find?_B_of_mem (p := p.trimStart hnil) (p.trimStart hnil).finish_mem_support hfin'
    obtain ⟨b, hfind⟩ := hfind_some
    have hnone : (p.trimStart hnil).walk.support.find?
        (fun x => decide (x ∈ B)) ≠ none := by simp [hfind]
    rw [leftoverPieces.eq_def]
    simp [hstart', hnone]
    have hfind' := firstB_spec (B := B) (p := p.trimStart hnil) hnone
    have hx : firstB B (p.trimStart hnil) hnone ∈ (p.trimStart hnil).support :=
      (mem_find?_B (B := B) hfind').1
    have hne : firstB B (p.trimStart hnil) hnone ≠ (p.trimStart hnil).start :=
      find?_B_ne_start hstart' hfind'
    have hterm : IsTerminalPath (G := G) B ((p.trimStart hnil).dropUntil hx) :=
      ⟨by
          simpa [dropUntil] using (mem_find?_B (B := B) hfind').2,
        by simpa [dropUntil] using hfin'⟩
    have hltD : ((p.trimStart hnil).dropUntil hx).support.card < n :=
      Nat.lt_trans (dropUntil_support_card_lt (p.trimStart hnil) hx hne) hlt
    have ihD := ih _ hltD ((p.trimStart hnil).dropUntil hx) rfl hterm.1 hterm.2
    have hcard_trim : (p.support ∩ B).card =
        ((p.trimStart hnil).support ∩ B).card + 1 := by
      have hps : p.support = insert p.start (p.trimStart hnil).support := by
        rw [support_trimStart, insert_erase p.start_mem_support]
      have hstart_not : p.start ∉ (p.trimStart hnil).support := by
        rw [support_trimStart]; exact notMem_erase _ _
      rw [hps, insert_inter_of_mem hs, card_insert_of_notMem]
      exact fun hz => hstart_not (mem_inter.1 hz).1
    have hinter :
        ((p.trimStart hnil).support ∩ B).card =
          (((p.trimStart hnil).dropUntil hx).support ∩ B).card := by
      have hunion := support_takeUntil_union_dropUntil (p.trimStart hnil) hx
      have hinters := inter_support_takeUntil_dropUntil_subset (p.trimStart hnil) hx
      have hb : firstB B (p.trimStart hnil) hnone ∈
          ((p.trimStart hnil).dropUntil hx).support := by
        simpa [dropUntil] using
          ((p.trimStart hnil).dropUntil hx).start_mem_support
      have hT : ((p.trimStart hnil).takeUntil hx).support ∩ B ⊆
          {firstB B (p.trimStart hnil) hnone} := by
        intro z hz
        have hzT := (mem_inter.1 hz).1
        have hzB := (mem_inter.1 hz).2
        by_cases hzb : z = firstB B (p.trimStart hnil) hnone
        · simp [hzb]
        · exact (takeUntil_ne_first_not_mem_B (B := B) hfind' hx hzT hzb hzB).elim
      have : (p.trimStart hnil).support ∩ B =
          ((p.trimStart hnil).dropUntil hx).support ∩ B := by
        ext z
        constructor
        · intro hz
          have hzU : z ∈ ((p.trimStart hnil).takeUntil hx).support ∪
              ((p.trimStart hnil).dropUntil hx).support := by
            simpa [hunion] using (mem_inter.1 hz).1
          rcases mem_union.1 hzU with hzT | hzD
          · have : z = firstB B (p.trimStart hnil) hnone :=
              mem_singleton.1 (hT (mem_inter.2 ⟨hzT, (mem_inter.1 hz).2⟩))
            simpa [this] using mem_inter.2 ⟨hb, (mem_find?_B (B := B) hfind').2⟩
          · exact mem_inter.2 ⟨hzD, (mem_inter.1 hz).2⟩
        · intro hz
          exact mem_inter.2
            ⟨(dropUntil_support_subset (p.trimStart hnil) hx) (mem_inter.1 hz).1,
              (mem_inter.1 hz).2⟩
      rw [this]
    simp [ihD, hcard_trim, hinter]
    have hpos : 1 ≤ (((p.trimStart hnil).dropUntil hx).support ∩ B).card :=
      card_pos.mpr ⟨_, mem_inter.2 ⟨((p.trimStart hnil).dropUntil hx).start_mem_support,
        (mem_find?_B (B := B) hfind').2⟩⟩
    omega

end GraphPath

lemma sum_map_eq_sum_toFinset {α : Type*} [DecidableEq α] {l : List α}
    (hn : l.Nodup) (f : α → ℕ) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hn' := List.nodup_cons.1 hn
    have ha : a ∉ l.toFinset := by simpa using hn'.1
    simp [sum_insert ha, ih hn'.2]

namespace PathCover

lemma pairwise_flatMap_leftoverPieces {B : Finset V}
    {l : List (GraphPath G)}
    (h : l.Pairwise fun p q => Disjoint p.support q.support) :
    (l.flatMap fun p => GraphPath.leftoverPieces B p).Pairwise
      fun a b => Disjoint a.support b.support := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    have h' := List.pairwise_cons.mp h
    rw [List.flatMap_cons]
    refine List.pairwise_append.mpr
      ⟨GraphPath.leftoverPieces_pairwise (B := B) p, ih h'.2, ?_⟩
    intro a ha b hb
    obtain ⟨q, hq, hbq⟩ := List.mem_flatMap.mp hb
    have da := GraphPath.leftoverPieces_support_subset (B := B) p a ha
    have db := GraphPath.leftoverPieces_support_subset (B := B) q b hbq
    exact (h'.1 q hq).mono da db

/-- Ordinary leftover cover of `K \ B` obtained by deleting `B` from each
path of an original-edge cover of `K`. -/
noncomputable def leftoverCover {K B : Finset V} (pc : PathCover G K) :
    PathCover G (K \ B) where
  paths := pc.paths.flatMap fun p => GraphPath.leftoverPieces B p
  disjoint := pairwise_flatMap_leftoverPieces pc.disjoint
  mem_iff := by
    intro y
    constructor
    · intro hy
      have hyK : y ∈ K := (mem_sdiff.1 hy).1
      have hyB : y ∉ B := (mem_sdiff.1 hy).2
      obtain ⟨p, hp, hyp⟩ := (pc.mem_iff y).1 hyK
      obtain ⟨q, hq, hyq⟩ :=
        GraphPath.leftoverPieces_exists_of_mem (B := B) p hyp hyB
      exact ⟨q, List.mem_flatMap.2 ⟨p, hp, hq⟩, hyq⟩
    · intro ⟨q, hq, hyq⟩
      obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.1 hq
      have hmem := (GraphPath.leftoverPieces_mem_iff (B := B) p y).1 ⟨q, hqp, hyq⟩
      exact mem_sdiff.2 ⟨(pc.mem_iff y).2 ⟨p, hp, hmem.1⟩, hmem.2⟩

lemma leftoverCover_card {K B : Finset V} (pc : PathCover G K)
    (hBK : B ⊆ K) (hInd : Independent (G := G) B)
    (hterm : IsTerminalCover (G := G) B pc) :
    (pc.leftoverCover (B := B)).card + pc.card = B.card := by
  have hlenp : ∀ p ∈ pc.paths,
      (GraphPath.leftoverPieces B p).length = (p.support ∩ B).card - 1 := by
    intro p hp
    exact GraphPath.leftoverPieces_length_of_terminal hInd (hterm p hp).1 (hterm p hp).2
  have hflat : (pc.leftoverCover (B := B)).card =
      (pc.paths.map fun p => (GraphPath.leftoverPieces B p).length).sum := by
    simp [leftoverCover, PathCover.card, List.length_flatMap]
  have hmap :
      ∀ {l : List (GraphPath G)},
        (∀ p ∈ l, (GraphPath.leftoverPieces B p).length = (p.support ∩ B).card - 1) →
          (l.map fun p => (GraphPath.leftoverPieces B p).length).sum =
            (l.map fun p => (p.support ∩ B).card - 1).sum := by
    intro l
    induction l with
    | nil => intro; simp
    | cons p ps ih =>
      intro h
      simp [h p List.mem_cons_self,
        ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
  have hsum :=
    sum_map_eq_sum_toFinset pc.nodup_paths fun p => (p.support ∩ B).card - 1
  have hex := pc.terminal_excess_add hBK hterm
  simp [hflat, hmap hlenp, hsum, hex]

end PathCover

/-- Deleting independent terminals from an actual `B`-terminal cover of `K`
yields an ordinary cover of `K \ B` of cardinality `|B| - q`, hence
`q + p(K \ B) ≤ |B|`. -/
lemma pathCoverNumber_add_le_card_B {K B : Finset V}
    (hBK : B ⊆ K) (hInd : Independent (G := G) B)
    {pc : PathCover G K} (hterm : IsTerminalCover (G := G) B pc) :
    pc.card + pathCoverNumber G (K \ B) ≤ B.card := by
  have hle := pathCoverNumber_le (G := G) (PathCover.leftoverCover (B := B) pc)
  have hcard := PathCover.leftoverCover_card pc hBK hInd hterm
  omega

end Nikoghosyan
