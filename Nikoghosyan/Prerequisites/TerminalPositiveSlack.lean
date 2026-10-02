/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalJoinBlocks

/-!
# Positive-slack endpoint-deficit induction

A connected cograph carrier with independent nonempty terminals, the
neighbor condition, and strong slack token `t ≥ 1` admits an ordinary
minimum original-edge path cover whose endpoint deficit is at most
`2t - 1`. No unique profile and no assumed deficit-bound field.

The argument inducts on carrier cardinality. Traceable carriers are
handled by the F-cut (`t = 1`) or the universal two-end bound (`t ≥ 2`).
A nontraceable connected carrier is a complete join; independence places
every terminal in one child `P`. The complementary child `Q` is merged
by original complete-join seams that consume two open ends whenever the
current deficit is at least three.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma isCograph_subset {U W : Finset V}
    (hW : IsCograph G W) (hUW : U ⊆ W) : IsCograph G U :=
  fun _ _ _ _ ha hb hc hd hp => hW (hUW ha) (hUW hb) (hUW hc) (hUW hd) hp

/-! ### List-sum bookkeeping for path-cover deficits -/

lemma list_sum_map_erase_one {α : Type*} [DecidableEq α] (f : α → ℕ)
    {a : α} {l : List α} (ha : a ∈ l) (hn : l.Nodup) :
    (l.map f).sum =
      ((l.filter fun x => decide (x ≠ a)).map f).sum + f a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    have hnxs : xs.Nodup := (List.nodup_cons.1 hn).2
    have hnx : x ∉ xs := (List.nodup_cons.1 hn).1
    rcases List.mem_cons.1 ha with hxa | hxs
    · subst hxa
      have hfilt : ((a :: xs).filter fun y => decide (y ≠ a)) = xs := by
        have hfalse : decide (a ≠ a) = false := decide_eq_false (by simp)
        rw [List.filter_cons, hfalse]
        refine List.filter_eq_self.2 ?_
        intro y hy
        exact decide_eq_true (fun h => hnx (h ▸ hy))
      rw [hfilt, List.map_cons, List.sum_cons, Nat.add_comm]
    · have hne : x ≠ a := fun h => hnx (h ▸ hxs)
      have hfilt : ((x :: xs).filter fun y => decide (y ≠ a)) =
          x :: xs.filter fun y => decide (y ≠ a) :=
        List.filter_cons_of_pos (decide_eq_true hne)
      rw [hfilt, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        ih hxs hnxs]
      omega

lemma list_sum_map_erase_two {α : Type*} [DecidableEq α] (f : α → ℕ)
    {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hn : l.Nodup) :
    (l.map f).sum =
      (((l.filter fun x => decide (x ≠ a)).filter fun x => decide (x ≠ b)).map f).sum
        + f a + f b := by
  have h1 := list_sum_map_erase_one f ha hn
  have hb' : b ∈ l.filter fun x => decide (x ≠ a) :=
    List.mem_filter.2 ⟨hb, decide_eq_true hne.symm⟩
  have hn' : (l.filter fun x => decide (x ≠ a)).Nodup := List.Nodup.filter _ hn
  have h2 := list_sum_map_erase_one f (a := b)
    (l := l.filter fun x => decide (x ≠ a)) hb' hn'
  omega

lemma PathCover.endpointDeficit_spliceTwoInsert {U B : Finset V}
    (pc : PathCover G U) {p q : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (b : V) (hb : b ∉ U) (r : GraphPath G)
    (hr : r.support = p.support ∪ {b} ∪ q.support) :
    (pc.spliceTwoInsert hp hq hne b hb r hr).endpointDeficit B +
        p.endpointDeficit B + q.endpointDeficit B =
      pc.endpointDeficit B + r.endpointDeficit B := by
  unfold PathCover.endpointDeficit PathCover.spliceTwoInsert
  have hsum :=
    list_sum_map_erase_two (fun s : GraphPath G => s.endpointDeficit B)
      hp hq hne pc.nodup_paths
  simp [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil] at hsum ⊢
  omega

lemma GraphPath.endpointDeficit_pos_iff (B : Finset V) (p : GraphPath G) :
    0 < p.endpointDeficit B ↔ p.start ∉ B ∨ p.finish ∉ B := by
  unfold GraphPath.endpointDeficit
  split_ifs <;> simp_all

lemma list_endpointDeficit_eq_two_mul (B : Finset V) :
    ∀ (ps : List (GraphPath G)),
      (∀ p ∈ ps, p.start ∉ B ∧ p.finish ∉ B) →
        (ps.map (fun p => p.endpointDeficit B)).sum = 2 * ps.length
  | [], _ => by simp
  | p :: ps, h => by
    have hp := h p (List.mem_cons.2 (Or.inl rfl))
    have hps : ∀ q ∈ ps, q.start ∉ B ∧ q.finish ∉ B := fun q hq =>
      h q (List.mem_cons.2 (Or.inr hq))
    have hpdef : p.endpointDeficit B = 2 := by
      unfold GraphPath.endpointDeficit
      simp [hp.1, hp.2]
    simp [List.map_cons, List.sum_cons, hpdef,
      list_endpointDeficit_eq_two_mul B ps hps, Nat.mul_succ, Nat.add_comm]

lemma PathCover.endpointDeficit_eq_two_mul_of_ends_outside {K B : Finset V}
    (pc : PathCover G K)
    (h : ∀ p ∈ pc.paths, p.start ∉ B ∧ p.finish ∉ B) :
    pc.endpointDeficit B = 2 * pc.card := by
  simpa [PathCover.endpointDeficit, PathCover.card] using
    list_endpointDeficit_eq_two_mul (G := G) B pc.paths h

lemma PathCover.cast_endpointDeficit_slack {U W B : Finset V}
    (pc : PathCover G U) (h : U = W) :
    (pc.cast h).endpointDeficit B = pc.endpointDeficit B := by
  simp [PathCover.endpointDeficit, PathCover.cast_paths pc h]

lemma PathCover.endpointDeficit_ofPath (B : Finset V) (p : GraphPath G) :
    (PathCover.ofPath p).endpointDeficit B = p.endpointDeficit B := by
  simp [PathCover.ofPath, PathCover.endpointDeficit]

lemma GraphPath.endpointDeficit_anti {B C : Finset V} (h : B ⊆ C)
    (p : GraphPath G) :
    p.endpointDeficit C ≤ p.endpointDeficit B := by
  unfold GraphPath.endpointDeficit
  have hs : (if p.start ∈ C then 0 else 1) ≤ (if p.start ∈ B then 0 else 1) := by
    by_cases hC : p.start ∈ C
    · simp [hC]
    · have hB : p.start ∉ B := fun hB => hC (h hB)
      simp [hC, hB]
  have hf : (if p.finish ∈ C then 0 else 1) ≤ (if p.finish ∈ B then 0 else 1) := by
    by_cases hC : p.finish ∈ C
    · simp [hC]
    · have hB : p.finish ∉ B := fun hB => hC (h hB)
      simp [hC, hB]
  omega

lemma list_endpointDeficit_anti {B C : Finset V} (hBC : B ⊆ C) :
    ∀ (ps : List (GraphPath G)),
      (ps.map (fun p => p.endpointDeficit C)).sum ≤
        (ps.map (fun p => p.endpointDeficit B)).sum
  | [] => by simp
  | p :: ps => by
    simp [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (GraphPath.endpointDeficit_anti hBC p)
      (list_endpointDeficit_anti hBC ps)

lemma PathCover.endpointDeficit_anti {K B C : Finset V} (hBC : B ⊆ C)
    (pc : PathCover G K) :
    pc.endpointDeficit C ≤ pc.endpointDeficit B :=
  list_endpointDeficit_anti (G := G) hBC pc.paths

lemma PathCover.endpointDeficit_unionDisjoint {A C B : Finset V}
    (hdisj : Disjoint A C)
    (pcA : PathCover G A) (pcC : PathCover G C) :
    (Cograph.PathCover.unionDisjoint hdisj pcA pcC).endpointDeficit B =
      pcA.endpointDeficit B + pcC.endpointDeficit B := by
  unfold PathCover.endpointDeficit Cograph.PathCover.unionDisjoint
  simp [List.map_append, List.sum_append]

/-! ### Two distinct open paths from deficit at least three -/

lemma list_exists_pos_deficit (B : Finset V) :
    ∀ (ps : List (GraphPath G)),
      1 ≤ (ps.map (fun p => p.endpointDeficit B)).sum →
        ∃ p ∈ ps, 0 < p.endpointDeficit B
  | [], h => by simp at h
  | p :: ps, h => by
    simp [List.map_cons, List.sum_cons] at h
    by_cases hp : 0 < p.endpointDeficit B
    · exact ⟨p, List.mem_cons.2 (Or.inl rfl), hp⟩
    · have hps : 1 ≤ (ps.map (fun q => q.endpointDeficit B)).sum := by omega
      obtain ⟨q, hq, hqpos⟩ := list_exists_pos_deficit B ps hps
      exact ⟨q, List.mem_cons.2 (Or.inr hq), hqpos⟩

lemma PathCover.exists_pos_deficit_path {K B : Finset V}
    (pc : PathCover G K) (h : 1 ≤ pc.endpointDeficit B) :
    ∃ p ∈ pc.paths, 0 < p.endpointDeficit B := by
  simpa [PathCover.endpointDeficit] using
    list_exists_pos_deficit (G := G) B pc.paths h

lemma list_sum_deficit_le_two_of_unique_open (B : Finset V) :
    ∀ (ps : List (GraphPath G)),
      ps.Nodup →
      (∀ p ∈ ps, ∀ q ∈ ps,
        0 < p.endpointDeficit B → 0 < q.endpointDeficit B → p = q) →
      (ps.map (fun p => p.endpointDeficit B)).sum ≤ 2
  | [], _, _ => by simp
  | p :: ps, hn, huniq => by
    have hnxs := (List.nodup_cons.1 hn).2
    have hnx := (List.nodup_cons.1 hn).1
    have huniq' : ∀ x ∈ ps, ∀ y ∈ ps,
        0 < x.endpointDeficit B → 0 < y.endpointDeficit B → x = y :=
      fun x hx y hy hxpos hypos =>
        huniq x (List.mem_cons.2 (Or.inr hx)) y (List.mem_cons.2 (Or.inr hy))
          hxpos hypos
    simp [List.map_cons, List.sum_cons]
    by_cases hp : 0 < p.endpointDeficit B
    · have hps0 : ∀ q ∈ ps, q.endpointDeficit B = 0 := by
        intro q hq
        by_contra hqpos
        have hqpos' : 0 < q.endpointDeficit B := Nat.pos_of_ne_zero hqpos
        have heq :=
          huniq p (List.mem_cons.2 (Or.inl rfl)) q (List.mem_cons.2 (Or.inr hq))
            hp hqpos'
        exact hnx (heq ▸ hq)
      have hsum0 : (ps.map (fun q => q.endpointDeficit B)).sum = 0 :=
        List.sum_eq_zero fun n hn' => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hn'
          exact hps0 q hq
      have hple : p.endpointDeficit B ≤ 2 := GraphPath.endpointDeficit_le_two B p
      omega
    · have := list_sum_deficit_le_two_of_unique_open B ps hnxs huniq'
      omega

lemma PathCover.sum_deficit_le_two_of_unique_open {K B : Finset V}
    (pc : PathCover G K)
    (huniq : ∀ p ∈ pc.paths, ∀ q ∈ pc.paths,
      0 < p.endpointDeficit B → 0 < q.endpointDeficit B → p = q) :
    pc.endpointDeficit B ≤ 2 := by
  simpa [PathCover.endpointDeficit] using
    list_sum_deficit_le_two_of_unique_open (G := G) B pc.paths pc.nodup_paths huniq

lemma PathCover.exists_two_open_paths {K B : Finset V}
    (pc : PathCover G K) (hdef : 3 ≤ pc.endpointDeficit B) :
    ∃ p q, p ∈ pc.paths ∧ q ∈ pc.paths ∧ p ≠ q ∧
      (p.start ∉ B ∨ p.finish ∉ B) ∧
      (q.start ∉ B ∨ q.finish ∉ B) := by
  have hpos : 1 ≤ pc.endpointDeficit B := by omega
  obtain ⟨p, hp, hppos⟩ := pc.exists_pos_deficit_path hpos
  by_contra h
  have huniq : ∀ x ∈ pc.paths, ∀ y ∈ pc.paths,
      0 < x.endpointDeficit B → 0 < y.endpointDeficit B → x = y := by
    intro x hx y hy hxpos hypos
    by_contra hne
    have hxopen : x.start ∉ B ∨ x.finish ∉ B :=
      (GraphPath.endpointDeficit_pos_iff (G := G) B x).1 hxpos
    have hyopen : y.start ∉ B ∨ y.finish ∉ B :=
      (GraphPath.endpointDeficit_pos_iff (G := G) B y).1 hypos
    exact h ⟨x, y, hx, hy, hne, hxopen, hyopen⟩
  have hle := pc.sum_deficit_le_two_of_unique_open huniq
  omega

/-! ### One connector merge reducing deficit by two -/

lemma GraphPath.orientFinishOpen_finish_open (B : Finset V) (p : GraphPath G)
    (h : p.start ∉ B ∨ p.finish ∉ B) :
    (p.orientFinishOpen B).finish ∉ B :=
  GraphPath.orientFinishOpen_finish_not_mem B p h

lemma GraphPath.orientStartOpen_start_open (B : Finset V) (p : GraphPath G)
    (h : p.start ∉ B ∨ p.finish ∉ B) :
    (p.orientStartOpen B).start ∉ B :=
  GraphPath.orientStartOpen_start_not_mem B p h

lemma GraphPath.orientFinishOpen_deficit (B : Finset V) (p : GraphPath G) :
    (p.orientFinishOpen B).endpointDeficit B = p.endpointDeficit B := by
  unfold GraphPath.orientFinishOpen
  split_ifs
  · exact GraphPath.endpointDeficit_reverse B p
  · rfl

lemma GraphPath.orientStartOpen_deficit (B : Finset V) (p : GraphPath G) :
    (p.orientStartOpen B).endpointDeficit B = p.endpointDeficit B := by
  unfold GraphPath.orientStartOpen
  split_ifs
  · exact GraphPath.endpointDeficit_reverse B p
  · rfl

lemma exists_insert_connector_reduce2 {U A Q B : Finset V}
    (hAQ : G.IsCompleteBetween (A : Set V) (Q : Set V))
    (pc : PathCover G U) (h2 : 2 ≤ pc.card)
    (hend : ∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A)
    (hdef : 3 ≤ pc.endpointDeficit B)
    {b : V} (hb : b ∈ Q) (hbU : b ∉ U) :
    ∃ pc' : PathCover G (insert b U),
      pc'.card = pc.card - 1 ∧
        (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) ∧
          pc'.endpointDeficit B + 2 ≤ pc.endpointDeficit B := by
  obtain ⟨p, q, hp, hq, hne, hpopen, hqopen⟩ := pc.exists_two_open_paths hdef
  let p' := p.orientFinishOpen B
  let q' := q.orientStartOpen B
  have hpA : p'.start ∈ A ∧ p'.finish ∈ A :=
    GraphPath.orientFinishOpen_mem_X (X := A) (B := B) p (hend p hp).1 (hend p hp).2
  have hqA : q'.start ∈ A ∧ q'.finish ∈ A :=
    GraphPath.orientStartOpen_mem_X (X := A) (B := B) q (hend q hq).1 (hend q hq).2
  have hp'supp : p'.support = p.support := GraphPath.orientFinishOpen_support B p
  have hq'supp : q'.support = q.support := GraphPath.orientStartOpen_support B q
  have hpb : b ∉ p'.support := by
    rw [hp'supp]
    exact fun h => hbU (pc.support_subset hp h)
  have hqb : b ∉ q'.support := by
    rw [hq'supp]
    exact fun h => hbU (pc.support_subset hq h)
  have hd : Disjoint p'.support q'.support := by
    rw [hp'supp, hq'supp]
    exact PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_spliceABA hAQ p' b q' hpA.2 hb hqA.1 hpb hqb hd
  have hr' : r.support = p.support ∪ {b} ∪ q.support := by
    simpa [hp'supp, hq'supp] using hr
  refine ⟨pc.spliceTwoInsert hp hq hne b hbU r hr',
    pc.spliceTwoInsert_card hp hq hne b hbU r hr', ?_, ?_⟩
  · intro s hsmem
    rcases pc.spliceTwoInsert_mem_paths hp hq hne b hbU r hr' hsmem with
      hseq | ⟨hspc, _, _⟩
    · subst hseq
      rw [hs, hf]
      exact ⟨hpA.1, hqA.2⟩
    · exact hend s hspc
  · have hsum :=
      PathCover.endpointDeficit_spliceTwoInsert (B := B) pc hp hq hne b hbU r hr'
    have hpfin : p'.finish ∉ B :=
      GraphPath.orientFinishOpen_finish_open B p hpopen
    have hqst : q'.start ∉ B :=
      GraphPath.orientStartOpen_start_open B q hqopen
    have hrdef :
        r.endpointDeficit B + 2 =
          p.endpointDeficit B + q.endpointDeficit B := by
      rw [← GraphPath.orientFinishOpen_deficit B p,
        ← GraphPath.orientStartOpen_deficit B q]
      unfold GraphPath.endpointDeficit
      rw [hs, hf]
      have hfin1 : (if p'.finish ∈ B then 0 else 1) = 1 := by simp [hpfin]
      have hst1 : (if q'.start ∈ B then 0 else 1) = 1 := by simp [hqst]
      split_ifs <;> omega
    omega

lemma exists_insert_connector_reduce1 {U A Q B : Finset V}
    (hAQ : G.IsCompleteBetween (A : Set V) (Q : Set V))
    (pc : PathCover G U) (h2 : 2 ≤ pc.card)
    (hend : ∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A)
    (hdef : 1 ≤ pc.endpointDeficit B)
    {b : V} (hb : b ∈ Q) (hbU : b ∉ U) :
    ∃ pc' : PathCover G (insert b U),
      pc'.card = pc.card - 1 ∧
        (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) ∧
          pc'.endpointDeficit B + 1 ≤ pc.endpointDeficit B := by
  obtain ⟨p, hp, hppos⟩ := pc.exists_pos_deficit_path hdef
  obtain ⟨q, hq, hne⟩ : ∃ q, q ∈ pc.paths ∧ q ≠ p := by
    obtain ⟨x, y, hx, hy, hxy⟩ := pc.exists_two_distinct h2
    by_cases hxp : x = p
    · exact ⟨y, hy, fun h => hxy (hxp.trans h.symm)⟩
    · exact ⟨x, hx, hxp⟩
  have hne' : p ≠ q := hne.symm
  have hpopen : p.start ∉ B ∨ p.finish ∉ B :=
    (GraphPath.endpointDeficit_pos_iff (G := G) B p).1 hppos
  let p' := p.orientFinishOpen B
  have hpA : p'.start ∈ A ∧ p'.finish ∈ A :=
    GraphPath.orientFinishOpen_mem_X (X := A) (B := B) p (hend p hp).1 (hend p hp).2
  have hqA := hend q hq
  have hp'supp : p'.support = p.support := GraphPath.orientFinishOpen_support B p
  have hpb : b ∉ p'.support := by
    rw [hp'supp]
    exact fun h => hbU (pc.support_subset hp h)
  have hqb : b ∉ q.support := fun h => hbU (pc.support_subset hq h)
  have hd : Disjoint p'.support q.support := by
    rw [hp'supp]
    exact PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne'
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_spliceABA hAQ p' b q hpA.2 hb hqA.1 hpb hqb hd
  have hr' : r.support = p.support ∪ {b} ∪ q.support := by
    simpa [hp'supp] using hr
  refine ⟨pc.spliceTwoInsert hp hq hne' b hbU r hr',
    pc.spliceTwoInsert_card hp hq hne' b hbU r hr', ?_, ?_⟩
  · intro s hsmem
    rcases pc.spliceTwoInsert_mem_paths hp hq hne' b hbU r hr' hsmem with
      hseq | ⟨hspc, _, _⟩
    · subst hseq
      rw [hs, hf]
      exact ⟨hpA.1, hqA.2⟩
    · exact hend s hspc
  · have hsum :=
      PathCover.endpointDeficit_spliceTwoInsert (B := B) pc hp hq hne' b hbU r hr'
    have hpfin : p'.finish ∉ B :=
      GraphPath.orientFinishOpen_finish_open B p hpopen
    have hred : r.endpointDeficit B + 1 ≤ p.endpointDeficit B + q.endpointDeficit B := by
      rw [← GraphPath.orientFinishOpen_deficit B p]
      unfold GraphPath.endpointDeficit
      rw [hs, hf]
      have hfin1 : (if p'.finish ∈ B then 0 else 1) = 1 := by simp [hpfin]
      split_ifs <;> omega
    omega

lemma exists_insert_connector_mono {U A Q B : Finset V}
    (hAQ : G.IsCompleteBetween (A : Set V) (Q : Set V))
    (pc : PathCover G U) (h2 : 2 ≤ pc.card)
    (hend : ∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A)
    {b : V} (hb : b ∈ Q) (hbU : b ∉ U) :
    ∃ pc' : PathCover G (insert b U),
      pc'.card = pc.card - 1 ∧
        (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) ∧
          pc'.endpointDeficit B ≤ pc.endpointDeficit B := by
  obtain ⟨p, q, hp, hq, hne⟩ := pc.exists_two_distinct h2
  have hpA := hend p hp
  have hqA := hend q hq
  have hpb : b ∉ p.support := fun h => hbU (pc.support_subset hp h)
  have hqb : b ∉ q.support := fun h => hbU (pc.support_subset hq h)
  have hd := PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_spliceABA hAQ p b q hpA.2 hb hqA.1 hpb hqb hd
  refine ⟨pc.spliceTwoInsert hp hq hne b hbU r hr,
    pc.spliceTwoInsert_card hp hq hne b hbU r hr, ?_, ?_⟩
  · intro s hsmem
    rcases pc.spliceTwoInsert_mem_paths hp hq hne b hbU r hr hsmem with
      hseq | ⟨hspc, _, _⟩
    · subst hseq
      rw [hs, hf]
      exact ⟨hpA.1, hqA.2⟩
    · exact hend s hspc
  · have hsum :=
      PathCover.endpointDeficit_spliceTwoInsert (B := B) pc hp hq hne b hbU r hr
    have hred : r.endpointDeficit B ≤ p.endpointDeficit B + q.endpointDeficit B := by
      unfold GraphPath.endpointDeficit
      rw [hs, hf]
      split_ifs <;> omega
    omega


/-! ### Iterate connector merges, preserving the `2t-1` budget -/

lemma exists_merge_all_connectors {A Q B : Finset V} {t : ℕ}
    (hAQ : G.IsCompleteBetween (A : Set V) (Q : Set V))
    (hdom : Q.card < pathCoverNumber G A)
    (pc : PathCover G A)
    (hpc : pc.card = pathCoverNumber G A)
    (hend : ∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A)
    (hdef : pc.endpointDeficit B ≤ 2 * (t + Q.card) - 1) :
    ∃ pc' : PathCover G (A ∪ Q),
      pc'.card = pathCoverNumber G A - Q.card ∧
        (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) ∧
          pc'.endpointDeficit B ≤ 2 * t - 1 := by
  have aux :
      ∀ (k : ℕ) (S : Finset V) (pcS : PathCover G (A ∪ S)),
        S ⊆ Q → (Q \ S).card = k →
          pcS.card = pathCoverNumber G A - S.card →
            (∀ p ∈ pcS.paths, p.start ∈ A ∧ p.finish ∈ A) →
              pcS.endpointDeficit B ≤ 2 * (t + k) - 1 →
                ∃ pc' : PathCover G (A ∪ Q),
                  pc'.card = pathCoverNumber G A - Q.card ∧
                    (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) ∧
                      pc'.endpointDeficit B ≤ 2 * t - 1 := by
    intro k
    induction k with
    | zero =>
      intro S pcS hS hk hcard hendS hdefS
      have hQS : Q \ S = ∅ := Finset.card_eq_zero.mp hk
      have hBeq : S = Q := subset_antisymm hS (sdiff_eq_empty_iff_subset.mp hQS)
      subst hBeq
      exact ⟨pcS, hcard, hendS, by simpa using hdefS⟩
    | succ k ih =>
      intro S pcS hS hk hcard hendS hdefS
      have hne : (Q \ S).Nonempty := card_pos.mp (by omega : 0 < (Q \ S).card)
      obtain ⟨b, hb⟩ := hne
      have hbQ : b ∈ Q := (mem_sdiff.1 hb).1
      have hbS : b ∉ S := (mem_sdiff.1 hb).2
      have hdisjAQ := disjoint_of_completeBetween hAQ
      have hbU : b ∉ A ∪ S := by
        intro h
        rcases mem_union.1 h with hA | hS'
        · exact Finset.disjoint_left.1 hdisjAQ hA hbQ
        · exact hbS hS'
      have h2 : 2 ≤ pcS.card := by
        have hsum : S.card + (Q \ S).card = Q.card := by
          rw [← card_union_of_disjoint, union_sdiff_of_subset hS]
          exact disjoint_sdiff
        omega
      have hnew :
          ∃ pc1 : PathCover G (insert b (A ∪ S)),
            pc1.card = pcS.card - 1 ∧
              (∀ p ∈ pc1.paths, p.start ∈ A ∧ p.finish ∈ A) ∧
                pc1.endpointDeficit B ≤ 2 * (t + k) - 1 := by
        by_cases h3 : 3 ≤ pcS.endpointDeficit B
        · obtain ⟨pc1, hc1, he1, hr⟩ :=
            exists_insert_connector_reduce2 (B := B) hAQ pcS h2 hendS h3 hbQ hbU
          refine ⟨pc1, hc1, he1, ?_⟩
          omega
        · by_cases h1 : 1 ≤ pcS.endpointDeficit B
          · obtain ⟨pc1, hc1, he1, hr⟩ :=
              exists_insert_connector_reduce1 (B := B) hAQ pcS h2 hendS h1 hbQ hbU
            refine ⟨pc1, hc1, he1, ?_⟩
            have : pcS.endpointDeficit B ≤ 2 := by omega
            omega
          · obtain ⟨pc1, hc1, he1, hr⟩ :=
              exists_insert_connector_mono (B := B) hAQ pcS h2 hendS hbQ hbU
            refine ⟨pc1, hc1, he1, ?_⟩
            omega
      obtain ⟨pc1, hcard1, hend1, hred⟩ := hnew
      have hU : insert b (A ∪ S) = A ∪ insert b S := by
        ext x
        simp [mem_insert, mem_union]
      let pc1' : PathCover G (A ∪ insert b S) := pc1.cast hU
      have hS' : insert b S ⊆ Q := insert_subset hbQ hS
      have hrem : Q \ insert b S = (Q \ S).erase b := sdiff_insert Q S b
      have hk' : (Q \ insert b S).card = k := by
        rw [hrem, card_erase_of_mem hb, hk]
        omega
      have hcard' : pc1'.card = pathCoverNumber G A - (insert b S).card := by
        rw [PathCover.cast_card, hcard1, hcard, card_insert_of_notMem hbS]
        omega
      have hend1' : ∀ p ∈ pc1'.paths, p.start ∈ A ∧ p.finish ∈ A := by
        intro p hp
        rw [PathCover.cast_paths pc1 hU] at hp
        exact hend1 p hp
      have hdef' : pc1'.endpointDeficit B ≤ 2 * (t + k) - 1 := by
        rw [PathCover.cast_endpointDeficit_slack]
        exact hred
      exact ih (insert b S) pc1' hS' hk' hcard' hend1' hdef'
  have hA : A ∪ (∅ : Finset V) = A := union_empty A
  let pc0 : PathCover G (A ∪ ∅) := pc.cast hA.symm
  have hcard0 : pc0.card = pathCoverNumber G A - (∅ : Finset V).card := by
    rw [PathCover.cast_card, hpc, card_empty, Nat.sub_zero]
  have hend0 : ∀ p ∈ pc0.paths, p.start ∈ A ∧ p.finish ∈ A := by
    intro p hp
    rw [PathCover.cast_paths pc hA.symm] at hp
    exact hend p hp
  have hdef0 : pc0.endpointDeficit B ≤ 2 * (t + Q.card) - 1 := by
    rw [PathCover.cast_endpointDeficit_slack]
    exact hdef
  exact aux Q.card ∅ pc0 (empty_subset Q) (by simp) hcard0 hend0 hdef0

/-! ### Traceable base under strong slack -/

lemma not_B_subset_ineligible_of_slack_t_one {K B : Finset V}
    (hcog : IsCograph G K) (hBK : B ⊆ K) (hBne : B.Nonempty)
    (hp : pathCoverNumber G K = 1)
    (hTH : TerminalHypothesisSlackStrong (G := G) K B 1) :
    ¬ B ⊆ ineligibleSet G K := by
  intro hBF
  have hFsub : ineligibleSet G K ⊆ K := ineligibleSet_subset (G := G) K
  by_cases hFne : (ineligibleSet G K).Nonempty
  · have hz := hTH.2 (ineligibleSet G K) hFsub hFne
    have hz' :
        terminalComponentCount (G := G) K B (ineligibleSet G K) =
          componentCount G (K \ ineligibleSet G K) :=
      terminalComponentCount_eq_of_B_subset (G := G) (K := K) hBF
    have hcut :=
      Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) hcog
    omega
  · have hF0 : ineligibleSet G K = ∅ := not_nonempty_iff_eq_empty.1 hFne
    have hB0 : B = ∅ := subset_empty.mp (hF0 ▸ hBF)
    exact hBne.ne_empty hB0

lemma exists_min_cover_deficit_le_of_p_eq_one {K B : Finset V} {t : ℕ}
    (hcog : IsCograph G K) (hBK : B ⊆ K) (hBne : B.Nonempty)
    (hp : pathCoverNumber G K = 1) (ht : 1 ≤ t)
    (hTH : TerminalHypothesisSlackStrong (G := G) K B t) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧
        pc.endpointDeficit B ≤ 2 * t - 1 := by
  obtain ⟨pc0, hpc0⟩ := exists_min_pathCover (G := G) K
  have hcard1 : pc0.card = 1 := by omega
  obtain ⟨p, hpths⟩ := PathCover.exists_singleton_of_card_one pc0 hcard1
  have hpdef : p.endpointDeficit B ≤ 2 := GraphPath.endpointDeficit_le_two B p
  have hpc0def : pc0.endpointDeficit B = p.endpointDeficit B := by
    simp [PathCover.endpointDeficit, hpths]
  by_cases ht1 : t = 1
  · subst ht1
    have hnot : ¬ B ⊆ ineligibleSet G K :=
      not_B_subset_ineligible_of_slack_t_one hcog hBK hBne hp hTH
    obtain ⟨b, hbB, hbE⟩ : ∃ b ∈ B, Eligible G K b := by
      by_contra h
      apply hnot
      intro x hx
      have hxK : x ∈ K := hBK hx
      have hnotE : ¬ Eligible G K x := fun hE => h ⟨x, hx, hE⟩
      exact (mem_ineligibleSet_iff (G := G)).2 ⟨hxK, hnotE⟩
    obtain ⟨q, hqU, hqend⟩ :=
      Cograph.exists_spanning_path_of_eligible_eq_one (G := G) hp hbE
    let q' : GraphPath G :=
      if q.start = b then q else q.reverse
    have hq'supp : q'.support = K := by
      unfold q'
      split_ifs <;> simp [hqU]
    have hq'end : q'.start = b ∨ q'.finish = b := by
      unfold q'
      split_ifs with hs
      · exact Or.inl hs
      · rcases hqend with hst | hfin
        · exact (hs hst).elim
        · simp [GraphPath.reverse, hfin]
    have hbdef : q'.endpointDeficit B ≤ 1 := by
      unfold GraphPath.endpointDeficit
      rcases hq'end with hs | hf
      · simp [hs, hbB]
        split_ifs <;> simp
      · simp [hf, hbB]
        split_ifs <;> simp
    refine ⟨PathCover.ofSupport q' hq'supp, ?_, ?_⟩
    · simpa [PathCover.ofSupport_card q' hq'supp] using hp.symm
    · have : (PathCover.ofSupport q' hq'supp).endpointDeficit B =
          q'.endpointDeficit B := by
        simp [PathCover.ofSupport, PathCover.cast_endpointDeficit_slack,
          PathCover.endpointDeficit_ofPath]
      omega
  · have : 2 ≤ t := by omega
    refine ⟨pc0, hpc0, ?_⟩
    omega

/-! ### Mixed-split slack inheritance with unchanged token -/

lemma terminalComponentCount_empty_eq_zero_of_BV {K B : Finset V}
    (hN : NeighborCondition (G := G) K B) (hBK : B ⊆ K)
    {b v : V} (hb : b ∈ B) (hv : v ∈ K \ B) (hadj : G.Adj b v) :
    terminalComponentCount (G := G) K B ∅ = 0 := by
  have hvK : v ∈ K := (mem_sdiff.1 hv).1
  have hbK : b ∈ K := hBK hb
  let Cmix := (G.induce (K : Set V)).connectedComponentMk ⟨v, hvK⟩
  have hno : ∀ C : (G.induce (K : Set V)).ConnectedComponent,
      componentFinset G K C ∩ B ≠ ∅ := by
    intro C he
    obtain ⟨x, hxC⟩ := componentFinset_nonempty (G := G) C
    have hxK : x ∈ K := (mem_filter.1 hxC).1
    have hxB : x ∉ B := fun hxB =>
      (notMem_empty x (he ▸ mem_inter.2 ⟨hxC, hxB⟩))
    have hxmix : x ∈ componentFinset G K Cmix :=
      sdiff_subset_mixed_component hN hBK hb hv hadj (mem_sdiff.2 ⟨hxK, hxB⟩)
    have hCeq : C = Cmix :=
      (connectedComponentMk_eq_of_mem_componentFinset' (G := G) hxC).symm.trans
        (connectedComponentMk_eq_of_mem_componentFinset' (G := G) hxmix)
    have hbC : b ∈ componentFinset G K C := by
      simpa [hCeq] using mem_componentFinset_of_adj_B (G := G) hbK hvK hadj
    exact (notMem_empty b (he ▸ mem_inter.2 ⟨hbC, hb⟩))
  have hz :
      terminalComponentCount (G := G) K B ∅ =
        Nat.card { C : (G.induce (K : Set V)).ConnectedComponent //
          componentFinset G K C ∩ B = ∅ } := by
    unfold terminalComponentCount IsFreeComponent
    rw [sdiff_empty, sdiff_empty]
  rw [hz]
  haveI : IsEmpty { C : (G.induce (K : Set V)).ConnectedComponent //
      componentFinset G K C ∩ B = ∅ } :=
    ⟨fun C => hno C.1 C.2⟩
  simpa [Nat.card_eq_zero] using Or.inl this

lemma exists_mixedSplit_of_BV {K B : Finset V}
    (hBK : B ⊆ K) (hN : NeighborCondition (G := G) K B)
    {b v : V} (hb : b ∈ B) (hv : v ∈ K \ B) (hadj : G.Adj b v) :
    Nonempty (MixedSplit (G := G) K B) :=
  exists_mixedSplit (G := G) hBK hN
    (terminalComponentCount_empty_eq_zero_of_BV hN hBK hb hv hadj)
    ⟨v, hv⟩

lemma TerminalHypothesisSlackStrong.restrict_mixed {K D B : Finset V} {t : ℕ}
    (hBK : B ⊆ K) (hD : D ⊆ K) (hI : K \ D ⊆ B)
    (hnocross : ∀ a ∈ D, ∀ b ∈ K \ D, ¬ G.Adj a b)
    (hTH : TerminalHypothesisSlackStrong (G := G) K B t) :
    TerminalHypothesisSlackStrong (G := G) D (B ∩ D) t := by
  constructor
  · have hz := hTH.1
    simpa [terminalComponentCount_mixed (S := (∅ : Finset V)) hBK hD
      (empty_subset D) hI hnocross] using hz
  · intro S hS hSne
    have hz := hTH.2 S (hS.trans hD) hSne
    simpa [terminalComponentCount_mixed hBK hD hS hI hnocross] using hz

/-! ### No-BV child: F-cut bound and ordinary cover -/

lemma sdiff_union_eq_union_sdiff_right {B W F : Finset V}
    (hdisj : Disjoint B W) (hF : F ⊆ W) :
    (B ∪ W) \ F = B ∪ (W \ F) := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hx
    rcases hx.1 with hB | hW
    · exact Or.inl hB
    · exact Or.inr ⟨hW, hx.2⟩
  · intro hx
    rcases hx with hB | hW
    · exact ⟨Or.inl hB, fun hF' => Finset.disjoint_left.1
        (disjoint_of_subset_right hF hdisj) hB hF'⟩
    · exact ⟨Or.inr hW.1, hW.2⟩

lemma B_sdiff_eq_of_disjoint_right {B W F : Finset V}
    (hdisj : Disjoint B W) (hF : F ⊆ W) :
    B \ F = B := by
  ext x
  simp only [mem_sdiff]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, fun hF' => Finset.disjoint_left.1
      (disjoint_of_subset_right hF hdisj) hx hF'⟩

lemma terminalComponentCount_noBV {K B W F : Finset V}
    (hKW : K = B ∪ W) (hdisj : Disjoint B W)
    (hanti : ∀ b ∈ B, ∀ w ∈ W, ¬ G.Adj b w) (hF : F ⊆ W) :
    terminalComponentCount (G := G) K B F = componentCount G (W \ F) := by
  have hrem : K \ F = (W \ F) ∪ B := by
    rw [hKW, sdiff_union_eq_union_sdiff_right hdisj hF, union_comm]
  have hBeq : B \ F = B := B_sdiff_eq_of_disjoint_right hdisj hF
  have hnc : ∀ a ∈ W \ F, ∀ b ∈ B, ¬ G.Adj a b :=
    fun a ha b hb hab => hanti b hb a (mem_sdiff.1 ha).1 hab.symm
  have h1 :
      terminalComponentCount (G := G) K B F =
        Nat.card
          { C : (G.induce (((W \ F) ∪ B : Finset V) : Set V)).ConnectedComponent //
            componentFinset G ((W \ F) ∪ B) C ∩ B = ∅ } := by
    unfold terminalComponentCount IsFreeComponent
    rw [hrem, hBeq]
  have h2 :=
    ncard_free_union_isolates (G := G) (A := W \ F) (J := B) (T := B)
      hnc (subset_refl B)
  have h3 :
      Nat.card
          { C : (G.induce ((W \ F : Finset V) : Set V)).ConnectedComponent //
            componentFinset G (W \ F) C ∩ B = ∅ } =
        componentCount G (W \ F) := by
    unfold componentCount
    refine Nat.card_congr ?_
    refine Equiv.subtypeUnivEquiv ?_
    intro C
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    have hsub : componentFinset G (W \ F) C ⊆ W \ F :=
      componentFinset_subset (G := G) C
    exact Finset.disjoint_left.1
      (disjoint_of_subset_left sdiff_subset hdisj.symm)
      (hsub (mem_inter.1 hx).1) (mem_inter.1 hx).2
  exact h1.trans (h2.trans h3)

lemma pathCoverNumber_W_le_of_noBV {K B W : Finset V} {t : ℕ}
    (hKW : K = B ∪ W) (hdisj : Disjoint B W)
    (hanti : ∀ b ∈ B, ∀ w ∈ W, ¬ G.Adj b w)
    (hcog : IsCograph G K) (ht : 1 ≤ t)
    (hTH : TerminalHypothesisSlackStrong (G := G) K B t) :
    pathCoverNumber G W ≤ t - 1 := by
  have hWsub : W ⊆ K := by
    intro w hw
    simpa [hKW] using mem_union.2 (Or.inr hw)
  have hWcog : IsCograph G W := isCograph_subset hcog hWsub
  set FW := ineligibleSet G W
  have hFsub : FW ⊆ W := ineligibleSet_subset (G := G) W
  have hFsubK : FW ⊆ K := hFsub.trans hWsub
  have hcut :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) hWcog
  have hident :=
    terminalComponentCount_noBV (G := G) hKW hdisj hanti hFsub
  have hcanon : componentCount G (W \ FW) = FW.card + pathCoverNumber G W := by
    simpa [FW] using hcut
  by_cases hFne : FW.Nonempty
  · have hz := hTH.2 FW hFsubK hFne
    have hle : FW.card + pathCoverNumber G W ≤ FW.card + t - 1 := by
      rw [← hcanon, ← hident]
      exact hz
    omega
  · have hF0 : FW = ∅ := not_nonempty_iff_eq_empty.1 hFne
    have hz := hTH.1
    have hz' : terminalComponentCount (G := G) K B ∅ = componentCount G W := by
      simpa [hF0] using hident
    have hcW : componentCount G W = pathCoverNumber G W := by
      simpa [hF0] using hcanon
    have hpred : Nat.pred t = t - 1 := rfl
    calc pathCoverNumber G W
        = componentCount G W := hcW.symm
      _ = terminalComponentCount (G := G) K B ∅ := hz'.symm
      _ ≤ Nat.pred t := hz
      _ = t - 1 := hpred

lemma exists_min_cover_of_noBV {K B W : Finset V}
    (hKW : K = B ∪ W) (hdisj : Disjoint B W)
    (hanti : ∀ b ∈ B, ∀ w ∈ W, ¬ G.Adj b w)
    (hInd : Independent (G := G) B) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧
        pc.endpointDeficit B = 2 * pathCoverNumber G W := by
  have hnc : ∀ a ∈ B, ∀ w ∈ W, ¬ G.Adj a w := hanti
  have hpB : pathCoverNumber G B = B.card :=
    pathCoverNumber_eq_card_of_independent (G := G) hInd
  have hpU := Cograph.pathCoverNumber_disjoint_union (G := G) hdisj hnc
  obtain ⟨pcW, hWcard⟩ := exists_min_pathCover (G := G) W
  let pcB := PathCover.singletons (G := G) B
  have hBcard : pcB.card = B.card := PathCover.singletons_card (G := G) B
  have hBterm : pcB.endpointDeficit B = 0 :=
    PathCover.deficit_eq_zero_of_terminal pcB
      (PathCover.singletons_terminal (U := B) (subset_refl B))
  have hWout : ∀ p ∈ pcW.paths, p.start ∉ B ∧ p.finish ∉ B := by
    intro p hp
    have hs : p.start ∈ W := pcW.support_subset hp p.start_mem_support
    have hf : p.finish ∈ W := pcW.support_subset hp p.finish_mem_support
    exact ⟨fun hB => Finset.disjoint_left.1 hdisj hB hs,
      fun hB => Finset.disjoint_left.1 hdisj hB hf⟩
  have hWdef : pcW.endpointDeficit B = 2 * pcW.card :=
    PathCover.endpointDeficit_eq_two_mul_of_ends_outside pcW hWout
  let pc := Cograph.PathCover.unionDisjoint hdisj pcB pcW
  refine ⟨pc.cast (hKW.symm), ?_, ?_⟩
  · have hsum := Cograph.PathCover.unionDisjoint_card hdisj pcB pcW
    have hpK : pathCoverNumber G K = B.card + pathCoverNumber G W := by
      rw [hKW, hpU, hpB]
    rw [PathCover.cast_card, hsum, hBcard, hWcard, hpK]
  · have hdef := PathCover.endpointDeficit_unionDisjoint (B := B) hdisj pcB pcW
    rw [PathCover.cast_endpointDeficit_slack, hdef, hBterm, hWdef, hWcard, Nat.zero_add]

/-! ### Q-dominant cover: all ends in Q, deficit `2 p(K)` -/

lemma exists_min_cover_Q_dominant {P Q B : Finset V} {t : ℕ}
    (hPne : P.Nonempty) (hQne : Q.Nonempty)
    (hAB : G.IsCompleteBetween (P : Set V) (Q : Set V))
    (hB : B ⊆ P)
    (hdom : P.card < pathCoverNumber G Q)
    (hpQle : pathCoverNumber G Q ≤ P.card + t - 1) :
    ∃ pc : PathCover G (P ∪ Q),
      pc.card = pathCoverNumber G (P ∪ Q) ∧
        pc.endpointDeficit B ≤ 2 * t - 2 := by
  have hBA : G.IsCompleteBetween (Q : Set V) (P : Set V) :=
    fun {q} hq {p} hp => (hAB hp hq).symm
  have hdom' : P.card < pathCoverNumber G Q := hdom
  obtain ⟨pc, hcard, hend⟩ :=
    exists_pathCover_complete_join_dominant (A := Q) (B := P) hBA hdom'
  have hdisj := disjoint_of_completeBetween hAB
  have hout : ∀ p ∈ pc.paths, p.start ∉ B ∧ p.finish ∉ B := by
    intro p hp
    have hsQ : p.start ∈ Q := (hend p hp).1
    have hfQ : p.finish ∈ Q := (hend p hp).2
    exact ⟨fun hsB => Finset.disjoint_left.1 hdisj (hB hsB) hsQ,
      fun hfB => Finset.disjoint_left.1 hdisj (hB hfB) hfQ⟩
  have hdef : pc.endpointDeficit B = 2 * pc.card :=
    PathCover.endpointDeficit_eq_two_mul_of_ends_outside pc hout
  have hpjoin := pathCoverNumber_complete_join hPne hQne hAB
  have hPnot : pathCoverNumber G P ≤ Q.card := by
    by_contra h
    exact not_both_dominant (Nat.lt_of_not_ge h) hdom
  have hunion : Q ∪ P = P ∪ Q := union_comm _ _
  have hpcard : pc.card = pathCoverNumber G (P ∪ Q) := by
    have hpQsub : 1 ≤ pathCoverNumber G Q - P.card :=
      Nat.succ_le_of_lt (Nat.sub_pos_of_lt hdom)
    have : pathCoverNumber G (P ∪ Q) = pathCoverNumber G Q - P.card := by
      have hpjoin' := hpjoin
      rw [hpjoin', Nat.sub_eq_zero_of_le hPnot]
      simp [Nat.max_eq_right hpQsub]
    have hcard' : pc.card = pathCoverNumber G Q - P.card := hcard
    omega
  refine ⟨pc.cast hunion, ?_, ?_⟩
  · simpa [PathCover.cast_card] using hpcard
  · rw [PathCover.cast_endpointDeficit_slack]
    have : pc.card ≤ t - 1 := by omega
    omega

/-! ### Cardinality-induction: connected slack deficit bound -/

lemma PathCover.ends_subset_of_support {K : Finset V} (pc : PathCover G K)
    {p : GraphPath G} (hp : p ∈ pc.paths) :
    p.start ∈ K ∧ p.finish ∈ K :=
  ⟨pc.support_subset hp p.start_mem_support,
    pc.support_subset hp p.finish_mem_support⟩

lemma exists_min_cover_deficit_le_of_slackStrong_card :
    ∀ (n : ℕ) (K B : Finset V) (t : ℕ),
      K.card = n →
      IsCograph G K →
      (G.induce (K : Set V)).Connected →
      B ⊆ K → B.Nonempty → Independent (G := G) B →
      NeighborCondition (G := G) K B →
      1 ≤ t →
      TerminalHypothesisSlackStrong (G := G) K B t →
      ∃ pc : PathCover G K,
        pc.card = pathCoverNumber G K ∧
          pc.endpointDeficit B ≤ 2 * t - 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro K B t hKn hcog hconn hBK hBne hInd hN ht hTH
    by_cases hp1 : pathCoverNumber G K ≤ 1
    · have hpos := one_le_pathCoverNumber_of_nonempty (G := G) (hBne.mono hBK)
      have hp : pathCoverNumber G K = 1 := by omega
      exact exists_min_cover_deficit_le_of_p_eq_one hcog hBK hBne hp ht hTH
    · have hp2 : 2 ≤ pathCoverNumber G K := by omega
      have h2card : 2 ≤ K.card :=
        hp2.trans (pathCoverNumber_le_card (G := G) K)
      obtain ⟨Praw, Qraw, hPrawsub, hQrawsub, hPrawne, hQrawne, hdisjraw, hcoverraw,
          hABraw, hPrawcard, hQrawcard⟩ :=
        Cograph.exists_complete_join_on (G := G) (Cograph.isCograph_iff.2 hcog)
          hconn h2card
      have hBside : B ⊆ Praw ∨ B ⊆ Qraw :=
        Independent.subset_join_side hABraw hInd (by simpa [hcoverraw] using hBK)
      obtain ⟨P0, Q0, hPsub, hQsub, hPne, hQne, hdisj, hcover, hAB, hPcard, hQcard, hBP⟩ :
          ∃ P Q : Finset V, P ⊆ K ∧ Q ⊆ K ∧ P.Nonempty ∧ Q.Nonempty ∧
            Disjoint P Q ∧ P ∪ Q = K ∧
              G.IsCompleteBetween (P : Set V) (Q : Set V) ∧
                P.card < K.card ∧ Q.card < K.card ∧ B ⊆ P := by
        rcases hBside with hP | hQ
        · exact ⟨Praw, Qraw, hPrawsub, hQrawsub, hPrawne, hQrawne, hdisjraw, hcoverraw,
            hABraw, hPrawcard, hQrawcard, hP⟩
        · exact ⟨Qraw, Praw, hQrawsub, hPrawsub, hQrawne, hPrawne, hdisjraw.symm,
            by rw [union_comm, hcoverraw],
            fun {q} hq {p} hp => (hABraw hp hq).symm,
            hQrawcard, hPrawcard, hQ⟩
      have hjoin : P0 ∪ Q0 = K := hcover
      have hPcog : IsCograph G P0 := isCograph_subset hcog hPsub
      have hQcog : IsCograph G Q0 := isCograph_subset hcog hQsub
      have hN_P : NeighborCondition (G := G) P0 B := NeighborCondition.mono hN hPsub
      have hTH_P : TerminalHypothesisSlackStrong (G := G) P0 B (t + Q0.card) :=
        terminalHypothesisSlackStrong_join_child hQne hdisj hBP
          (by simpa [hjoin] using hTH)
      have htP : 1 ≤ t + Q0.card := by omega
      have hpQle : pathCoverNumber G Q0 ≤ P0.card + t - 1 :=
        pathCoverNumber_B_free_join_side_le_slack hPne hQne hAB
          (by simpa [hjoin] using hcog) hBP
          (by simpa [hjoin] using hTH)
      by_cases hQdom : P0.card < pathCoverNumber G Q0
      · obtain ⟨pc, hcard, hdef⟩ :=
          exists_min_cover_Q_dominant (B := B) (t := t) hPne hQne hAB hBP hQdom hpQle
        refine ⟨pc.cast hjoin, ?_, ?_⟩
        · simpa [PathCover.cast_card, hjoin] using hcard
        · have : (pc.cast hjoin).endpointDeficit B = pc.endpointDeficit B := by
            subst hjoin
            rfl
          omega
      · have hPdom : Q0.card < pathCoverNumber G P0 := by
          have hpjoin := pathCoverNumber_complete_join hPne hQne hAB
          have hnot1 : pathCoverNumber G (P0 ∪ Q0) ≠ 1 := by
            simpa [hjoin] using (Nat.ne_of_gt (Nat.succ_le_iff.mp hp2))
          have hQle : pathCoverNumber G Q0 ≤ P0.card := Nat.le_of_not_gt hQdom
          have hQ0sub : pathCoverNumber G Q0 - P0.card = 0 :=
            Nat.sub_eq_zero_of_le hQle
          by_contra hPle
          have hP0sub : pathCoverNumber G P0 - Q0.card = 0 :=
            Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hPle)
          have : pathCoverNumber G (P0 ∪ Q0) = 1 := by
            rw [hpjoin, hP0sub, hQ0sub]
            simp
          exact hnot1 this
        -- Build a minimum cover of P0 with deficit ≤ 2(t+|Q0|)-1.
        have hPcover :
            ∃ pc : PathCover G P0,
              pc.card = pathCoverNumber G P0 ∧
                pc.endpointDeficit B ≤ 2 * (t + Q0.card) - 1 := by
          by_cases hBV : ∃ b v, b ∈ B ∧ v ∈ P0 \ B ∧ G.Adj b v
          · obtain ⟨b, v, hb, hv, hadj⟩ := hBV
            obtain ⟨s⟩ :=
              exists_mixedSplit_of_BV (K := P0) (B := B) hBP hN_P hb hv hadj
            have hIeq : s.I = P0 \ s.D := s.I_eq
            have hI : P0 \ s.D ⊆ B := by simpa [hIeq] using s.hI
            have hDsubK : s.D ⊆ K := s.hDsub.trans hPsub
            have hDlt : s.D.card < n := by
              have : s.D.card ≤ P0.card := card_le_card s.hDsub
              omega
            have hDcog : IsCograph G s.D := isCograph_subset hPcog s.hDsub
            have hBd : B ∩ s.D ⊆ s.D := inter_subset_right
            have hBdne : (B ∩ s.D).Nonempty := s.hBd
            have hN_D : NeighborCondition (G := G) s.D (B ∩ s.D) :=
              NeighborCondition.restrict_inter hN_P s.hDsub
            have hTH_D : TerminalHypothesisSlackStrong (G := G) s.D (B ∩ s.D)
                (t + Q0.card) :=
              TerminalHypothesisSlackStrong.restrict_mixed hBP s.hDsub hI
                (by simpa [hIeq] using s.hnocross) hTH_P
            have hIndD : Independent (G := G) (B ∩ s.D) :=
              hInd.mono inter_subset_left
            obtain ⟨pcD, hDcard', hDdef⟩ :=
              ih s.D.card hDlt s.D (B ∩ s.D) (t + Q0.card) rfl hDcog s.hconn
                hBd hBdne hIndD hN_D htP hTH_D
            have hDdefB : pcD.endpointDeficit B ≤ pcD.endpointDeficit (B ∩ s.D) :=
              PathCover.endpointDeficit_anti inter_subset_left pcD
            have hdisjDI : Disjoint s.D s.I := s.hdisj
            obtain ⟨pcI, hIcard, hIterm⟩ :=
              exists_min_terminalCover_subset_B (K := s.I) (B := B)
                s.hI hInd
            have hIdef : pcI.endpointDeficit B = 0 :=
              PathCover.deficit_eq_zero_of_terminal pcI hIterm
            let pcP := Cograph.PathCover.unionDisjoint hdisjDI pcD pcI
            have hunionDI : s.D ∪ s.I = P0 := s.hDU
            refine ⟨pcP.cast hunionDI, ?_, ?_⟩
            · have hsum := Cograph.PathCover.unionDisjoint_card hdisjDI pcD pcI
              have hpU :=
                Cograph.pathCoverNumber_disjoint_union (G := G) hdisjDI s.hnocross
              have hpP : pathCoverNumber G P0 = pathCoverNumber G s.D + pathCoverNumber G s.I := by
                convert hpU
                exact s.hDU.symm
              rw [PathCover.cast_card, hsum, hDcard', hIcard, hpP]
            · have hdefU :=
                PathCover.endpointDeficit_unionDisjoint (B := B) hdisjDI pcD pcI
              rw [PathCover.cast_endpointDeficit_slack, hdefU, hIdef]
              exact hDdefB.trans hDdef
          · -- no BV edge in P0
            let W := P0 \ B
            have hPW : P0 = B ∪ W := (union_sdiff_of_subset hBP).symm
            have hdisjBW : Disjoint B W := disjoint_sdiff
            have hanti : ∀ b ∈ B, ∀ w ∈ W, ¬ G.Adj b w := by
              intro b hb w hw hadj
              exact hBV ⟨b, w, hb, hw, hadj⟩
            obtain ⟨pcP, hPcard', hPdef⟩ :=
              exists_min_cover_of_noBV (K := P0) (B := B) (W := W)
                hPW hdisjBW hanti hInd
            have hpW : pathCoverNumber G W ≤ t + Q0.card - 1 :=
              pathCoverNumber_W_le_of_noBV hPW hdisjBW hanti hPcog htP hTH_P
            refine ⟨pcP, hPcard', ?_⟩
            have : 2 * pathCoverNumber G W ≤ 2 * (t + Q0.card) - 2 := by
              have : pathCoverNumber G W ≤ t + Q0.card - 1 := by
                simpa [Nat.pred_eq_sub_one] using hpW
              omega
            omega
        obtain ⟨pcP, hPmin, hPdef⟩ := hPcover
        have hendP : ∀ p ∈ pcP.paths, p.start ∈ P0 ∧ p.finish ∈ P0 :=
          fun p hp => pcP.ends_subset_of_support hp
        obtain ⟨pcK, hKcard, _, hKdef⟩ :=
          exists_merge_all_connectors (A := P0) (Q := Q0) (B := B) (t := t)
            hAB hPdom pcP hPmin hendP hPdef
        refine ⟨pcK.cast hjoin, ?_, ?_⟩
        · have hpjoin := pathCoverNumber_complete_join hPne hQne hAB
          have hQle : pathCoverNumber G Q0 ≤ P0.card := Nat.le_of_not_gt hQdom
          have hpKeq : pathCoverNumber G K = pathCoverNumber G P0 - Q0.card := by
            have hpPsub : 1 ≤ pathCoverNumber G P0 - Q0.card :=
              Nat.succ_le_of_lt (Nat.sub_pos_of_lt hPdom)
            have hpjoin' : pathCoverNumber G (P0 ∪ Q0) =
                max 1 (max (pathCoverNumber G P0 - Q0.card)
                  (pathCoverNumber G Q0 - P0.card)) := hpjoin
            rw [← hjoin, hpjoin', Nat.sub_eq_zero_of_le hQle,
              Nat.max_eq_left (Nat.zero_le _), Nat.max_eq_right hpPsub]
          rw [PathCover.cast_card, hKcard, hpKeq]
        · rw [PathCover.cast_endpointDeficit_slack]
          exact hKdef

/-- Connected cograph, independent nonempty terminals, neighbor condition
and strong slack `t ≥ 1` yield an ordinary minimum cover of deficit
`≤ 2t - 1`. -/
theorem exists_min_cover_deficit_le_of_slackStrong {K B : Finset V} {t : ℕ}
    (hcog : IsCograph G K)
    (hconn : (G.induce (K : Set V)).Connected)
    (hBK : B ⊆ K) (hBne : B.Nonempty)
    (hInd : Independent (G := G) B)
    (hN : NeighborCondition (G := G) K B)
    (ht : 1 ≤ t)
    (hTH : TerminalHypothesisSlackStrong (G := G) K B t) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧
        pc.endpointDeficit B ≤ 2 * t - 1 :=
  exists_min_cover_deficit_le_of_slackStrong_card K.card K B t rfl
    hcog hconn hBK hBne hInd hN ht hTH

end Nikoghosyan
