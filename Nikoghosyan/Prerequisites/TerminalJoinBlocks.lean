/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalMixedReduction

/-!
# Outside original-edge path-block splicing for B-terminal covers

`exists_splice_two_through` inserts a single connector vertex between two
`A`-ended cover paths. The no-BV join spectrum needs the same operation for
an entire outside original-edge `GraphPath` block: splice the block between
two current `B`-ended paths, drop precisely those two paths, and keep every
remaining disjoint support.

Original `B`-vertices may become internal after splicing. The helper does
not require every `B`-vertex to remain an endpoint.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma IsCompleteBetween.mono {A A' B B' : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    G.IsCompleteBetween (A' : Set V) (B' : Set V) :=
  fun {a} ha {b} hb => hAB (hA ha) (hB hb)

lemma IsCompleteBetween.symm {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    G.IsCompleteBetween (B : Set V) (A : Set V) :=
  fun {b} hb {a} ha => (hAB ha hb).symm

lemma exists_two_mem_of_two_le_card {s : Finset V} (h : 2 ≤ s.card) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  have hpos : 0 < s.card := by omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  have herase : 0 < (s.erase a).card := by
    rw [card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := card_pos.mp herase
  have hb' := mem_erase.mp hb
  exact ⟨a, b, ha, hb'.2, hb'.1.symm⟩

/-- Concatenate `p`, an outside original-edge block, and `q` along two
original complete-join seams. Outer ends of `p` and `q` stay in `A`. -/
lemma exists_splice_through_block {A Y : Finset V}
    (hAY : G.IsCompleteBetween (A : Set V) (Y : Set V))
    (p block q : GraphPath G)
    (hpA : p.finish ∈ A) (hqA : q.start ∈ A)
    (hblock : block.support ⊆ Y)
    (hpb : Disjoint p.support block.support)
    (hqb : Disjoint q.support block.support)
    (hpq : Disjoint p.support q.support) :
    ∃ r : GraphPath G,
      r.support = p.support ∪ block.support ∪ q.support ∧
        r.start = p.start ∧ r.finish = q.finish := by
  have hadj1 : G.Adj p.finish block.start :=
    hAY hpA (hblock block.start_mem_support)
  let mid := p.splice block hadj1 hpb
  have hqs : Disjoint mid.support q.support := by
    unfold mid
    rw [GraphPath.support_splice, disjoint_union_left]
    exact ⟨hpq, hqb.symm⟩
  have hadj2 : G.Adj mid.finish q.start := by
    have hf : mid.finish = block.finish :=
      GraphPath.finish_splice p block hadj1 hpb
    rw [hf]
    exact (hAY hqA (hblock block.finish_mem_support)).symm
  refine ⟨mid.splice q hadj2 hqs, ?_, rfl, rfl⟩
  ext x
  simp [mid, GraphPath.support_splice, mem_union, or_assoc, or_left_comm]

/-- Replace two distinct cover paths by a single path whose support is those
two supports together with an outside block support `W`. -/
noncomputable def PathCover.spliceTwoInsertBlock {U W : Finset V}
    (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hWU : Disjoint W U) (r : GraphPath G)
    (hr : r.support = p.support ∪ W ∪ q.support) :
    PathCover G (U ∪ W) where
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
        PathCover.pairwise_disjoint_of_mem pc.disjoint hspc hp hsp
      have hdisjq : Disjoint s.support q.support :=
        PathCover.pairwise_disjoint_of_mem pc.disjoint hspc hq hsq
      have hsW : Disjoint s.support W :=
        disjoint_of_subset_left (pc.support_subset hspc) hWU.symm
      refine Finset.disjoint_left.2 ?_
      intro x hxs hxr
      have hxrs : x ∈ p.support ∪ W ∪ q.support := by rwa [hr] at hxr
      have hx1 : x ∈ p.support ∨ x ∈ W ∨ x ∈ q.support := by
        simpa [mem_union, or_assoc, or_left_comm] using hxrs
      rcases hx1 with hxp | hxW | hxq
      · exact Finset.disjoint_left.1 hdisjp hxs hxp
      · exact Finset.disjoint_left.1 hsW hxs hxW
      · exact Finset.disjoint_left.1 hdisjq hxs hxq
  mem_iff := by
    intro x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxU | hxW
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
      · refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
        rw [hr]
        exact mem_union.2 (Or.inl (mem_union.2 (Or.inr hxW)))
    · intro ⟨s, hs, hxs⟩
      rcases List.mem_append.1 hs with hsL | hsR
      · have hs1 := List.mem_filter.1 hsL
        have hs0 := List.mem_filter.1 hs1.1
        exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨s, hs0.1, hxs⟩))
      · have : s = r := List.mem_singleton.1 hsR
        subst this
        have hx' : x ∈ p.support ∪ W ∪ q.support := by rwa [hr] at hxs
        have hx1 : x ∈ p.support ∨ x ∈ W ∨ x ∈ q.support := by
          simpa [mem_union, or_assoc, or_left_comm] using hx'
        rcases hx1 with hxp | hxW | hxq
        · exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨p, hp, hxp⟩))
        · exact mem_union.2 (Or.inr hxW)
        · exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨q, hq, hxq⟩))

lemma PathCover.spliceTwoInsertBlock_card {U W : Finset V}
    (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hWU : Disjoint W U) (r : GraphPath G)
    (hr : r.support = p.support ∪ W ∪ q.support) :
    (pc.spliceTwoInsertBlock hp hq hne hWU r hr).card = pc.card - 1 := by
  have hlen := length_filter_ne_two (a := p) (b := q) hp hq hne pc.nodup_paths
  have hfilt :=
    length_filter_ne_of_mem_nodup (a := p) (l := pc.paths) hp pc.nodup_paths
  have hb' : q ∈ pc.paths.filter fun x => decide (x ≠ p) :=
    List.mem_filter.2 ⟨hq, decide_eq_true hne.symm⟩
  have hpos : 2 ≤ pc.paths.length := by
    have : 1 ≤ (pc.paths.filter fun x => decide (x ≠ p)).length :=
      Nat.succ_le_of_lt (List.length_pos_of_mem hb')
    omega
  change
      ((pc.paths.filter fun s => decide (s ≠ p)).filter (fun s => decide (s ≠ q))
          ++ [r]).length =
        pc.paths.length - 1
  rw [List.length_append, List.length_singleton, hlen]
  omega

lemma PathCover.spliceTwoInsertBlock_mem_paths {U W : Finset V}
    (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hWU : Disjoint W U) (r : GraphPath G)
    (hr : r.support = p.support ∪ W ∪ q.support)
    {s : GraphPath G}
    (hs : s ∈ (pc.spliceTwoInsertBlock hp hq hne hWU r hr).paths) :
    s = r ∨ s ∈ pc.paths ∧ s ≠ p ∧ s ≠ q := by
  have hs' := List.mem_append.1 hs
  rcases hs' with hsL | hsR
  · have hs1 := List.mem_filter.1 hsL
    have hs0 := List.mem_filter.1 hs1.1
    exact Or.inr ⟨hs0.1, of_decide_eq_true hs0.2, of_decide_eq_true hs1.2⟩
  · exact Or.inl (List.mem_singleton.1 hsR)

/-- Insert an outside original-edge path block between two `A`-ended cover
paths. The resulting cover stays `A`-ended, and the cardinality drops by one. -/
lemma exists_splice_two_through_block {A Y U : Finset V}
    (hAY : G.IsCompleteBetween (A : Set V) (Y : Set V))
    (pc : PathCover G U) (h2 : 2 ≤ pc.card)
    (hend : ∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A)
    (block : GraphPath G) (hblock : block.support ⊆ Y)
    (hdisj : Disjoint block.support U) :
    ∃ pc' : PathCover G (U ∪ block.support),
      pc'.card = pc.card - 1 ∧
        (∀ p ∈ pc'.paths, p.start ∈ A ∧ p.finish ∈ A) := by
  obtain ⟨p, q, hp, hq, hne⟩ := pc.exists_two_distinct h2
  have hpb : Disjoint p.support block.support :=
    disjoint_of_subset_left (pc.support_subset hp) hdisj.symm
  have hqb : Disjoint q.support block.support :=
    disjoint_of_subset_left (pc.support_subset hq) hdisj.symm
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_splice_through_block hAY p block q (hend p hp).2 (hend q hq).1
      hblock hpb hqb
      (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne)
  refine ⟨pc.spliceTwoInsertBlock hp hq hne hdisj r hr,
    pc.spliceTwoInsertBlock_card hp hq hne hdisj r hr, ?_⟩
  intro s hsmem
  rcases pc.spliceTwoInsertBlock_mem_paths hp hq hne hdisj r hr hsmem with
    hseq | ⟨hspc, _, _⟩
  · subst hseq
    rw [hs, hf]
    exact ⟨(hend p hp).1, (hend q hq).2⟩
  · exact hend s hspc

lemma pathAt_support_subset_carrier {K : Finset V} (pc : PathCover G K)
    (i : Fin pc.card) : (pathAt pc i).support ⊆ K :=
  pathAt_support_subset pc i

/-- Alternating original complete-join chain `Y₀, W₀, Y₁, …, W_{a-1}, Y_a`. -/
lemma exists_YV_chain {Y W : Finset V}
    (hWY : G.IsCompleteBetween (W : Set V) (Y : Set V))
    (hdisjYW : Disjoint Y W)
    (pcY : PathCover G Y) (pcW : PathCover G W) (a : ℕ)
    (haY : a + 1 ≤ pcY.card) (haW : pcW.card = a) :
    ∃ r : GraphPath G,
      r.start = (pathAt pcY ⟨0, (Nat.succ_pos a).trans_le haY⟩).start ∧
        r.finish = (pathAt pcY ⟨a, Nat.succ_le_iff.mp haY⟩).finish ∧
          ∀ x, x ∈ r.support ↔
            (∃ i : Fin (a + 1),
                x ∈ (pathAt pcY ⟨i.1, Nat.lt_of_lt_of_le i.2 haY⟩).support) ∨
              ∃ j : Fin a,
                x ∈ (pathAt pcW ⟨j.1, haW ▸ j.2⟩).support := by
  have hY0 : 0 < pcY.card := (Nat.succ_pos a).trans_le haY
  have haYlt : a < pcY.card := Nat.succ_le_iff.mp haY
  have go :
      ∀ (t : ℕ) (ht : t ≤ a),
        ∃ r : GraphPath G,
          r.start = (pathAt pcY ⟨0, hY0⟩).start ∧
            r.finish = (pathAt pcY ⟨t, Nat.lt_of_le_of_lt ht haYlt⟩).finish ∧
              ∀ x, x ∈ r.support ↔
                (∃ i : Fin (t + 1),
                    x ∈ (pathAt pcY
                      ⟨i.1, Nat.lt_of_lt_of_le i.2
                        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ht haYlt))⟩).support) ∨
                  ∃ j : Fin t,
                    x ∈ (pathAt pcW
                      ⟨j.1, Nat.lt_of_lt_of_le j.2 (ht.trans (le_of_eq haW.symm))⟩).support := by
    intro t
    induction t with
    | zero =>
      intro _ht
      refine ⟨pathAt pcY ⟨0, hY0⟩, rfl, rfl, ?_⟩
      intro x
      constructor
      · intro hx
        refine Or.inl ⟨⟨0, Nat.zero_lt_one⟩, ?_⟩
        simpa using hx
      · intro hx
        rcases hx with ⟨i, hxi⟩ | ⟨j, _⟩
        · have hi0 : i.1 = 0 := Nat.lt_one_iff.mp i.2
          have : (⟨i.1, Nat.lt_of_lt_of_le i.2
                (Nat.succ_le_of_lt hY0)⟩ : Fin pcY.card) =
              ⟨0, hY0⟩ := Fin.ext hi0
          simpa [this] using hxi
        · exact Fin.elim0 j
    | succ t ih =>
      intro ht
      obtain ⟨r, hrs, hrf, hrmem⟩ := ih (Nat.le_of_succ_le ht)
      have htW : t < pcW.card := by omega
      have htY : t + 1 < pcY.card := by omega
      let wp := pathAt pcW ⟨t, htW⟩
      let yp := pathAt pcY ⟨t + 1, htY⟩
      have hrW : Disjoint r.support wp.support := by
        refine Finset.disjoint_left.2 ?_
        intro x hxr hxw
        have hx := (hrmem x).1 hxr
        rcases hx with ⟨i, hxi⟩ | ⟨j, hxj⟩
        · have hxY : x ∈ Y := pathAt_support_subset pcY _ hxi
          have hxW : x ∈ W := pathAt_support_subset pcW ⟨t, htW⟩ hxw
          exact Finset.disjoint_left.1 hdisjYW hxY hxW
        · have hne : (⟨j.1, by omega⟩ : Fin pcW.card) ≠ ⟨t, htW⟩ := by
            intro h
            have : j.1 = t := congrArg Fin.val h
            exact (Nat.ne_of_lt j.2) this
          exact Finset.disjoint_left.1 (pathAt_disjoint pcW hne) hxj hxw
      have hadj1 : G.Adj r.finish wp.start := by
        have hfY : r.finish ∈ Y := by
          have : r.finish = (pathAt pcY ⟨t, by omega⟩).finish := hrf
          rw [this]
          exact pathAt_support_subset pcY _ (pathAt pcY ⟨t, by omega⟩).finish_mem_support
        have hsW : wp.start ∈ W := pathAt_support_subset pcW ⟨t, htW⟩ wp.start_mem_support
        exact (hWY hsW hfY).symm
      let mid := r.splice wp hadj1 hrW
      have hmidY : Disjoint mid.support yp.support := by
        unfold mid
        rw [GraphPath.support_splice, disjoint_union_left]
        constructor
        · refine Finset.disjoint_left.2 ?_
          intro x hxr hxy
          have hx := (hrmem x).1 hxr
          rcases hx with ⟨i, hxi⟩ | ⟨j, hxj⟩
          · have hne : (⟨i.1, by omega⟩ : Fin pcY.card) ≠ ⟨t + 1, htY⟩ := by
              intro h
              have : i.1 = t + 1 := congrArg Fin.val h
              exact (Nat.ne_of_lt i.2) this
            exact Finset.disjoint_left.1 (pathAt_disjoint pcY hne) hxi hxy
          · have hxW : x ∈ W := pathAt_support_subset pcW _ hxj
            have hxY : x ∈ Y := pathAt_support_subset pcY ⟨t + 1, htY⟩ hxy
            exact Finset.disjoint_left.1 hdisjYW hxY hxW
        · have hxW : wp.support ⊆ W := pathAt_support_subset pcW ⟨t, htW⟩
          have hxY : yp.support ⊆ Y := pathAt_support_subset pcY ⟨t + 1, htY⟩
          exact disjoint_of_subset_left hxW (disjoint_of_subset_right hxY hdisjYW.symm)
      have hadj2 : G.Adj mid.finish yp.start := by
        have hf : mid.finish = wp.finish := GraphPath.finish_splice r wp hadj1 hrW
        rw [hf]
        have hsY : yp.start ∈ Y := pathAt_support_subset pcY ⟨t + 1, htY⟩ yp.start_mem_support
        have hfW : wp.finish ∈ W := pathAt_support_subset pcW ⟨t, htW⟩ wp.finish_mem_support
        exact hWY hfW hsY
      refine ⟨mid.splice yp hadj2 hmidY, ?_, ?_, ?_⟩
      · have hs0 : (mid.splice yp hadj2 hmidY).start = r.start := by
          rw [GraphPath.start_splice]
          unfold mid
          rw [GraphPath.start_splice]
        exact hs0.trans hrs
      · have hfin : (mid.splice yp hadj2 hmidY).finish = yp.finish :=
          GraphPath.finish_splice mid yp hadj2 hmidY
        have hidx : (⟨t + 1, htY⟩ : Fin pcY.card) =
            ⟨t.succ, Nat.lt_of_le_of_lt ht haYlt⟩ := Fin.ext rfl
        have hyp : yp.finish =
            (pathAt pcY ⟨t.succ, Nat.lt_of_le_of_lt ht haYlt⟩).finish := by
          simp [yp, hidx]
        exact hfin.trans hyp
      · intro x
        constructor
        · intro hx
          have hx' : x ∈ mid.support ∪ yp.support := by
            simpa [GraphPath.support_splice] using hx
          rcases mem_union.1 hx' with hxm | hxy
          · have hxm' : x ∈ r.support ∪ wp.support := by
              simpa [mid, GraphPath.support_splice] using hxm
            rcases mem_union.1 hxm' with hxr | hxw
            · have hx := (hrmem x).1 hxr
              rcases hx with ⟨i, hxi⟩ | ⟨j, hxj⟩
              · refine Or.inl ⟨⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self _)⟩, ?_⟩
                simpa using hxi
              · refine Or.inr ⟨⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩, ?_⟩
                simpa using hxj
            · refine Or.inr ⟨⟨t, Nat.lt_succ_self _⟩, ?_⟩
              simpa [wp] using hxw
          · refine Or.inl ⟨⟨t + 1, Nat.lt_succ_self _⟩, ?_⟩
            simpa [yp] using hxy
        · intro hx
          have hxmidyp : x ∈ mid.support ∪ yp.support →
              x ∈ (mid.splice yp hadj2 hmidY).support := by
            intro h
            simpa [GraphPath.support_splice] using h
          rcases hx with ⟨i, hxi⟩ | ⟨j, hxj⟩
          · have hi : i.1 < t + 2 := i.2
            have hsplit : i.1 < t + 1 ∨ i.1 = t + 1 :=
              Nat.lt_succ_iff_lt_or_eq.mp hi
            rcases hsplit with hlt | heq
            · have hxr : x ∈ r.support :=
                (hrmem x).2 (Or.inl ⟨⟨i.1, hlt⟩, by simpa using hxi⟩)
              exact hxmidyp (mem_union.2 (Or.inl (by
                simpa [mid, GraphPath.support_splice] using mem_union.2 (Or.inl hxr))))
            · have : (⟨i.1, Nat.lt_of_lt_of_le i.2 (by omega)⟩ : Fin pcY.card) =
                  ⟨t + 1, htY⟩ := Fin.ext heq
              have hxy : x ∈ yp.support := by simpa [this, yp] using hxi
              exact hxmidyp (mem_union.2 (Or.inr hxy))
          · have hj : j.1 < t + 1 := j.2
            have hsplit : j.1 < t ∨ j.1 = t :=
              Nat.lt_succ_iff_lt_or_eq.mp hj
            rcases hsplit with hlt | heq
            · have hxr : x ∈ r.support :=
                (hrmem x).2 (Or.inr ⟨⟨j.1, hlt⟩, by simpa using hxj⟩)
              exact hxmidyp (mem_union.2 (Or.inl (by
                simpa [mid, GraphPath.support_splice] using mem_union.2 (Or.inl hxr))))
            · have : (⟨j.1, by omega⟩ : Fin pcW.card) = ⟨t, htW⟩ := Fin.ext heq
              have hxw : x ∈ wp.support := by simpa [this, wp] using hxj
              exact hxmidyp (mem_union.2 (Or.inl (by
                simpa [mid, GraphPath.support_splice] using mem_union.2 (Or.inr hxw))))
  exact go a le_rfl


/-- Attach two distinct original `B`-ends to a `Y`-started/`Y`-ended chain. -/
lemma exists_anchor_B_ended {B Y W : Finset V}
    (hBY : G.IsCompleteBetween (B : Set V) (Y : Set V))
    {b1 b2 : V} (hb1 : b1 ∈ B) (hb2 : b2 ∈ B) (hne : b1 ≠ b2)
    (r : GraphPath G) (hs : r.start ∈ Y) (hf : r.finish ∈ Y)
    (hBW : Disjoint B W) (hBY' : Disjoint B Y)
    (hr : r.support ⊆ W ∪ Y) :
    ∃ p : GraphPath G,
      p.start = b1 ∧ p.finish = b2 ∧
        p.support = {b1} ∪ r.support ∪ {b2} := by
  have hb1r : b1 ∉ r.support := by
    intro h
    have : b1 ∈ W ∪ Y := hr h
    rcases mem_union.1 this with hW | hY
    · exact Finset.disjoint_left.1 hBW hb1 hW
    · exact Finset.disjoint_left.1 hBY' hb1 hY
  have hb2r : b2 ∉ r.support := by
    intro h
    have : b2 ∈ W ∪ Y := hr h
    rcases mem_union.1 this with hW | hY
    · exact Finset.disjoint_left.1 hBW hb2 hW
    · exact Finset.disjoint_left.1 hBY' hb2 hY
  let sb1 := GraphPath.singleton (G := G) b1
  let sb2 := GraphPath.singleton (G := G) b2
  have hsb1 : sb1.support = {b1} := GraphPath.support_singleton b1
  have hsb2 : sb2.support = {b2} := GraphPath.support_singleton b2
  have h1 : Disjoint sb1.support r.support := by
    rw [hsb1]
    exact disjoint_singleton_left.2 hb1r
  have hadj1 : G.Adj sb1.finish r.start := by
    change G.Adj b1 r.start
    exact hBY hb1 hs
  let mid := sb1.splice r hadj1 h1
  have h2 : Disjoint mid.support sb2.support := by
    unfold mid
    rw [GraphPath.support_splice, hsb1, hsb2, disjoint_union_left]
    exact ⟨by simp [hne], disjoint_singleton_right.2 hb2r⟩
  have hadj2 : G.Adj mid.finish sb2.start := by
    have : mid.finish = r.finish := GraphPath.finish_splice sb1 r hadj1 h1
    rw [this]
    change G.Adj r.finish b2
    exact (hBY hb2 hf).symm
  refine ⟨mid.splice sb2 hadj2 h2, rfl, rfl, ?_⟩
  ext x
  simp [mid, GraphPath.support_splice, hsb1, hsb2, mem_union]

end Nikoghosyan
