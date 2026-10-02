/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalSufficiency
import Nikoghosyan.Cograph.PathCoverUnion
import Nikoghosyan.Cograph.SaturatedJoin

/-!
# General B-terminal construction: slack, join placement, splicing

The weaker universal “every cograph has a minimum B-ended cover” is false
(central star-of-pairs). This module records the actual join-child cuts,
forbids a dominant B-free join side via the F-cut, packages the traceable
base as a PathCover, unions no-cross terminal covers, and splices an already
B-ended child cover through original complete-join connectors.

Traceable `p(K) = 1` and `leftoverCover` are imported, not re-proved.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Slack form of the terminal cut hypothesis. Original `TerminalHypothesis`
is the case `t = 0`. -/
def TerminalHypothesisSlack (K B : Finset V) (t : ℕ) : Prop :=
  terminalComponentCount (G := G) K B ∅ ≤ t ∧
    ∀ S ⊆ K, S.Nonempty →
      terminalComponentCount (G := G) K B S ≤ S.card + t - 1

lemma terminalHypothesis_iff_slack_zero {K B : Finset V} :
    TerminalHypothesis (G := G) K B ↔
      TerminalHypothesisSlack (G := G) K B 0 := by
  constructor
  · intro h
    refine ⟨by simpa using h.1, ?_⟩
    intro S hS hne
    simpa using h.2 S hS hne
  · intro h
    refine ⟨Nat.eq_zero_of_le_zero h.1, ?_⟩
    intro S hS hne
    simpa using h.2 S hS hne

lemma NeighborCondition.mono {K K' B : Finset V}
    (hN : NeighborCondition (G := G) K B) (hKK : K' ⊆ K) :
    NeighborCondition (G := G) K' B := by
  intro b v w hb hv hw hbv hbw
  have hvK : v ∈ K \ B :=
    mem_sdiff.2 ⟨hKK (mem_sdiff.1 hv).1, (mem_sdiff.1 hv).2⟩
  have hwK : w ∈ K \ B :=
    mem_sdiff.2 ⟨hKK (mem_sdiff.1 hw).1, (mem_sdiff.1 hw).2⟩
  exact hN hb hvK hwK hbv hbw

lemma isCompleteBetween_subset_left {A A' B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) (hsub : A' ⊆ A) :
    G.IsCompleteBetween (A' : Set V) (B : Set V) :=
  fun {a} ha {b} hb => hAB (hsub ha) hb

lemma sdiff_union_union_eq_sdiff_left {X Y S : Finset V}
    (hdisj : Disjoint X Y) (_hS : S ⊆ X) :
    (X ∪ Y) \ (S ∪ Y) = X \ S := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hx
    rcases hx with ⟨hxXY, hxnot⟩
    have hxY : x ∉ Y := fun hY => hxnot (Or.inr hY)
    have hxS : x ∉ S := fun hS' => hxnot (Or.inl hS')
    rcases hxXY with hxX | hxY'
    · exact ⟨hxX, hxS⟩
    · exact (hxY hxY').elim
  · intro hx
    have hxY : x ∉ Y := fun hY => Finset.disjoint_left.1 hdisj hx.1 hY
    exact ⟨Or.inl hx.1, fun h => h.elim hx.2 hxY⟩

lemma sdiff_union_right_of_disjoint {X Y B S : Finset V}
    (hB : B ⊆ X) (hdisj : Disjoint X Y) :
    B \ (S ∪ Y) = B \ S := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hx
    exact ⟨hx.1, fun hS => hx.2 (Or.inl hS)⟩
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro h
    rcases h with hS | hY
    · exact hx.2 hS
    · exact Finset.disjoint_left.1 hdisj (hB hx.1) hY

lemma terminalComponentCount_join_delete_right {X Y B S : Finset V}
    (hdisj : Disjoint X Y) (hB : B ⊆ X) (hS : S ⊆ X) :
    terminalComponentCount (G := G) (X ∪ Y) B (S ∪ Y) =
      terminalComponentCount (G := G) X B S := by
  have hK : (X ∪ Y) \ (S ∪ Y) = X \ S :=
    sdiff_union_union_eq_sdiff_left hdisj hS
  have hB' : B \ (S ∪ Y) = B \ S :=
    sdiff_union_right_of_disjoint hB hdisj
  unfold terminalComponentCount IsFreeComponent
  rw [hK, hB']

/-- Actual weaker child cuts after deleting a join side `Y`:
`z_B(X-S) ≤ |Y| + |S| - 1`. -/
lemma terminalComponentCount_join_child_le {X Y B S : Finset V}
    (hYne : Y.Nonempty) (hdisj : Disjoint X Y) (hB : B ⊆ X) (hS : S ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B) :
    terminalComponentCount (G := G) X B S ≤ S.card + Y.card - 1 := by
  have hcut : S ∪ Y ⊆ X ∪ Y :=
    union_subset (hS.trans subset_union_left) subset_union_right
  have hne : (S ∪ Y).Nonempty := hYne.mono subset_union_right
  have hz := hTH.2 (S ∪ Y) hcut hne
  have hEq :=
    terminalComponentCount_join_delete_right (G := G) (B := B) hdisj hB hS
  have hcard : (S ∪ Y).card = S.card + Y.card :=
    card_union_of_disjoint (disjoint_of_subset_left hS hdisj)
  omega

lemma terminalComponentCount_join_child_empty_le {X Y B : Finset V}
    (hYne : Y.Nonempty) (hdisj : Disjoint X Y) (hB : B ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B) :
    terminalComponentCount (G := G) X B ∅ ≤ Y.card - 1 := by
  simpa using
    terminalComponentCount_join_child_le (S := (∅ : Finset V))
      hYne hdisj hB (empty_subset X) hTH

lemma terminalHypothesisSlack_join_child {X Y B : Finset V}
    (hYne : Y.Nonempty) (hdisj : Disjoint X Y) (hB : B ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B) :
    TerminalHypothesisSlack (G := G) X B Y.card :=
  ⟨(terminalComponentCount_join_child_empty_le hYne hdisj hB hTH).trans
      (Nat.sub_le _ _),
    fun S hS _hne =>
      terminalComponentCount_join_child_le hYne hdisj hB hS hTH⟩

lemma Independent.not_meets_both_completeJoin {X Y B : Finset V}
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hInd : Independent (G := G) B)
    {x y : V} (hx : x ∈ B ∩ X) (hy : y ∈ B ∩ Y) : False :=
  hInd (mem_inter.1 hx).1 (mem_inter.1 hy).1
    (hAB (mem_inter.1 hx).2 (mem_inter.1 hy).2)

lemma Independent.subset_join_side {X Y B : Finset V}
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hInd : Independent (G := G) B) (hBK : B ⊆ X ∪ Y) :
    B ⊆ X ∨ B ⊆ Y := by
  by_cases hX : B ∩ Y = ∅
  · refine Or.inl ?_
    intro b hb
    have hbK : b ∈ X ∪ Y := hBK hb
    rcases mem_union.1 hbK with hbX | hbY
    · exact hbX
    · have : b ∈ B ∩ Y := mem_inter.2 ⟨hb, hbY⟩
      exact (notMem_empty b (hX ▸ this)).elim
  · have hYne : (B ∩ Y).Nonempty := nonempty_iff_ne_empty.2 hX
    refine Or.inr ?_
    intro b hb
    have hbK : b ∈ X ∪ Y := hBK hb
    rcases mem_union.1 hbK with hbX | hbY
    · obtain ⟨y, hy⟩ := hYne
      exact (Independent.not_meets_both_completeJoin hAB hInd
        (mem_inter.2 ⟨hb, hbX⟩) hy).elim
    · exact hbY

/-- If every terminal is ineligible, the canonical F-cut plus
`TerminalHypothesis` forces a negative path-cover number. -/
lemma not_B_subset_ineligibleSet {K B : Finset V}
    (hK : IsCograph G K) (hBK : B ⊆ K) (hBne : B.Nonempty)
    (hTH : TerminalHypothesis (G := G) K B) :
    ¬ B ⊆ ineligibleSet G K := by
  intro hBF
  have hFsub : ineligibleSet G K ⊆ K := ineligibleSet_subset (G := G) K
  have hFne : (ineligibleSet G K).Nonempty := hBne.mono hBF
  have hz := hTH.2 (ineligibleSet G K) hFsub hFne
  have hz' :
      terminalComponentCount (G := G) K B (ineligibleSet G K) =
        componentCount G (K \ ineligibleSet G K) :=
    terminalComponentCount_eq_of_B_subset (G := G) (K := K) hBF
  have hcut :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) hK
  have hp : 1 ≤ pathCoverNumber G K :=
    one_le_pathCoverNumber_of_nonempty (G := G) (hBne.mono hBK)
  omega

/-- A B-free complete-join child cannot be dominant. -/
lemma not_dominant_B_free_join_side {X Y B : Finset V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hKcog : IsCograph G (X ∪ Y))
    (hB : B ⊆ X) (hBne : B.Nonempty)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B) :
    ¬ X.card < pathCoverNumber G Y := by
  intro hdom
  have hBA : G.IsCompleteBetween (Y : Set V) (X : Set V) :=
    fun {y} hy {x} hx => (hAB hx hy).symm
  have hF := ineligibleSet_complete_join_dominant hYne hXne hBA hdom
  have hBF : B ⊆ ineligibleSet G (X ∪ Y) := by
    intro b hb
    have hEq : ineligibleSet G (X ∪ Y) = X ∪ ineligibleSet G Y := by
      simpa [union_comm] using hF
    rw [hEq]
    exact mem_union.2 (Or.inl (hB hb))
  exact not_B_subset_ineligibleSet (G := G) hKcog
    (hB.trans subset_union_left) hBne hTH hBF

lemma dominant_of_terminal_join {X Y B : Finset V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hKcog : IsCograph G (X ∪ Y))
    (hB : B ⊆ X) (hBne : B.Nonempty)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B)
    (hpK : 2 ≤ pathCoverNumber G (X ∪ Y)) :
    Y.card < pathCoverNumber G X := by
  have hYnot : ¬ X.card < pathCoverNumber G Y :=
    not_dominant_B_free_join_side hXne hYne hAB hKcog hB hBne hTH
  have hpY : pathCoverNumber G Y ≤ X.card := Nat.le_of_not_gt hYnot
  have hj := pathCoverNumber_complete_join hXne hYne hAB
  have hYsub : pathCoverNumber G Y - X.card = 0 := Nat.sub_eq_zero_of_le hpY
  have hnot1 : pathCoverNumber G (X ∪ Y) ≠ 1 := by omega
  have hpX : ¬ pathCoverNumber G X ≤ Y.card := by
    intro hle
    have hxsub : pathCoverNumber G X - Y.card = 0 := Nat.sub_eq_zero_of_le hle
    have : pathCoverNumber G (X ∪ Y) = 1 := by
      rw [hj, hxsub, hYsub]
      simp
    exact hnot1 this
  exact Nat.lt_of_not_ge hpX

/-- One-path cover of a spanning original-edge path. -/
def PathCover.ofSupport (p : GraphPath G) {K : Finset V} (h : p.support = K) :
    PathCover G K :=
  (PathCover.ofPath p).cast h

lemma PathCover.ofSupport_card (p : GraphPath G) {K : Finset V}
    (h : p.support = K) :
    (PathCover.ofSupport p h).card = 1 := by
  simp [PathCover.ofSupport, PathCover.ofPath_card]

lemma PathCover.ofSupport_terminal {B K : Finset V} (p : GraphPath G)
    (h : p.support = K) (hs : p.start ∈ B) (hf : p.finish ∈ B) :
    IsTerminalCover (G := G) B (PathCover.ofSupport p h) := by
  intro q hq
  have : q = p := by
    simpa [PathCover.ofSupport, PathCover.ofPath, PathCover.cast_paths] using hq
  subst this
  exact ⟨hs, hf⟩

/-- Traceable base packaged as a minimum `B`-terminal `PathCover`. -/
lemma exists_min_terminalCover_of_pathCoverNumber_eq_one {K B : Finset V}
    (h2 : 2 ≤ K.card) (hcog : IsCograph G K)
    (hconn : (G.induce (K : Set V)).Connected)
    (hp : pathCoverNumber G K = 1) (hBK : B ⊆ K) (hBne : B.Nonempty)
    (hTH : TerminalHypothesis (G := G) K B) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc := by
  obtain ⟨p, hpK, hs, hf⟩ :=
    exists_B_ended_spanning_path h2 hcog hconn hp hBK hBne hTH
  refine ⟨PathCover.ofSupport p hpK, ?_,
    PathCover.ofSupport_terminal p hpK hs hf⟩
  simpa [PathCover.ofSupport_card p hpK] using hp.symm

lemma exists_min_terminalCover_disjoint_union {A C B : Finset V}
    (hdisj : Disjoint A C)
    (hnocross : ∀ a ∈ A, ∀ b ∈ C, ¬ G.Adj a b)
    (hA : ∃ pc : PathCover G A,
      pc.card = pathCoverNumber G A ∧ IsTerminalCover (G := G) B pc)
    (hC : ∃ pc : PathCover G C,
      pc.card = pathCoverNumber G C ∧ IsTerminalCover (G := G) B pc) :
    ∃ pc : PathCover G (A ∪ C),
      pc.card = pathCoverNumber G (A ∪ C) ∧
        IsTerminalCover (G := G) B pc := by
  obtain ⟨pcA, hAcard, hAterm⟩ := hA
  obtain ⟨pcC, hCcard, hCterm⟩ := hC
  refine ⟨Cograph.PathCover.unionDisjoint hdisj pcA pcC, ?_, ?_⟩
  · have hsum := Cograph.PathCover.unionDisjoint_card hdisj pcA pcC
    have hp := Cograph.pathCoverNumber_disjoint_union (G := G) hdisj hnocross
    omega
  · exact isTerminalCover_unionDisjoint hdisj pcA pcC hAterm hCterm

/-- Splice every connector of a complete join through an already `B`-ended
cover of the dominant child. Ends remain in `B`. -/
lemma exists_terminalCover_splice_connectors {X Y B : Finset V}
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hB : B ⊆ X)
    (hdom : Y.card < pathCoverNumber G X)
    (hX : ∃ pc : PathCover G X,
      pc.card = pathCoverNumber G X ∧ IsTerminalCover (G := G) B pc) :
    ∃ pc : PathCover G (X ∪ Y),
      pc.card = pathCoverNumber G X - Y.card ∧
        IsTerminalCover (G := G) B pc := by
  obtain ⟨pc0, h0, hterm0⟩ := hX
  have hend0 : ∀ p ∈ pc0.paths, p.start ∈ B ∧ p.finish ∈ B := hterm0
  have hBB : G.IsCompleteBetween (B : Set V) (Y : Set V) :=
    isCompleteBetween_subset_left hAB hB
  have aux :
      ∀ (k : ℕ) (S : Finset V) (pc : PathCover G (X ∪ S)),
        S ⊆ Y → (Y \ S).card = k →
          pc.card = pathCoverNumber G X - S.card →
            IsTerminalCover (G := G) B pc →
              ∃ pc' : PathCover G (X ∪ Y),
                pc'.card = pathCoverNumber G X - Y.card ∧
                  IsTerminalCover (G := G) B pc' := by
    intro k
    induction k with
    | zero =>
      intro S pc hS hk hcard hterm
      have hBS : Y \ S = ∅ := Finset.card_eq_zero.mp hk
      have hBeq : S = Y :=
        subset_antisymm hS (sdiff_eq_empty_iff_subset.mp hBS)
      subst hBeq
      exact ⟨pc, hcard, hterm⟩
    | succ k ih =>
      intro S pc hS hk hcard hterm
      have hne : (Y \ S).Nonempty :=
        card_pos.mp (by omega : 0 < (Y \ S).card)
      obtain ⟨y, hy⟩ := hne
      have hyY : y ∈ Y := (mem_sdiff.1 hy).1
      have hyS : y ∉ S := (mem_sdiff.1 hy).2
      have hdisjXY := disjoint_of_completeBetween hAB
      have hyU : y ∉ X ∪ S := by
        intro h
        rcases mem_union.1 h with hX | hS'
        · exact Finset.disjoint_left.1 hdisjXY hX hyY
        · exact hyS hS'
      have hsum : S.card + (Y \ S).card = Y.card := by
        rw [← card_union_of_disjoint, union_sdiff_of_subset hS]
        exact disjoint_sdiff
      have h2 : 2 ≤ pc.card := by
        have hdom' : Y.card + 1 ≤ pathCoverNumber G X := Nat.succ_le_iff.2 hdom
        omega
      have hend : ∀ p ∈ pc.paths, p.start ∈ B ∧ p.finish ∈ B := hterm
      obtain ⟨pc1, hcard1, hend1⟩ :=
        exists_splice_two_through hBB pc h2 hend hyY hyU
      have hU : insert y (X ∪ S) = X ∪ insert y S := by
        ext x
        simp [mem_insert, mem_union]
      let pc1' : PathCover G (X ∪ insert y S) := pc1.cast hU
      have hS' : insert y S ⊆ Y := insert_subset hyY hS
      have hrem : Y \ insert y S = (Y \ S).erase y := sdiff_insert Y S y
      have hk' : (Y \ insert y S).card = k := by
        rw [hrem, card_erase_of_mem hy, hk]
        omega
      have hcard' : pc1'.card = pathCoverNumber G X - (insert y S).card := by
        rw [PathCover.cast_card, hcard1, hcard, card_insert_of_notMem hyS]
        omega
      have hterm' : IsTerminalCover (G := G) B pc1' := by
        intro p hp
        rw [PathCover.cast_paths pc1 hU] at hp
        exact hend1 p hp
      exact ih (insert y S) pc1' hS' hk' hcard' hterm'
  have hA : X ∪ (∅ : Finset V) = X := union_empty X
  let pc0' : PathCover G (X ∪ ∅) := pc0.cast hA.symm
  have hcard0 : pc0'.card = pathCoverNumber G X - (∅ : Finset V).card := by
    rw [PathCover.cast_card, h0, card_empty, Nat.sub_zero]
  have hterm0' : IsTerminalCover (G := G) B pc0' := by
    intro p hp
    rw [PathCover.cast_paths pc0 hA.symm] at hp
    exact hend0 p hp
  exact aux Y.card ∅ pc0' (empty_subset Y) (by simp) hcard0 hterm0'

lemma exists_min_terminalCover_complete_join {X Y B : Finset V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hB : B ⊆ X)
    (hdom : Y.card < pathCoverNumber G X)
    (hX : ∃ pc : PathCover G X,
      pc.card = pathCoverNumber G X ∧ IsTerminalCover (G := G) B pc) :
    ∃ pc : PathCover G (X ∪ Y),
      pc.card = pathCoverNumber G (X ∪ Y) ∧
        IsTerminalCover (G := G) B pc := by
  obtain ⟨pc, hcard, hterm⟩ :=
    exists_terminalCover_splice_connectors hAB hB hdom hX
  have hp := pathCoverNumber_eq_sub_of_dominant hXne hYne hAB hdom
  exact ⟨pc, hcard.trans hp.symm, hterm⟩

/-- Empty carrier. -/
lemma exists_min_terminalCover_empty (B : Finset V) :
    ∃ pc : PathCover G (∅ : Finset V),
      pc.card = pathCoverNumber G (∅ : Finset V) ∧
        IsTerminalCover (G := G) B pc :=
  pathCoverNumber_empty_terminal (G := G) B

/-- Singleton `{b}` with `b ∈ B`. -/
lemma exists_min_terminalCover_singleton {B : Finset V} {b : V} (hb : b ∈ B) :
    ∃ pc : PathCover G ({b} : Finset V),
      pc.card = pathCoverNumber G ({b} : Finset V) ∧
        IsTerminalCover (G := G) B pc :=
  exists_terminalCover_singleton (G := G) hb

end Nikoghosyan
