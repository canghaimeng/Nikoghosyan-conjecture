/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalConstruction
import Nikoghosyan.Prerequisites.TerminalSpectrum
import Nikoghosyan.AllCographFactor
import Nikoghosyan.Cograph.Cotree

/-!
# Terminal feasibility: strong slack, mixed reduction, traceable mixed cover

The weak empty bound `z(K) ≤ t` does not let `t` universal connectors produce a
B-ended cover (four-vertex star). Deleting a nonempty join side `Y` from a
strict host yields the stronger empty child cut `z(X) ≤ |Y| - 1`. This module
records that strong slack, its join inheritance, NeighborCondition mixed
support, root dominance `p(Y) ≤ |X| - 1`, and an actual minimum B-ended cover
when the host mixed block is connected and traceable. Connector splicing and
leftover identities are imported, not re-proved.

The remaining obligation is a minimum B-ended cover of a connected mixed
cograph with `p ≥ 2`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Strong slack: empty cut uses `Nat.pred t` (so `t = 0` recovers `z = 0`,
and `t ≥ 1` recovers `z ≤ t - 1`). Nonempty cuts are `z ≤ |S| + t - 1`. -/
def TerminalHypothesisSlackStrong (K B : Finset V) (t : ℕ) : Prop :=
  terminalComponentCount (G := G) K B ∅ ≤ Nat.pred t ∧
    ∀ S ⊆ K, S.Nonempty →
      terminalComponentCount (G := G) K B S ≤ S.card + t - 1

lemma terminalHypothesis_iff_slackStrong_zero {K B : Finset V} :
    TerminalHypothesis (G := G) K B ↔
      TerminalHypothesisSlackStrong (G := G) K B 0 := by
  constructor
  · intro h
    refine ⟨by simpa [Nat.pred] using (h.1 : _ = 0), ?_⟩
    intro S hS hne
    simpa using h.2 S hS hne
  · intro h
    refine ⟨Nat.eq_zero_of_le_zero (by simpa [Nat.pred] using h.1), ?_⟩
    intro S hS hne
    simpa using h.2 S hS hne

/-- Weak slack is implied by strong slack. For `t ≥ 1` the empty bounds
differ by one, and weak slack is insufficient for connector feasibility. -/
lemma TerminalHypothesisSlack.of_strong {K B : Finset V} {t : ℕ}
    (h : TerminalHypothesisSlackStrong (G := G) K B t) :
    TerminalHypothesisSlack (G := G) K B t :=
  ⟨h.1.trans (Nat.pred_le t), h.2⟩

lemma TerminalHypothesisSlackStrong.of_terminalHypothesis {K B : Finset V}
    (h : TerminalHypothesis (G := G) K B) :
    TerminalHypothesisSlackStrong (G := G) K B 0 :=
  (terminalHypothesis_iff_slackStrong_zero (G := G) (K := K) (B := B)).1 h

lemma pred_add_card_eq {t : ℕ} {Y : Finset V} (_hYne : Y.Nonempty) :
    Nat.pred (t + Y.card) = Y.card + t - 1 := by
  rw [Nat.pred_eq_sub_one, Nat.add_comm t]

/-- After deleting a nonempty join side, the mixed child inherits *strong*
slack with parameter `t + |Y|`. The empty bound is `z(X) ≤ |Y| + t - 1`. -/
lemma terminalHypothesisSlackStrong_join_child {X Y B : Finset V} {t : ℕ}
    (hYne : Y.Nonempty) (hdisj : Disjoint X Y) (hB : B ⊆ X)
    (hTH : TerminalHypothesisSlackStrong (G := G) (X ∪ Y) B t) :
    TerminalHypothesisSlackStrong (G := G) X B (t + Y.card) := by
  have hYsub : Y ⊆ X ∪ Y := subset_union_right
  have hempty :
      terminalComponentCount (G := G) X B ∅ ≤ Nat.pred (t + Y.card) := by
    have hz := hTH.2 Y hYsub hYne
    have hEq :
        terminalComponentCount (G := G) (X ∪ Y) B Y =
          terminalComponentCount (G := G) X B ∅ := by
      simpa using
        terminalComponentCount_join_delete_right (G := G) (B := B)
          (S := (∅ : Finset V)) hdisj hB (empty_subset X)
    have hpred := pred_add_card_eq (t := t) hYne
    have : terminalComponentCount (G := G) X B ∅ ≤ Y.card + t - 1 := by
      rwa [hEq] at hz
    rwa [hpred]
  refine ⟨hempty, ?_⟩
  intro S hS _hSne
  have hcut : S ∪ Y ⊆ X ∪ Y :=
    union_subset (hS.trans subset_union_left) subset_union_right
  have hne : (S ∪ Y).Nonempty := hYne.mono subset_union_right
  have hz := hTH.2 (S ∪ Y) hcut hne
  have hEq :=
    terminalComponentCount_join_delete_right (G := G) (B := B) hdisj hB hS
  have hcard : (S ∪ Y).card = S.card + Y.card :=
    card_union_of_disjoint (disjoint_of_subset_left hS hdisj)
  omega

lemma terminalHypothesisSlackStrong_join_child_of_terminal {X Y B : Finset V}
    (hYne : Y.Nonempty) (hdisj : Disjoint X Y) (hB : B ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B) :
    TerminalHypothesisSlackStrong (G := G) X B Y.card := by
  have h0 : TerminalHypothesisSlackStrong (G := G) (X ∪ Y) B 0 :=
    TerminalHypothesisSlackStrong.of_terminalHypothesis hTH
  simpa using
    terminalHypothesisSlackStrong_join_child (t := 0) hYne hdisj hB h0

/-- Empty strong bound after deleting `Y` from a strict host: `z(X) ≤ |Y| - 1`. -/
lemma terminalComponentCount_join_child_empty_strong {X Y B : Finset V}
    (hYne : Y.Nonempty) (hdisj : Disjoint X Y) (hB : B ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B) :
    terminalComponentCount (G := G) X B ∅ ≤ Y.card - 1 :=
  terminalComponentCount_join_child_empty_le hYne hdisj hB hTH

lemma union_sdiff_union_eq_sdiff_right {X Y F : Finset V}
    (hdisj : Disjoint X Y) (_hF : F ⊆ Y) :
    (X ∪ Y) \ (X ∪ F) = Y \ F := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hx
    rcases hx with ⟨hxXY, hxnot⟩
    have hxX : x ∉ X := fun hX => hxnot (Or.inl hX)
    have hxF : x ∉ F := fun hF' => hxnot (Or.inr hF')
    rcases hxXY with hxX' | hxY
    · exact (hxX hxX').elim
    · exact ⟨hxY, hxF⟩
  · intro hx
    have hxX : x ∉ X := fun hX => Finset.disjoint_left.1 hdisj hX hx.1
    exact ⟨Or.inr hx.1, fun h => h.elim hxX hx.2⟩

/-- Root dominance: a B-free join side satisfies `p(Y) ≤ |X| - 1` under
strict `TerminalHypothesis`. Cut `S = X ∪ F(Y)`. -/
lemma pathCoverNumber_B_free_join_side_lt {X Y B : Finset V}
    (hXne : X.Nonempty) (_hYne : Y.Nonempty)
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hKcog : IsCograph G (X ∪ Y))
    (hB : B ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B) :
    pathCoverNumber G Y + 1 ≤ X.card := by
  have hdisj := disjoint_of_completeBetween hAB
  have hYcog : IsCograph G Y :=
    fun a b c d ha hb hc hd hp =>
      hKcog (mem_union.2 (Or.inr ha)) (mem_union.2 (Or.inr hb))
        (mem_union.2 (Or.inr hc)) (mem_union.2 (Or.inr hd)) hp
  set FY := ineligibleSet G Y
  have hFYsub : FY ⊆ Y := ineligibleSet_subset (G := G) Y
  have hS : X ∪ FY ⊆ X ∪ Y :=
    union_subset subset_union_left (hFYsub.trans subset_union_right)
  have hSne : (X ∪ FY).Nonempty := hXne.mono subset_union_left
  have hBS : B ⊆ X ∪ FY := hB.trans subset_union_left
  have hz := hTH.2 (X ∪ FY) hS hSne
  have hz' :
      terminalComponentCount (G := G) (X ∪ Y) B (X ∪ FY) =
        componentCount G ((X ∪ Y) \ (X ∪ FY)) :=
    terminalComponentCount_eq_of_B_subset (G := G) hBS
  have hdiff := union_sdiff_union_eq_sdiff_right hdisj hFYsub
  have hcut :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) hYcog
  have hcard : (X ∪ FY).card = X.card + FY.card :=
    card_union_of_disjoint (disjoint_of_subset_right hFYsub hdisj)
  have hle : componentCount G (Y \ FY) ≤ (X ∪ FY).card - 1 := by
    simpa [hz', hdiff] using hz
  have hle' : componentCount G (Y \ FY) ≤ X.card + FY.card - 1 := by
    rwa [hcard] at hle
  have hcanon : componentCount G (Y \ FY) = FY.card + pathCoverNumber G Y := by
    simpa [FY] using hcut
  have hXpos : 1 ≤ X.card := card_pos.2 hXne
  omega

lemma pathCoverNumber_B_free_join_side_le_slack {X Y B : Finset V} {t : ℕ}
    (hXne : X.Nonempty) (_hYne : Y.Nonempty)
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hKcog : IsCograph G (X ∪ Y))
    (hB : B ⊆ X)
    (hTH : TerminalHypothesisSlackStrong (G := G) (X ∪ Y) B t) :
    pathCoverNumber G Y ≤ X.card + t - 1 := by
  have hdisj := disjoint_of_completeBetween hAB
  have hYcog : IsCograph G Y :=
    fun a b c d ha hb hc hd hp =>
      hKcog (mem_union.2 (Or.inr ha)) (mem_union.2 (Or.inr hb))
        (mem_union.2 (Or.inr hc)) (mem_union.2 (Or.inr hd)) hp
  set FY := ineligibleSet G Y
  have hFYsub : FY ⊆ Y := ineligibleSet_subset (G := G) Y
  have hS : X ∪ FY ⊆ X ∪ Y :=
    union_subset subset_union_left (hFYsub.trans subset_union_right)
  have hSne : (X ∪ FY).Nonempty := hXne.mono subset_union_left
  have hBS : B ⊆ X ∪ FY := hB.trans subset_union_left
  have hz := hTH.2 (X ∪ FY) hS hSne
  have hz' :
      terminalComponentCount (G := G) (X ∪ Y) B (X ∪ FY) =
        componentCount G ((X ∪ Y) \ (X ∪ FY)) :=
    terminalComponentCount_eq_of_B_subset (G := G) hBS
  have hdiff := union_sdiff_union_eq_sdiff_right hdisj hFYsub
  have hcut :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) hYcog
  have hcard : (X ∪ FY).card = X.card + FY.card :=
    card_union_of_disjoint (disjoint_of_subset_right hFYsub hdisj)
  have hle : componentCount G (Y \ FY) ≤ (X ∪ FY).card + t - 1 := by
    simpa [hz', hdiff] using hz
  have hcanon : componentCount G (Y \ FY) = FY.card + pathCoverNumber G Y := by
    simpa [FY] using hcut
  omega

/-- If `p(K) ≥ 2` on a complete join with independent terminals in `X`,
root dominance forces `X` to be the unique dominant child. -/
lemma dominant_mixed_child_of_slack_zero {X Y B : Finset V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hAB : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hKcog : IsCograph G (X ∪ Y))
    (hB : B ⊆ X)
    (hTH : TerminalHypothesis (G := G) (X ∪ Y) B)
    (hpK : 2 ≤ pathCoverNumber G (X ∪ Y)) :
    Y.card < pathCoverNumber G X := by
  have hpY : pathCoverNumber G Y + 1 ≤ X.card :=
    pathCoverNumber_B_free_join_side_lt hXne hYne hAB hKcog hB hTH
  have hj := pathCoverNumber_complete_join hXne hYne hAB
  have hYsub : pathCoverNumber G Y ≤ X.card := by omega
  have hY0 : pathCoverNumber G Y - X.card = 0 := Nat.sub_eq_zero_of_le hYsub
  have hnot1 : pathCoverNumber G (X ∪ Y) ≠ 1 := by omega
  have hpX : ¬ pathCoverNumber G X ≤ Y.card := by
    intro hle
    have hxsub : pathCoverNumber G X - Y.card = 0 := Nat.sub_eq_zero_of_le hle
    have : pathCoverNumber G (X ∪ Y) = 1 := by
      rw [hj, hxsub, hY0]
      simp
    exact hnot1 this
  exact Nat.lt_of_not_ge hpX

/-! ### Endpoint deficit of an ordinary path cover -/

/-- Number of path ends that miss `B`. A non-`B` singleton contributes `2`. -/
def GraphPath.endpointDeficit (B : Finset V) (p : GraphPath G) : ℕ :=
  (if p.start ∈ B then 0 else 1) + (if p.finish ∈ B then 0 else 1)

lemma GraphPath.endpointDeficit_le_two (B : Finset V) (p : GraphPath G) :
    p.endpointDeficit B ≤ 2 := by
  unfold GraphPath.endpointDeficit
  split_ifs <;> simp

lemma GraphPath.endpointDeficit_eq_zero_iff (B : Finset V) (p : GraphPath G) :
    p.endpointDeficit B = 0 ↔ p.start ∈ B ∧ p.finish ∈ B := by
  unfold GraphPath.endpointDeficit
  split_ifs <;> simp_all

lemma GraphPath.endpointDeficit_reverse (B : Finset V) (p : GraphPath G) :
    p.reverse.endpointDeficit B = p.endpointDeficit B := by
  unfold GraphPath.endpointDeficit GraphPath.reverse
  simp [Nat.add_comm]

/-- Orient so that an open end, if any, is the finish. -/
def GraphPath.orientFinishOpen (B : Finset V) (p : GraphPath G) : GraphPath G :=
  if p.finish ∈ B then p.reverse else p

lemma GraphPath.orientFinishOpen_support (B : Finset V) (p : GraphPath G) :
    (p.orientFinishOpen B).support = p.support := by
  unfold GraphPath.orientFinishOpen
  split_ifs <;> simp

lemma GraphPath.orientFinishOpen_mem_X {X B : Finset V} (p : GraphPath G)
    (hs : p.start ∈ X) (hf : p.finish ∈ X) :
    (p.orientFinishOpen B).start ∈ X ∧ (p.orientFinishOpen B).finish ∈ X := by
  unfold GraphPath.orientFinishOpen
  split_ifs <;> simp [GraphPath.reverse, hs, hf]

lemma GraphPath.orientFinishOpen_finish_not_mem (B : Finset V) (p : GraphPath G)
    (h : p.start ∉ B ∨ p.finish ∉ B) :
    (p.orientFinishOpen B).finish ∉ B := by
  unfold GraphPath.orientFinishOpen
  split_ifs with hf
  · simp [GraphPath.reverse]
    rcases h with hs | hf'
    · exact hs
    · exact (hf' hf).elim
  · exact hf

/-- Orient so that an open end, if any, is the start. -/
def GraphPath.orientStartOpen (B : Finset V) (p : GraphPath G) : GraphPath G :=
  if p.start ∈ B then p.reverse else p

lemma GraphPath.orientStartOpen_support (B : Finset V) (p : GraphPath G) :
    (p.orientStartOpen B).support = p.support := by
  unfold GraphPath.orientStartOpen
  split_ifs <;> simp

lemma GraphPath.orientStartOpen_mem_X {X B : Finset V} (p : GraphPath G)
    (hs : p.start ∈ X) (hf : p.finish ∈ X) :
    (p.orientStartOpen B).start ∈ X ∧ (p.orientStartOpen B).finish ∈ X := by
  unfold GraphPath.orientStartOpen
  split_ifs <;> simp [GraphPath.reverse, hs, hf]

lemma GraphPath.orientStartOpen_start_not_mem (B : Finset V) (p : GraphPath G)
    (h : p.start ∉ B ∨ p.finish ∉ B) :
    (p.orientStartOpen B).start ∉ B := by
  unfold GraphPath.orientStartOpen
  split_ifs with hs
  · simp [GraphPath.reverse]
    rcases h with hs' | hf
    · exact (hs' hs).elim
    · exact hf
  · exact hs

noncomputable def PathCover.endpointDeficit {K : Finset V} (B : Finset V)
    (pc : PathCover G K) : ℕ :=
  (pc.paths.map (fun p => p.endpointDeficit B)).sum

lemma PathCover.deficit_eq_zero_of_terminal {K B : Finset V}
    (pc : PathCover G K) (h : IsTerminalCover (G := G) B pc) :
    pc.endpointDeficit B = 0 := by
  unfold PathCover.endpointDeficit
  refine List.sum_eq_zero ?_
  intro n hn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn
  have ht := h p hp
  simp [GraphPath.endpointDeficit, ht.1, ht.2]

lemma PathCover.terminalCover_of_deficit_eq_zero {K B : Finset V}
    (pc : PathCover G K) (h : pc.endpointDeficit B = 0) :
    IsTerminalCover (G := G) B pc := by
  intro p hp
  have hmem :
      p.endpointDeficit B ∈ pc.paths.map (fun q => q.endpointDeficit B) :=
    List.mem_map.2 ⟨p, hp, rfl⟩
  have hle :
      p.endpointDeficit B ≤
        (pc.paths.map (fun q => q.endpointDeficit B)).sum :=
    List.le_sum_of_mem hmem
  have hp0 : p.endpointDeficit B = 0 := by
    unfold PathCover.endpointDeficit at h
    omega
  exact (GraphPath.endpointDeficit_eq_zero_iff (G := G) B p).1 hp0

lemma PathCover.singletons_terminal {B U : Finset V} (hUB : U ⊆ B) :
    IsTerminalCover (G := G) B (PathCover.singletons (G := G) U) := by
  intro p hp
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hp
  have hvB : v ∈ B := hUB (mem_toList.1 hv)
  exact ⟨hvB, hvB⟩

lemma pathCoverNumber_eq_card_of_independent {U : Finset V}
    (h : Independent (G := G) U) :
    pathCoverNumber G U = U.card := by
  have hc := componentCount_of_independent (G := G) h
  have hle := componentCount_le_pathCoverNumber (G := G) U
  have hge := pathCoverNumber_le_card (G := G) U
  omega

lemma exists_min_terminalCover_subset_B {K B : Finset V}
    (hKB : K ⊆ B) (hInd : Independent (G := G) B) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc := by
  have hIndK : Independent (G := G) K := hInd.mono hKB
  refine ⟨PathCover.singletons (G := G) K, ?_, PathCover.singletons_terminal hKB⟩
  simp [pathCoverNumber_eq_card_of_independent (G := G) hIndK]

/-! ### NeighborCondition mixed support -/

lemma all_nonterminals_mem_component_of_BV_edge {K B : Finset V}
    (hN : NeighborCondition (G := G) K B) (hBK : B ⊆ K)
    {b v w : V} (hb : b ∈ B) (hv : v ∈ K \ B) (hw : w ∈ K \ B)
    (hadj : G.Adj b v) :
    w ∈ componentFinset G K
      ((G.induce (K : Set V)).connectedComponentMk ⟨v, (mem_sdiff.1 hv).1⟩) := by
  have hR :=
    reachable_all_nonterminals_of_neighbor (G := G) hN hBK hb hv hw hadj
  have hvK : v ∈ K := (mem_sdiff.1 hv).1
  have hwK : w ∈ K := (mem_sdiff.1 hw).1
  have hC :
      (G.induce (K : Set V)).connectedComponentMk ⟨w, hwK⟩ =
        (G.induce (K : Set V)).connectedComponentMk ⟨v, hvK⟩ :=
    (Quot.sound hR).symm
  exact mem_filter.2 ⟨hwK, ⟨hwK, hC⟩⟩

lemma adj_mem_componentFinset' {U : Finset V}
    {C : (G.induce (U : Set V)).ConnectedComponent} {x y : V}
    (hx : x ∈ componentFinset G U C) (hy : y ∈ U) (hadj : G.Adj x y) :
    y ∈ componentFinset G U C := by
  have hxU : x ∈ U := (mem_filter.1 hx).1
  obtain ⟨_, hxC⟩ := (mem_filter.1 hx).2
  have hadj' : (G.induce (U : Set V)).Adj ⟨x, hxU⟩ ⟨y, hy⟩ := by
    simpa [induce_adj] using hadj
  have hyC :
      (G.induce (U : Set V)).connectedComponentMk ⟨y, hy⟩ = C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hadj').symm.trans hxC
  exact mem_filter.2 ⟨hy, ⟨hy, hyC⟩⟩

lemma mem_componentFinset_of_adj_B {K : Finset V}
    {b v : V} (hbK : b ∈ K) (hvK : v ∈ K) (hadj : G.Adj b v) :
    b ∈ componentFinset G K
      ((G.induce (K : Set V)).connectedComponentMk ⟨v, hvK⟩) :=
  adj_mem_componentFinset' (G := G)
    (mem_filter.2 ⟨hvK, ⟨hvK, rfl⟩⟩) hbK hadj.symm

/-- If a `B`–`(K \ B)` edge exists, every vertex of `K \ B` lies in that
one induced component. -/
lemma sdiff_subset_mixed_component {K B : Finset V}
    (hN : NeighborCondition (G := G) K B) (hBK : B ⊆ K)
    {b v : V} (hb : b ∈ B) (hv : v ∈ K \ B) (hadj : G.Adj b v) :
    K \ B ⊆
      componentFinset G K
        ((G.induce (K : Set V)).connectedComponentMk ⟨v, (mem_sdiff.1 hv).1⟩) := by
  intro w hw
  exact all_nonterminals_mem_component_of_BV_edge hN hBK hb hv hw hadj

/-- Outside the mixed component of a `B`–`V` edge, only terminals remain. -/
lemma sdiff_mixed_component_subset_B {K B : Finset V}
    (hN : NeighborCondition (G := G) K B) (hBK : B ⊆ K)
    {b v : V} (hb : b ∈ B) (hv : v ∈ K \ B) (hadj : G.Adj b v) :
    K \
        componentFinset G K
          ((G.induce (K : Set V)).connectedComponentMk ⟨v, (mem_sdiff.1 hv).1⟩) ⊆
      B := by
  intro x hx
  have hxK : x ∈ K := (mem_sdiff.1 hx).1
  have hxC : x ∉
      componentFinset G K
        ((G.induce (K : Set V)).connectedComponentMk ⟨v, (mem_sdiff.1 hv).1⟩) :=
    (mem_sdiff.1 hx).2
  by_contra hxB
  have hxV : x ∈ K \ B := mem_sdiff.2 ⟨hxK, hxB⟩
  exact hxC (all_nonterminals_mem_component_of_BV_edge hN hBK hb hv hxV hadj)

lemma no_cross_mixed_component {K : Finset V}
    {C : (G.induce (K : Set V)).ConnectedComponent}
    {x y : V} (hx : x ∈ componentFinset G K C)
    (hy : y ∈ K) (hyC : y ∉ componentFinset G K C) :
    ¬ G.Adj x y := by
  intro hadj
  exact hyC (adj_mem_componentFinset' (G := G) hx hy hadj)

/-- No-cross union of a mixed B-ended minimum cover with a terminal subset of
`B` remains a minimum B-ended cover. -/
lemma exists_min_terminalCover_mixed_union_isolates {D I B : Finset V}
    (hdisj : Disjoint D I) (hI : I ⊆ B)
    (hInd : Independent (G := G) B)
    (hnocross : ∀ a ∈ D, ∀ b ∈ I, ¬ G.Adj a b)
    (hD : ∃ pc : PathCover G D,
      pc.card = pathCoverNumber G D ∧ IsTerminalCover (G := G) B pc) :
    ∃ pc : PathCover G (D ∪ I),
      pc.card = pathCoverNumber G (D ∪ I) ∧
        IsTerminalCover (G := G) B pc := by
  obtain ⟨pcI, hIcard, hIterm⟩ :=
    exists_min_terminalCover_subset_B (K := I) (B := B) hI hInd
  exact exists_min_terminalCover_disjoint_union hdisj hnocross hD
    ⟨pcI, hIcard, hIterm⟩

/-- Host existence when `K = B ∪ W` is connected and traceable: actual
minimum B-ended cover, no supplied child witness. -/
theorem exists_min_terminalCover_of_sides_of_mixed_traceable
    (P : AllCographSides G) (hpat : NoInducedP4UnionP1 G) (htough : OneTough G)
    (hconn : (G.induce ((P.B ∪ P.W : Finset V) : Set V)).Connected)
    (hp : pathCoverNumber G (P.B ∪ P.W) = 1) :
    ∃ pc : PathCover G (P.B ∪ P.W),
      pc.card = pathCoverNumber G (P.B ∪ P.W) ∧
        IsTerminalCover (G := G) P.B pc := by
  have hrep := P.repairedTerminalHypothesis_of_oneTough hpat htough
  have h2 : 2 ≤ (P.B ∪ P.W).card := by
    have hB2 : 2 ≤ P.B.card := by
      have hm := P.hm
      have hBc := P.hBcard
      omega
    exact hB2.trans (card_le_card subset_union_left)
  have hBne : P.B.Nonempty := by
    refine card_pos.mp ?_
    have hm := P.hm
    have hBc := P.hBcard
    omega
  exact exists_min_terminalCover_of_pathCoverNumber_eq_one
    h2 hrep.1 hconn hp P.B_subset_K hBne hrep.2.2.2.1

/-- If a minimum B-terminal cover exists and equals the host choice
`q = max(p(K), m - |U|)`, the original endpoint-seam cycle is realized. -/
theorem exists_univ_cycle_of_sides_of_min_eq_chosenQ
    (P : AllCographSides G) (htough : OneTough G)
    (hmin : ∃ pc : PathCover G (P.B ∪ P.W),
      pc.card = pathCoverNumber G (P.B ∪ P.W) ∧
        IsTerminalCover (G := G) P.B pc)
    (hchoice : P.chosenQ = pathCoverNumber G (P.B ∪ P.W)) :
    ∃ c : GraphCycle G, c.support = (univ : Finset V) := by
  obtain ⟨pc, hcard, hterm⟩ := hmin
  exact P.exists_univ_cycle_of_chosen_terminal_cover htough pc
    (hchoice ▸ hcard) hterm

/-- Connected host with `p(K) = 1` and `p(K) ≥ m - |U|` yields the original
spanning cycle, with no extra terminal-cover premise. -/
theorem exists_univ_cycle_of_sides_of_traceable_chosenQ
    (P : AllCographSides G) (hpat : NoInducedP4UnionP1 G) (htough : OneTough G)
    (hconn : (G.induce ((P.B ∪ P.W : Finset V) : Set V)).Connected)
    (hp : pathCoverNumber G (P.B ∪ P.W) = 1)
    (hchoice : P.chosenQ = pathCoverNumber G (P.B ∪ P.W)) :
    ∃ c : GraphCycle G, c.support = (univ : Finset V) :=
  exists_univ_cycle_of_sides_of_min_eq_chosenQ P htough
    (exists_min_terminalCover_of_sides_of_mixed_traceable P hpat htough hconn hp)
    hchoice

end Nikoghosyan
