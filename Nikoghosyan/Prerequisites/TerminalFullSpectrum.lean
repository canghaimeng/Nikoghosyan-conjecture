/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Cograph.ProtectedInduction
import Nikoghosyan.Prerequisites.TerminalMinimum
import Nikoghosyan.Prerequisites.TerminalRefinement

/-!
# Full original-B terminal spectrum

Under `RepairedTerminalHypothesis` on a nonempty independent terminal set
`B ⊆ K`, every integer `targetq` in the closed interval
`[p(K), |B| - p(K \ B)]` is realized by an actual original-edge
`B`-ended path cover of `K`.

The lower endpoint is the general minimum `B`-ended cover. A one-step
ascent from an actual cover of cardinality `r ≥ 1` with
`p(K \ B) + r < |B|` uses the concrete augmentation cycle, the
graph-general protected-path theorem on that augmentation (no host
`OneTough` or cofreeness on the augmented graph), and fresh-vertex
deletion of the resulting `augA`–`augA` path.

The existing module `TerminalSpectrum` only records the necessary
interval bound and is imported by `TerminalFeasibility`; this file
must not replace it.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma augA_subset_augCarrier {K B : Finset V} {q : ℕ} (hBK : B ⊆ K) :
    augA (B := B) (q := q) ⊆ augCarrier (q := q) K := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_augA (B := B) (q := q)).1 hx
  exact mem_union_left _ ((mem_augOldImage (q := q)).2 ⟨a, hBK ha, rfl⟩)

lemma augA_nonempty {B : Finset V} {q : ℕ} (hBne : B.Nonempty) :
    (augA (B := B) (q := q)).Nonempty := by
  obtain ⟨b, hb⟩ := hBne
  exact ⟨Sum.inl b, (mem_augA (B := B) (q := q)).2 ⟨b, hb, rfl⟩⟩

/-- One-step original-B ascent: from an actual `B`-ended cover of
cardinality `r ≥ 1` with strict leftover slack, produce an actual
`B`-ended cover of cardinality `r + 1`. -/
lemma exists_terminalCover_succ {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    {pc : PathCover G K} (hterm : IsTerminalCover (G := G) B pc)
    (hqpos : 1 ≤ pc.card)
    (hstrict : pathCoverNumber G (K \ B) + pc.card < B.card) :
    ∃ pc' : PathCover G K,
      pc'.card = pc.card + 1 ∧ IsTerminalCover (G := G) B pc' := by
  rcases hrep with ⟨hcog, hBK, _hInd, _hTH, _hN⟩
  have hBne : B.Nonempty := by
    refine card_pos.mp ?_
    have : 1 ≤ B.card := by
      have hle : pc.card ≤ pathCoverNumber G (K \ B) + pc.card := Nat.le_add_left _ _
      omega
    exact this
  obtain ⟨c, hc⟩ :=
    PathCover.exists_augCycle (B := B) (q := pc.card) pc hBK hterm rfl hqpos hstrict
  obtain ⟨p, hp, hs, hf, _hne, _hprot⟩ :=
    Cograph.exists_protectedAt_of_strict
      (G := augGraph (G := G) B pc.card) (U := augCarrier (q := pc.card) K)
      (A := augA (B := B) (q := pc.card)) c hc
      (augA_subset_augCarrier (q := pc.card) hBK)
      (augA_nonempty (q := pc.card) hBne)
      (isCograph_augRemainder_carrier (B := B) (q := pc.card) hBK
        (Cograph.isCograph_iff.2 hcog))
      (pathCoverNumber_augRemainder_lt_A (B := B) (q := pc.card) hBK hstrict)
  obtain ⟨pc', hcard, hterm'⟩ :=
    exists_terminalCover_of_augPath (B := B) (q := pc.card) p hp hs hf
  exact ⟨pc', hcard, hterm'⟩

/-- Full original-B spectrum: every integer in the closed necessary
interval is attained by an actual original-edge `B`-ended cover. -/
theorem exists_terminalCover_of_card {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hBne : B.Nonempty) (targetq : ℕ)
    (hlo : pathCoverNumber G K ≤ targetq)
    (hhi : targetq + pathCoverNumber G (K \ B) ≤ B.card) :
    ∃ pc : PathCover G K,
      pc.card = targetq ∧ IsTerminalCover (G := G) B pc := by
  have hBK : B ⊆ K := hrep.2.1
  have hppos : 1 ≤ pathCoverNumber G K :=
    one_le_pathCoverNumber_of_nonempty (hBne.mono hBK)
  refine Nat.strongRecOn
      (motive := fun n =>
        pathCoverNumber G K ≤ n →
          n + pathCoverNumber G (K \ B) ≤ B.card →
            ∃ pc : PathCover G K,
              pc.card = n ∧ IsTerminalCover (G := G) B pc)
      targetq ?_ hlo hhi
  intro n ih hlo' hhi'
  by_cases heq : n = pathCoverNumber G K
  · obtain ⟨pc, hcard, hterm⟩ := exists_general_min_terminalCover hrep hBne
    exact ⟨pc, hcard.trans heq.symm, hterm⟩
  · have hnlt : pathCoverNumber G K < n := Nat.lt_of_le_of_ne hlo' (Ne.symm heq)
    have npos : 1 ≤ n := hppos.trans hlo'
    have hnpred : n - 1 < n := Nat.sub_lt (Nat.succ_le_iff.mp npos) (by decide)
    have hloPred : pathCoverNumber G K ≤ n - 1 := Nat.le_sub_one_of_lt hnlt
    have hhiPred : n - 1 + pathCoverNumber G (K \ B) ≤ B.card := by omega
    obtain ⟨pc, hcard, hterm⟩ := ih (n - 1) hnpred hloPred hhiPred
    have hqpos : 1 ≤ pc.card := by
      have : 1 ≤ n - 1 := by omega
      omega
    have hstrict : pathCoverNumber G (K \ B) + pc.card < B.card := by omega
    obtain ⟨pc', hcard', hterm'⟩ :=
      exists_terminalCover_succ hrep hterm (by simpa [hcard] using hqpos)
        (by simpa [hcard] using hstrict)
    refine ⟨pc', ?_, hterm'⟩
    have : n - 1 + 1 = n := Nat.sub_add_cancel npos
    omega

theorem exists_terminalCover_interval {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hBne : B.Nonempty) :
    ∀ targetq : ℕ,
      pathCoverNumber G K ≤ targetq →
      targetq + pathCoverNumber G (K \ B) ≤ B.card →
      ∃ pc : PathCover G K,
        pc.card = targetq ∧ IsTerminalCover (G := G) B pc :=
  fun targetq => exists_terminalCover_of_card hrep hBne targetq

end Nikoghosyan
