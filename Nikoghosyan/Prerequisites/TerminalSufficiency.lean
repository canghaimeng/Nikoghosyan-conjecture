/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Cograph.HamiltonBalanced
import Nikoghosyan.Prerequisites.TerminalCutTransport

/-!
# Traceable B-ended spanning paths under TerminalHypothesis

A connected cograph `K` of order at least two with `p(K) = 1`, nonempty
`B ⊆ K`, and the strict terminal cut hypothesis admits an original-edge
spanning path with both ends in `B`.

If no `B`–`B` spanning-path pair exists, every eligible terminal lies in
one actual `R`-class (critical `D`-class, or balanced `Q_x`) and the
remainder of `B` lies in `F(K)`. The checked Hamilton-endpoint
certificate then supplies a nonempty cut `S ⊆ F(K)` or an `R`-class
`P` whose leftover components are too many to satisfy
`z_B(K-S) ≤ |S| - 1`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma GraphPath.start_ne_finish_of_two_le_card (p : GraphPath G)
    (h : 2 ≤ p.support.card) : p.start ≠ p.finish := by
  intro heq
  have hnil : p.walk.Nil := (GraphPath.nil_iff_start_eq_finish p).2 heq
  have hs := GraphPath.support_eq_singleton_of_nil p hnil
  have : p.support.card = 1 := by rw [hs, card_singleton]
  omega

lemma mem_of_spanningPathCompatible {U : Finset V} {x y : V}
    (h : SpanningPathCompatible (G := G) U x y) : x ∈ U ∧ y ∈ U := by
  obtain ⟨_, p, hp, hends⟩ := h
  constructor
  · rcases hends with ⟨hs, _⟩ | ⟨_, hf⟩
    · simpa [hs, hp] using p.start_mem_support
    · simpa [hf, hp] using p.finish_mem_support
  · rcases hends with ⟨_, hf⟩ | ⟨hs, _⟩
    · simpa [hf, hp] using p.finish_mem_support
    · simpa [hs, hp] using p.start_mem_support

lemma exists_spanningPathCompatible_of_eligible {U : Finset V} {x : V}
    (h2 : 2 ≤ U.card) (hp : pathCoverNumber G U = 1)
    (hE : Eligible G U x) :
    ∃ y, SpanningPathCompatible (G := G) U x y := by
  obtain ⟨p, hpU, hy⟩ :=
    Cograph.exists_spanning_path_of_eligible_eq_one (G := G) hp hE
  have hcard : 2 ≤ p.support.card := by simpa [hpU] using h2
  have hne := GraphPath.start_ne_finish_of_two_le_card p hcard
  rcases hy with hs | hf
  · refine ⟨p.finish, ?_⟩
    refine ⟨?_, p, hpU, Or.inl ⟨hs, rfl⟩⟩
    simpa [hs] using hne
  · refine ⟨p.start, ?_⟩
    refine ⟨?_, p, hpU, Or.inr ⟨rfl, hf⟩⟩
    simpa [hf] using hne.symm

lemma IsFreeComponent_of_B_subset {K B S : Finset V}
    (hB : B ⊆ S)
    (C : (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent) :
    IsFreeComponent (G := G) K B S C := by
  have hBS : B \ S = ∅ := sdiff_eq_empty_iff_subset.2 hB
  simp [IsFreeComponent, hBS]

lemma terminalComponentCount_eq_of_B_subset {K B S : Finset V}
    (hB : B ⊆ S) :
    terminalComponentCount (G := G) K B S = componentCount G (K \ S) := by
  unfold terminalComponentCount componentCount
  refine Nat.card_congr ?_
  exact Equiv.subtypeUnivEquiv (fun C => IsFreeComponent_of_B_subset (G := G) hB C)

lemma connectedComponentMk_eq_of_mem_componentFinset' {U : Finset V}
    {C : (G.induce (U : Set V)).ConnectedComponent} {x : V}
    (hx : x ∈ componentFinset G U C) :
    (G.induce (U : Set V)).connectedComponentMk ⟨x, (mem_filter.1 hx).1⟩ = C := by
  obtain ⟨_, hC⟩ := (mem_filter.1 hx).2
  exact hC

/-- If every surviving terminal lies in one actual remainder component,
then `z_B(K-S) ≥ c(K-S) - 1`. -/
lemma terminalComponentCount_ge_pred_of_inOne {K B S W : Finset V}
    (hIn : Cograph.InOneComponent (G := G) (K \ S) W)
    (hB : B \ S ⊆ W) :
    componentCount G (K \ S) - 1 ≤
      terminalComponentCount (G := G) K B S := by
  by_cases hsurv : (B \ S).Nonempty
  · have hWne : W.Nonempty := hsurv.mono hB
    obtain ⟨C0, hC0⟩ :=
      Cograph.exists_component_of_inOneComponent (G := G) hWne hIn
    have huniq :
        ∀ C : (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent,
          ¬ IsFreeComponent (G := G) K B S C → C = C0 := by
      intro C hnf
      have hne : (componentFinset G (K \ S) C ∩ (B \ S)).Nonempty :=
        nonempty_iff_ne_empty.2 hnf
      obtain ⟨b, hbint⟩ := hne
      have hbC : b ∈ componentFinset G (K \ S) C := (mem_inter.1 hbint).1
      have hbB : b ∈ B \ S := (mem_inter.1 hbint).2
      have hbW : b ∈ W := hB hbB
      obtain ⟨hbU, hbC0⟩ := hC0 b hbW
      have hbMk := connectedComponentMk_eq_of_mem_componentFinset' (G := G) hbC
      have hUeq : (mem_filter.1 hbC).1 = hbU := rfl
      exact hbMk.symm.trans hbC0
    haveI : Fintype
        (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent :=
      inferInstance
    let α := (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent
    let p : α → Prop := fun C => IsFreeComponent (G := G) K B S C
    have hsub : Subsingleton { C : α // ¬ p C } :=
      ⟨fun a b => Subtype.ext ((huniq a.1 a.2).trans (huniq b.1 b.2).symm)⟩
    have hnf : Fintype.card { C : α // ¬ p C } ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.2 hsub
    have hle : Fintype.card { C : α // p C } ≤ Fintype.card α :=
      Fintype.card_subtype_le _
    have hsum :
        Fintype.card { C : α // p C } + Fintype.card { C : α // ¬ p C } =
          Fintype.card α := by
      rw [Fintype.card_subtype_compl]
      exact Nat.add_sub_of_le hle
    have hz : terminalComponentCount (G := G) K B S =
        Fintype.card { C : α // p C } := by
      rw [terminalComponentCount, Nat.card_eq_fintype_card]
    have hc : componentCount G (K \ S) = Fintype.card α := by
      rw [componentCount, Nat.card_eq_fintype_card]
    omega
  · have hBsub : B ⊆ S := by
      intro x hx
      by_contra hxS
      exact hsurv ⟨x, mem_sdiff.2 ⟨hx, hxS⟩⟩
    have hz :=
      terminalComponentCount_eq_of_B_subset (G := G) (K := K) hBsub
    have hcpos : componentCount G (K \ S) - 1 ≤ componentCount G (K \ S) :=
      Nat.sub_le _ _
    simpa [hz] using hcpos

lemma exists_B_ended_spanning_path {K B : Finset V}
    (h2 : 2 ≤ K.card) (hcog : IsCograph G K)
    (hconn : (G.induce (K : Set V)).Connected)
    (hp : pathCoverNumber G K = 1) (hBK : B ⊆ K) (hBne : B.Nonempty)
    (hTH : TerminalHypothesis (G := G) K B) :
    ∃ p : GraphPath G, p.support = K ∧ p.start ∈ B ∧ p.finish ∈ B := by
  by_contra hnone
  have hnoR : ∀ {x y : V}, x ∈ B → y ∈ B →
      ¬ SpanningPathCompatible (G := G) K x y := by
    intro x y hx hy hR
    obtain ⟨_, p, hpU, hends⟩ := hR
    apply hnone
    rcases hends with ⟨hs, hf⟩ | ⟨hs, hf⟩
    · exact ⟨p, hpU, hs ▸ hx, hf ▸ hy⟩
    · exact ⟨p, hpU, hs ▸ hy, hf ▸ hx⟩
  have hdata :=
    Cograph.hamilton_endpoints_of_traceable_cograph_canonical
      (G := G) h2 hcog hconn hp
  rcases hdata with hcrit | hbal
  · obtain ⟨A, Y, hAne, hYne, hunion, hAY, hcritAY, hA, hEeq, hFeq, hRiff, hpart⟩ :=
      hcrit
    obtain ⟨p0, hp0⟩ :=
      Cograph.exists_spanning_path_of_pathCoverNumber_eq_one (G := G) hp
    have hE0 := (Cograph.Eligible_of_support_ends p0 hp0).1
    have h0K : p0.start ∈ K := Eligible.mem (G := G) hE0
    have h0A : p0.start ∈ eligibleSet G A := by
      have : p0.start ∈ eligibleSet G K :=
        (mem_eligibleSet_iff (G := G)).2 ⟨h0K, hE0⟩
      rwa [← hEeq]
    let EB := B ∩ eligibleSet G A
    obtain ⟨x, hxEA, hxBof⟩ :
        ∃ x, x ∈ eligibleSet G A ∧ (EB.Nonempty → x ∈ B) := by
      by_cases hEB : EB.Nonempty
      · obtain ⟨x, hx⟩ := hEB
        exact ⟨x, (mem_inter.1 hx).2, fun _ => (mem_inter.1 hx).1⟩
      · exact ⟨p0.start, h0A, fun h => (hEB h).elim⟩
    obtain ⟨S, hSsub, hSne, hScut, hScomp⟩ := hpart x hxEA
    have hBsub :
        B ⊆ ineligibleSet G K ∪ Cograph.dNonadjClass (G := G) A x := by
      intro z hz
      by_cases hzE : z ∈ eligibleSet G K
      · have hzEA : z ∈ eligibleSet G A := by rwa [← hEeq]
        by_cases hzP : z ∈ Cograph.dNonadjClass (G := G) A x
        · exact mem_union.2 (Or.inr hzP)
        · have hzD : DistinctPathCompatible (G := G) A x z := by
            have hiff := Cograph.mem_dNonadjClass_iff (G := G) (U := A) (x := x) (y := z)
            have : ¬ (z ∈ eligibleSet G A ∧
                ¬ DistinctPathCompatible (G := G) A x z) := by
              simpa [hiff] using hzP
            tauto
          have hxB : x ∈ B :=
            hxBof ⟨z, mem_inter.2 ⟨hz, hzEA⟩⟩
          exact (hnoR hxB hz ((hRiff x z).2 hzD)).elim
      · have hzK : z ∈ K := hBK hz
        have hnotE : ¬ Eligible G K z := by
          intro hE
          exact hzE ((mem_eligibleSet_iff (G := G)).2 ⟨hzK, hE⟩)
        exact mem_union.2 (Or.inl ((mem_ineligibleSet_iff (G := G)).2 ⟨hzK, hnotE⟩))
    have hBrem :
        B \ S ⊆
          (ineligibleSet G K ∪ Cograph.dNonadjClass (G := G) A x) \ S :=
      fun z hz =>
        mem_sdiff.2 ⟨hBsub (mem_sdiff.1 hz).1, (mem_sdiff.1 hz).2⟩
    have hSsubK : S ⊆ K :=
      hSsub.trans (ineligibleSet_subset (G := G) K)
    have hzge :=
      terminalComponentCount_ge_pred_of_inOne (G := G) (K := K) (B := B)
        (S := S) hScomp hBrem
    have hTHS := hTH.2 S hSsubK hSne
    have hc : componentCount G (K \ S) = S.card + 1 := hScut
    have hge : S.card ≤ terminalComponentCount (G := G) K B S := by
      have hpred : (S.card + 1) - 1 ≤ terminalComponentCount (G := G) K B S := by
        simpa [hc] using hzge
      simpa using hpred
    have hle : terminalComponentCount (G := G) K B S ≤ S.card - 1 := hTHS
    have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.mpr hSne)
    omega
  · obtain ⟨hEall, hcut, _hclass⟩ := hbal
    obtain ⟨b, hb⟩ := hBne
    have hbK : b ∈ K := hBK hb
    have hBsub : B ⊆ Cograph.rNonadjClass (G := G) K b := by
      intro z hz
      by_contra hzP
      have hzK : z ∈ K := hBK hz
      have hR : SpanningPathCompatible (G := G) K b z := by
        have hiff :=
          Cograph.mem_rNonadjClass_iff (G := G) (U := K) (x := b) (y := z)
        have : ¬ (z ∈ K ∧ ¬ SpanningPathCompatible (G := G) K b z) := by
          simpa [hiff] using hzP
        tauto
      exact hnoR hb hz hR
    set P := Cograph.rNonadjClass (G := G) K b
    have hPsub : P ⊆ K := Cograph.rNonadjClass_subset (G := G) K b
    have hPne : P.Nonempty := ⟨b, Cograph.mem_rNonadjClass_self hbK⟩
    have hcutP : componentCount G (K \ P) = P.card := hcut b hbK
    have hz : terminalComponentCount (G := G) K B P = P.card :=
      (terminalComponentCount_eq_of_B_subset (G := G) (K := K) hBsub).trans hcutP
    have hTHP : terminalComponentCount (G := G) K B P ≤ P.card - 1 :=
      hTH.2 P hPsub hPne
    have hpos : 1 ≤ P.card := Nat.succ_le_of_lt (card_pos.mpr hPne)
    omega

/-- Host specialization: a connected traceable original side `K = B ∪ W`
with original 1-toughness has a `B`-ended spanning path. -/
lemma exists_B_ended_spanning_path_of_sides (P : AllCographSides G)
    (htough : OneTough G)
    (hconn : (G.induce ((P.B ∪ P.W : Finset V) : Set V)).Connected)
    (hp : pathCoverNumber G (P.B ∪ P.W) = 1) :
    ∃ p : GraphPath G, p.support = P.B ∪ P.W ∧ p.start ∈ P.B ∧ p.finish ∈ P.B := by
  have hBge : 2 ≤ P.B.card := by simpa [P.hBcard] using P.hm
  have h2 : 2 ≤ (P.B ∪ P.W).card :=
    hBge.trans (card_le_card (subset_union_left (s₁ := P.B)))
  have hBne : P.B.Nonempty :=
    card_pos.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hBge)
  exact exists_B_ended_spanning_path h2 P.hKcog hconn hp P.B_subset_K hBne
    (P.terminalHypothesis_of_oneTough htough)

end Nikoghosyan
