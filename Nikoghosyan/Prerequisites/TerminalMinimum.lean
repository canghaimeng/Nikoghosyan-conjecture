/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalPositiveSlack

/-!
# General ordinary minimum B-ended cover under RepairedTerminalHypothesis

All-terminal carriers use the singleton cover. A disconnected mixed carrier
reduces by the actual MixedSplit to a strictly smaller connected child.
A connected traceable carrier uses the existing B-ended spanning path.
A connected nontraceable carrier is a complete join; independence places
every terminal in the unique dominant child, the complementary connectors
are merged through the positive-slack deficit bound, and the resulting
ordinary cover has deficit zero.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma TerminalHypothesisSlackStrong.of_repaired {K B : Finset V}
    (h : TerminalHypothesis (G := G) K B) {t : ℕ} (ht : t = 0) :
    TerminalHypothesisSlackStrong (G := G) K B t := by
  subst ht
  exact TerminalHypothesisSlackStrong.of_terminalHypothesis h

lemma exists_min_terminalCover_of_repaired_card :
    ∀ (n : ℕ) (K B : Finset V),
      K.card = n →
      RepairedTerminalHypothesis (G := G) K B →
      B.Nonempty →
      ∃ pc : PathCover G K,
        pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro K B hKn hrep hBne
    rcases hrep with ⟨hcog, hBK, hInd, hTH, hN⟩
    by_cases hKB : K ⊆ B
    · exact exists_min_terminalCover_subset_B hKB hInd
    · have hVne : (K \ B).Nonempty := by
        refine nonempty_iff_ne_empty.2 ?_
        intro hempty
        exact hKB (sdiff_eq_empty_iff_subset.1 hempty)
      by_cases hconn : (G.induce (K : Set V)).Connected
      · by_cases hp1 : pathCoverNumber G K ≤ 1
        · have hpos := one_le_pathCoverNumber_of_nonempty (G := G) (hBne.mono hBK)
          have hp : pathCoverNumber G K = 1 := by omega
          by_cases h2 : 2 ≤ K.card
          · exact exists_min_terminalCover_of_pathCoverNumber_eq_one
              h2 hcog hconn hp hBK hBne hTH
          · have hcard1 : K.card = 1 := by
              have : 1 ≤ K.card := card_pos.2 (hBne.mono hBK)
              omega
            obtain ⟨x, hx⟩ := card_eq_one.1 hcard1
            have hxB : x ∈ B := by
              obtain ⟨b, hb⟩ := hBne
              have hbK : b ∈ K := hBK hb
              have : b = x := by simpa [hx] using hbK
              simpa [this] using hb
            refine exists_min_terminalCover_subset_B ?_ hInd
            simpa [hx] using singleton_subset_iff.2 hxB
        · have hp2 : 2 ≤ pathCoverNumber G K := by omega
          have h2card : 2 ≤ K.card :=
            hp2.trans (pathCoverNumber_le_card (G := G) K)
          obtain ⟨Praw, Qraw, hPrawsub, hQrawsub, hPrawne, hQrawne, hdisjraw,
              hcoverraw, hABraw, hPrawcard, hQrawcard⟩ :=
            Cograph.exists_complete_join_on (G := G) (Cograph.isCograph_iff.2 hcog)
              hconn h2card
          have hBside : B ⊆ Praw ∨ B ⊆ Qraw :=
            Independent.subset_join_side hABraw hInd (by simpa [hcoverraw] using hBK)
          obtain ⟨P0, Q0, hPsub, hQsub, hPne, hQne, hdisj, hcover, hAB,
              hPcard, hQcard, hBP⟩ :
              ∃ P Q : Finset V, P ⊆ K ∧ Q ⊆ K ∧ P.Nonempty ∧ Q.Nonempty ∧
                Disjoint P Q ∧ P ∪ Q = K ∧
                  G.IsCompleteBetween (P : Set V) (Q : Set V) ∧
                    P.card < K.card ∧ Q.card < K.card ∧ B ⊆ P := by
            rcases hBside with hP | hQ
            · exact ⟨Praw, Qraw, hPrawsub, hQrawsub, hPrawne, hQrawne, hdisjraw,
                hcoverraw, hABraw, hPrawcard, hQrawcard, hP⟩
            · exact ⟨Qraw, Praw, hQrawsub, hPrawsub, hQrawne, hPrawne, hdisjraw.symm,
                by rw [union_comm, hcoverraw],
                fun {q} hq {p} hp => (hABraw hp hq).symm,
                hQrawcard, hPrawcard, hQ⟩
          have hjoin : P0 ∪ Q0 = K := hcover
          have hPcog : IsCograph G P0 := isCograph_subset hcog hPsub
          have hN_P : NeighborCondition (G := G) P0 B := NeighborCondition.mono hN hPsub
          have hTHK : TerminalHypothesis (G := G) (P0 ∪ Q0) B := by
            simpa [hjoin] using hTH
          have hTH_P : TerminalHypothesisSlackStrong (G := G) P0 B Q0.card :=
            terminalHypothesisSlackStrong_join_child_of_terminal hQne hdisj hBP hTHK
          have htP : 1 ≤ Q0.card := Nat.succ_le_of_lt (card_pos.2 hQne)
          have hQnotdom : ¬ P0.card < pathCoverNumber G Q0 :=
            not_dominant_B_free_join_side hPne hQne hAB
              (by simpa [hjoin] using hcog) hBP hBne hTHK
          have hPdom : Q0.card < pathCoverNumber G P0 := by
            have hpjoin := pathCoverNumber_complete_join hPne hQne hAB
            have hnot1 : pathCoverNumber G (P0 ∪ Q0) ≠ 1 := by
              simpa [hjoin] using (Nat.ne_of_gt (Nat.succ_le_iff.mp hp2))
            have hQle : pathCoverNumber G Q0 ≤ P0.card := Nat.le_of_not_gt hQnotdom
            by_contra hPle
            have hP0sub : pathCoverNumber G P0 - Q0.card = 0 :=
              Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hPle)
            have hQ0sub : pathCoverNumber G Q0 - P0.card = 0 :=
              Nat.sub_eq_zero_of_le hQle
            have : pathCoverNumber G (P0 ∪ Q0) = 1 := by
              rw [hpjoin, hP0sub, hQ0sub]; simp
            exact hnot1 this
          have hPcover :
              ∃ pc : PathCover G P0,
                pc.card = pathCoverNumber G P0 ∧
                  pc.endpointDeficit B ≤ 2 * Q0.card - 1 := by
            by_cases hPconn : (G.induce (P0 : Set V)).Connected
            · exact exists_min_cover_deficit_le_of_slackStrong
                hPcog hPconn hBP hBne hInd hN_P htP hTH_P
            · by_cases hBV : ∃ b v, b ∈ B ∧ v ∈ P0 \ B ∧ G.Adj b v
              · obtain ⟨b, v, hb, hv, hadj⟩ := hBV
                obtain ⟨s⟩ :=
                  exists_mixedSplit_of_BV (K := P0) (B := B) hBP hN_P hb hv hadj
                have hIeq : s.I = P0 \ s.D := s.I_eq
                have hI : P0 \ s.D ⊆ B := by simpa [hIeq] using s.hI
                have hDlt : s.D.card < n := by
                  have : s.D.card ≤ P0.card := card_le_card s.hDsub
                  omega
                have hDcog : IsCograph G s.D := isCograph_subset hPcog s.hDsub
                have hN_D : NeighborCondition (G := G) s.D (B ∩ s.D) :=
                  NeighborCondition.restrict_inter hN_P s.hDsub
                have hTH_D : TerminalHypothesisSlackStrong (G := G) s.D (B ∩ s.D)
                    Q0.card :=
                  TerminalHypothesisSlackStrong.restrict_mixed hBP s.hDsub hI
                    (by simpa [hIeq] using s.hnocross) hTH_P
                have hIndD : Independent (G := G) (B ∩ s.D) :=
                  hInd.mono inter_subset_left
                obtain ⟨pcD, hDcard', hDdef⟩ :=
                  exists_min_cover_deficit_le_of_slackStrong
                    hDcog s.hconn inter_subset_right s.hBd hIndD hN_D htP hTH_D
                have hDdefB : pcD.endpointDeficit B ≤ pcD.endpointDeficit (B ∩ s.D) :=
                  PathCover.endpointDeficit_anti inter_subset_left pcD
                obtain ⟨pcI, hIcard, hIterm⟩ :=
                  exists_min_terminalCover_subset_B (K := s.I) (B := B) s.hI hInd
                have hIdef : pcI.endpointDeficit B = 0 :=
                  PathCover.deficit_eq_zero_of_terminal pcI hIterm
                let pcP := Cograph.PathCover.unionDisjoint s.hdisj pcD pcI
                refine ⟨pcP.cast s.hDU, ?_, ?_⟩
                · have hsum := Cograph.PathCover.unionDisjoint_card s.hdisj pcD pcI
                  have hpU :=
                    Cograph.pathCoverNumber_disjoint_union (G := G) s.hdisj s.hnocross
                  have hpP :
                      pathCoverNumber G P0 =
                        pathCoverNumber G s.D + pathCoverNumber G s.I := by
                    convert hpU
                    exact s.hDU.symm
                  rw [PathCover.cast_card, hsum, hDcard', hIcard, hpP]
                · have hdefU :=
                    PathCover.endpointDeficit_unionDisjoint (B := B) s.hdisj pcD pcI
                  rw [PathCover.cast_endpointDeficit_slack, hdefU, hIdef]
                  exact hDdefB.trans hDdef
              · let W := P0 \ B
                have hPW : P0 = B ∪ W := (union_sdiff_of_subset hBP).symm
                have hanti : ∀ b ∈ B, ∀ w ∈ W, ¬ G.Adj b w := by
                  intro b hb w hw hadj
                  exact hBV ⟨b, w, hb, hw, hadj⟩
                obtain ⟨pcP, hPcard', hPdef⟩ :=
                  exists_min_cover_of_noBV hPW disjoint_sdiff hanti hInd
                have hpW : pathCoverNumber G W ≤ Q0.card - 1 :=
                  pathCoverNumber_W_le_of_noBV hPW disjoint_sdiff hanti hPcog htP hTH_P
                refine ⟨pcP, hPcard', ?_⟩
                have : 2 * pathCoverNumber G W ≤ 2 * Q0.card - 2 := by omega
                omega
          obtain ⟨pcP, hPmin, hPdef⟩ := hPcover
          have hendP : ∀ p ∈ pcP.paths, p.start ∈ P0 ∧ p.finish ∈ P0 :=
            fun p hp => pcP.ends_subset_of_support hp
          obtain ⟨pcK, hKcard, _, hKdef⟩ :=
            exists_merge_all_connectors (A := P0) (Q := Q0) (B := B) (t := 0)
              hAB hPdom pcP hPmin hendP (by simpa using hPdef)
          refine ⟨pcK.cast hjoin, ?_, ?_⟩
          · have hpjoin := pathCoverNumber_complete_join hPne hQne hAB
            have hQle : pathCoverNumber G Q0 ≤ P0.card := Nat.le_of_not_gt hQnotdom
            have hpKeq : pathCoverNumber G K = pathCoverNumber G P0 - Q0.card := by
              have hpPsub : 1 ≤ pathCoverNumber G P0 - Q0.card :=
                Nat.succ_le_of_lt (Nat.sub_pos_of_lt hPdom)
              have hpjoin' := hpjoin
              rw [← hjoin, hpjoin', Nat.sub_eq_zero_of_le hQle,
                Nat.max_eq_left (Nat.zero_le _), Nat.max_eq_right hpPsub]
            rw [PathCover.cast_card, hKcard, hpKeq]
          · have h0 : (pcK.cast hjoin).endpointDeficit B = 0 := by
              rw [PathCover.cast_endpointDeficit_slack]
              have : 2 * (0 : ℕ) - 1 = 0 := rfl
              have : pcK.endpointDeficit B ≤ 0 := by simpa [this] using hKdef
              omega
            exact PathCover.terminalCover_of_deficit_eq_zero _ h0
      · obtain ⟨s⟩ :=
          exists_mixedSplit (G := G) hBK hN hTH.1 hVne
        have hIeq : s.I = K \ s.D := s.I_eq
        have hI : K \ s.D ⊆ B := by simpa [hIeq] using s.hI
        have hrepD : RepairedTerminalHypothesis (G := G) s.D (B ∩ s.D) :=
          repairedTerminalHypothesis_mixed ⟨hcog, hBK, hInd, hTH, hN⟩
            s.hDsub hI (by simpa [hIeq] using s.hnocross) s.hconn s.hBd
        have hDlt : s.D.card < n := by
          have hss : s.D ⊂ K := by
            refine Finset.ssubset_iff_subset_ne.2 ⟨s.hDsub, ?_⟩
            intro hDeq
            have : (G.induce (K : Set V)).Connected := by
              rw [← hDeq]
              exact s.hconn
            exact hconn this
          have : s.D.card < K.card := card_lt_card hss
          omega
        obtain ⟨pcD, hDcard, hDterm⟩ :=
          ih s.D.card hDlt s.D (B ∩ s.D) rfl hrepD s.hBd
        have hDtermB : IsTerminalCover (G := G) B pcD :=
          IsTerminalCover.of_subset hDterm inter_subset_left
        obtain ⟨pc, hcard, hterm⟩ :=
          exists_min_terminalCover_mixed_union_isolates
            s.hdisj s.hI hInd s.hnocross ⟨pcD, hDcard, hDtermB⟩
        refine ⟨pc.cast s.hDU, ?_, ?_⟩
        · rw [PathCover.cast_card, hcard]
          exact congrArg (pathCoverNumber G) s.hDU
        · intro p hp
          rw [PathCover.cast_paths pc s.hDU] at hp
          exact hterm p hp

theorem exists_general_min_terminalCover {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hBne : B.Nonempty) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc :=
  exists_min_terminalCover_of_repaired_card K.card K B rfl hrep hBne

end Nikoghosyan
