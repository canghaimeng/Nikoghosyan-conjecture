/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalCanonicalJoin

/-!
# Ordered `B`-profile layers and a real remaining-BV terminal cover

Nonterminal `B`-profiles of a `NeighborCondition` carrier form a finite
inclusion chain. Distinct profile modules are completely joined by original
edges, and a terminal sees exactly the suffix of modules whose profile
contains it. The universal common-neighbour layer is the maximum module
(profile `B`).

When a remaining mixed child has a unique realized profile, that profile
equals the child terminals `Bd`, so the child is the original complete join
`Bd ∨ W`. The ineligible cut of `W` after deleting `Bd` yields
`p(W) ≤ |Bd| + |Y| - 1`. If moreover `p(W) + 1 = |Bd|`, splicing unused
terminals through a `W`-ended cover and capping both outer ends produces an
actual `Bd`-ended spanning path of `D`. Union with isolated terminals and
the checked complete-join splice through `Y` then give a minimum `B`-ended
cover of the original carrier. No desired cover is assumed.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Ordered profile modules -/

/-- Nonterminals of `K \ B` whose `B`-profile equals `P`. -/
noncomputable def profileModule (K B P : Finset V) : Finset V :=
  (K \ B).filter (fun v => Bprofile (G := G) B v = P)

lemma mem_profileModule {K B P : Finset V} {v : V} :
    v ∈ profileModule (G := G) K B P ↔
      v ∈ K \ B ∧ Bprofile (G := G) B v = P :=
  mem_filter

/-- Realized `B`-profiles of nonterminals of `K`. -/
noncomputable def realizedProfiles (K B : Finset V) : Finset (Finset V) :=
  (K \ B).image (fun v => Bprofile (G := G) B v)

lemma mem_realizedProfiles {K B P : Finset V} :
    P ∈ realizedProfiles (G := G) K B ↔
      ∃ v ∈ K \ B, Bprofile (G := G) B v = P :=
  mem_image

lemma profileModule_subset_sdiff {K B P : Finset V} :
    profileModule (G := G) K B P ⊆ K \ B :=
  filter_subset _ _

lemma Bprofile_subset (B : Finset V) (v : V) :
    Bprofile (G := G) B v ⊆ B :=
  filter_subset _ _

/-- The universal common-neighbour layer is exactly the module of profile `B`. -/
lemma commonNeighborLayer_eq_profileModule {K B : Finset V} :
    commonNeighborLayer (G := G) K B = profileModule (G := G) K B B := by
  ext v
  constructor
  · intro hv
    have hvKB : v ∈ K \ B := (mem_filter.1 hv).1
    have hall : ∀ b ∈ B, G.Adj b v := (mem_filter.1 hv).2
    have hP : Bprofile (G := G) B v = B := by
      ext b
      constructor
      · intro hb
        exact (mem_filter.1 hb).1
      · intro hb
        exact mem_filter.2 ⟨hb, hall b hb⟩
    exact mem_filter.2 ⟨hvKB, hP⟩
  · intro hv
    have hvKB : v ∈ K \ B := (mem_filter.1 hv).1
    have hP : Bprofile (G := G) B v = B := (mem_filter.1 hv).2
    refine mem_filter.2 ⟨hvKB, ?_⟩
    intro b hb
    have : b ∈ Bprofile (G := G) B v := by simpa [hP] using hb
    exact (mem_filter.1 this).2

lemma realizedProfiles_nested {K B : Finset V}
    (hK : IsCograph G K) (hInd : Independent (G := G) B) (hBK : B ⊆ K)
    (hN : NeighborCondition (G := G) K B)
    {P Q : Finset V}
    (hP : P ∈ realizedProfiles (G := G) K B)
    (hQ : Q ∈ realizedProfiles (G := G) K B) :
    P ⊆ Q ∨ Q ⊆ P := by
  obtain ⟨v, hv, hPv⟩ := mem_image.1 hP
  obtain ⟨w, hw, hQw⟩ := mem_image.1 hQ
  have hnest := Bprofile_nested (G := G) hK hInd hBK hN hv hw
  simpa [hPv, hQw] using hnest

lemma isCompleteBetween_profileModules {K B P Q : Finset V}
    (hN : NeighborCondition (G := G) K B) (hne : P ≠ Q) :
    G.IsCompleteBetween
      (profileModule (G := G) K B P : Set V)
      (profileModule (G := G) K B Q : Set V) :=
  isCompleteBetween_of_Bprofile_ne (G := G) hN hne

/-- A terminal is adjacent to every vertex of a profile module iff it lies
in that profile. -/
lemma adj_profileModule_iff {K B P : Finset V} {b v : V}
    (hb : b ∈ B) (hv : v ∈ profileModule (G := G) K B P) :
    G.Adj b v ↔ b ∈ P := by
  have hPv : Bprofile (G := G) B v = P := (mem_filter.1 hv).2
  constructor
  · intro hadj
    have : b ∈ Bprofile (G := G) B v := mem_filter.2 ⟨hb, hadj⟩
    simpa [hPv] using this
  · intro hbP
    have : b ∈ Bprofile (G := G) B v := by simpa [hPv] using hbP
    exact (mem_filter.1 this).2

lemma profileModule_cograph {K B P : Finset V} (hK : IsCograph G K) :
    IsCograph G (profileModule (G := G) K B P) :=
  IsCograph.subset (G := G) hK
    ((profileModule_subset_sdiff (G := G)).trans sdiff_subset)

/-! ### Unique remaining profile is the full child terminal set -/

lemma Bprofile_subset_inter_of_nocross {D B : Finset V} {v : V}
    (hv : v ∈ D \ B)
    (hnocross : ∀ a ∈ D, ∀ i ∈ B \ D, ¬ G.Adj a i) :
    Bprofile (G := G) B v ⊆ B ∩ D := by
  intro b hb
  have hbB : b ∈ B := (mem_filter.1 hb).1
  have hadj : G.Adj b v := (mem_filter.1 hb).2
  have hvD : v ∈ D := (mem_sdiff.1 hv).1
  have hbD : b ∈ D := by
    by_contra hbD
    exact hnocross v hvD b (mem_sdiff.2 ⟨hbB, hbD⟩) hadj.symm
  exact mem_inter.2 ⟨hbB, hbD⟩

lemma D_sdiff_inter_eq (D B : Finset V) : D \ (B ∩ D) = D \ B := by
  ext x
  constructor
  · intro hx
    have hxD : x ∈ D := (mem_sdiff.1 hx).1
    have hxBd : x ∉ B ∩ D := (mem_sdiff.1 hx).2
    exact mem_sdiff.2 ⟨hxD, fun hB => hxBd (mem_inter.2 ⟨hB, hxD⟩)⟩
  · intro hx
    have hxD : x ∈ D := (mem_sdiff.1 hx).1
    have hxB : x ∉ B := (mem_sdiff.1 hx).2
    exact mem_sdiff.2 ⟨hxD, fun hBd => hxB (mem_inter.1 hBd).1⟩

/-- On a connected mixed child, a unique realized `B`-profile equals `B ∩ D`. -/
lemma unique_Bprofile_eq_Bd {D B : Finset V}
    (hconn : (G.induce (D : Set V)).Connected)
    (hInd : Independent (G := G) B)
    (hBd : (B ∩ D).Nonempty) (hWne : (D \ B).Nonempty)
    (hnocross : ∀ a ∈ D, ∀ i ∈ B \ D, ¬ G.Adj a i)
    (huniq : ∀ v ∈ D \ B, ∀ w ∈ D \ B,
      Bprofile (G := G) B v = Bprofile (G := G) B w) :
    ∀ v ∈ D \ B, Bprofile (G := G) B v = B ∩ D := by
  obtain ⟨v0, hv0⟩ := hWne
  let P := Bprofile (G := G) B v0
  have hPsub : P ⊆ B ∩ D :=
    Bprofile_subset_inter_of_nocross (G := G) hv0 hnocross
  have halleq : ∀ v ∈ D \ B, Bprofile (G := G) B v = P :=
    fun v hv => huniq v hv v0 hv0
  have hW' : (D \ (B ∩ D)).Nonempty := by
    rw [D_sdiff_inter_eq]
    exact ⟨v0, hv0⟩
  have hBdP : B ∩ D ⊆ P := by
    intro b hb
    have hIndD : Independent (G := G) (B ∩ D) := hInd.mono inter_subset_left
    obtain ⟨w, hw, hadj⟩ :=
      exists_nonterminal_adj (G := G) (K := D) (B := B ∩ D)
        hconn hIndD inter_subset_right hb hW'
    have hwDB : w ∈ D \ B := by
      rwa [← D_sdiff_inter_eq D B]
    have hPw : Bprofile (G := G) B w = P := halleq w hwDB
    have hbB : b ∈ B := (mem_inter.1 hb).1
    have hbP : b ∈ Bprofile (G := G) B w := mem_filter.2 ⟨hbB, hadj⟩
    simpa [hPw] using hbP
  intro v hv
  exact (halleq v hv).trans (Subset.antisymm hPsub hBdP)

lemma complete_Bd_of_unique_profile {D B : Finset V}
    (huniq : ∀ v ∈ D \ B, Bprofile (G := G) B v = B ∩ D) :
    G.IsCompleteBetween ((B ∩ D : Finset V) : Set V)
      ((D \ B : Finset V) : Set V) := by
  intro b hb w hw
  have hP : Bprofile (G := G) B w = B ∩ D := huniq w hw
  have hbP : b ∈ Bprofile (G := G) B w := by simpa [hP] using hb
  exact (mem_filter.1 hbP).2

/-! ### Slack F-cut bound `p(W) ≤ |Bd| + |Y| - 1` -/

lemma pathCoverNumber_W_le_of_slack {D Bd Y : Finset V}
    (hBd : Bd ⊆ D) (hBdne : Bd.Nonempty)
    (_hYne : Y.Nonempty)
    (hcogW : IsCograph G (D \ Bd))
    (hslack : TerminalHypothesisSlackStrong (G := G) D Bd Y.card) :
    pathCoverNumber G (D \ Bd) ≤ Bd.card + Y.card - 1 := by
  set W := D \ Bd
  set FW := ineligibleSet G W
  have hFWsub : FW ⊆ W := ineligibleSet_subset (G := G) W
  have hS : Bd ∪ FW ⊆ D :=
    union_subset hBd (hFWsub.trans sdiff_subset)
  have hSne : (Bd ∪ FW).Nonempty := hBdne.mono subset_union_left
  have hBdS : Bd ⊆ Bd ∪ FW := subset_union_left
  have hz := hslack.2 (Bd ∪ FW) hS hSne
  have hz' :
      terminalComponentCount (G := G) D Bd (Bd ∪ FW) =
        componentCount G (D \ (Bd ∪ FW)) :=
    terminalComponentCount_eq_of_B_subset (G := G) hBdS
  have hdiff : D \ (Bd ∪ FW) = W \ FW := by
    have hDW : Bd ∪ W = D := union_sdiff_of_subset hBd
    simpa [W, hDW] using
      union_sdiff_union_eq_sdiff_right (X := Bd) (Y := W) (F := FW)
        disjoint_sdiff hFWsub
  have hcut :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) hcogW
  have hcard : (Bd ∪ FW).card = Bd.card + FW.card :=
    card_union_of_disjoint (disjoint_of_subset_right hFWsub disjoint_sdiff)
  have hle : componentCount G (W \ FW) ≤ (Bd ∪ FW).card + Y.card - 1 := by
    simpa [hz', hdiff] using hz
  have hcanon : componentCount G (W \ FW) = FW.card + pathCoverNumber G W := by
    simpa [FW, W] using hcut
  omega

/-! ### Cap both outer ends of a `W`-ended path by two terminals -/

lemma exists_cap_both_ends {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p : GraphPath G) (hs : p.start ∈ A) (hf : p.finish ∈ A)
    {b1 b2 : V} (hb1 : b1 ∈ B) (hb2 : b2 ∈ B) (hne : b1 ≠ b2)
    (h1 : b1 ∉ p.support) (h2 : b2 ∉ p.support) :
    ∃ r : GraphPath G,
      r.start = b1 ∧ r.finish = b2 ∧
        r.support = insert b2 (insert b1 p.support) := by
  have hadj1 : G.Adj b1 p.start := (hAB hs hb1).symm
  let q := p.consAdj hadj1 h1
  have hfq : q.finish = p.finish := rfl
  have hadj2 : G.Adj q.finish b2 := by
    rw [hfq]
    exact hAB hf hb2
  have h2q : b2 ∉ q.support := by
    intro hb2q
    have : b2 ∈ insert b1 p.support := by
      simpa [q, GraphPath.support_consAdj] using hb2q
    rcases mem_insert.1 this with hbs | hbp
    · exact hne.symm hbs
    · exact h2 hbp
  refine ⟨q.concatAdj hadj2 h2q, rfl, rfl, ?_⟩
  simp [q, GraphPath.support_concatAdj, GraphPath.support_consAdj]

lemma eq_pair_of_card_two {T : Finset V} {b1 b2 : V}
    (hb1 : b1 ∈ T) (hb2 : b2 ∈ T) (hne : b1 ≠ b2) (hcard : T.card = 2) :
    T = ({b1, b2} : Finset V) := by
  have hsub : ({b1, b2} : Finset V) ⊆ T :=
    insert_subset hb1 (singleton_subset_iff.2 hb2)
  have hcard2 : ({b1, b2} : Finset V).card = 2 := by
    rw [card_insert_of_notMem, card_singleton]
    simp [mem_singleton, hne]
  exact (eq_of_subset_of_card_le hsub (by omega)).symm

/-- From a nonempty `W`-ended cover of `U` and `|T| = card + 1` unused
terminals complete to `W`, produce a single `T`-ended path spanning `U ∪ T`. -/
lemma exists_T_ended_path_of_W_ended_cover {W T U : Finset V}
    (hWT : G.IsCompleteBetween (W : Set V) (T : Set V))
    (hdisj : Disjoint T U)
    (pc : PathCover G U)
    (hend : ∀ p ∈ pc.paths, p.start ∈ W ∧ p.finish ∈ W)
    (hpos : 1 ≤ pc.card)
    (hT : T.card = pc.card + 1) :
    ∃ r : GraphPath G,
      r.start ∈ T ∧ r.finish ∈ T ∧ r.start ≠ r.finish ∧
        r.support = U ∪ T := by
  have aux :
      ∀ (k : ℕ) (U T : Finset V) (pc : PathCover G U),
        pc.card = k →
        1 ≤ k →
        Disjoint T U →
        (∀ p ∈ pc.paths, p.start ∈ W ∧ p.finish ∈ W) →
        T.card = k + 1 →
        G.IsCompleteBetween (W : Set V) (T : Set V) →
        ∃ r : GraphPath G,
          r.start ∈ T ∧ r.finish ∈ T ∧ r.start ≠ r.finish ∧
            r.support = U ∪ T := by
    intro k
    induction k with
    | zero =>
      intro U T pc hcard hpos hdisj hend hT hWT
      omega
    | succ k ih =>
      intro U T pc hcard hpos hdisj hend hT hWT
      by_cases hk1 : k = 0
      · have hcard1 : pc.card = 1 := by omega
        obtain ⟨p, hpseq⟩ := PathCover.exists_singleton_of_card_one pc hcard1
        have hp : p ∈ pc.paths := by simp [hpseq]
        have hs : p.start ∈ W := (hend p hp).1
        have hf : p.finish ∈ W := (hend p hp).2
        have hT2 : 2 ≤ T.card := by omega
        obtain ⟨b1, b2, hb1, hb2, hne⟩ := exists_two_mem_of_two_le_card hT2
        have h1p : b1 ∉ p.support := fun h =>
          (Finset.disjoint_left.1 hdisj hb1) ((pc.mem_iff b1).2 ⟨p, hp, h⟩)
        have h2p : b2 ∉ p.support := fun h =>
          (Finset.disjoint_left.1 hdisj hb2) ((pc.mem_iff b2).2 ⟨p, hp, h⟩)
        obtain ⟨r, hrs, hrf, hrsup⟩ :=
          exists_cap_both_ends hWT p hs hf hb1 hb2 hne h1p h2p
        have hU : p.support = U := by
          ext x
          constructor
          · intro hx
            exact (pc.mem_iff x).2 ⟨p, hp, hx⟩
          · intro hx
            obtain ⟨q, hq, hxq⟩ := (pc.mem_iff x).1 hx
            have : q = p := by simpa [hpseq] using hq
            subst this
            exact hxq
        have hTpair : T = ({b1, b2} : Finset V) :=
          eq_pair_of_card_two hb1 hb2 hne (by omega)
        refine ⟨r, by simpa [hrs] using hb1, by simpa [hrf] using hb2, ?_, ?_⟩
        · simpa [hrs, hrf] using hne
        · rw [hrsup, hU, hTpair]
          ext x
          simp [mem_union, mem_insert, mem_singleton, or_left_comm, or_assoc]
      · have h2 : 2 ≤ pc.card := by omega
        have hTne : T.Nonempty := card_pos.mp (by omega)
        obtain ⟨t, ht⟩ := hTne
        have htU : t ∉ U := Finset.disjoint_left.1 hdisj ht
        obtain ⟨pc', hcard', hend'⟩ :=
          exists_splice_two_through hWT pc h2 hend ht htU
        let T' := T.erase t
        have hdisj' : Disjoint T' (insert t U) := by
          refine disjoint_insert_right.2 ⟨notMem_erase t T, ?_⟩
          exact disjoint_of_subset_left (erase_subset t T) hdisj
        have hT' : T'.card = pc'.card + 1 := by
          rw [card_erase_of_mem ht, hcard']
          omega
        have hWT' : G.IsCompleteBetween (W : Set V) (T' : Set V) :=
          IsCompleteBetween.mono hWT subset_rfl (erase_subset t T)
        have hpos' : 1 ≤ pc'.card := by omega
        have hck : pc'.card = k := by omega
        have hposk : 1 ≤ k := by omega
        have hTk : T'.card = k + 1 := by omega
        obtain ⟨r, hrs, hrf, hne, hrsup⟩ :=
          ih (insert t U) T' pc' hck hposk hdisj' hend' hTk hWT'
        refine ⟨r, mem_of_mem_erase hrs, mem_of_mem_erase hrf, hne, ?_⟩
        rw [hrsup]
        ext x
        constructor
        · intro hx
          have hx' : x ∈ insert t U ∪ T.erase t := by simpa [T'] using hx
          rcases mem_union.1 hx' with hxL | hxR
          · rcases mem_insert.1 hxL with rfl | hxU
            · exact mem_union.2 (Or.inr ht)
            · exact mem_union.2 (Or.inl hxU)
          · exact mem_union.2 (Or.inr (mem_of_mem_erase hxR))
        · intro hx
          rcases mem_union.1 hx with hxU | hxT
          · exact mem_union.2 (Or.inl (mem_insert.2 (Or.inr hxU)))
          · by_cases hxt : x = t
            · subst hxt
              exact mem_union.2 (Or.inl (mem_insert_self _ _))
            · exact mem_union.2 (Or.inr (mem_erase.2 ⟨hxt, hxT⟩))
  exact aux pc.card U T pc rfl hpos hdisj hend hT hWT

/-! ### Minimum `Bd`-ended cover of the unique-profile join `Bd ∨ W` -/

lemma exists_min_Bd_ended_cover_of_join_excess_one {Bd W : Finset V}
    (hBdne : Bd.Nonempty)
    (hdisj : Disjoint Bd W)
    (hAB : G.IsCompleteBetween (Bd : Set V) (W : Set V))
    (hInd : Independent (G := G) Bd)
    (hp : pathCoverNumber G W + 1 = Bd.card) :
    ∃ pc : PathCover G (Bd ∪ W),
      pc.card = pathCoverNumber G (Bd ∪ W) ∧
        IsTerminalCover (G := G) Bd pc := by
  by_cases hW : W.Nonempty
  · have hpWpos : 1 ≤ pathCoverNumber G W :=
      one_le_pathCoverNumber_of_nonempty (G := G) hW
    obtain ⟨pcW, hWcard⟩ := exists_min_pathCover (G := G) W
    have hendW : ∀ p ∈ pcW.paths, p.start ∈ W ∧ p.finish ∈ W := by
      intro p hpW
      exact ⟨pcW.support_subset hpW p.start_mem_support,
        pcW.support_subset hpW p.finish_mem_support⟩
    have hT : Bd.card = pcW.card + 1 := by omega
    have hpos : 1 ≤ pcW.card := by omega
    have hBA : G.IsCompleteBetween (W : Set V) (Bd : Set V) :=
      IsCompleteBetween.symm hAB
    obtain ⟨r, hrs, hrf, _hne, hrsup⟩ :=
      exists_T_ended_path_of_W_ended_cover hBA hdisj pcW hendW hpos hT
    have hsupp : r.support = Bd ∪ W := by
      rw [hrsup, union_comm]
    refine ⟨PathCover.ofSupport r hsupp, ?_, ?_⟩
    · have hcard1 : (PathCover.ofSupport r hsupp).card = 1 :=
        PathCover.ofSupport_card r hsupp
      have hle := pathCoverNumber_le (G := G) (PathCover.ofSupport r hsupp)
      have hU : (Bd ∪ W).Nonempty := hBdne.mono subset_union_left
      have hge := one_le_pathCoverNumber_of_nonempty (G := G) hU
      omega
    · exact PathCover.ofSupport_terminal r hsupp hrs hrf
  · have hW0 : W = ∅ := not_nonempty_iff_eq_empty.1 hW
    subst hW0
    have heq : Bd ∪ (∅ : Finset V) = Bd := union_empty Bd
    obtain ⟨pc, hcard, hterm⟩ :=
      exists_min_terminalCover_subset_B (K := Bd) (B := Bd) subset_rfl hInd
    refine ⟨pc.cast heq.symm, ?_, ?_⟩
    · rw [PathCover.cast_card, hcard, heq]
    · intro p hp
      rw [PathCover.cast_paths pc heq.symm] at hp
      exact hterm p hp

/-! ### Lift unique-profile remaining-BV child to a host `B`-ended cover -/

lemma exists_min_terminalCover_of_unique_profile_child {D I B : Finset V}
    (hdisj : Disjoint D I) (hI : I ⊆ B)
    (hInd : Independent (G := G) B)
    (hnocross : ∀ a ∈ D, ∀ i ∈ I, ¬ G.Adj a i)
    (_hconn : (G.induce (D : Set V)).Connected)
    (hBd : (B ∩ D).Nonempty) (_hWne : (D \ B).Nonempty)
    (huniq : ∀ v ∈ D \ B, Bprofile (G := G) B v = B ∩ D)
    (hp : pathCoverNumber G (D \ B) + 1 = (B ∩ D).card) :
    ∃ pc : PathCover G (D ∪ I),
      pc.card = pathCoverNumber G (D ∪ I) ∧
        IsTerminalCover (G := G) B pc := by
  have hAB : G.IsCompleteBetween ((B ∩ D : Finset V) : Set V)
      ((D \ B : Finset V) : Set V) :=
    complete_Bd_of_unique_profile (G := G) huniq
  have hIndBd : Independent (G := G) (B ∩ D) := hInd.mono inter_subset_left
  have hdisjDW : Disjoint (B ∩ D) (D \ B) := by
    refine disjoint_left.2 ?_
    intro x hxBd hxW
    exact (mem_sdiff.1 hxW).2 (mem_inter.1 hxBd).1
  have hDU : (B ∩ D) ∪ (D \ B) = D := by
    ext x
    constructor
    · intro hx
      rcases mem_union.1 hx with h | h
      · exact (mem_inter.1 h).2
      · exact (mem_sdiff.1 h).1
    · intro hx
      by_cases hB : x ∈ B
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hB, hx⟩))
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hx, hB⟩))
  obtain ⟨pcD0, hcard0, hterm0⟩ :=
    exists_min_Bd_ended_cover_of_join_excess_one
      hBd hdisjDW hAB hIndBd hp
  refine exists_min_terminalCover_mixed_union_isolates hdisj hI hInd hnocross
    ⟨pcD0.cast hDU, ?_, ?_⟩
  · rw [PathCover.cast_card, hcard0]
    exact congrArg (pathCoverNumber G) hDU
  · intro p hpD
    rw [PathCover.cast_paths pcD0 hDU] at hpD
    exact IsTerminalCover.of_subset hterm0 inter_subset_left p hpD

/-- Remaining mixed child of the canonical join, unique profile, excess-one
terminals: actual minimum `B`-ended cover of `K`. -/
theorem exists_min_terminalCover_of_canonical_unique_profile
    (H : CanonicalJoinSplit (G := G))
    (s : MixedSplit (G := G) H.X H.B)
    (huniq : ∀ v ∈ s.D \ H.B, ∀ w ∈ s.D \ H.B,
      Bprofile (G := G) H.B v = Bprofile (G := G) H.B w)
    (hp : pathCoverNumber G (s.D \ H.B) + 1 = (H.B ∩ s.D).card) :
    ∃ pc : PathCover G H.K,
      pc.card = pathCoverNumber G H.K ∧
        IsTerminalCover (G := G) H.B pc := by
  have hIeq : s.I = H.X \ s.D := s.I_eq
  have hnocrossB : ∀ a ∈ s.D, ∀ i ∈ H.B \ s.D, ¬ G.Adj a i := by
    intro a ha i hi
    have hiB : i ∈ H.B := (mem_sdiff.1 hi).1
    have hiD : i ∉ s.D := (mem_sdiff.1 hi).2
    have hiX : i ∈ H.X := H.B_subset_X hiB
    have hiI : i ∈ s.I := by
      have : i ∈ H.X \ s.D := mem_sdiff.2 ⟨hiX, hiD⟩
      simpa [hIeq] using this
    exact s.hnocross a ha i hiI
  have hprof : ∀ v ∈ s.D \ H.B, Bprofile (G := G) H.B v = H.B ∩ s.D :=
    unique_Bprofile_eq_Bd (G := G) s.hconn H.hInd s.hBd s.hnonterm
      hnocrossB huniq
  obtain ⟨pcX, hcardX, htermX⟩ :=
    exists_min_terminalCover_of_unique_profile_child
      s.hdisj s.hI H.hInd s.hnocross s.hconn s.hBd s.hnonterm hprof hp
  have hXeq : s.D ∪ s.I = H.X := s.hDU
  have hcardX' : (pcX.cast hXeq).card = pathCoverNumber G H.X := by
    rw [PathCover.cast_card, hcardX]
    exact congrArg (pathCoverNumber G) hXeq
  have htermX' : IsTerminalCover (G := G) H.B (pcX.cast hXeq) := by
    intro p hpX
    rw [PathCover.cast_paths pcX hXeq] at hpX
    exact htermX p hpX
  by_cases hpK : 2 ≤ pathCoverNumber G H.K
  · have hTH' : TerminalHypothesis (G := G) (H.X ∪ H.Y) H.B := by
      simpa [H.union_X_Y] using H.hTH
    have hcog' : IsCograph G (H.X ∪ H.Y) := by
      simpa [H.union_X_Y] using H.hcog
    have hpK' : 2 ≤ pathCoverNumber G (H.X ∪ H.Y) := by
      simpa [H.union_X_Y] using hpK
    have hdom : H.Y.card < pathCoverNumber G H.X :=
      dominant_mixed_child_of_slack_zero H.X_nonempty H.hYne H.complete_X_Y
        hcog' H.B_subset_X hTH' hpK'
    have hjoin :=
      exists_min_terminalCover_complete_join H.X_nonempty H.hYne H.complete_X_Y
        H.B_subset_X hdom ⟨pcX.cast hXeq, hcardX', htermX'⟩
    have hKeq : H.X ∪ H.Y = H.K := H.union_X_Y
    obtain ⟨pc, hcard, hterm⟩ := hjoin
    refine ⟨pc.cast hKeq, ?_, ?_⟩
    · rw [PathCover.cast_card, hcard]
      exact congrArg (pathCoverNumber G) hKeq
    · intro p hpKs
      rw [PathCover.cast_paths pc hKeq] at hpKs
      exact hterm p hpKs
  · have hp1 : pathCoverNumber G H.K = 1 := by
      have hpos : 1 ≤ pathCoverNumber G H.K :=
        one_le_pathCoverNumber_of_nonempty (G := G) (H.hBne.mono H.hBK)
      omega
    exact exists_min_terminalCover_of_pathCoverNumber_eq_one
      H.two_le_card H.hcog H.hconn hp1 H.hBK H.hBne H.hTH

end Nikoghosyan
