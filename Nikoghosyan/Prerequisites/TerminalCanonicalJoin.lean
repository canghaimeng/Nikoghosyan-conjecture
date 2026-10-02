/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalNoBVJoinSpectrum

/-!
# Canonical common-neighbour join of a connected mixed carrier

On a connected mixed cograph `K` with independent terminals `B`, nested
`B`-neighbourhoods inside `K \ B` produce a nonempty universal common
neighbour layer

  `Y = { v ∈ K \ B | ∀ b ∈ B, G.Adj b v }`.

The complement `X = K \ Y` contains `B`, and `Y` is completely joined to
`X` by original edges: terminals see every vertex of `Y` by definition,
and a nonterminal `x ∈ X \ B` misses some `b ∈ B` while every `y ∈ Y`
sees that `b`, so `NeighborCondition` forces `x–y`.

This is an original-edge split, not a supplied cotree. If `X` has no
`B`–`(X \ B)` edge, the checked `NoBVJoinBase` supplies a minimum
`B`-ended cover and the full interval spectrum. If a `B`–`(X \ B)` edge
remains, `MixedSplit` isolates terminal singletons of `X` with child
terminals `B ∩ D`, and deleting `Y` leaves strong slack of token `|Y|`
on both `X` and `D`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Neighbour rows and the universal common-neighbour layer -/

/-- Original neighbourhood of a terminal inside the nonterminals. -/
noncomputable def neighborRow (K B : Finset V) (b : V) : Finset V :=
  (K \ B).filter (fun x => G.Adj b x)

/-- Vertices of `K \ B` adjacent to every terminal. -/
noncomputable def commonNeighborLayer (K B : Finset V) : Finset V :=
  (K \ B).filter (fun v => ∀ b ∈ B, G.Adj b v)

lemma mem_neighborRow {K B : Finset V} {b x : V} :
    x ∈ neighborRow (G := G) K B b ↔ x ∈ K \ B ∧ G.Adj b x :=
  mem_filter

lemma mem_commonNeighborLayer {K B : Finset V} {v : V} :
    v ∈ commonNeighborLayer (G := G) K B ↔
      v ∈ K \ B ∧ ∀ b ∈ B, G.Adj b v :=
  mem_filter

lemma neighborRow_eq_filter {K B : Finset V} {b : V} :
    neighborRow (G := G) K B b = (K \ B).filter (fun x => G.Adj b x) :=
  rfl

/-- A connected mixed carrier of order at least two gives every terminal
an original nonterminal neighbour, because independence forbids a
`B`–`B` first step. -/
lemma exists_nonterminal_adj {K B : Finset V} {b : V}
    (hconn : (G.induce (K : Set V)).Connected)
    (hInd : Independent (G := G) B) (hBK : B ⊆ K)
    (hb : b ∈ B) (hVne : (K \ B).Nonempty) :
    ∃ v ∈ K \ B, G.Adj b v := by
  obtain ⟨v0, hv0⟩ := hVne
  have hbK : b ∈ K := hBK hb
  have hv0K : v0 ∈ K := (mem_sdiff.1 hv0).1
  have hne : b ≠ v0 := fun h => (mem_sdiff.1 hv0).2 (h ▸ hb)
  have hpre : (G.induce (K : Set V)).Preconnected :=
    ((connected_iff _).1 hconn).1
  have hreach : (G.induce (K : Set V)).Reachable ⟨b, hbK⟩ ⟨v0, hv0K⟩ :=
    hpre ⟨b, hbK⟩ ⟨v0, hv0K⟩
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => exact (hne rfl).elim
  | cons hadj q =>
      rename_i mid
      have hadjG : G.Adj b mid.val := by simpa [induce_adj] using hadj
      refine ⟨mid.val, mem_sdiff.2 ⟨mid.property, ?_⟩, hadjG⟩
      exact hInd.not_mem_of_adj hb hadjG.symm

lemma neighborRow_nonempty {K B : Finset V} {b : V}
    (hconn : (G.induce (K : Set V)).Connected)
    (hInd : Independent (G := G) B) (hBK : B ⊆ K)
    (hb : b ∈ B) (hVne : (K \ B).Nonempty) :
    (neighborRow (G := G) K B b).Nonempty := by
  obtain ⟨v, hv, hadj⟩ := exists_nonterminal_adj hconn hInd hBK hb hVne
  exact ⟨v, mem_filter.2 ⟨hv, hadj⟩⟩

/-- Nested `B`-rows: a minimum-cardinality row is contained in every row. -/
lemma exists_min_neighborRow {K B : Finset V}
    (hK : IsCograph G K) (hInd : Independent (G := G) B) (hBK : B ⊆ K)
    (hN : NeighborCondition (G := G) K B) (hBne : B.Nonempty) :
    ∃ b0 ∈ B, ∀ b ∈ B,
      neighborRow (G := G) K B b0 ⊆ neighborRow (G := G) K B b := by
  obtain ⟨b0, hb0, hmin⟩ :=
    B.exists_min_image (fun b => (neighborRow (G := G) K B b).card) hBne
  refine ⟨b0, hb0, ?_⟩
  intro b hb
  have hnest :=
    neighborSet_nested (G := G) hK hInd hBK hN hb0 hb
  rcases hnest with hle | hge
  · simpa [neighborRow] using hle
  · have hge' : neighborRow (G := G) K B b ⊆ neighborRow (G := G) K B b0 := by
      simpa [neighborRow] using hge
    have hcard := hmin b hb
    have heq := eq_of_subset_of_card_le hge' hcard
    exact heq.symm.subset

lemma commonNeighborLayer_nonempty {K B : Finset V}
    (hK : IsCograph G K) (hInd : Independent (G := G) B) (hBK : B ⊆ K)
    (hN : NeighborCondition (G := G) K B)
    (hconn : (G.induce (K : Set V)).Connected)
    (hBne : B.Nonempty) (hVne : (K \ B).Nonempty) :
    (commonNeighborLayer (G := G) K B).Nonempty := by
  obtain ⟨b0, hb0, hmin⟩ :=
    exists_min_neighborRow (G := G) hK hInd hBK hN hBne
  obtain ⟨v, hv⟩ := neighborRow_nonempty (G := G) hconn hInd hBK hb0 hVne
  have hvKB : v ∈ K \ B := (mem_filter.1 hv).1
  have hall : ∀ b ∈ B, G.Adj b v := by
    intro b hb
    have hvb : v ∈ neighborRow (G := G) K B b := hmin b hb hv
    exact (mem_filter.1 hvb).2
  exact ⟨v, mem_filter.2 ⟨hvKB, hall⟩⟩

lemma two_le_card_of_mixed {K B : Finset V}
    (hBK : B ⊆ K) (hBne : B.Nonempty) (hVne : (K \ B).Nonempty) :
    2 ≤ K.card := by
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨v, hv⟩ := hVne
  have hne : b ≠ v := fun h => (mem_sdiff.1 hv).2 (h ▸ hb)
  have hpair : ({b, v} : Finset V) ⊆ K :=
    insert_subset (hBK hb) (singleton_subset_iff.2 (mem_sdiff.1 hv).1)
  have hcard2 : ({b, v} : Finset V).card = 2 := by
    rw [card_insert_of_notMem, card_singleton]
    simp [mem_singleton, hne]
  exact hcard2.symm.le.trans (card_le_card hpair)

/-! ### Canonical join split -/

/-- Original-edge complete join `K = X ∨ Y` whose right side is the
universal common-neighbour layer of independent terminals `B ⊆ X`. -/
structure CanonicalJoinSplit (G : SimpleGraph V) where
  K : Finset V
  B : Finset V
  hrep : RepairedTerminalHypothesis (G := G) K B
  hconn : (G.induce (K : Set V)).Connected
  hBne : B.Nonempty
  hVne : (K \ B).Nonempty

namespace CanonicalJoinSplit

variable (H : CanonicalJoinSplit (G := G))

lemma hcog : IsCograph G H.K := H.hrep.1

lemma hBK : H.B ⊆ H.K := H.hrep.2.1

lemma hInd : Independent (G := G) H.B := H.hrep.2.2.1

lemma hTH : TerminalHypothesis (G := G) H.K H.B := H.hrep.2.2.2.1

lemma hN : NeighborCondition (G := G) H.K H.B := H.hrep.2.2.2.2

noncomputable def Y : Finset V := commonNeighborLayer (G := G) H.K H.B

noncomputable def X : Finset V := H.K \ H.Y

lemma Y_eq : H.Y = commonNeighborLayer (G := G) H.K H.B := rfl

lemma X_eq : H.X = H.K \ H.Y := rfl

lemma Y_subset_sdiff : H.Y ⊆ H.K \ H.B := filter_subset _ _

lemma Y_subset_K : H.Y ⊆ H.K :=
  (H.Y_subset_sdiff).trans sdiff_subset

lemma hYne : H.Y.Nonempty :=
  commonNeighborLayer_nonempty (G := G) H.hcog H.hInd H.hBK H.hN
    H.hconn H.hBne H.hVne

lemma B_subset_X : H.B ⊆ H.X := by
  intro b hb
  refine mem_sdiff.2 ⟨H.hBK hb, ?_⟩
  intro hY
  exact (mem_sdiff.1 (H.Y_subset_sdiff hY)).2 hb

lemma disjoint_X_Y : Disjoint H.X H.Y :=
  disjoint_comm.1 (disjoint_sdiff : Disjoint H.Y H.X)

lemma union_X_Y : H.X ∪ H.Y = H.K :=
  sdiff_union_of_subset H.Y_subset_K

lemma X_nonempty : H.X.Nonempty := H.hBne.mono H.B_subset_X

lemma mem_Y {y : V} : y ∈ H.Y ↔ y ∈ H.K \ H.B ∧ ∀ b ∈ H.B, G.Adj b y :=
  mem_filter

lemma adj_B_Y {b y : V} (hb : b ∈ H.B) (hy : y ∈ H.Y) : G.Adj b y :=
  (H.mem_Y.1 hy).2 b hb

/-- `Y` is completely joined to `X` by original edges. -/
lemma complete_X_Y : G.IsCompleteBetween (H.X : Set V) (H.Y : Set V) := by
  intro x hx y hy
  have hyY : y ∈ H.K \ H.B := (H.mem_Y.1 hy).1
  have hall : ∀ b ∈ H.B, G.Adj b y := (H.mem_Y.1 hy).2
  have hxK : x ∈ H.K := (mem_sdiff.1 hx).1
  have hxnotY : x ∉ H.Y := (mem_sdiff.1 hx).2
  by_cases hxB : x ∈ H.B
  · exact hall x hxB
  · have hxKB : x ∈ H.K \ H.B := mem_sdiff.2 ⟨hxK, hxB⟩
    have hnotall : ¬ ∀ b ∈ H.B, G.Adj b x := by
      intro hallx
      exact hxnotY (mem_filter.2 ⟨hxKB, hallx⟩)
    obtain ⟨b, hb, hnbx⟩ : ∃ b ∈ H.B, ¬ G.Adj b x := by
      by_contra hnone
      refine hnotall ?_
      intro b hb
      by_contra hnb
      exact hnone ⟨b, hb, hnb⟩
    have hyb : G.Adj b y := hall b hb
    exact (H.hN hb hyY hxKB hyb hnbx).symm

lemma W_eq : H.X \ H.B = (H.K \ H.B) \ H.Y := by
  ext w
  constructor
  · intro hw
    have hwX := mem_sdiff.1 hw
    have hwK := mem_sdiff.1 hwX.1
    exact mem_sdiff.2 ⟨mem_sdiff.2 ⟨hwK.1, hwX.2⟩, hwK.2⟩
  · intro hw
    have hwKB := mem_sdiff.1 hw
    have hwK := mem_sdiff.1 hwKB.1
    exact mem_sdiff.2 ⟨mem_sdiff.2 ⟨hwK.1, hwKB.2⟩, hwK.2⟩

lemma two_le_card : 2 ≤ H.K.card :=
  two_le_card_of_mixed H.hBK H.hBne H.hVne

lemma X_cograph : IsCograph G H.X :=
  IsCograph.subset (G := G) H.hcog sdiff_subset

lemma Y_cograph : IsCograph G H.Y :=
  IsCograph.subset (G := G) H.hcog H.Y_subset_K

lemma card_X_lt : H.X.card < H.K.card := by
  obtain ⟨y, hy⟩ := H.hYne
  have hyK : y ∈ H.K := H.Y_subset_K hy
  have hyX : y ∉ H.X := fun hX => (mem_sdiff.1 hX).2 hy
  have hlt : (H.K.erase y).card < H.K.card := card_erase_lt_of_mem hyK
  have hsub : H.X ⊆ H.K.erase y := by
    intro x hx
    exact mem_erase.2 ⟨fun h => hyX (h ▸ hx), (mem_sdiff.1 hx).1⟩
  exact (card_le_card hsub).trans_lt hlt

/-- Deleting the connector layer yields strong slack of token `|Y|`. -/
lemma slack_X :
    TerminalHypothesisSlackStrong (G := G) H.X H.B H.Y.card := by
  have hunion : H.X ∪ H.Y = H.K := H.union_X_Y
  simpa [hunion] using
    terminalHypothesisSlackStrong_join_child_of_terminal
      (G := G) H.hYne H.disjoint_X_Y H.B_subset_X
      (by simpa [hunion] using H.hTH)

end CanonicalJoinSplit

lemma NeighborCondition.restrict_of_subset {K X B : Finset V}
    (hN : NeighborCondition (G := G) K B) (hX : X ⊆ K) :
    NeighborCondition (G := G) X B := by
  intro b v w hb hv hw hbv hbw
  have hvK : v ∈ K \ B :=
    mem_sdiff.2 ⟨hX (mem_sdiff.1 hv).1, (mem_sdiff.1 hv).2⟩
  have hwK : w ∈ K \ B :=
    mem_sdiff.2 ⟨hX (mem_sdiff.1 hw).1, (mem_sdiff.1 hw).2⟩
  exact hN hb hvK hwK hbv hbw

namespace CanonicalJoinSplit

variable (H : CanonicalJoinSplit (G := G))

lemma hN_X : NeighborCondition (G := G) H.X H.B :=
  NeighborCondition.restrict_of_subset H.hN sdiff_subset

/-! ### No remaining `B`–`(X \ B)` edge: reduce to `NoBVJoinBase` -/

lemma disjoint_B_W : Disjoint H.B (H.X \ H.B) := disjoint_sdiff

lemma disjoint_B_Y : Disjoint H.B H.Y :=
  disjoint_of_subset_right H.Y_subset_sdiff disjoint_sdiff

lemma disjoint_W_Y : Disjoint (H.X \ H.B) H.Y :=
  disjoint_of_subset_left sdiff_subset H.disjoint_X_Y

lemma union_B_W_Y : H.B ∪ (H.X \ H.B) ∪ H.Y = H.K := by
  have hXW : H.B ∪ (H.X \ H.B) = H.X := union_sdiff_of_subset H.B_subset_X
  rw [hXW, H.union_X_Y]

lemma complete_BW_Y :
    G.IsCompleteBetween ((H.B ∪ (H.X \ H.B) : Finset V) : Set V)
      (H.Y : Set V) := by
  have hEq : (H.B ∪ (H.X \ H.B) : Finset V) = H.X :=
    union_sdiff_of_subset H.B_subset_X
  simpa [hEq] using H.complete_X_Y

/-- Package the canonical split as a no-BV complete-join base. -/
noncomputable def toNoBVJoinBase
    (hanti : ∀ b ∈ H.B, ∀ w ∈ H.X \ H.B, ¬ G.Adj b w)
    (hpK : 2 ≤ pathCoverNumber G H.K) :
    NoBVJoinBase (G := G) where
  B := H.B
  W := H.X \ H.B
  Y := H.Y
  hBne := H.hBne
  hYne := H.hYne
  hdisjBW := H.disjoint_B_W
  hdisjBY := H.disjoint_B_Y
  hdisjWY := H.disjoint_W_Y
  hInd := H.hInd
  hanti := hanti
  hXY := H.complete_BW_Y
  hKcog := H.union_B_W_Y ▸ H.hcog
  hTH := H.union_B_W_Y ▸ H.hTH
  hpK := H.union_B_W_Y ▸ hpK

lemma toNoBVJoinBase_K
    (hanti : ∀ b ∈ H.B, ∀ w ∈ H.X \ H.B, ¬ G.Adj b w)
    (hpK : 2 ≤ pathCoverNumber G H.K) :
    (H.toNoBVJoinBase hanti hpK).K = H.K := by
  simp only [NoBVJoinBase.K, CanonicalJoinSplit.toNoBVJoinBase]
  exact H.union_B_W_Y

lemma exists_min_terminalCover_noBV
    (hanti : ∀ b ∈ H.B, ∀ w ∈ H.X \ H.B, ¬ G.Adj b w)
    (hpK : 2 ≤ pathCoverNumber G H.K) :
    ∃ pc : PathCover G H.K,
      pc.card = pathCoverNumber G H.K ∧
        IsTerminalCover (G := G) H.B pc := by
  let H0 := H.toNoBVJoinBase hanti hpK
  obtain ⟨pc, hcard, hterm⟩ := H0.exists_min_terminalCover_noBV
  have hKeq : H0.K = H.K := H.toNoBVJoinBase_K hanti hpK
  refine ⟨pc.cast hKeq, ?_, ?_⟩
  · rw [PathCover.cast_card, hcard]
    exact congrArg (pathCoverNumber G) hKeq
  · intro p hp
    rw [PathCover.cast_paths pc hKeq] at hp
    exact hterm p hp

lemma exists_terminalCover_noBV_spectrum {q : ℕ}
    (hanti : ∀ b ∈ H.B, ∀ w ∈ H.X \ H.B, ¬ G.Adj b w)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hlo : pathCoverNumber G H.K ≤ q)
    (hhi : q + pathCoverNumber G (H.K \ H.B) ≤ H.B.card) :
    ∃ pc : PathCover G H.K,
      pc.card = q ∧ IsTerminalCover (G := G) H.B pc := by
  let H0 := H.toNoBVJoinBase hanti hpK
  have hKeq : H0.K = H.K := H.toNoBVJoinBase_K hanti hpK
  have hBeq : H0.B = H.B := by
    dsimp [H0]
    rfl
  have hKsdiff : H0.K \ H0.B = H.K \ H.B := by
    rw [hKeq, hBeq]
  have hlo' : pathCoverNumber G H0.K ≤ q := by
    rwa [hKeq]
  have hhi' : q + pathCoverNumber G (H0.K \ H0.B) ≤ H0.B.card := by
    rw [hKsdiff]
    exact hhi
  obtain ⟨pc, hcard, hterm⟩ := H0.exists_terminalCover_noBV_spectrum hlo' hhi'
  refine ⟨pc.cast hKeq, ?_, ?_⟩
  · rw [PathCover.cast_card]
    exact hcard
  · intro p hp
    rw [PathCover.cast_paths pc hKeq] at hp
    exact hterm p hp

/-! ### Remaining `B`–`(X \ B)` edges: mixed split of the slack child -/

lemma terminalComponentCount_empty_eq_zero_of_BV
    {b w : V} (hb : b ∈ H.B) (hw : w ∈ H.X \ H.B) (hadj : G.Adj b w) :
    terminalComponentCount (G := G) H.X H.B ∅ = 0 := by
  have hBKX : H.B ⊆ H.X := H.B_subset_X
  have hwX : w ∈ H.X := (mem_sdiff.1 hw).1
  have hwX0 : w ∈ H.X \ (∅ : Finset V) := by simp [hwX]
  have hbX0 : b ∈ H.X \ (∅ : Finset V) := by simp [hBKX hb]
  have hsub : H.X ⊆ H.X \ (∅ : Finset V) := by simp
  haveI : Fintype
      { C : (G.induce ((H.X \ (∅ : Finset V) : Finset V) : Set V)).ConnectedComponent //
        IsFreeComponent (G := G) H.X H.B ∅ C } := inferInstance
  unfold terminalComponentCount
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_eq_zero_iff.2 ⟨fun C => ?_⟩
  have hfree : IsFreeComponent (G := G) H.X H.B ∅ C.1 := C.2
  obtain ⟨x, hx⟩ := componentFinset_nonempty (G := G) C.1
  have hxX0 : x ∈ H.X \ (∅ : Finset V) := (mem_filter.1 hx).1
  have hxX : x ∈ H.X := by simpa using hxX0
  have hxnotB : x ∉ H.B := by
    intro hB
    have : x ∈ componentFinset G (H.X \ (∅ : Finset V)) C.1 ∩
        (H.B \ (∅ : Finset V)) :=
      mem_inter.2 ⟨hx, by simpa using hB⟩
    exact (notMem_empty x (hfree ▸ this))
  have hxXB : x ∈ H.X \ H.B := mem_sdiff.2 ⟨hxX, hxnotB⟩
  have hreachX :
      (G.induce (H.X : Set V)).Reachable ⟨w, hwX⟩ ⟨x, hxX⟩ :=
    reachable_all_nonterminals_of_neighbor (G := G) H.hN_X hBKX hb hw hxXB hadj
  have hreach :
      (G.induce ((H.X \ (∅ : Finset V) : Finset V) : Set V)).Reachable
        ⟨w, hwX0⟩ ⟨x, hxX0⟩ :=
    hreachX.map (induceIncl G hsub)
  have hxC := connectedComponentMk_eq_of_mem_componentFinset' (G := G) hx
  have hCw :
      (G.induce ((H.X \ (∅ : Finset V) : Finset V) : Set V)).connectedComponentMk
          ⟨w, hwX0⟩ = C.1 :=
    (ConnectedComponent.eq.2 hreach).trans hxC
  have hadj' :
      (G.induce ((H.X \ (∅ : Finset V) : Finset V) : Set V)).Adj
        ⟨b, hbX0⟩ ⟨w, hwX0⟩ := by
    simpa [induce_adj] using hadj
  have hbMk :
      (G.induce ((H.X \ (∅ : Finset V) : Finset V) : Set V)).connectedComponentMk
          ⟨b, hbX0⟩ = C.1 :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hadj').trans hCw
  have hbC : b ∈ componentFinset G (H.X \ (∅ : Finset V)) C.1 :=
    mem_filter.2 ⟨hbX0, ⟨hbX0, hbMk⟩⟩
  have hbB0 : b ∈ H.B \ (∅ : Finset V) := by simpa using hb
  exact (notMem_empty b (hfree ▸ mem_inter.2 ⟨hbC, hbB0⟩))

lemma exists_mixedSplit_child
    (hBV : ∃ b ∈ H.B, ∃ w ∈ H.X \ H.B, G.Adj b w) :
    Nonempty (MixedSplit (G := G) H.X H.B) := by
  obtain ⟨b, hb, w, hw, hadj⟩ := hBV
  have hz : terminalComponentCount (G := G) H.X H.B ∅ = 0 :=
    H.terminalComponentCount_empty_eq_zero_of_BV hb hw hadj
  have hVne : (H.X \ H.B).Nonempty := ⟨w, hw⟩
  exact exists_mixedSplit (G := G) H.B_subset_X H.hN_X hz hVne

lemma slack_restrict_mixed
    {D : Finset V} (hD : D ⊆ H.X) (hI : H.X \ D ⊆ H.B)
    (hnocross : ∀ a ∈ D, ∀ i ∈ H.X \ D, ¬ G.Adj a i) :
    TerminalHypothesisSlackStrong (G := G) D (H.B ∩ D) H.Y.card := by
  have hslack := H.slack_X
  constructor
  · have h := hslack.1
    simpa [terminalComponentCount_mixed (G := G) (S := (∅ : Finset V))
      H.B_subset_X hD (empty_subset D) hI hnocross] using h
  · intro S hS hSne
    have hz := hslack.2 S (hS.trans hD) hSne
    simpa [terminalComponentCount_mixed (G := G) H.B_subset_X hD hS hI hnocross]
      using hz

lemma slack_mixed_component (s : MixedSplit (G := G) H.X H.B) :
    TerminalHypothesisSlackStrong (G := G) s.D (H.B ∩ s.D) H.Y.card :=
  H.slack_restrict_mixed s.hDsub
    (by simpa [s.I_eq] using s.hI)
    (by simpa [s.I_eq] using s.hnocross)

lemma complete_D_Y (s : MixedSplit (G := G) H.X H.B) :
    G.IsCompleteBetween (s.D : Set V) (H.Y : Set V) :=
  IsCompleteBetween.mono H.complete_X_Y s.hDsub subset_rfl

lemma I_subset_X (s : MixedSplit (G := G) H.X H.B) : s.I ⊆ H.X := by
  intro i hi
  have : i ∈ s.D ∪ s.I := mem_union.2 (Or.inr hi)
  rwa [s.hDU] at this

lemma complete_I_Y (s : MixedSplit (G := G) H.X H.B) :
    G.IsCompleteBetween (s.I : Set V) (H.Y : Set V) :=
  IsCompleteBetween.mono H.complete_X_Y (H.I_subset_X s) subset_rfl

end CanonicalJoinSplit

/-! ### Nested `B`-profiles of nonterminals are completely joined -/

/-- The set of terminals adjacent to a nonterminal. -/
noncomputable def Bprofile (B : Finset V) (v : V) : Finset V :=
  B.filter (fun b => G.Adj b v)

lemma mem_Bprofile {B : Finset V} {b v : V} :
    b ∈ Bprofile (G := G) B v ↔ b ∈ B ∧ G.Adj b v :=
  mem_filter

/-- Distinct `B`-profiles of nonterminals force an original edge, by a
`B`-witness of the profile difference and `NeighborCondition`. -/
lemma adj_of_Bprofile_ne {K B : Finset V}
    (hN : NeighborCondition (G := G) K B)
    {v w : V} (hv : v ∈ K \ B) (hw : w ∈ K \ B)
    (hne : Bprofile (G := G) B v ≠ Bprofile (G := G) B w) :
    G.Adj v w := by
  by_cases hsub : Bprofile (G := G) B v ⊆ Bprofile (G := G) B w
  · have hnot : ¬ Bprofile (G := G) B w ⊆ Bprofile (G := G) B v := by
      intro hge
      exact hne (Subset.antisymm hsub hge)
    obtain ⟨b, hbw, hbv⟩ := not_subset.1 hnot
    have hbB : b ∈ B := (mem_filter.1 hbw).1
    have hadj : G.Adj b w := (mem_filter.1 hbw).2
    have hnbv : ¬ G.Adj b v := fun h => hbv (mem_filter.2 ⟨hbB, h⟩)
    exact (hN hbB hw hv hadj hnbv).symm
  · obtain ⟨b, hbv, hbw⟩ := not_subset.1 hsub
    have hbB : b ∈ B := (mem_filter.1 hbv).1
    have hadj : G.Adj b v := (mem_filter.1 hbv).2
    have hnbw : ¬ G.Adj b w := fun h => hbw (mem_filter.2 ⟨hbB, h⟩)
    exact hN hbB hv hw hadj hnbw

/-- `B`-profiles of nonterminals form a chain under inclusion. -/
lemma Bprofile_nested {K B : Finset V}
    (hK : IsCograph G K) (hInd : Independent (G := G) B) (hBK : B ⊆ K)
    (hN : NeighborCondition (G := G) K B)
    {v w : V} (hv : v ∈ K \ B) (hw : w ∈ K \ B) :
    Bprofile (G := G) B v ⊆ Bprofile (G := G) B w ∨
      Bprofile (G := G) B w ⊆ Bprofile (G := G) B v := by
  by_contra h
  have h1 : ¬ Bprofile (G := G) B v ⊆ Bprofile (G := G) B w :=
    fun hst => h (Or.inl hst)
  have h2 : ¬ Bprofile (G := G) B w ⊆ Bprofile (G := G) B v :=
    fun hts => h (Or.inr hts)
  obtain ⟨b, hbv, hbw⟩ := not_subset.1 h1
  obtain ⟨b', hbw', hbv'⟩ := not_subset.1 h2
  have hb : b ∈ B := (mem_filter.1 hbv).1
  have hb' : b' ∈ B := (mem_filter.1 hbw').1
  have hbvA : G.Adj b v := (mem_filter.1 hbv).2
  have hnbw : ¬ G.Adj b w := fun h => hbw (mem_filter.2 ⟨hb, h⟩)
  have hb'wA : G.Adj b' w := (mem_filter.1 hbw').2
  have hnb'v : ¬ G.Adj b' v := fun h => hbv' (mem_filter.2 ⟨hb', h⟩)
  exact not_incomparable_B_neighbors (G := G) hK hInd hBK hN hb hb'
    hv hw hbvA hnb'v hb'wA hnbw

lemma isCompleteBetween_of_Bprofile_ne {K B : Finset V}
    (hN : NeighborCondition (G := G) K B)
    {P Q : Finset V} (hne : P ≠ Q) :
    G.IsCompleteBetween
      (((K \ B).filter (fun v => Bprofile (G := G) B v = P) : Finset V) : Set V)
      (((K \ B).filter (fun v => Bprofile (G := G) B v = Q) : Finset V) : Set V) := by
  intro v hv w hw
  have hvKB : v ∈ K \ B := (mem_filter.1 hv).1
  have hwKB : w ∈ K \ B := (mem_filter.1 hw).1
  have hPv : Bprofile (G := G) B v = P := (mem_filter.1 hv).2
  have hQw : Bprofile (G := G) B w = Q := (mem_filter.1 hw).2
  have hne' : Bprofile (G := G) B v ≠ Bprofile (G := G) B w := by
    simpa [hPv, hQw] using hne
  exact adj_of_Bprofile_ne (G := G) hN hvKB hwKB hne'

/-! ### Combined existence: traceable base or no-BV canonical join -/

lemma exists_canonicalJoinSplit {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hconn : (G.induce (K : Set V)).Connected)
    (hBne : B.Nonempty) (hVne : (K \ B).Nonempty) :
    Nonempty (CanonicalJoinSplit (G := G)) :=
  ⟨⟨K, B, hrep, hconn, hBne, hVne⟩⟩

/-- Connected mixed repaired carrier: either a traceable `p = 1` cover,
or the canonical no-BV remainder of a `p ≥ 2` join, yields an actual
minimum `B`-ended cover. Remaining `B`–`(X \ B)` edges are not claimed. -/
theorem exists_min_terminalCover_of_canonical_noBV {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hconn : (G.induce (K : Set V)).Connected)
    (hBne : B.Nonempty) (hVne : (K \ B).Nonempty)
    (hnoBV : ∀ b ∈ B, ∀ w ∈ (K \ commonNeighborLayer (G := G) K B) \ B,
      ¬ G.Adj b w) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc := by
  let H : CanonicalJoinSplit (G := G) := ⟨K, B, hrep, hconn, hBne, hVne⟩
  have hanti : ∀ b ∈ H.B, ∀ w ∈ H.X \ H.B, ¬ G.Adj b w := by
    intro b hb w hw
    have : H.X = K \ commonNeighborLayer (G := G) K B := rfl
    simpa [this] using hnoBV b hb w hw
  by_cases hp : 2 ≤ pathCoverNumber G K
  · exact H.exists_min_terminalCover_noBV hanti hp
  · have hp1 : pathCoverNumber G K = 1 := by
      have hpos : 1 ≤ pathCoverNumber G K :=
        one_le_pathCoverNumber_of_nonempty (G := G)
          (hBne.mono hrep.2.1)
      omega
    exact exists_min_terminalCover_of_pathCoverNumber_eq_one
      (two_le_card_of_mixed hrep.2.1 hBne hVne) hrep.1 hconn hp1
      hrep.2.1 hBne hrep.2.2.2.1

theorem exists_terminalCover_of_canonical_noBV_spectrum {K B : Finset V}
    (hrep : RepairedTerminalHypothesis (G := G) K B)
    (hconn : (G.induce (K : Set V)).Connected)
    (hBne : B.Nonempty) (hVne : (K \ B).Nonempty)
    (hnoBV : ∀ b ∈ B, ∀ w ∈ (K \ commonNeighborLayer (G := G) K B) \ B,
      ¬ G.Adj b w)
    (hpK : 2 ≤ pathCoverNumber G K)
    {q : ℕ} (hlo : pathCoverNumber G K ≤ q)
    (hhi : q + pathCoverNumber G (K \ B) ≤ B.card) :
    ∃ pc : PathCover G K,
      pc.card = q ∧ IsTerminalCover (G := G) B pc := by
  let H : CanonicalJoinSplit (G := G) := ⟨K, B, hrep, hconn, hBne, hVne⟩
  have hanti : ∀ b ∈ H.B, ∀ w ∈ H.X \ H.B, ¬ G.Adj b w := by
    intro b hb w hw
    have : H.X = K \ commonNeighborLayer (G := G) K B := rfl
    simpa [this] using hnoBV b hb w hw
  exact H.exists_terminalCover_noBV_spectrum hanti hpK hlo hhi

end Nikoghosyan
