/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalJoinBlocks

/-!
# No-BV complete-join base with nonterminal `W` and its full spectrum

Hypotheses: `X = B ⊔ W` with `B` independent and anti-complete to `W`,
complete join `X ∨ Y`, `Y` nonempty, `G[K]` a cograph, strict
`TerminalHypothesis` on `(K, B)`, and `p(K) ≥ 2`. No `B`-ended cover is
supplied.

The original cut `Y ∪ F(W)` yields `p(W) ≤ |Y| - 1` because surviving
`B`-singletons are non-free. Join recurrences then give
`p(K) = |B| + p(W) - |Y|` and `p(K \ B) = max(1, p(Y) - |W|)`.

For each `q` in `[p(K), |B| - p(K \ B)]` set `d = |B| - q`,
`a = max(p(W), p(Y) - d)`, `k = a + d`. Ordinary refinement produces
covers of `W` and `Y` of those sizes. An anchored original `B`-ended path
`B₁, Y₁, W₁, …, Y_a, B₂` plus remaining `B`-singletons is a terminal
cover of size `|B| - 1`; the leftover `d - 1` whole `Y`-paths splice
between current `B`-ended paths down to cardinality `q`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- No-BV complete-join base: independent terminals anti-complete to a
possibly empty nonterminal block, completely joined to a nonempty side. -/
structure NoBVJoinBase (G : SimpleGraph V) where
  B : Finset V
  W : Finset V
  Y : Finset V
  hBne : B.Nonempty
  hYne : Y.Nonempty
  hdisjBW : Disjoint B W
  hdisjBY : Disjoint B Y
  hdisjWY : Disjoint W Y
  hInd : Independent (G := G) B
  hanti : ∀ b ∈ B, ∀ w ∈ W, ¬ G.Adj b w
  hXY : G.IsCompleteBetween ((B ∪ W : Finset V) : Set V) (Y : Set V)
  hKcog : IsCograph G (B ∪ W ∪ Y)
  hTH : TerminalHypothesis (G := G) (B ∪ W ∪ Y) B
  hpK : 2 ≤ pathCoverNumber G (B ∪ W ∪ Y)

namespace NoBVJoinBase

variable (H : NoBVJoinBase (G := G))

def X : Finset V := H.B ∪ H.W

def K : Finset V := H.B ∪ H.W ∪ H.Y

lemma X_eq : H.X = H.B ∪ H.W := rfl

lemma K_eq : H.K = H.X ∪ H.Y := by
  simp [NoBVJoinBase.K, NoBVJoinBase.X, union_assoc]

lemma hXYcomplete : G.IsCompleteBetween (H.X : Set V) (H.Y : Set V) := by
  simpa [NoBVJoinBase.X] using H.hXY

lemma disjoint_X_Y : Disjoint H.X H.Y := by
  rw [NoBVJoinBase.X, disjoint_union_left]
  exact ⟨H.hdisjBY, H.hdisjWY⟩

lemma hBYcomplete : G.IsCompleteBetween (H.B : Set V) (H.Y : Set V) :=
  IsCompleteBetween.mono H.hXYcomplete subset_union_left subset_rfl

lemma hWYcomplete : G.IsCompleteBetween (H.W : Set V) (H.Y : Set V) :=
  IsCompleteBetween.mono H.hXYcomplete subset_union_right subset_rfl

lemma B_subset_K : H.B ⊆ H.K :=
  subset_union_left.trans subset_union_left

lemma W_subset_K : H.W ⊆ H.K :=
  subset_union_right.trans subset_union_left

lemma Y_subset_K : H.Y ⊆ H.K := subset_union_right

lemma B_subset_X : H.B ⊆ H.X := subset_union_left

lemma nocross_BW : ∀ b ∈ H.B, ∀ w ∈ H.W, ¬ G.Adj b w := H.hanti

lemma W_cograph : IsCograph G H.W :=
  IsCograph.subset (G := G) H.hKcog H.W_subset_K

lemma Y_cograph : IsCograph G H.Y :=
  IsCograph.subset (G := G) H.hKcog H.Y_subset_K

lemma X_cograph : IsCograph G H.X :=
  IsCograph.subset (G := G) H.hKcog (show H.X ⊆ H.B ∪ H.W ∪ H.Y from subset_union_left)

lemma B_nonempty : H.B.Nonempty := H.hBne

lemma X_nonempty : H.X.Nonempty := H.hBne.mono H.B_subset_X

lemma pathCoverNumber_B : pathCoverNumber G H.B = H.B.card :=
  pathCoverNumber_eq_card_of_independent (G := G) H.hInd

lemma pathCoverNumber_X :
    pathCoverNumber G H.X = H.B.card + pathCoverNumber G H.W := by
  have hsum :=
    Cograph.pathCoverNumber_disjoint_union (G := G) H.hdisjBW H.hanti
  simpa [NoBVJoinBase.X, H.pathCoverNumber_B] using hsum

/-- Remainder after the original cut `Y ∪ F(W)` is `B ∪ (W \ F(W))`. -/
lemma sdiff_cut_YF : H.K \ (H.Y ∪ ineligibleSet G H.W) =
    H.B ∪ (H.W \ ineligibleSet G H.W) := by
  ext x
  simp only [NoBVJoinBase.K, mem_sdiff, mem_union, mem_sdiff]
  constructor
  · intro hx
    rcases hx with ⟨hK, hnot⟩
    have hxY : x ∉ H.Y := fun hY => hnot (Or.inl hY)
    have hxF : x ∉ ineligibleSet G H.W := fun hF => hnot (Or.inr hF)
    rcases hK with (hB | hW) | hY
    · exact Or.inl hB
    · exact Or.inr ⟨hW, hxF⟩
    · exact (hxY hY).elim
  · intro hx
    rcases hx with hB | hWF
    · refine ⟨Or.inl (Or.inl hB), ?_⟩
      intro h
      rcases h with hY | hF
      · exact Finset.disjoint_left.1 H.hdisjBY hB hY
      · exact Finset.disjoint_left.1 H.hdisjBW hB
          (ineligibleSet_subset (G := G) H.W hF)
    · refine ⟨Or.inl (Or.inr hWF.1), ?_⟩
      intro h
      rcases h with hY | hF
      · exact Finset.disjoint_left.1 H.hdisjWY hWF.1 hY
      · exact hWF.2 hF

lemma nocross_Wrem_B :
    ∀ a ∈ H.W \ ineligibleSet G H.W, ∀ b ∈ H.B, ¬ G.Adj a b := by
  intro a ha b hb hab
  exact H.hanti b hb a (mem_sdiff.1 ha).1 hab.symm

lemma all_free_of_disjoint_T {A T : Finset V} (h : Disjoint A T)
    (C : (G.induce (A : Set V)).ConnectedComponent) :
    componentFinset G A C ∩ T = ∅ := by
  apply eq_empty_of_forall_notMem
  intro x hx
  have hxA : x ∈ A := componentFinset_subset (G := G) C (mem_inter.1 hx).1
  exact Finset.disjoint_left.1 h hxA (mem_inter.1 hx).2

/-- Exact free-component count of the original cut `Y ∪ F(W)`:
surviving `B`-singletons are non-free, so `z_B = c(W \ F(W))`. -/
lemma terminalComponentCount_cut_YF :
    terminalComponentCount (G := G) H.K H.B (H.Y ∪ ineligibleSet G H.W) =
      componentCount G (H.W \ ineligibleSet G H.W) := by
  have hEq := H.sdiff_cut_YF
  have hnc := H.nocross_Wrem_B
  have hJ : H.B ⊆ H.B := subset_rfl
  -- Rewrite the remainder as A ∪ J with J = B ⊆ surviving terminals.
  have h1 :
      terminalComponentCount (G := G) H.K H.B (H.Y ∪ ineligibleSet G H.W) =
        Nat.card
          { C : (G.induce
              ((H.B ∪ (H.W \ ineligibleSet G H.W) : Finset V) : Set V)).ConnectedComponent //
            componentFinset G (H.B ∪ (H.W \ ineligibleSet G H.W)) C ∩
              (H.B \ (H.Y ∪ ineligibleSet G H.W)) = ∅ } := by
    unfold terminalComponentCount IsFreeComponent
    rw [hEq]
  have hBsurv : H.B \ (H.Y ∪ ineligibleSet G H.W) = H.B := by
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · exact And.left
    · intro hx
      refine ⟨hx, ?_⟩
      intro h
      rcases h with hY | hF
      · exact Finset.disjoint_left.1 H.hdisjBY hx hY
      · exact Finset.disjoint_left.1 H.hdisjBW hx
          (ineligibleSet_subset (G := G) H.W hF)
  have h2 :=
    ncard_free_union_isolates (G := G)
      (A := H.W \ ineligibleSet G H.W) (J := H.B) (T := H.B)
      (fun a ha b hb => H.nocross_Wrem_B a ha b hb) subset_rfl
  have h3 :
      Nat.card
          { C : (G.induce ((H.W \ ineligibleSet G H.W : Finset V) : Set V)).ConnectedComponent //
            componentFinset G (H.W \ ineligibleSet G H.W) C ∩ H.B = ∅ } =
        componentCount G (H.W \ ineligibleSet G H.W) := by
    unfold componentCount
    refine Nat.card_congr ?_
    exact Equiv.subtypeUnivEquiv fun C =>
      all_free_of_disjoint_T (G := G)
        (disjoint_of_subset_left sdiff_subset H.hdisjBW.symm) C
  -- Align J-union order B ∪ A vs A ∪ B.
  have hcomm :
      H.B ∪ (H.W \ ineligibleSet G H.W) =
        (H.W \ ineligibleSet G H.W) ∪ H.B := union_comm _ _
  have h1' :
      Nat.card
          { C : (G.induce
              ((H.B ∪ (H.W \ ineligibleSet G H.W) : Finset V) : Set V)).ConnectedComponent //
            componentFinset G (H.B ∪ (H.W \ ineligibleSet G H.W)) C ∩
              (H.B \ (H.Y ∪ ineligibleSet G H.W)) = ∅ } =
        Nat.card
          { C : (G.induce
              (((H.W \ ineligibleSet G H.W) ∪ H.B : Finset V) : Set V)).ConnectedComponent //
            componentFinset G ((H.W \ ineligibleSet G H.W) ∪ H.B) C ∩ H.B = ∅ } := by
    rw [hcomm, hBsurv]
  rw [h1, h1', h2, h3]

/-- Original cut `Y ∪ F(W)`: `p(W) ≤ |Y| - 1`. -/
lemma pathCoverNumber_W_lt :
    pathCoverNumber G H.W + 1 ≤ H.Y.card := by
  set FW := ineligibleSet G H.W
  have hFsub : FW ⊆ H.W := ineligibleSet_subset (G := G) H.W
  have hS : H.Y ∪ FW ⊆ H.K :=
    union_subset H.Y_subset_K (hFsub.trans H.W_subset_K)
  have hSne : (H.Y ∪ FW).Nonempty := H.hYne.mono subset_union_left
  have hz := H.hTH.2 (H.Y ∪ FW) hS hSne
  have hz' := H.terminalComponentCount_cut_YF
  have hcanon :
      componentCount G (H.W \ FW) = FW.card + pathCoverNumber G H.W :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) H.W_cograph
  have hcard : (H.Y ∪ FW).card = H.Y.card + FW.card :=
    card_union_of_disjoint (disjoint_of_subset_right hFsub H.hdisjWY.symm)
  have hle : componentCount G (H.W \ FW) ≤ (H.Y ∪ FW).card - 1 := by
    have hz0 := hz
    have hz1 : terminalComponentCount (G := G) H.K H.B (H.Y ∪ FW) ≤
        (H.Y ∪ FW).card - 1 := by
      simpa [NoBVJoinBase.K] using hz0
    rw [hz'] at hz1
    exact hz1
  have hYpos : 1 ≤ H.Y.card := card_pos.2 H.hYne
  omega

lemma K_eq_join : H.X ∪ H.Y = H.B ∪ H.W ∪ H.Y := by
  simp [NoBVJoinBase.X]

lemma pathCoverNumber_Y_lt_X :
    pathCoverNumber G H.Y + 1 ≤ H.X.card :=
  pathCoverNumber_B_free_join_side_lt (G := G) H.X_nonempty H.hYne
    H.hXYcomplete (by simpa [H.K_eq_join] using H.hKcog) H.B_subset_X
    (by simpa [H.K_eq_join] using H.hTH)

lemma dominant_X :
    H.Y.card < pathCoverNumber G H.X :=
  dominant_mixed_child_of_slack_zero (G := G) H.X_nonempty H.hYne
    H.hXYcomplete (by simpa [H.K_eq_join] using H.hKcog) H.B_subset_X
    (by simpa [H.K_eq_join] using H.hTH) (by simpa [H.K_eq_join] using H.hpK)

lemma pathCoverNumber_K :
    pathCoverNumber G H.K = H.B.card + pathCoverNumber G H.W - H.Y.card := by
  have hdom := H.dominant_X
  have hj :=
    pathCoverNumber_eq_sub_of_dominant H.X_nonempty H.hYne H.hXYcomplete hdom
  have hX := H.pathCoverNumber_X
  simpa [H.K_eq, hX] using hj

lemma pathCoverNumber_KsdiffB :
    pathCoverNumber G (H.K \ H.B) =
      max 1 (pathCoverNumber G H.Y - H.W.card) := by
  have hEq : H.K \ H.B = H.W ∪ H.Y := by
    ext x
    simp only [NoBVJoinBase.K, mem_sdiff, mem_union]
    constructor
    · intro hx
      rcases hx with ⟨(hB | hW) | hY, hnB⟩
      · exact (hnB hB).elim
      · exact Or.inl hW
      · exact Or.inr hY
    · intro hx
      rcases hx with hW | hY
      · exact ⟨Or.inl (Or.inr hW), fun hB => Finset.disjoint_left.1 H.hdisjBW hB hW⟩
      · exact ⟨Or.inr hY, fun hB => Finset.disjoint_left.1 H.hdisjBY hB hY⟩
  rw [hEq]
  by_cases hWne : H.W.Nonempty
  · have hj := pathCoverNumber_complete_join hWne H.hYne H.hWYcomplete
    have hpW : pathCoverNumber G H.W ≤ H.Y.card := by
      have := H.pathCoverNumber_W_lt
      omega
    have hWsub : pathCoverNumber G H.W - H.Y.card = 0 :=
      Nat.sub_eq_zero_of_le hpW
    simpa [hj, hWsub, max_comm] using rfl
  · have hW0 : H.W = ∅ := not_nonempty_iff_eq_empty.1 hWne
    have : H.W ∪ H.Y = H.Y := by simp [hW0]
    have hpY : 1 ≤ pathCoverNumber G H.Y :=
      one_le_pathCoverNumber_of_nonempty (G := G) H.hYne
    simp [this, hW0, Nat.sub_zero, max_eq_right hpY]

lemma interval_nonempty :
    pathCoverNumber G H.K + pathCoverNumber G (H.K \ H.B) ≤ H.B.card := by
  have hpK := H.pathCoverNumber_K
  have hpKB := H.pathCoverNumber_KsdiffB
  have hpW : pathCoverNumber G H.W + 1 ≤ H.Y.card := H.pathCoverNumber_W_lt
  have hpWle : pathCoverNumber G H.W ≤ H.W.card :=
    pathCoverNumber_le_card (G := G) H.W
  have hpYle : pathCoverNumber G H.Y ≤ H.Y.card :=
    pathCoverNumber_le_card (G := G) H.Y
  have hpKge : 2 ≤ H.B.card + pathCoverNumber G H.W - H.Y.card := by
    have h2 : 2 ≤ pathCoverNumber G H.K := by
      simpa [NoBVJoinBase.K] using H.hpK
    rwa [hpK] at h2
  rw [hpK, hpKB]
  by_cases h : pathCoverNumber G H.Y ≤ H.W.card
  · have h0 : pathCoverNumber G H.Y - H.W.card = 0 := Nat.sub_eq_zero_of_le h
    have hmax : max 1 (pathCoverNumber G H.Y - H.W.card) = 1 := by
      simp [h0]
    rw [hmax]
    have hYbd : pathCoverNumber G H.W + 1 ≤ H.Y.card := H.pathCoverNumber_W_lt
    have hBpos : 1 ≤ H.B.card := card_pos.2 H.hBne
    by_cases hge : H.Y.card ≤ H.B.card + pathCoverNumber G H.W
    · omega
    · have hz0 : H.B.card + pathCoverNumber G H.W - H.Y.card = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hge)
      omega
  · have hgt : H.W.card < pathCoverNumber G H.Y := Nat.lt_of_not_ge h
    have hmax : max 1 (pathCoverNumber G H.Y - H.W.card) =
        pathCoverNumber G H.Y - H.W.card :=
      max_eq_right (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hgt))
    rw [hmax]
    have hYbd : pathCoverNumber G H.W + 1 ≤ H.Y.card := H.pathCoverNumber_W_lt
    have hpYle := pathCoverNumber_le_card (G := G) H.Y
    have hpWle := pathCoverNumber_le_card (G := G) H.W
    have hge : H.Y.card ≤ H.B.card + pathCoverNumber G H.W := by omega
    have hrestore :
        H.B.card + pathCoverNumber G H.W - H.Y.card + H.Y.card =
          H.B.card + pathCoverNumber G H.W :=
      Nat.sub_add_cancel hge
    have hgeW : H.W.card ≤ pathCoverNumber G H.Y := Nat.le_of_lt hgt
    have hrestoreY :
        pathCoverNumber G H.Y - H.W.card + H.W.card =
          pathCoverNumber G H.Y :=
      Nat.sub_add_cancel hgeW
    omega

/-- Spectrum parameters for a feasible cardinality `q`. -/
noncomputable def d (q : ℕ) : ℕ := H.B.card - q

noncomputable def a (q : ℕ) : ℕ :=
  max (pathCoverNumber G H.W) (pathCoverNumber G H.Y - H.d q)

noncomputable def k (q : ℕ) : ℕ := H.a q + H.d q

lemma spectrum_params {q : ℕ}
    (hlo : pathCoverNumber G H.K ≤ q)
    (hhi : q + pathCoverNumber G (H.K \ H.B) ≤ H.B.card) :
    1 ≤ H.d q ∧
      pathCoverNumber G H.W ≤ H.a q ∧
        H.a q ≤ H.W.card ∧
          pathCoverNumber G H.Y ≤ H.k q ∧
            H.k q ≤ H.Y.card ∧
              H.a q + 1 ≤ H.k q ∧
                H.d q + 2 ≤ H.B.card := by
  have hpK := H.pathCoverNumber_K
  have hpKB := H.pathCoverNumber_KsdiffB
  have hq2 : 2 ≤ q :=
    le_trans (by simpa [NoBVJoinBase.K, NoBVJoinBase.X] using H.hpK) hlo
  have hneKB : (H.K \ H.B).Nonempty :=
    H.hYne.mono fun y hy =>
      mem_sdiff.2 ⟨H.Y_subset_K hy, fun hB =>
        Finset.disjoint_left.1 H.hdisjBY hB hy⟩
  have hpKBpos : 1 ≤ pathCoverNumber G (H.K \ H.B) :=
    one_le_pathCoverNumber_of_nonempty (G := G) hneKB
  have hdge : 1 ≤ H.d q := by
    change 1 ≤ H.B.card - q
    omega
  have hq2' : 2 ≤ q := hq2
  have hBge : H.d q + 2 ≤ H.B.card := by
    change H.B.card - q + 2 ≤ H.B.card
    omega
  have haW : pathCoverNumber G H.W ≤ H.a q := le_max_left _ _
  have hkge : H.a q + 1 ≤ H.k q := by
    change H.a q + 1 ≤ H.a q + H.d q
    omega
  have hpWle := pathCoverNumber_le_card (G := G) H.W
  have hpYle := pathCoverNumber_le_card (G := G) H.Y
  have hpWbd := H.pathCoverNumber_W_lt
  have hd_from_hi : pathCoverNumber G (H.K \ H.B) ≤ H.d q := by
    change pathCoverNumber G (H.K \ H.B) ≤ H.B.card - q
    omega
  have ha_le_W : H.a q ≤ H.W.card := by
    refine max_le hpWle ?_
    have hle : pathCoverNumber G H.Y - H.W.card ≤ H.d q := by
      have : pathCoverNumber G H.Y - H.W.card ≤
          max 1 (pathCoverNumber G H.Y - H.W.card) := le_max_right _ _
      have hkb : max 1 (pathCoverNumber G H.Y - H.W.card) ≤ H.d q := by
        simpa [hpKB] using hd_from_hi
      exact this.trans hkb
    omega
  have hadd :
      H.a q + H.d q =
        max (pathCoverNumber G H.W + H.d q)
          (pathCoverNumber G H.Y - H.d q + H.d q) := by
    simp [NoBVJoinBase.a, max_add_add_right]
  have hk_le_Y : H.k q ≤ H.Y.card := by
    change H.a q + H.d q ≤ H.Y.card
    rw [hadd]
    refine max_le ?_ ?_
    · have hqlo : H.B.card + pathCoverNumber G H.W - H.Y.card ≤ q := by
        simpa [hpK] using hlo
      have hqB : q ≤ H.B.card := by omega
      have hYle : H.Y.card ≤ H.B.card + pathCoverNumber G H.W := by
        have h2 : 2 ≤ H.B.card + pathCoverNumber G H.W - H.Y.card := by
          have h2' : 2 ≤ pathCoverNumber G H.K := by
            simpa [NoBVJoinBase.K] using H.hpK
          rwa [hpK] at h2'
        omega
      have : pathCoverNumber G H.W + H.d q ≤ H.Y.card := by
        change pathCoverNumber G H.W + (H.B.card - q) ≤ H.Y.card
        have hcancel : H.B.card - q + q = H.B.card := Nat.sub_add_cancel hqB
        have hcancelY :
            H.B.card + pathCoverNumber G H.W - H.Y.card + H.Y.card =
              H.B.card + pathCoverNumber G H.W :=
          Nat.sub_add_cancel hYle
        omega
      exact this
    · by_cases hle : H.d q ≤ pathCoverNumber G H.Y
      · have : pathCoverNumber G H.Y - H.d q + H.d q =
            pathCoverNumber G H.Y := Nat.sub_add_cancel hle
        simpa [this] using hpYle
      · have h0 : pathCoverNumber G H.Y - H.d q = 0 :=
          Nat.sub_eq_zero_of_le (le_of_not_ge hle)
        have hqlo : H.B.card + pathCoverNumber G H.W - H.Y.card ≤ q := by
          simpa [hpK] using hlo
        have hqB : q ≤ H.B.card := by omega
        have hYle : H.Y.card ≤ H.B.card + pathCoverNumber G H.W := by
          have h2 : 2 ≤ H.B.card + pathCoverNumber G H.W - H.Y.card := by
            have h2' : 2 ≤ pathCoverNumber G H.K := by
              simpa [NoBVJoinBase.K] using H.hpK
            rwa [hpK] at h2'
          omega
        have hdY : H.d q ≤ H.Y.card := by
          change H.B.card - q ≤ H.Y.card
          omega
        simpa [h0] using hdY
  have hkY : pathCoverNumber G H.Y ≤ H.k q := by
    change pathCoverNumber G H.Y ≤ H.a q + H.d q
    rw [hadd]
    by_cases hle : H.d q ≤ pathCoverNumber G H.Y
    · have : pathCoverNumber G H.Y - H.d q + H.d q =
          pathCoverNumber G H.Y := Nat.sub_add_cancel hle
      simpa [this] using le_max_right _ _
    · have h0 : pathCoverNumber G H.Y - H.d q = 0 :=
        Nat.sub_eq_zero_of_le (le_of_not_ge hle)
      have : pathCoverNumber G H.Y ≤ H.d q := le_of_not_ge hle
      have : pathCoverNumber G H.Y ≤
          pathCoverNumber G H.Y - H.d q + H.d q := by
        simpa [h0] using this
      exact this.trans (le_max_right _ _)
  exact ⟨hdge, haW, ha_le_W, hkY, hk_le_Y, hkge, hBge⟩

lemma chain_start_mem_Y {pcY : PathCover G H.Y} {pcW : PathCover G H.W} {a : ℕ}
    (haY : a + 1 ≤ pcY.card) (haW : pcW.card = a)
    {r : GraphPath G}
    (hs : r.start = (pathAt pcY ⟨0, (Nat.succ_pos a).trans_le haY⟩).start) :
    r.start ∈ H.Y := by
  rw [hs]
  exact pathAt_support_subset pcY _ (pathAt pcY ⟨0, (Nat.succ_pos a).trans_le haY⟩).start_mem_support

lemma chain_finish_mem_Y {pcY : PathCover G H.Y} {pcW : PathCover G H.W} {a : ℕ}
    (haY : a + 1 ≤ pcY.card) (haW : pcW.card = a)
    {r : GraphPath G}
    (hf : r.finish = (pathAt pcY ⟨a, Nat.succ_le_iff.mp haY⟩).finish) :
    r.finish ∈ H.Y := by
  rw [hf]
  exact pathAt_support_subset pcY _ (pathAt pcY ⟨a, Nat.succ_le_iff.mp haY⟩).finish_mem_support

lemma chain_support_subset {pcY : PathCover G H.Y} {pcW : PathCover G H.W} {a : ℕ}
    (haY : a + 1 ≤ pcY.card) (haW : pcW.card = a)
    {r : GraphPath G}
    (hrmem : ∀ x, x ∈ r.support ↔
      (∃ i : Fin (a + 1), x ∈ (pathAt pcY ⟨i.1, Nat.lt_of_lt_of_le i.2 haY⟩).support) ∨
        ∃ j : Fin a, x ∈ (pathAt pcW ⟨j.1, haW ▸ j.2⟩).support) :
    r.support ⊆ H.W ∪ H.Y := by
  intro x hx
  have hx' := (hrmem x).1 hx
  rcases hx' with ⟨i, hxi⟩ | ⟨j, hxj⟩
  · exact mem_union.2 (Or.inr (pathAt_support_subset pcY _ hxi))
  · exact mem_union.2 (Or.inl (pathAt_support_subset pcW _ hxj))

/-- Every integer in the repaired interval is realized by an actual original-edge
`B`-terminal cover of `K`. No `B`-ended cover is assumed as an input. -/
lemma exists_terminalCover_noBV_of_card {q : ℕ}
    (hlo : pathCoverNumber G H.K ≤ q)
    (hhi : q + pathCoverNumber G (H.K \ H.B) ≤ H.B.card) :
    ∃ pc : PathCover G H.K,
      pc.card = q ∧ IsTerminalCover (G := G) H.B pc := by
  obtain ⟨hdge, haW, ha_le_W, hkY, hk_le_Y, hkge, hBge⟩ :=
    H.spectrum_params hlo hhi
  obtain ⟨pcW, hWcard⟩ :=
    exists_pathCover_card (G := G) H.W haW ha_le_W
  obtain ⟨pcY, hYcard⟩ :=
    exists_pathCover_card (G := G) H.Y hkY hk_le_Y
  have haY : H.a q + 1 ≤ pcY.card := by omega
  have haWc : pcW.card = H.a q := hWcard
  obtain ⟨r, hrs, hrf, hrmem⟩ :=
    exists_YV_chain H.hWYcomplete H.hdisjWY.symm pcY pcW (H.a q) haY haWc
  have hsY := H.chain_start_mem_Y haY haWc hrs
  have hfY := H.chain_finish_mem_Y haY haWc hrf
  have hrsub := H.chain_support_subset haY haWc hrmem
  have hB2 : 2 ≤ H.B.card := by omega
  obtain ⟨b1, b2, hb1, hb2, hne⟩ := exists_two_mem_of_two_le_card hB2
  obtain ⟨p, hps, hpf, hpsupp⟩ :=
    exists_anchor_B_ended H.hBYcomplete hb1 hb2 hne r hsY hfY
      H.hdisjBW H.hdisjBY hrsub
  -- Remaining terminals and the anchor form a B-ended cover of B ∪ W ∪ used Y.
  let remB : Finset V := (H.B.erase b1).erase b2
  have hremB : remB ⊆ H.B := (erase_subset _ _).trans (erase_subset _ _)
  have hdisjRem : Disjoint remB p.support := by
    refine Finset.disjoint_left.2 ?_
    intro x hxrem hxp
    have hxB : x ∈ H.B := hremB hxrem
    have hxne2 : x ≠ b2 := (mem_erase.mp hxrem).1
    have hxne1 : x ≠ b1 := (mem_erase.mp (mem_erase.mp hxrem).2).1
    have hxps : x ∈ {b1} ∪ r.support ∪ {b2} := by rwa [hpsupp] at hxp
    rcases mem_union.1 hxps with hxL | hxR
    · rcases mem_union.1 hxL with hx1 | hxr
      · exact hxne1 (mem_singleton.1 hx1)
      · have : x ∈ H.W ∪ H.Y := hrsub hxr
        rcases mem_union.1 this with hW | hY
        · exact Finset.disjoint_left.1 H.hdisjBW hxB hW
        · exact Finset.disjoint_left.1 H.hdisjBY hxB hY
    · exact hxne2 (mem_singleton.1 hxR)
  have hpc0supp : p.support ∪ remB = H.B ∪ r.support := by
    ext x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxp | hxrem
      · have : x ∈ {b1} ∪ r.support ∪ {b2} := by rwa [hpsupp] at hxp
        rcases mem_union.1 this with hxL | hxR
        · rcases mem_union.1 hxL with hx1 | hxr
          · exact mem_union.2 (Or.inl (by simpa [mem_singleton.1 hx1] using hb1))
          · exact mem_union.2 (Or.inr hxr)
        · exact mem_union.2 (Or.inl (by simpa [mem_singleton.1 hxR] using hb2))
      · exact mem_union.2 (Or.inl (hremB hxrem))
    · intro hx
      rcases mem_union.1 hx with hxB | hxr
      · by_cases h1 : x = b1
        · refine mem_union.2 (Or.inl ?_)
          have : x ∈ {b1} ∪ r.support ∪ {b2} := by
            simp [h1]
          rwa [← hpsupp] at this
        · by_cases h2 : x = b2
          · refine mem_union.2 (Or.inl ?_)
            have : x ∈ {b1} ∪ r.support ∪ {b2} := by
              simp [h2]
            rwa [← hpsupp] at this
          · refine mem_union.2 (Or.inr ?_)
            exact mem_erase.2 ⟨h2, mem_erase.2 ⟨h1, hxB⟩⟩
      · refine mem_union.2 (Or.inl ?_)
        have : x ∈ {b1} ∪ r.support ∪ {b2} :=
          mem_union.2 (Or.inl (mem_union.2 (Or.inr hxr)))
        rwa [← hpsupp] at this
  let pcAnchor : PathCover G p.support := PathCover.ofSupport p rfl
  let pcRem : PathCover G remB := PathCover.singletons (G := G) remB
  have htermA : IsTerminalCover (G := G) H.B pcAnchor :=
    PathCover.ofSupport_terminal p rfl (by simpa [hps]) (by simpa [hpf])
  have htermR : IsTerminalCover (G := G) H.B pcRem :=
    PathCover.singletons_terminal hremB
  let pc0' := PathCover.appendDisjoint hdisjRem pcRem pcAnchor
  have hU0 : remB ∪ p.support = H.B ∪ r.support := by
    simpa [union_comm] using hpc0supp
  let pc0 : PathCover G (H.B ∪ r.support) := pc0'.cast hU0
  have hcard0 : pc0.card = H.B.card - 1 := by
    have h2le : 2 ≤ H.B.card := hB2
    have hb2e : b2 ∈ H.B.erase b1 := mem_erase.2 ⟨hne.symm, hb2⟩
    have hremc : remB.card = H.B.card - 2 := by
      simp [remB, card_erase_of_mem hb2e, card_erase_of_mem hb1]
      omega
    have := PathCover.appendDisjoint_card hdisjRem pcRem pcAnchor
    have hA : pcAnchor.card = 1 := PathCover.ofSupport_card p rfl
    have hR : pcRem.card = remB.card := PathCover.singletons_card remB
    rw [PathCover.cast_card, this, hA, hR, hremc]
    omega
  have hterm0 : IsTerminalCover (G := G) H.B pc0 := by
    intro s hs
    rw [PathCover.cast_paths] at hs
    have : s ∈ pcRem.paths ∨ s ∈ pcAnchor.paths :=
      (PathCover.appendDisjoint_mem_iff hdisjRem pcRem pcAnchor).1 hs
    rcases this with h | h
    · exact htermR s h
    · exact htermA s h

  have hidxY : ∀ j : ℕ, j < H.d q - 1 → H.a q + 1 + j < pcY.card := by
    intro j hj
    have hck : pcY.card = H.k q := hYcard
    change pcY.card = H.a q + H.d q at hck
    omega
  let extra : ℕ → Finset V := fun t =>
    (Finset.range t).biUnion fun j =>
      if hj : j < H.d q - 1 then
        (pathAt pcY ⟨H.a q + 1 + j, hidxY j hj⟩).support
      else
        ∅
  have extra_zero : extra 0 = ∅ := by
    simp [extra]
  have extra_succ : ∀ t, extra (t + 1) =
      extra t ∪
        (if ht : t < H.d q - 1 then
          (pathAt pcY ⟨H.a q + 1 + t, hidxY t ht⟩).support
        else ∅) := by
    intro t
    ext x
    simp only [extra, mem_union, mem_biUnion, mem_range]
    constructor
    · intro hx
      obtain ⟨j, hj, hxj⟩ := hx
      have hsplit : j < t ∨ j = t := Nat.lt_succ_iff_lt_or_eq.mp hj
      rcases hsplit with hlt | rfl
      · exact Or.inl ⟨j, hlt, hxj⟩
      · exact Or.inr hxj
    · intro hx
      rcases hx with ⟨j, hjt, hxj⟩ | hxj
      · exact ⟨j, Nat.lt_succ_of_lt hjt, hxj⟩
      · exact ⟨t, Nat.lt_succ_self t, hxj⟩
  have go :
      ∀ (t : ℕ) (ht : t ≤ H.d q - 1),
        ∃ pc : PathCover G (H.B ∪ r.support ∪ extra t),
          pc.card = H.B.card - 1 - t ∧
            IsTerminalCover (G := G) H.B pc := by
    intro t
    induction t with
    | zero =>
      intro _ht
      have hU : H.B ∪ r.support ∪ extra 0 = H.B ∪ r.support := by
        simp [extra_zero]
      refine ⟨pc0.cast hU.symm, ?_, ?_⟩
      · rw [PathCover.cast_card]
        simpa only [Nat.sub_zero] using hcard0
      · intro s hs
        rw [PathCover.cast_paths] at hs
        exact hterm0 s hs
    | succ t ih =>
      intro ht
      obtain ⟨pc, hcard, hterm⟩ := ih (Nat.le_of_succ_le ht)
      have htlt : t < H.d q - 1 := by omega
      have h2 : 2 ≤ pc.card := by
        have hq2 : 2 ≤ q := le_trans (by simpa [NoBVJoinBase.K] using H.hpK) hlo
        omega
      let block := pathAt pcY ⟨H.a q + 1 + t, hidxY t htlt⟩
      have hblockY : block.support ⊆ H.Y := pathAt_support_subset pcY _
      have hdisjU : Disjoint block.support (H.B ∪ r.support ∪ extra t) := by
        refine Finset.disjoint_left.2 ?_
        intro x hxb hxU
        have hxY : x ∈ H.Y := hblockY hxb
        rcases mem_union.1 hxU with hxL | hxE
        · rcases mem_union.1 hxL with hxB | hxr
          · exact Finset.disjoint_left.1 H.hdisjBY hxB hxY
          · rcases (hrmem x).1 hxr with ⟨i, hxi⟩ | ⟨j, hxj⟩
            · have hne : (⟨i.1, Nat.lt_of_lt_of_le i.2 haY⟩ : Fin pcY.card) ≠
                  ⟨H.a q + 1 + t, hidxY t htlt⟩ := by
                intro h
                have : i.1 = H.a q + 1 + t := congrArg Fin.val h
                omega
              exact Finset.disjoint_left.1 (pathAt_disjoint pcY hne) hxi hxb
            · exact Finset.disjoint_left.1 H.hdisjWY
                (pathAt_support_subset pcW _ hxj) hxY
        · obtain ⟨j, hjrange, hxj⟩ := mem_biUnion.1 hxE
          have hjt : j < t := mem_range.mp hjrange
          have hjlt : j < H.d q - 1 := by omega
          have hxj' : x ∈ (pathAt pcY ⟨H.a q + 1 + j, hidxY j hjlt⟩).support := by
            simpa [extra, hjlt] using hxj
          have hne : (⟨H.a q + 1 + j, hidxY j hjlt⟩ : Fin pcY.card) ≠
              ⟨H.a q + 1 + t, hidxY t htlt⟩ := by
            intro h
            have : H.a q + 1 + j = H.a q + 1 + t := congrArg Fin.val h
            omega
          exact Finset.disjoint_left.1 (pathAt_disjoint pcY hne) hxj' hxb
      obtain ⟨pc1, hcard1, hend1⟩ :=
        exists_splice_two_through_block H.hBYcomplete pc h2 hterm block hblockY hdisjU
      have hUeq : (H.B ∪ r.support ∪ extra t) ∪ block.support =
          H.B ∪ r.support ∪ extra (t + 1) := by
        have hif : (if ht' : t < H.d q - 1 then
            (pathAt pcY ⟨H.a q + 1 + t, hidxY t ht'⟩).support else ∅) =
            block.support := by
          simp [block, htlt]
        rw [extra_succ, hif, union_assoc]
      exact ⟨pc1.cast hUeq, by rw [PathCover.cast_card, hcard1]; omega, by
        intro s hs
        rw [PathCover.cast_paths] at hs
        exact hend1 s hs⟩
  obtain ⟨pcFin, hcardFin, htermFin⟩ := go (H.d q - 1) le_rfl
  have hUeqK : H.B ∪ r.support ∪ extra (H.d q - 1) = H.K := by
    ext x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxL | hxE
      · rcases mem_union.1 hxL with hxB | hxr
        · exact H.B_subset_K hxB
        · have : x ∈ H.W ∪ H.Y := hrsub hxr
          rcases mem_union.1 this with hW | hY
          · exact H.W_subset_K hW
          · exact H.Y_subset_K hY
      · obtain ⟨j, hjrange, hxj⟩ := mem_biUnion.1 hxE
        have hj : j < H.d q - 1 := mem_range.mp hjrange
        have hjlt : j < H.d q - 1 := hj
        have : x ∈ H.Y := pathAt_support_subset pcY _ (by
          simpa [extra, hjlt] using hxj)
        exact H.Y_subset_K this
    · intro hx
      have hx' : x ∈ H.B ∨ x ∈ H.W ∨ x ∈ H.Y := by
        simpa [NoBVJoinBase.K, mem_union, or_assoc] using hx
      rcases hx' with hxB | hxW | hxY
      · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl hxB)))
      · obtain ⟨pw, hpw, hxw⟩ := (pcW.mem_iff x).1 hxW
        obtain ⟨j, rfl⟩ := exists_pathAt pcW hpw
        have : x ∈ r.support :=
          (hrmem x).2 (Or.inr ⟨⟨j.1, by simpa [hWcard] using j.2⟩, by simpa using hxw⟩)
        exact mem_union.2 (Or.inl (mem_union.2 (Or.inr this)))
      · obtain ⟨py, hpy, hxy⟩ := (pcY.mem_iff x).1 hxY
        obtain ⟨i, rfl⟩ := exists_pathAt pcY hpy
        by_cases hi : i.1 < H.a q + 1
        · have : x ∈ r.support :=
            (hrmem x).2 (Or.inl ⟨⟨i.1, hi⟩, by simpa using hxy⟩)
          exact mem_union.2 (Or.inl (mem_union.2 (Or.inr this)))
        · have hge : H.a q + 1 ≤ i.1 := Nat.le_of_not_gt hi
          have hj : i.1 - (H.a q + 1) < H.d q := by
            have : i.1 < pcY.card := i.2
            have : pcY.card = H.a q + H.d q := by
              simpa [NoBVJoinBase.k] using hYcard
            omega
          have hje : i.1 - (H.a q + 1) < H.d q - 1 ∨
              i.1 - (H.a q + 1) = H.d q - 1 := by omega
          -- both included: range (d-1) is 0..d-2, last index d-2 = a+d-1 - (a+1) wait
          -- extra (d-1) includes j = 0..d-2, indices a+1 .. a+d-1
          -- last Y index is k-1 = a+d-1. j = (a+d-1)-(a+1) = d-2.
          -- So j max in extra(d-1) is d-2, missing j = d-1?
          -- k = a+d paths indexed 0..a+d-1
          -- chain uses 0..a (a+1 paths)
          -- extra (d-1) uses j=0..d-2, indices a+1 .. a+d-1 - wait a+1+(d-2)=a+d-1. Yes last index a+d-1.
          -- j = d-2 max, j < d-1. Index a+1+(d-2)=a+d-1 = k-1. All remaining Y-paths included.
          have hjlt : i.1 - (H.a q + 1) < H.d q - 1 := by
            have : i.1 < pcY.card := i.2
            have : pcY.card = H.a q + H.d q := by
              simpa [NoBVJoinBase.k] using hYcard
            have : i.1 ≤ H.a q + H.d q - 1 := by omega
            omega
          refine mem_union.2 (Or.inr ?_)
          refine mem_biUnion.2 ⟨i.1 - (H.a q + 1), mem_range.2 hjlt, ?_⟩
          have hjlt' : i.1 - (H.a q + 1) < H.d q - 1 := hjlt
          have hidx : H.a q + 1 + (i.1 - (H.a q + 1)) = i.1 := by omega
          have hfin : (⟨H.a q + 1 + (i.1 - (H.a q + 1)), hidxY _ hjlt'⟩ : Fin pcY.card) = i :=
            Fin.ext hidx
          have hxif : x ∈
              (if h : i.1 - (H.a q + 1) < H.d q - 1 then
                (pathAt pcY ⟨H.a q + 1 + (i.1 - (H.a q + 1)), hidxY _ h⟩).support
              else ∅) := by
            simp [hjlt', hfin]
            exact hxy
          simpa [extra] using hxif
  let pcK : PathCover G H.K := pcFin.cast hUeqK
  refine ⟨pcK, ?_, ?_⟩
  · have hcd : pcFin.card = q := by
      have : H.B.card - 1 - (H.d q - 1) = H.B.card - H.d q := by omega
      have : H.B.card - H.d q = q := by
        change H.B.card - (H.B.card - q) = q
        have hqB : q ≤ H.B.card := by omega
        omega
      omega
    change (pcFin.cast hUeqK).card = q
    rw [PathCover.cast_card]
    exact hcd
  · intro s hs
    rw [PathCover.cast_paths] at hs
    exact htermFin s hs

lemma exists_min_terminalCover_noBV :
    ∃ pc : PathCover G H.K,
      pc.card = pathCoverNumber G H.K ∧
        IsTerminalCover (G := G) H.B pc :=
  H.exists_terminalCover_noBV_of_card le_rfl H.interval_nonempty

lemma exists_terminalCover_noBV_spectrum {q : ℕ}
    (hlo : pathCoverNumber G H.K ≤ q)
    (hhi : q + pathCoverNumber G (H.K \ H.B) ≤ H.B.card) :
    ∃ pc : PathCover G H.K,
      pc.card = q ∧ IsTerminalCover (G := G) H.B pc :=
  H.exists_terminalCover_noBV_of_card hlo hhi

end NoBVJoinBase

end Nikoghosyan
