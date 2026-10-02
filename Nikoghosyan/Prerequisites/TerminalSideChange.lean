/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalCanonicalJoin

/-!
# Terminal side-change for a general small-`p(D)` mixed child

On a canonical complete join `K = X ∨ Y` with mixed split `X = D ⊔ I`,
the side-change lemma does **not** require a unique inner `B`-profile.
If `p(D) ≤ |Y| - 1` and `p(K) ≥ 2`, ordinary join/union recurrences give
`p(K) = p(D) + |I| - |Y|`, hence `|I| ≥ 3`. Strict `TerminalHypothesis`
on `(K, I)` follows by a complete survivor split:

* empty cut: `K` is connected and `I` is nonempty;
* `Y` deleted: free `I`-components are those of `D \ S`, and
  `c(D-SD) ≤ p(D) + |SD| ≤ |Y| - 1 + |SD|`;
* `Y` survives and `I` survives: the original complete join connects the
  remainder through a surviving terminal, free count `0`;
* `Y` survives, `I` deleted, `D` survives: the remainder is connected,
  free count `1`, and `|I| ≥ 3` supplies the strict bound;
* `X` deleted: `c(Y-SY) ≤ p(Y) + |SY| ≤ |X| - 1 + |SY|`.

The already proved `NoBVJoinBase` with terminals `I`, nonterminal block
`D` and connector `Y` then supplies an actual minimum `I`-ended cover of
`K`. Since `I ⊆ B`, this is a minimum original-`B` cover. No unique
profile, no supplied `B`-ended cover, and no assumed minimum cover of
`D` are used. The `I`-terminal spectrum is not claimed to be the original
`B` interval.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Remainder identities -/

lemma sdiff_union_eq_sdiff_of_subset_right {A B S : Finset V}
    (hB : B ⊆ S) : (A ∪ B) \ S = A \ S := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hx
    rcases hx.1 with hA | hB'
    · exact ⟨hA, hx.2⟩
    · exact (hx.2 (hB hB')).elim
  · intro hx
    exact ⟨Or.inl hx.1, hx.2⟩

lemma sdiff_union_eq_sdiff_of_subset_left {A B S : Finset V}
    (hA : A ⊆ S) : (A ∪ B) \ S = B \ S := by
  rw [union_comm]
  exact sdiff_union_eq_sdiff_of_subset_right hA

lemma sdiff_union_distrib (A B S : Finset V) :
    (A ∪ B) \ S = (A \ S) ∪ (B \ S) :=
  union_sdiff_distrib A B S

lemma sdiff_eq_sdiff_inter {A B : Finset V} : A \ B = A \ (B ∩ A) := by
  ext x
  simp only [mem_sdiff, mem_inter]
  constructor
  · intro h
    exact ⟨h.1, fun hBA => h.2 hBA.1⟩
  · intro h
    exact ⟨h.1, fun hB => h.2 ⟨hB, h.1⟩⟩

lemma IsCompleteBetween.mono_sdiff {A B S : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    G.IsCompleteBetween ((A \ S : Finset V) : Set V)
      ((B \ S : Finset V) : Set V) :=
  IsCompleteBetween.mono hAB sdiff_subset sdiff_subset

/-! ### Free-component helpers -/

lemma ncard_free_eq_componentCount_of_disjoint {A T : Finset V}
    (h : Disjoint A T) :
    Nat.card
        { C : (G.induce (A : Set V)).ConnectedComponent //
          componentFinset G A C ∩ T = ∅ } =
      componentCount G A := by
  unfold componentCount
  refine Nat.card_congr ?_
  exact Equiv.subtypeUnivEquiv fun C => by
    apply eq_empty_of_forall_notMem
    intro x hx
    exact Finset.disjoint_left.1 h
      (componentFinset_subset (G := G) C (mem_inter.1 hx).1)
      (mem_inter.1 hx).2

/-- A connected remainder that still meets the surviving terminals is
`B`-free-count zero. -/
lemma terminalComponentCount_eq_zero_of_connected_meets
    {K B S : Finset V} {b : V}
    (hbKS : b ∈ K \ S) (hbBS : b ∈ B \ S)
    (hconn : (G.induce ((K \ S : Finset V) : Set V)).Connected) :
    terminalComponentCount (G := G) K B S = 0 := by
  haveI : Fintype
      { C : (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent //
        IsFreeComponent (G := G) K B S C } := inferInstance
  unfold terminalComponentCount
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_eq_zero_iff.2 ⟨fun C => ?_⟩
  have hss : Subsingleton
      (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  have hCeq :
      C.1 =
        (G.induce ((K \ S : Finset V) : Set V)).connectedComponentMk
          ⟨b, hbKS⟩ :=
    Subsingleton.elim _ _
  have hbC : b ∈ componentFinset G (K \ S) C.1 := by
    rw [hCeq]
    exact mem_filter.2 ⟨hbKS, ⟨hbKS, rfl⟩⟩
  exact notMem_empty b (C.2 ▸ mem_inter.2 ⟨hbC, hbBS⟩)

lemma disjoint_sdiff_sideChange {A B S : Finset V} (h : Disjoint A B) :
    Disjoint (A \ S) (B \ S) :=
  h.mono sdiff_subset sdiff_subset

lemma nocross_sdiff {A B S : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    ∀ a ∈ A \ S, ∀ b ∈ B \ S, ¬ G.Adj a b :=
  fun a ha b hb => hnocross a (mem_sdiff.1 ha).1 b (mem_sdiff.1 hb).1

/-! ### Cardinality of the isolated terminals -/

namespace CanonicalJoinSplit

variable (H : CanonicalJoinSplit (G := G))

lemma union_I_D_Y (s : MixedSplit (G := G) H.X H.B) :
    s.I ∪ s.D ∪ H.Y = H.K := by
  have hX : s.D ∪ s.I = H.X := s.hDU
  calc
    s.I ∪ s.D ∪ H.Y = (s.D ∪ s.I) ∪ H.Y := by
      rw [union_comm s.I s.D]
    _ = H.X ∪ H.Y := by rw [hX]
    _ = H.K := H.union_X_Y

lemma D_subset_X (s : MixedSplit (G := G) H.X H.B) : s.D ⊆ H.X := s.hDsub

lemma D_subset_K (s : MixedSplit (G := G) H.X H.B) : s.D ⊆ H.K :=
  (H.D_subset_X s).trans sdiff_subset

lemma I_subset_K (s : MixedSplit (G := G) H.X H.B) : s.I ⊆ H.K :=
  (H.I_subset_X s).trans sdiff_subset

lemma disjoint_D_Y (s : MixedSplit (G := G) H.X H.B) : Disjoint s.D H.Y :=
  disjoint_of_subset_left (H.D_subset_X s) H.disjoint_X_Y

lemma disjoint_I_Y (s : MixedSplit (G := G) H.X H.B) : Disjoint s.I H.Y :=
  disjoint_of_subset_left (H.I_subset_X s) H.disjoint_X_Y

lemma Independent_I (s : MixedSplit (G := G) H.X H.B) :
    Independent (G := G) s.I :=
  H.hInd.mono s.hI

lemma pathCoverNumber_I (s : MixedSplit (G := G) H.X H.B) :
    pathCoverNumber G s.I = s.I.card :=
  pathCoverNumber_eq_card_of_independent (G := G) (H.Independent_I s)

lemma pathCoverNumber_X_of_mixed (s : MixedSplit (G := G) H.X H.B) :
    pathCoverNumber G H.X =
      pathCoverNumber G s.D + s.I.card := by
  have hsum :=
    Cograph.pathCoverNumber_disjoint_union (G := G) s.hdisj s.hnocross
  have hX : s.D ∪ s.I = H.X := s.hDU
  simpa [hX, H.pathCoverNumber_I s] using hsum

lemma pathCoverNumber_Y_lt_X :
    pathCoverNumber G H.Y + 1 ≤ H.X.card :=
  pathCoverNumber_B_free_join_side_lt (G := G) H.X_nonempty H.hYne
    H.complete_X_Y (by simpa [H.union_X_Y] using H.hcog) H.B_subset_X
    (by simpa [H.union_X_Y] using H.hTH)

/-- Join recurrence on the canonical split: `p(K) ≥ 2` forces
`p(K) = p(X) - |Y|`. -/
lemma pathCoverNumber_K_eq_X_sub_Y
    (hpK : 2 ≤ pathCoverNumber G H.K) :
    pathCoverNumber G H.K = pathCoverNumber G H.X - H.Y.card := by
  have hj :=
    pathCoverNumber_complete_join H.X_nonempty H.hYne H.complete_X_Y
  have hunion : H.X ∪ H.Y = H.K := H.union_X_Y
  rw [hunion] at hj
  have hpYle : pathCoverNumber G H.Y ≤ H.X.card := by
    have := H.pathCoverNumber_Y_lt_X
    omega
  have hY0 : pathCoverNumber G H.Y - H.X.card = 0 :=
    Nat.sub_eq_zero_of_le hpYle
  have hnot1 : pathCoverNumber G H.K ≠ 1 := by omega
  have hmax :
      max 1 (max (pathCoverNumber G H.X - H.Y.card)
        (pathCoverNumber G H.Y - H.X.card)) =
        pathCoverNumber G H.X - H.Y.card := by
    have hpos : 1 ≤ pathCoverNumber G H.X - H.Y.card := by
      have : pathCoverNumber G H.K =
          max 1 (max (pathCoverNumber G H.X - H.Y.card) 0) := by
        simpa [hY0] using hj
      have hne1 :
          max 1 (max (pathCoverNumber G H.X - H.Y.card) 0) ≠ 1 := by
        simpa [this] using hnot1
      have :
          ¬ pathCoverNumber G H.X - H.Y.card ≤ 1 ∨
            1 < pathCoverNumber G H.X - H.Y.card := by
        omega
      omega
    simp [hY0, max_eq_right hpos]
  exact hj.trans hmax

lemma pathCoverNumber_K_eq_mixed
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K) :
    pathCoverNumber G H.K =
      pathCoverNumber G s.D + s.I.card - H.Y.card := by
  rw [H.pathCoverNumber_K_eq_X_sub_Y hpK, H.pathCoverNumber_X_of_mixed s]

/-- Isolated terminals are at least three when the mixed child is
`Y`-small and the host cover number is at least two. -/
lemma I_card_ge_three
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    3 ≤ s.I.card := by
  have hXeq : pathCoverNumber G H.X =
      pathCoverNumber G s.D + s.I.card := H.pathCoverNumber_X_of_mixed s
  have hKeq : pathCoverNumber G H.K =
      pathCoverNumber G H.X - H.Y.card := H.pathCoverNumber_K_eq_X_sub_Y hpK
  have hYle : H.Y.card ≤ pathCoverNumber G H.X := by
    have : 1 ≤ pathCoverNumber G H.X - H.Y.card := by
      have hne1 : pathCoverNumber G H.K ≠ 1 := by omega
      have : pathCoverNumber G H.K = pathCoverNumber G H.X - H.Y.card := hKeq
      omega
    omega
  have hsum : s.I.card + pathCoverNumber G s.D =
      pathCoverNumber G H.K + H.Y.card := by
    have : pathCoverNumber G H.X =
        pathCoverNumber G H.K + H.Y.card := by
      have := Nat.sub_add_cancel hYle
      omega
    omega
  have hge : 3 + pathCoverNumber G s.D ≤
      pathCoverNumber G H.K + H.Y.card := by omega
  omega

lemma I_nonempty_of_small_pD
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    s.I.Nonempty := by
  have hpos : 0 < s.I.card :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 3) (H.I_card_ge_three s hpK hpD)
  exact card_pos.mp hpos

/-! ### Strict `TH(K, I)` -/

lemma terminalComponentCount_I_empty
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    terminalComponentCount (G := G) H.K s.I ∅ = 0 := by
  obtain ⟨i, hi⟩ := H.I_nonempty_of_small_pD s hpK hpD
  have hiK : i ∈ H.K \ (∅ : Finset V) := by
    simpa [sdiff_empty] using H.I_subset_K s hi
  have hiI : i ∈ s.I \ (∅ : Finset V) := by simpa [sdiff_empty] using hi
  have hconn : (G.induce ((H.K \ (∅ : Finset V) : Finset V) : Set V)).Connected := by
    have hEq : H.K \ (∅ : Finset V) = H.K := sdiff_empty
    rw [hEq]
    exact H.hconn
  exact terminalComponentCount_eq_zero_of_connected_meets (G := G)
    hiK hiI hconn

/-- Deleting the whole connector: free `I`-count equals `c(D \ S)`. -/
lemma terminalComponentCount_I_of_Y_subset
    (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    (_hS : S ⊆ H.K) (hY : H.Y ⊆ S) :
    terminalComponentCount (G := G) H.K s.I S =
      componentCount G (s.D \ S) := by
  have hKeq : H.K \ S = H.X \ S := by
    have hunion : H.X ∪ H.Y = H.K := H.union_X_Y
    rw [← hunion]
    exact sdiff_union_eq_sdiff_of_subset_right hY
  have hXeq : H.X \ S = (s.D \ S) ∪ (s.I \ S) :=
    (congrArg (fun t => t \ S) s.hDU.symm).trans
      (union_sdiff_distrib s.D s.I S)
  have hRem : H.K \ S = (s.D \ S) ∪ (s.I \ S) := by
    rw [hKeq, hXeq]
  have hIeq : s.I \ S = s.I \ S := rfl
  have hnc := nocross_sdiff (G := G) s.hnocross (S := S)
  have hJ : s.I \ S ⊆ s.I \ S := subset_rfl
  unfold terminalComponentCount IsFreeComponent
  have h1 :
      Nat.card
          { C : (G.induce ((H.K \ S : Finset V) : Set V)).ConnectedComponent //
            componentFinset G (H.K \ S) C ∩ (s.I \ S) = ∅ } =
        Nat.card
          { C : (G.induce
              (((s.D \ S) ∪ (s.I \ S) : Finset V) : Set V)).ConnectedComponent //
            componentFinset G ((s.D \ S) ∪ (s.I \ S)) C ∩ (s.I \ S) = ∅ } := by
    rw [hRem]
  have h2 :=
    ncard_free_union_isolates (G := G) (A := s.D \ S) (J := s.I \ S)
      (T := s.I \ S) hnc hJ
  have hdisj : Disjoint (s.D \ S) (s.I \ S) :=
    disjoint_sdiff_sideChange s.hdisj
  have h3 :=
    ncard_free_eq_componentCount_of_disjoint (G := G) (A := s.D \ S)
      (T := s.I \ S) hdisj
  exact h1.trans (h2.trans h3)

lemma terminalComponentCount_I_Y_deleted_le
    (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    (hS : S ⊆ H.K) (hY : H.Y ⊆ S)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    terminalComponentCount (G := G) H.K s.I S ≤ S.card - 1 := by
  have hz :
      terminalComponentCount (G := G) H.K s.I S =
        componentCount G (s.D \ S) :=
    H.terminalComponentCount_I_of_Y_subset s hS hY
  have hSD : S ∩ s.D ⊆ s.D := inter_subset_right
  have hDs : s.D \ S = s.D \ (S ∩ s.D) := sdiff_eq_sdiff_inter
  have hcle :
      componentCount G (s.D \ S) ≤
        pathCoverNumber G s.D + (S ∩ s.D).card := by
    rw [hDs]
    exact componentCount_sdiff_le (G := G) s.D (S ∩ s.D) hSD
  have hdisjYD : Disjoint H.Y (S ∩ s.D) :=
    (H.disjoint_D_Y s).symm.mono_right inter_subset_right
  have hsub : H.Y ∪ (S ∩ s.D) ⊆ S :=
    union_subset hY inter_subset_left
  have hcard : H.Y.card + (S ∩ s.D).card ≤ S.card := by
    have hcu : (H.Y ∪ (S ∩ s.D)).card = H.Y.card + (S ∩ s.D).card :=
      card_union_of_disjoint hdisjYD
    have hle := card_le_card hsub
    omega
  have hYpos : 1 ≤ H.Y.card := card_pos.2 H.hYne
  have : componentCount G (s.D \ S) + 1 ≤ S.card := by omega
  have hz' :
      terminalComponentCount (G := G) H.K s.I S + 1 ≤ S.card := by
    simpa [hz] using this
  omega

lemma remainder_eq_X_union_Y_sdiff (S : Finset V) :
    H.K \ S = (H.X \ S) ∪ (H.Y \ S) := by
  have hunion : H.X ∪ H.Y = H.K := H.union_X_Y
  rw [← hunion, union_sdiff_distrib]

lemma complete_remaining (S : Finset V) :
    G.IsCompleteBetween ((H.X \ S : Finset V) : Set V)
      ((H.Y \ S : Finset V) : Set V) :=
  IsCompleteBetween.mono_sdiff (S := S) H.complete_X_Y

lemma connected_remaining_join {S : Finset V}
    (hX : (H.X \ S).Nonempty) (hY : (H.Y \ S).Nonempty) :
    (G.induce ((H.K \ S : Finset V) : Set V)).Connected := by
  rw [H.remainder_eq_X_union_Y_sdiff S]
  exact Cograph.induce_connected_of_completeJoin (G := G) hX hY
    (H.complete_remaining S)

lemma X_sdiff_eq_D_union_I (s : MixedSplit (G := G) H.X H.B) (S : Finset V) :
    H.X \ S = (s.D \ S) ∪ (s.I \ S) :=
  (congrArg (fun t => t \ S) s.hDU.symm).trans
    (union_sdiff_distrib s.D s.I S)

lemma I_sdiff_subset_K_sdiff (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    {i : V} (hi : i ∈ s.I \ S) : i ∈ H.K \ S :=
  mem_sdiff.2 ⟨H.I_subset_K s (mem_sdiff.1 hi).1, (mem_sdiff.1 hi).2⟩

lemma I_sdiff_subset_X_sdiff (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    {i : V} (hi : i ∈ s.I \ S) : i ∈ H.X \ S :=
  mem_sdiff.2 ⟨H.I_subset_X s (mem_sdiff.1 hi).1, (mem_sdiff.1 hi).2⟩

lemma D_sdiff_subset_X_sdiff (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    {d : V} (hd : d ∈ s.D \ S) : d ∈ H.X \ S :=
  mem_sdiff.2 ⟨H.D_subset_X s (mem_sdiff.1 hd).1, (mem_sdiff.1 hd).2⟩

/-- `Y` survives and `I` survives: remainder is a complete join meeting
`I`, so the free count is zero. -/
lemma terminalComponentCount_I_Y_I_survive
    (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    (hY : (H.Y \ S).Nonempty) (hI : (s.I \ S).Nonempty) :
    terminalComponentCount (G := G) H.K s.I S = 0 := by
  obtain ⟨i, hi⟩ := hI
  have hXne : (H.X \ S).Nonempty := ⟨i, H.I_sdiff_subset_X_sdiff s hi⟩
  have hconn := H.connected_remaining_join hXne hY
  exact terminalComponentCount_eq_zero_of_connected_meets (G := G)
    (H.I_sdiff_subset_K_sdiff s hi) hi hconn

/-- `Y` survives, `I` is deleted, `D` survives: one connected free
component. -/
lemma terminalComponentCount_I_Y_survive_I_deleted_D_survive
    (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    (hY : (H.Y \ S).Nonempty) (hI : s.I ⊆ S) (hD : (s.D \ S).Nonempty) :
    terminalComponentCount (G := G) H.K s.I S = 1 := by
  obtain ⟨d, hd⟩ := hD
  have hXne : (H.X \ S).Nonempty := ⟨d, H.D_sdiff_subset_X_sdiff s hd⟩
  have hconn := H.connected_remaining_join hXne hY
  have hUne : (H.K \ S).Nonempty := ⟨d, mem_sdiff.2
    ⟨H.D_subset_K s (mem_sdiff.1 hd).1, (mem_sdiff.1 hd).2⟩⟩
  have hc1 :=
    Cograph.componentCount_eq_one_of_connected (G := G) hUne hconn
  have hIsub : s.I ⊆ S := hI
  have hz :=
    terminalComponentCount_eq_of_B_subset (G := G) (K := H.K) (B := s.I)
      (S := S) hIsub
  omega

lemma terminalComponentCount_I_X_deleted
    (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    (_hS : S ⊆ H.K) (hX : H.X ⊆ S) :
    terminalComponentCount (G := G) H.K s.I S =
      componentCount G (H.Y \ S) := by
  have hKeq : H.K \ S = H.Y \ S := by
    have hunion : H.X ∪ H.Y = H.K := H.union_X_Y
    rw [← hunion]
    exact sdiff_union_eq_sdiff_of_subset_left hX
  have hIsub : s.I ⊆ S := (H.I_subset_X s).trans hX
  have hz :=
    terminalComponentCount_eq_of_B_subset (G := G) (K := H.K) (B := s.I)
      (S := S) hIsub
  simpa [hKeq] using hz

lemma terminalComponentCount_I_X_deleted_le
    (s : MixedSplit (G := G) H.X H.B) {S : Finset V}
    (hS : S ⊆ H.K) (hX : H.X ⊆ S) :
    terminalComponentCount (G := G) H.K s.I S ≤ S.card - 1 := by
  have hz :
      terminalComponentCount (G := G) H.K s.I S =
        componentCount G (H.Y \ S) :=
    H.terminalComponentCount_I_X_deleted s hS hX
  have hSY : S ∩ H.Y ⊆ H.Y := inter_subset_right
  have hYs : H.Y \ S = H.Y \ (S ∩ H.Y) := sdiff_eq_sdiff_inter
  have hcle :
      componentCount G (H.Y \ S) ≤
        pathCoverNumber G H.Y + (S ∩ H.Y).card := by
    rw [hYs]
    exact componentCount_sdiff_le (G := G) H.Y (S ∩ H.Y) hSY
  have hpY := H.pathCoverNumber_Y_lt_X
  have hdisjXY : Disjoint H.X (S ∩ H.Y) :=
    disjoint_of_subset_right inter_subset_right H.disjoint_X_Y
  have hsub : H.X ∪ (S ∩ H.Y) ⊆ S :=
    union_subset hX inter_subset_left
  have hcard : H.X.card + (S ∩ H.Y).card ≤ S.card := by
    have hcu : (H.X ∪ (S ∩ H.Y)).card = H.X.card + (S ∩ H.Y).card :=
      card_union_of_disjoint hdisjXY
    have hle := card_le_card hsub
    omega
  have hXpos : 1 ≤ H.X.card := card_pos.2 H.X_nonempty
  have : componentCount G (H.Y \ S) + 1 ≤ S.card := by omega
  have hz' :
      terminalComponentCount (G := G) H.K s.I S + 1 ≤ S.card := by
    simpa [hz] using this
  omega

lemma terminalHypothesis_I_of_small_pD
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    TerminalHypothesis (G := G) H.K s.I := by
  refine ⟨H.terminalComponentCount_I_empty s hpK hpD, ?_⟩
  intro S hS hSne
  by_cases hYdel : H.Y ⊆ S
  · exact H.terminalComponentCount_I_Y_deleted_le s hS hYdel hpD
  · have hYsurv : (H.Y \ S).Nonempty := by
      obtain ⟨y, hy, hyS⟩ := not_subset.1 hYdel
      exact ⟨y, mem_sdiff.2 ⟨hy, hyS⟩⟩
    by_cases hIsurv : (s.I \ S).Nonempty
    · have hz := H.terminalComponentCount_I_Y_I_survive s hYsurv hIsurv
      have hpos : 1 ≤ S.card := card_pos.2 hSne
      omega
    · have hIdel : s.I ⊆ S := by
        intro i hi
        by_contra hiS
        exact hIsurv ⟨i, mem_sdiff.2 ⟨hi, hiS⟩⟩
      by_cases hDsurv : (s.D \ S).Nonempty
      · have hz :=
          H.terminalComponentCount_I_Y_survive_I_deleted_D_survive s
            hYsurv hIdel hDsurv
        have hIcard : 3 ≤ s.I.card := H.I_card_ge_three s hpK hpD
        have hScard : 3 ≤ S.card :=
          hIcard.trans (card_le_card hIdel)
        omega
      · have hDdel : s.D ⊆ S := by
          intro d hd
          by_contra hdS
          exact hDsurv ⟨d, mem_sdiff.2 ⟨hd, hdS⟩⟩
        have hXdel : H.X ⊆ S := by
          have hX : s.D ∪ s.I = H.X := s.hDU
          rw [← hX]
          exact union_subset hDdel hIdel
        exact H.terminalComponentCount_I_X_deleted_le s hS hXdel

/-! ### NoBV packaging on terminals `I` -/

noncomputable def toNoBVJoinBase_I
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    NoBVJoinBase (G := G) where
  B := s.I
  W := s.D
  Y := H.Y
  hBne := H.I_nonempty_of_small_pD s hpK hpD
  hYne := H.hYne
  hdisjBW := s.hdisj.symm
  hdisjBY := H.disjoint_I_Y s
  hdisjWY := H.disjoint_D_Y s
  hInd := H.Independent_I s
  hanti := by
    intro i hi d hd hadj
    exact s.hnocross d hd i hi hadj.symm
  hXY := by
    have hX : s.I ∪ s.D = H.X := by
      rw [union_comm, s.hDU]
    simpa [hX] using H.complete_X_Y
  hKcog := by
    have hEq : s.I ∪ s.D ∪ H.Y = H.K := H.union_I_D_Y s
    simpa [hEq] using H.hcog
  hTH := by
    have hEq : s.I ∪ s.D ∪ H.Y = H.K := H.union_I_D_Y s
    simpa [hEq] using H.terminalHypothesis_I_of_small_pD s hpK hpD
  hpK := by
    have hEq : s.I ∪ s.D ∪ H.Y = H.K := H.union_I_D_Y s
    simpa [hEq] using hpK

lemma toNoBVJoinBase_I_K
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    (H.toNoBVJoinBase_I s hpK hpD).K = H.K := by
  simp only [NoBVJoinBase.K, CanonicalJoinSplit.toNoBVJoinBase_I]
  exact H.union_I_D_Y s

/-- Actual minimum `I`-ended cover of the canonical host, hence a
minimum original-`B` cover, when the mixed child is `Y`-small. No unique
inner profile is assumed. -/
theorem exists_min_terminalCover_of_small_pD
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    ∃ pc : PathCover G H.K,
      pc.card = pathCoverNumber G H.K ∧
        IsTerminalCover (G := G) H.B pc := by
  let H0 := H.toNoBVJoinBase_I s hpK hpD
  obtain ⟨pc, hcard, hterm⟩ := H0.exists_min_terminalCover_noBV
  have hKeq : H0.K = H.K := H.toNoBVJoinBase_I_K s hpK hpD
  refine ⟨pc.cast hKeq, ?_, ?_⟩
  · rw [PathCover.cast_card, hcard]
    exact congrArg (pathCoverNumber G) hKeq
  · intro p hp
    rw [PathCover.cast_paths pc hKeq] at hp
    have ht := hterm p hp
    exact ⟨s.hI ht.1, s.hI ht.2⟩

end CanonicalJoinSplit

/-- Connected mixed repaired carrier: a remaining mixed child of the
canonical join with `p(D) ≤ |Y| - 1` and `p(K) ≥ 2` has an actual
minimum original-`B` path cover, obtained by side-changing the terminals
to the isolated set `I` and applying the checked no-BV construction.
No unique remaining profile is assumed. -/
theorem exists_min_terminalCover_of_canonical_small_pD
    (H : CanonicalJoinSplit (G := G))
    (s : MixedSplit (G := G) H.X H.B)
    (hpK : 2 ≤ pathCoverNumber G H.K)
    (hpD : pathCoverNumber G s.D + 1 ≤ H.Y.card) :
    ∃ pc : PathCover G H.K,
      pc.card = pathCoverNumber G H.K ∧
        IsTerminalCover (G := G) H.B pc :=
  H.exists_min_terminalCover_of_small_pD s hpK hpD

end Nikoghosyan
