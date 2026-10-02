/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.NonadjacentRows

/-!
# Manuscript `thm:remaining`

Original-host cut on the real `H / B / R` partition of a
`CanonicalNormalForm`, instantiated at the extended-cut container
`T = ownCut(x)`. Every own-group row sits in that cut by adjacent
constancy `cuts_eq_of_own_adj` and the full nonadjacent lemma. The
resulting original cut contradicts `OneTough`. Cut notation is imported
from `ExtendedCuts`; this file does not recopy those globals.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

variable {F : CycleFactor G} (N : CanonicalNormalForm F)

lemma exists_noncore_index : ∃ j : Fin F.card, j ≠ N.core := by
  have hlt : 1 < Fintype.card (Fin F.card) := by
    simpa [Fintype.card_fin] using
      (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) N.hThree)
  exact Fintype.exists_ne_of_one_lt_card hlt N.core

lemma disjoint_own_extendedHost {j : Fin F.card} (hj : j ≠ N.core) :
    Disjoint (ownSupport N hj) (extendedHost N hj) :=
  disjoint_union_right.2 ⟨(disjoint_core_own N hj).symm,
    disjoint_ownSupport_foreignSupport N hj⟩

lemma partition_host_own {j : Fin F.card} (hj : j ≠ N.core) :
    extendedHost N hj ∪ ownSupport N hj = univ := by
  simpa [extendedHost, union_comm, union_assoc, union_left_comm] using
    (partition_core_own_foreign N hj)

lemma disjoint_own_cut {j : Fin F.card} (hj : j ≠ N.core) {T : Finset V}
    (hTsub : T ⊆ extendedHost N hj) :
    Disjoint (ownSupport N hj) T :=
  Disjoint.mono_right hTsub (disjoint_own_extendedHost N hj)

/-- No original `B`–`(Q \ T)` edge. -/
lemma no_adj_own_sdiff_cut {j : Fin F.card} (hj : j ≠ N.core) {T : Finset V}
    (_hTsub : T ⊆ extendedHost N hj)
    (hrows : ∀ z ∈ ownSupport N hj, rowAt N z ⊆ T)
    {b q : V} (hb : b ∈ ownSupport N hj)
    (hq : q ∈ extendedHost N hj \ T) :
    ¬ G.Adj b q := by
  intro hadj
  have hqQ : q ∈ extendedHost N hj := (mem_sdiff.1 hq).1
  have hqT : q ∉ T := (mem_sdiff.1 hq).2
  rcases mem_union.1 hqQ with hqH | hqR
  · have hqA : q ∈ rowAt N b :=
      (mem_rowProfile_iff (G := G)).2 ⟨hqH, hadj⟩
    exact hqT (hrows b hb hqA)
  · exact anticomplete_own_foreign N hj hb hqR hadj

lemma univ_sdiff_cut_eq {j : Fin F.card} (hj : j ≠ N.core) {T : Finset V}
    (hTsub : T ⊆ extendedHost N hj) :
    univ \ T = (extendedHost N hj \ T) ∪ ownSupport N hj := by
  have hpart := partition_host_own N hj
  have hdisj := disjoint_own_cut N hj hTsub
  ext v
  constructor
  · intro hv
    have hvT : v ∉ T := (mem_sdiff.1 hv).2
    have hvQR : v ∈ extendedHost N hj ∪ ownSupport N hj :=
      hpart ▸ mem_univ v
    rcases mem_union.1 hvQR with hvQ | hvB
    · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hvQ, hvT⟩))
    · exact mem_union.2 (Or.inr hvB)
  · intro hv
    rcases mem_union.1 hv with hvQ | hvB
    · exact mem_sdiff.2 ⟨mem_univ v, (mem_sdiff.1 hvQ).2⟩
    · refine mem_sdiff.2 ⟨mem_univ v, ?_⟩
      intro hvT
      exact disjoint_left.1 hdisj hvB hvT

/-- Internal given-cut: `T ⊆ Q` containing every old `H`-row of `B`, with
`c(Q \ T) − |T| = δ ≥ 0`, contradicts original `OneTough`. -/
lemma oneTough_false_of_host_cut_containing_all_own_rows
    {j : Fin F.card} (hj : j ≠ N.core)
    (hTough : OneTough G)
    {T : Finset V} (hTsub : T ⊆ extendedHost N hj)
    (hrows : ∀ z ∈ ownSupport N hj, rowAt N z ⊆ T)
    {x : V} (hx : x ∈ ownSupport N hj)
    {δ : ℤ}
    (hatt : (componentCount G (extendedHost N hj \ T) : ℤ) - (T.card : ℤ) = δ)
    (hδ : 0 ≤ δ) :
    False := by
  have hBne : (ownSupport N hj).Nonempty := ownSupport_nonempty N hj
  have hAne : (rowAt N x).Nonempty := rowAt_nonempty N hj hx
  have hAsub : rowAt N x ⊆ T := hrows x hx
  have hTpos : 1 ≤ T.card :=
    Nat.succ_le_iff.2 (card_pos.2 (hAne.mono hAsub))
  have hnocross :
      ∀ a ∈ extendedHost N hj \ T, ∀ b ∈ ownSupport N hj, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact no_adj_own_sdiff_cut N hj hTsub hrows hb ha hab.symm
  have hdisjRem : Disjoint (extendedHost N hj \ T) (ownSupport N hj) :=
    Disjoint.mono_left sdiff_subset (disjoint_own_extendedHost N hj).symm
  have hadd :=
    Cograph.componentCount_union_of_no_cross (G := G) hdisjRem hnocross
  have hGeq : componentCount G (univ \ T) =
      componentCount G (extendedHost N hj \ T) +
        componentCount G (ownSupport N hj) := by
    rw [univ_sdiff_cut_eq N hj hTsub, hadd]
  have hcB : 1 ≤ componentCount G (ownSupport N hj) :=
    one_le_componentCount_of_nonempty hBne
  have hcQ_ge : (T.card : ℤ) ≤
      (componentCount G (extendedHost N hj \ T) : ℤ) := by
    omega
  have hcQnat : T.card ≤ componentCount G (extendedHost N hj \ T) :=
    Int.ofNat_le.mp hcQ_ge
  have hcQpos : 1 ≤ componentCount G (extendedHost N hj \ T) :=
    le_trans hTpos hcQnat
  have h2 : 2 ≤ componentCount G (univ \ T) := by
    rw [hGeq]
    omega
  have hle := hTough T h2
  have hgt : T.card < componentCount G (univ \ T) := by
    rw [hGeq]
    omega
  exact (not_le_of_gt hgt hle).elim

/-- Every own-group row sits in `T_x`. Adjacent vertices share the unique
maximizer by `cuts_eq_of_own_adj`; nonadjacent vertices use the full
nonadjacent lemma. The case `x = z` is handled inside the latter. -/
lemma all_own_rows_subset_ownCut
    {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x : V} (hx : x ∈ ownSupport N hj) :
    ∀ z ∈ ownSupport N hj, rowAt N z ⊆ ownCut N hj x := by
  intro z hz
  by_cases hadj : G.Adj x z
  · have hEq := cuts_eq_of_own_adj N hj hpat hmin hx hz hadj
    have hsub : rowAt N z ⊆ ownCut N hj z := rowAt_subset_ownCut N hj z
    simpa [hEq.2] using hsub
  · exact nonadjacent_rows_subset_ownCut N hj hpat hmin hx hz hadj

/-- Manuscript `thm:remaining`: a globally minimum original-edge factor of
a non-Hamiltonian 1-tough cofree host of order at least three cannot
exist. -/
theorem remaining_min_factor_not_hamiltonian
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian) : False := by
  obtain ⟨N⟩ := exists_canonical_normal_form hT hord hpat F hmin hNonHam
  obtain ⟨j, hj⟩ := exists_noncore_index (N := N)
  obtain ⟨x, hx⟩ := ownSupport_nonempty N hj
  refine oneTough_false_of_host_cut_containing_all_own_rows (N := N) hj hT
    (ownCut_subset_host N hj x)
    (all_own_rows_subset_ownCut N hj hpat hmin hx) hx
    (ownCut_attains N hj hpat hx)
    (cutDelta_nonneg N hj hpat hmin hx)

end Nikoghosyan
