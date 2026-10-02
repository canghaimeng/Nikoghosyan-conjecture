/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.NormalGroups
import Nikoghosyan.Cograph.ProfileMaximum
import Nikoghosyan.Absorption.StrictMerger
import Nikoghosyan.Locality
import Nikoghosyan.Absorption.Released
import Nikoghosyan.ExtendedCutAssembly

/-!
# Manuscript `prop:extended-cuts` cut framework

For a canonical normal form `N` of a globally minimum original-edge
factor, one representative satellite `j ≠ core`, own support `B`, foreign
support `R`, and core support `H`, the host `Q = H ∪ R` carries, at each
`x ∈ B`, an integer profile `δ_x = p(Q \ A_x) − |A_x|` and a canonical
container `T_x = A_x ∪ F(Q \ A_x)`.

Kernel-checked here:

* `Q \ A_x` is a cograph;
* every foreign vertex has an old eligible neighbour in `E(H \ A_x)`;
* `T_x ⊆ Q` and `c(Q \ T_x) − |T_x| = δ_x`;
* mutual row-containment forces `δ_x = δ_z` and `T_x = T_z`;
* a located foreign factor cycle that strictly saves at `x` contradicts
  global minimality;
* a negative integer `δ_x` is a global strict saving
  `p(Q \ A_x) < p(H \ A_x) = |A_x|`;
* same-own-group rows sit in the common old gate, and any escape of
  `A_z` from `T_x` lies in old `F(H \ A_x)` and new `E(Q \ A_x)`.

A global strict saving *does* localise to a single foreign cycle under
`LocalityHyp`. The P₃-plus-three-triangles example only shows that
`p(J) ≤ p(L)` can fail; it does not obstruct single-cycle localisation
of a strict saving.

`PathCover.card_le_card` on the Locality copy was renamed to
`card_le_card_locality`, so this module now imports public `Locality`,
`Released`, and `ExtendedCutAssembly`. `cutDelta_nonneg` is the
composition of `neg_cutDelta_is_global_saving`, `localityHyp_at`,
`exists_single_saving`, and `not_strict_saving_located_foreign`.
Same-own-cycle constancy uses `exists_single_release_eq` and
`Cograph.exists_released_three_cycle`. Cross edges use the four-block
assembler.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

variable {F : CycleFactor G} (N : CanonicalNormalForm F)

/-- Core support `H`. -/
def coreSupport : Finset V := (F.getCycle N.core).support

/-- Own-group support `B` of the canonical class of satellite `j`. -/
noncomputable def ownSupport {j : Fin F.card} (hj : j ≠ N.core) : Finset V :=
  F.selectedSupport (N.own j hj)

/-- Foreign-group support `R` of the complementary gate classes. -/
noncomputable def foreignSupport {j : Fin F.card} (hj : j ≠ N.core) : Finset V :=
  F.selectedSupport (N.foreign j hj)

/-- Extended host `Q = H ∪ R`. -/
noncomputable def extendedHost {j : Fin F.card} (hj : j ≠ N.core) : Finset V :=
  coreSupport N ∪ foreignSupport N hj

/-- Core row `A_x = N_H(x)`. -/
noncomputable def rowAt (x : V) : Finset V :=
  rowProfile (G := G) (coreSupport N) x

/-- Integer profile `δ_x = p(Q \ A_x) − |A_x|`. -/
noncomputable def cutDelta {j : Fin F.card} (hj : j ≠ N.core) (x : V) : ℤ :=
  Cograph.profileDelta (G := G) (extendedHost N hj) (rowAt N x)

/-- Canonical container `T_x = A_x ∪ F(Q \ A_x)`. -/
noncomputable def ownCut {j : Fin F.card} (hj : j ≠ N.core) (x : V) : Finset V :=
  Cograph.profileContainer (G := G) (extendedHost N hj) (rowAt N x)

lemma ownSupport_nonempty {j : Fin F.card} (hj : j ≠ N.core) :
    (ownSupport N hj).Nonempty := by
  obtain ⟨t, ht⟩ := N.hOwnNe j hj
  obtain ⟨y, hy⟩ := (F.getCycle t).support_nonempty
  exact ⟨y, (CycleFactor.mem_selectedSupport (F := F)).2 ⟨t, ht, hy⟩⟩

lemma foreignSupport_nonempty {j : Fin F.card} (hj : j ≠ N.core) :
    (foreignSupport N hj).Nonempty := by
  obtain ⟨t, ht⟩ := N.hForeignNe j hj
  obtain ⟨y, hy⟩ := (F.getCycle t).support_nonempty
  exact ⟨y, (CycleFactor.mem_selectedSupport (F := F)).2 ⟨t, ht, hy⟩⟩

lemma disjoint_core_own {j : Fin F.card} (hj : j ≠ N.core) :
    Disjoint (coreSupport N) (ownSupport N hj) :=
  N.hDisjHB j hj

lemma disjoint_core_foreign {j : Fin F.card} (hj : j ≠ N.core) :
    Disjoint (coreSupport N) (foreignSupport N hj) :=
  N.hDisjHR j hj

lemma disjoint_ownSupport_foreignSupport {j : Fin F.card} (hj : j ≠ N.core) :
    Disjoint (ownSupport N hj) (foreignSupport N hj) :=
  N.hDisjBR j hj

lemma partition_core_own_foreign {j : Fin F.card} (hj : j ≠ N.core) :
    coreSupport N ∪ ownSupport N hj ∪ foreignSupport N hj = univ :=
  N.hPartition j hj

lemma anticomplete_own_foreign {j : Fin F.card} (hj : j ≠ N.core)
    {u v : V} (hu : u ∈ ownSupport N hj) (hv : v ∈ foreignSupport N hj) :
    ¬ G.Adj u v :=
  N.hAnticompleteBR j hj hu hv

lemma rowAt_subset_core (x : V) : rowAt N x ⊆ coreSupport N :=
  rowProfile_subset (G := G) (coreSupport N) x

lemma rowAt_subset_host {j : Fin F.card} (hj : j ≠ N.core) (x : V) :
    rowAt N x ⊆ extendedHost N hj :=
  (rowAt_subset_core N x).trans subset_union_left

lemma exists_own_index {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    ∃ t, ∃ ht : t ≠ N.core,
      t ∈ N.own j hj ∧ x ∈ (F.getCycle t).support ∧
        N.gateOf t ht = N.gateOf j hj := by
  obtain ⟨t, htOwn, hxt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hx
  obtain ⟨ht, heq⟩ := (N.hOwnMem j hj t).1 htOwn
  exact ⟨t, ht, htOwn, hxt, heq⟩

lemma exists_foreign_index {j : Fin F.card} (hj : j ≠ N.core) {y : V}
    (hy : y ∈ foreignSupport N hj) :
    ∃ t, ∃ ht : t ≠ N.core,
      t ∈ N.foreign j hj ∧ y ∈ (F.getCycle t).support ∧
        N.gateOf t ht ≠ N.gateOf j hj := by
  obtain ⟨t, htFor, hyt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hy
  obtain ⟨ht, hne⟩ := (N.hForeignMem j hj t).1 htFor
  exact ⟨t, ht, htFor, hyt, hne⟩

lemma own_index_ne_foreign {j t i : Fin F.card} (hj : j ≠ N.core)
    (htOwn : t ∈ N.own j hj) (hiFor : i ∈ N.foreign j hj) : t ≠ i := by
  intro h
  subst h
  obtain ⟨ht, heq⟩ := (N.hOwnMem j hj t).1 htOwn
  obtain ⟨hi, hne⟩ := (N.hForeignMem j hj t).1 hiFor
  have hproof : ht = hi := Subsingleton.elim ht hi
  exact hne (hproof ▸ heq)

lemma rowAt_ssubset_core {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    rowAt N x ⊂ coreSupport N := by
  obtain ⟨t, ht, _, hxt, _hgate⟩ := exists_own_index N hj hx
  have hAS : rowAt N x ⊆ N.gateOf t ht := by
    simpa [rowAt, coreSupport] using (N.hGateRows t ht x hxt).2.2.2.2
  have hS : N.gateOf t ht ⊂ coreSupport N := by
    simpa [coreSupport] using N.hGateProper t ht
  exact Finset.ssubset_of_subset_of_ssubset hAS hS

lemma rowAt_nonempty {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    (rowAt N x).Nonempty := by
  obtain ⟨t, ht, _, hxt, _⟩ := exists_own_index N hj hx
  simpa [rowAt, coreSupport] using (N.hGateRows t ht x hxt).1

lemma saturated_rowAt {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    Cograph.Saturated (G := G) (coreSupport N) (rowAt N x) := by
  obtain ⟨t, ht, _, hxt, _⟩ := exists_own_index N hj hx
  simpa [rowAt, coreSupport] using (N.hGateRows t ht x hxt).2.2.1

lemma canonicalContainer_rowAt {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    Cograph.canonicalContainer (G := G) (coreSupport N) (rowAt N x) =
      N.gateOf j hj := by
  obtain ⟨t, ht, _, hxt, hgate⟩ := exists_own_index N hj hx
  have hC :
      Cograph.canonicalContainer (G := G) (coreSupport N) (rowAt N x) =
        N.gateOf t ht := by
    simpa [rowAt, coreSupport] using (N.hGateRows t ht x hxt).2.2.2.1
  exact hC.trans hgate

lemma sdiff_host_eq_remainder_union_foreign {j : Fin F.card} (hj : j ≠ N.core)
    (x : V) :
    extendedHost N hj \ rowAt N x =
      (coreSupport N \ rowAt N x) ∪ foreignSupport N hj := by
  have hAsub : rowAt N x ⊆ coreSupport N := rowAt_subset_core N x
  have hdisj : Disjoint (rowAt N x) (foreignSupport N hj) :=
    Disjoint.mono_left hAsub (disjoint_core_foreign N hj)
  ext z
  constructor
  · intro hz
    have hzQ : z ∈ coreSupport N ∪ foreignSupport N hj := (mem_sdiff.1 hz).1
    have hzA : z ∉ rowAt N x := (mem_sdiff.1 hz).2
    rcases mem_union.1 hzQ with hzH | hzR
    · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzH, hzA⟩))
    · exact mem_union.2 (Or.inr hzR)
  · intro hz
    rcases mem_union.1 hz with hzH | hzR
    · exact mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hzH).1),
        (mem_sdiff.1 hzH).2⟩
    · exact mem_sdiff.2 ⟨mem_union.2 (Or.inr hzR),
        fun hA => (disjoint_left.1 hdisj) hA hzR⟩

lemma not_mem_core_of_own {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) : x ∉ coreSupport N :=
  disjoint_right.1 (disjoint_core_own N hj) hx

lemma not_mem_foreign_of_own {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) : x ∉ foreignSupport N hj :=
  disjoint_left.1 (disjoint_ownSupport_foreignSupport N hj) hx

/-- `x` is isolated from `Q \ A_x`, so that remainder is a cograph. -/
lemma isCograph_host_remainder {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x : V} (hx : x ∈ ownSupport N hj) :
    IsCograph G (extendedHost N hj \ rowAt N x) := by
  have hanti : ∀ d ∈ foreignSupport N hj, ¬ G.Adj x d := fun d hd =>
    anticomplete_own_foreign N hj hx hd
  have hK :=
    isCograph_K_of_anticomplete_x (G := G) hpat
      (not_mem_core_of_own N hj hx) (not_mem_foreign_of_own N hj hx) hanti
  rw [sdiff_host_eq_remainder_union_foreign]
  simpa [rowAt] using hK

lemma host_remainder_nonempty {j : Fin F.card} (hj : j ≠ N.core) (x : V) :
    (extendedHost N hj \ rowAt N x).Nonempty := by
  obtain ⟨y, hy⟩ := foreignSupport_nonempty N hj
  have hyA : y ∉ rowAt N x := by
    intro hA
    exact (disjoint_left.1
      (Disjoint.mono_left (rowAt_subset_core N x) (disjoint_core_foreign N hj)))
      hA hy
  exact ⟨y, mem_sdiff.2 ⟨mem_union.2 (Or.inr hy), hyA⟩⟩

/-- Every foreign vertex has an old eligible neighbour in `E(H \ A_x)`. -/
lemma foreign_meets_old_eligible {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x y : V}
    (hx : x ∈ ownSupport N hj) (hy : y ∈ foreignSupport N hj) :
    ∃ u ∈ eligibleSet G (coreSupport N \ rowAt N x), G.Adj y u := by
  obtain ⟨i, hi, _, hyi, hneGate⟩ := exists_foreign_index N hj hy
  have hST : N.gateOf j hj ≠ N.gateOf i hi := by
    intro h
    exact hneGate (h.symm)
  have hXsat :
      Cograph.Saturated (G := G) (F.getCycle N.core).support
        (rowProfile (G := G) (F.getCycle N.core).support x) := by
    simpa [coreSupport, rowAt] using saturated_rowAt N hj hx
  have hXgate :
      Cograph.canonicalContainer (G := G) (F.getCycle N.core).support
          (rowProfile (G := G) (F.getCycle N.core).support x) =
        N.gateOf j hj := by
    simpa [coreSupport, rowAt] using canonicalContainer_rowAt N hj hx
  have hDrow :
      (rowProfile (G := G) (F.getCycle N.core).support y).Nonempty ∧
        IsCograph G ((F.getCycle N.core).support \
          rowProfile (G := G) (F.getCycle N.core).support y) ∧
          Cograph.Saturated (G := G) (F.getCycle N.core).support
            (rowProfile (G := G) (F.getCycle N.core).support y) ∧
            Cograph.canonicalContainer (G := G) (F.getCycle N.core).support
                (rowProfile (G := G) (F.getCycle N.core).support y) =
              N.gateOf i hi := by
    have hrow := N.hGateRows i hi y hyi
    exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1⟩
  have hmeet :=
    drow_meets_eligible_of_distinct_gates hpat (F.getCycle N.core)
      (disjoint_core_own N hj) N.hCoreNoncog hDrow hx hXsat hXgate hST
  simpa [coreSupport, rowAt] using hmeet

lemma ownCut_subset_host {j : Fin F.card} (hj : j ≠ N.core) (x : V) :
    ownCut N hj x ⊆ extendedHost N hj :=
  Cograph.profileContainer_subset (G := G) (rowAt_subset_host N hj x)

lemma rowAt_subset_ownCut {j : Fin F.card} (hj : j ≠ N.core) (x : V) :
    rowAt N x ⊆ ownCut N hj x :=
  subset_union_left

/-- Signed cut identity: `c(Q \ T_x) − |T_x| = δ_x`. -/
lemma ownCut_attains {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x : V} (hx : x ∈ ownSupport N hj) :
    (componentCount G (extendedHost N hj \ ownCut N hj x) : ℤ) -
      ((ownCut N hj x).card : ℤ) =
        cutDelta N hj x := by
  have hK : IsCograph G (extendedHost N hj \ rowAt N x) :=
    isCograph_host_remainder N hj hpat hx
  simpa [ownCut, cutDelta] using
    Cograph.profileContainer_attains_of_canonical (G := G)
      (rowAt_subset_host N hj x) hK (host_remainder_nonempty N hj x)

/-- If `A_z ⊆ T_x` then `δ_x ≤ δ_z`, because `T_x` attains `δ_x` and is a
nested candidate for the `z`-profile. -/
lemma cutDelta_le_of_row_subset_cut {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x z : V}
    (hx : x ∈ ownSupport N hj) (hAz : rowAt N z ⊆ ownCut N hj x) :
    cutDelta N hj x ≤ cutDelta N hj z := by
  have hatt := ownCut_attains N hj hpat hx
  have hbound :=
    Cograph.profileDelta_le_of_nested (G := G) (U := extendedHost N hj)
      (A := rowAt N z) (T := ownCut N hj x) hAz (ownCut_subset_host N hj x)
  exact hatt ▸ hbound

/-- Mutual row-containment forces equal integer profiles and equal unique
largest maximizers. -/
lemma cuts_eq_of_mutual_row_containment {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x z : V}
    (hx : x ∈ ownSupport N hj) (hz : z ∈ ownSupport N hj)
    (hAz : rowAt N z ⊆ ownCut N hj x)
    (hAx : rowAt N x ⊆ ownCut N hj z) :
    cutDelta N hj x = cutDelta N hj z ∧ ownCut N hj x = ownCut N hj z := by
  have hxz := cutDelta_le_of_row_subset_cut N hj hpat hx hAz
  have hzx := cutDelta_le_of_row_subset_cut N hj hpat hz hAx
  have hδ : cutDelta N hj x = cutDelta N hj z := le_antisymm hxz hzx
  have hKx : IsCograph G (extendedHost N hj \ rowAt N x) :=
    isCograph_host_remainder N hj hpat hx
  have hKz : IsCograph G (extendedHost N hj \ rowAt N z) :=
    isCograph_host_remainder N hj hpat hz
  have hattx := ownCut_attains N hj hpat hx
  have hattz := ownCut_attains N hj hpat hz
  have hx_in_z := hattx.trans hδ
  have hz_in_x := hattz.trans hδ.symm
  have hsubxz : ownCut N hj x ⊆ ownCut N hj z :=
    Cograph.profile_maximizer_subset_container_of_canonical (G := G)
      (U := extendedHost N hj) (A := rowAt N z) (T := ownCut N hj x)
      hAz (ownCut_subset_host N hj x) hKz (by simpa [ownCut, cutDelta] using hx_in_z)
  have hsubzx : ownCut N hj z ⊆ ownCut N hj x :=
    Cograph.profile_maximizer_subset_container_of_canonical (G := G)
      (U := extendedHost N hj) (A := rowAt N x) (T := ownCut N hj z)
      hAx (ownCut_subset_host N hj z) hKx (by simpa [ownCut, cutDelta] using hz_in_x)
  exact ⟨hδ, subset_antisymm hsubxz hsubzx⟩

lemma support_union_eq_selected_triple {i k t : Fin F.card} (C : GraphCycle G)
    (hC : C.support =
      (F.getCycle i).support ∪ (F.getCycle k).support ∪ (F.getCycle t).support) :
    C.support = F.selectedSupport ({i, k, t} : Finset (Fin F.card)) := by
  rw [hC, Finset.union_assoc, CycleFactor.selectedSupport_triple]

lemma gateRows_as_Drows {t : Fin F.card} (ht : t ≠ N.core) :
    ∀ d ∈ (F.getCycle t).support,
      (rowProfile (G := G) (F.getCycle N.core).support d).Nonempty ∧
        IsCograph G ((F.getCycle N.core).support \
          rowProfile (G := G) (F.getCycle N.core).support d) ∧
          Cograph.Saturated (G := G) (F.getCycle N.core).support
            (rowProfile (G := G) (F.getCycle N.core).support d) ∧
            Cograph.canonicalContainer (G := G) (F.getCycle N.core).support
                (rowProfile (G := G) (F.getCycle N.core).support d) =
              N.gateOf t ht := by
  intro d hd
  have hrow := N.hGateRows t ht d hd
  exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1⟩

lemma gateRows_as_Xsat {t : Fin F.card} (ht : t ≠ N.core) {S : Finset V}
    (hS : N.gateOf t ht = S) :
    ∀ y ∈ (F.getCycle t).support,
      Cograph.Saturated (G := G) (F.getCycle N.core).support
        (rowProfile (G := G) (F.getCycle N.core).support y) ∧
        Cograph.canonicalContainer (G := G) (F.getCycle N.core).support
            (rowProfile (G := G) (F.getCycle N.core).support y) = S := by
  intro y hy
  have hrow := N.hGateRows t ht y hy
  exact ⟨hrow.2.2.1, hrow.2.2.2.1.trans hS⟩

/-- A located foreign factor cycle that strictly saves at `x` merges the
core, that foreign block, and the own block of `x`, contradicting a
globally minimum factor. Locality is used only to *produce* such a cycle;
it is not a hypothesis here. -/
lemma not_strict_saving_located_foreign {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x : V} (hx : x ∈ ownSupport N hj)
    {i : Fin F.card} (hiFor : i ∈ N.foreign j hj)
    (hsave : pathCoverNumber G
        ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) <
      (rowAt N x).card) :
    False := by
  obtain ⟨t, ht, htOwn, hxt, hgate⟩ := exists_own_index N hj hx
  obtain ⟨hi, hneGate⟩ := (N.hForeignMem j hj i).1 hiFor
  have hti : t ≠ i := own_index_ne_foreign N hj htOwn hiFor
  have htc : t ≠ N.core := ht
  have hic : i ≠ N.core := hi
  have hST : N.gateOf j hj ≠ N.gateOf i hi := hneGate.symm
  have hHD : Disjoint (F.getCycle N.core).support (F.getCycle i).support :=
    F.disjoint_getCycle hic.symm
  have hHX : Disjoint (F.getCycle N.core).support (F.getCycle t).support :=
    F.disjoint_getCycle htc.symm
  have hDX : Disjoint (F.getCycle i).support (F.getCycle t).support :=
    F.disjoint_getCycle hti.symm
  have hanti : ∀ d ∈ (F.getCycle i).support, ¬ G.Adj x d := by
    intro d hd
    have hdR : d ∈ foreignSupport N hj :=
      (CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hiFor, hd⟩
    exact anticomplete_own_foreign N hj hx hdR
  have hpK : pathCoverNumber G
      (((F.getCycle N.core).support \
          rowProfile (G := G) (F.getCycle N.core).support x) ∪
        (F.getCycle i).support) <
      (rowProfile (G := G) (F.getCycle N.core).support x).card := by
    simpa [coreSupport, rowAt] using hsave
  obtain ⟨γ, hγ⟩ :=
    exists_cycle_of_strict_merger hpat (F.getCycle N.core) (F.getCycle i)
      (F.getCycle t) hHD hHX hDX N.hCoreNoncog
      (gateRows_as_Drows N hi) (gateRows_as_Xsat N ht hgate) hST hxt hanti hpK
  have hspan :
      γ.support = F.selectedSupport ({N.core, i, t} : Finset (Fin F.card)) :=
    support_union_eq_selected_triple (i := N.core) (k := i) (t := t) γ hγ
  have h3 : 2 ≤ ({N.core, i, t} : Finset (Fin F.card)).card := by
    have hcard := card_selected_triple (i := N.core) (j := i) (k := t)
      hic.symm htc.symm hti.symm
    omega
  exact CycleFactor.not_exists_merge_of_min F hmin
    ({N.core, i, t} : Finset (Fin F.card)) h3 γ hspan

lemma remainder_old_nonempty {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    (coreSupport N \ rowAt N x).Nonempty := by
  obtain ⟨y, hyH, hyA⟩ := exists_of_ssubset (rowAt_ssubset_core N hj hx)
  exact ⟨y, mem_sdiff.2 ⟨hyH, hyA⟩⟩

lemma pathCoverNumber_remainder_eq_row {j : Fin F.card} (hj : j ≠ N.core)
    {x : V} (hx : x ∈ ownSupport N hj) :
    pathCoverNumber G (coreSupport N \ rowAt N x) = (rowAt N x).card :=
  pathCoverNumber_k0_of_saturated (saturated_rowAt N hj hx)

lemma foreign_cycles_disjoint {j : Fin F.card} (hj : j ≠ N.core)
    {i k : Fin F.card} (_hi : i ∈ N.foreign j hj) (_hk : k ∈ N.foreign j hj)
    (hik : i ≠ k) :
    Disjoint (F.getCycle i).support (F.getCycle k).support :=
  F.disjoint_getCycle hik

lemma disjoint_remainder_foreign_cycle {j : Fin F.card} (hj : j ≠ N.core)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj) (x : V) :
    Disjoint (coreSupport N \ rowAt N x) (F.getCycle i).support := by
  have hi' : i ≠ N.core := ((N.hForeignMem j hj i).1 hi).1
  exact Disjoint.mono_left sdiff_subset (F.disjoint_getCycle hi'.symm)

/-- Negative integer `δ_x` is a global strict saving of `Q \ A_x` against
the old remainder `H \ A_x`. Locality saving then localises this to one
foreign cycle; that localisation cannot live in this file while
`PathCover.card_le_card` is declared both in `Locality` and in
`EndpointSeamAssembly`. -/
lemma neg_cutDelta_is_global_saving {j : Fin F.card} (hj : j ≠ N.core)
    {x : V} (hx : x ∈ ownSupport N hj) (hneg : cutDelta N hj x < 0) :
    pathCoverNumber G (extendedHost N hj \ rowAt N x) <
      pathCoverNumber G (coreSupport N \ rowAt N x) := by
  have hpL := pathCoverNumber_remainder_eq_row N hj hx
  have hneg' :
      (pathCoverNumber G (extendedHost N hj \ rowAt N x) : ℤ) -
        ((rowAt N x).card : ℤ) < 0 := by
    simpa [cutDelta, Cograph.profileDelta] using hneg
  have : pathCoverNumber G (extendedHost N hj \ rowAt N x) <
      (rowAt N x).card := Int.ofNat_lt.mp (by omega)
  simpa [hpL] using this

/-- Packed `LocalityHyp` data for `c = F.getCycle`, `I = N.foreign j hj`,
and `L = H \ A_x`. The corresponding `unionJ` equals `Q \ A_x` by
`sdiff_host_eq_remainder_union_foreign`. -/
lemma locality_family_data {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x : V} (hx : x ∈ ownSupport N hj) :
    (N.foreign j hj).Nonempty ∧
      (coreSupport N \ rowAt N x).Nonempty ∧
        (∀ i ∈ N.foreign j hj,
          Disjoint (coreSupport N \ rowAt N x) (F.getCycle i).support) ∧
          (∀ i ∈ N.foreign j hj, ∀ k ∈ N.foreign j hj, i ≠ k →
            Disjoint (F.getCycle i).support (F.getCycle k).support) ∧
            IsCograph G (extendedHost N hj \ rowAt N x) ∧
              (∀ i ∈ N.foreign j hj, ∀ d ∈ (F.getCycle i).support,
                ∃ u ∈ eligibleSet G (coreSupport N \ rowAt N x), G.Adj d u) := by
  refine ⟨N.hForeignNe j hj, remainder_old_nonempty N hj hx, ?_, ?_,
    isCograph_host_remainder N hj hpat hx, ?_⟩
  · intro i hi
    exact disjoint_remainder_foreign_cycle N hj hi x
  · intro i hi k hk hik
    exact foreign_cycles_disjoint N hj hi hk hik
  · intro i hi d hd
    have hdR : d ∈ foreignSupport N hj :=
      (CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hi, hd⟩
    exact foreign_meets_old_eligible N hj hpat hx hdR

lemma selectedSupport_eq_foreign {j : Fin F.card} (hj : j ≠ N.core) :
    selectedSupport (c := F.getCycle) (N.foreign j hj) = foreignSupport N hj := by
  simp [selectedSupport, foreignSupport, CycleFactor.selectedSupport]

lemma unionJ_eq_host_remainder {j : Fin F.card} (hj : j ≠ N.core) (x : V) :
    unionJ (coreSupport N \ rowAt N x) F.getCycle (N.foreign j hj) =
      extendedHost N hj \ rowAt N x := by
  unfold unionJ
  rw [selectedSupport_eq_foreign, sdiff_host_eq_remainder_union_foreign]

lemma localityHyp_at {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x : V} (hx : x ∈ ownSupport N hj) :
    LocalityHyp F.getCycle (coreSupport N \ rowAt N x) (N.foreign j hj) := by
  obtain ⟨hI, hL, hdisj, hpair, hcog, hsees⟩ := locality_family_data N hj hpat hx
  refine ⟨hI, hL, hdisj, hpair, ?_, hsees⟩
  simpa [unionJ_eq_host_remainder N hj x] using hcog

/-- Integer `δ_x ≥ 0`. A negative profile is a global saving, which
localises to one foreign cycle and contradicts a minimum factor. -/
lemma cutDelta_nonneg {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x : V} (hx : x ∈ ownSupport N hj) :
    0 ≤ cutDelta N hj x := by
  by_contra hneg0
  have hneg : cutDelta N hj x < 0 := lt_of_not_ge hneg0
  have hglob := neg_cutDelta_is_global_saving N hj hx hneg
  have Hloc := localityHyp_at N hj hpat hx
  have hsave :
      pathCoverNumber G
          (unionJ (coreSupport N \ rowAt N x) F.getCycle (N.foreign j hj)) <
        pathCoverNumber G (coreSupport N \ rowAt N x) := by
    simpa [unionJ_eq_host_remainder N hj x] using hglob
  obtain ⟨i, hi, hsi⟩ := exists_single_saving F.getCycle Hloc hsave
  have hpL := pathCoverNumber_remainder_eq_row N hj hx
  have hsi' : pathCoverNumber G
      ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) <
        (rowAt N x).card := by
    simpa [hpL] using hsi
  exact not_strict_saving_located_foreign N hj hpat hmin hx hi hsi'

lemma rowAt_subset_own_gate {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    rowAt N x ⊆ N.gateOf j hj := by
  obtain ⟨t, ht, _, hxt, hgate⟩ := exists_own_index N hj hx
  have hsub : rowAt N x ⊆ N.gateOf t ht := by
    simpa [rowAt, coreSupport] using (N.hGateRows t ht x hxt).2.2.2.2
  exact hsub.trans (hgate ▸ Subset.rfl)

/-- Every same-own-group row sits in the old canonical gate of `A_x`. -/
lemma same_own_row_subset_old_canonical {j : Fin F.card} (hj : j ≠ N.core)
    {x z : V} (hx : x ∈ ownSupport N hj) (hz : z ∈ ownSupport N hj) :
    rowAt N z ⊆
      Cograph.canonicalContainer (G := G) (coreSupport N) (rowAt N x) := by
  have hgate := rowAt_subset_own_gate N hj hz
  simpa [canonicalContainer_rowAt N hj hx] using hgate

lemma ownCut_eq_row_union_new_ineligible {j : Fin F.card} (hj : j ≠ N.core)
    (x : V) :
    ownCut N hj x =
      rowAt N x ∪ ineligibleSet G (extendedHost N hj \ rowAt N x) :=
  rfl

lemma sdiff_host_ownCut {j : Fin F.card} (hj : j ≠ N.core) (x : V) :
    extendedHost N hj \ ownCut N hj x =
      (extendedHost N hj \ rowAt N x) \
        ineligibleSet G (extendedHost N hj \ rowAt N x) :=
  Cograph.sdiff_profileContainer (G := G) (rowAt_subset_host N hj x)

lemma sdiff_host_ownCut_eq_new_eligible {j : Fin F.card} (hj : j ≠ N.core)
    (x : V) :
    extendedHost N hj \ ownCut N hj x =
      eligibleSet G (extendedHost N hj \ rowAt N x) := by
  rw [sdiff_host_ownCut]
  ext z
  constructor
  · intro hz
    have hzK : z ∈ extendedHost N hj \ rowAt N x := (mem_sdiff.1 hz).1
    have hzF : z ∉ ineligibleSet G (extendedHost N hj \ rowAt N x) :=
      (mem_sdiff.1 hz).2
    refine (mem_eligibleSet_iff (G := G)).2 ⟨hzK, ?_⟩
    by_contra hnot
    exact hzF ((mem_ineligibleSet_iff (G := G)).2 ⟨hzK, hnot⟩)
  · intro hz
    have hzK : z ∈ extendedHost N hj \ rowAt N x :=
      ((mem_eligibleSet_iff (G := G)).1 hz).1
    have hE : Eligible G (extendedHost N hj \ rowAt N x) z :=
      ((mem_eligibleSet_iff (G := G)).1 hz).2
    refine mem_sdiff.2 ⟨hzK, ?_⟩
    intro hzF
    exact ((mem_ineligibleSet_iff (G := G)).1 hzF).2 hE

/-- If `A_z` fails to sit in `T_x`, the escaping vertices lie in the old
ineligible set of `H \ A_x`. Same-own-group rows share the old gate. -/
lemma escape_row_subset_old_ineligible {j : Fin F.card} (hj : j ≠ N.core)
    {x z : V} (hx : x ∈ ownSupport N hj) (hz : z ∈ ownSupport N hj) :
    rowAt N z \ ownCut N hj x ⊆
      ineligibleSet G (coreSupport N \ rowAt N x) := by
  intro v hv
  have hvAz : v ∈ rowAt N z := (mem_sdiff.1 hv).1
  have hvT : v ∉ ownCut N hj x := (mem_sdiff.1 hv).2
  have hvS : v ∈
      Cograph.canonicalContainer (G := G) (coreSupport N) (rowAt N x) :=
    same_own_row_subset_old_canonical N hj hx hz hvAz
  have hvAF :
      v ∈ rowAt N x ∪ ineligibleSet G (coreSupport N \ rowAt N x) := by
    simpa [Cograph.canonicalContainer_eq] using hvS
  rcases mem_union.1 hvAF with hvA | hvF
  · exact (hvT (rowAt_subset_ownCut N hj x hvA)).elim
  · exact hvF

/-- Escaping vertices of `A_z` from `T_x` are new-eligible in `Q \ A_x`. -/
lemma escape_row_subset_new_eligible {j : Fin F.card} (hj : j ≠ N.core)
    {x z : V} (_hz : z ∈ ownSupport N hj) :
    rowAt N z \ ownCut N hj x ⊆
      eligibleSet G (extendedHost N hj \ rowAt N x) := by
  intro v hv
  have hvAz : v ∈ rowAt N z := (mem_sdiff.1 hv).1
  have hvT : v ∉ ownCut N hj x := (mem_sdiff.1 hv).2
  have hvQ : v ∈ extendedHost N hj := rowAt_subset_host N hj z hvAz
  have hvrem : v ∈ extendedHost N hj \ ownCut N hj x :=
    mem_sdiff.2 ⟨hvQ, hvT⟩
  simpa [sdiff_host_ownCut_eq_new_eligible N hj x] using hvrem

/-- Same-own-group row containment dichotomy: either `A_z ⊆ T_x`, or some
vertex of `A_z` escapes into old `F(H \ A_x)` and new `E(Q \ A_x)`. -/
lemma same_own_row_subset_or_escape {j : Fin F.card} (hj : j ≠ N.core)
    {x z : V} (hx : x ∈ ownSupport N hj) (hz : z ∈ ownSupport N hj) :
    rowAt N z ⊆ ownCut N hj x ∨
      ∃ v, v ∈ rowAt N z ∧
        v ∈ ineligibleSet G (coreSupport N \ rowAt N x) ∧
          v ∈ eligibleSet G (extendedHost N hj \ rowAt N x) := by
  by_cases hsub : rowAt N z ⊆ ownCut N hj x
  · exact Or.inl hsub
  · have hne : (rowAt N z \ ownCut N hj x).Nonempty :=
      (nonempty_iff_ne_empty).2 fun hemp =>
        hsub ((sdiff_eq_empty_iff_subset).1 hemp)
    obtain ⟨v, hv⟩ := hne
    exact Or.inr ⟨v, (mem_sdiff.1 hv).1,
      escape_row_subset_old_ineligible N hj hx hz hv,
      escape_row_subset_new_eligible N hj hz hv⟩

lemma isCograph_old_remainder {j : Fin F.card} (hj : j ≠ N.core) {x : V}
    (hx : x ∈ ownSupport N hj) :
    IsCograph G (coreSupport N \ rowAt N x) := by
  obtain ⟨t, ht, _, hxt, _⟩ := exists_own_index N hj hx
  simpa [coreSupport, rowAt] using (N.hGateRows t ht x hxt).2.1

lemma remainder_union_foreign_cycle_subset {j : Fin F.card} (hj : j ≠ N.core)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj) (x : V) :
    (coreSupport N \ rowAt N x) ∪ (F.getCycle i).support ⊆
      extendedHost N hj \ rowAt N x := by
  rw [sdiff_host_eq_remainder_union_foreign]
  intro v hv
  rcases mem_union.1 hv with hL | hD
  · exact mem_union.2 (Or.inl hL)
  · exact mem_union.2
      (Or.inr ((CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hi, hD⟩))

lemma isCograph_remainder_union_foreign {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x : V} (hx : x ∈ ownSupport N hj)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj) :
    IsCograph G
      ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) := by
  have hQ : IsCograph G (extendedHost N hj \ rowAt N x) :=
    isCograph_host_remainder N hj hpat hx
  have hQ' := Cograph.isCograph_iff.2 hQ
  exact Cograph.isCograph_iff.1
    (Cograph.IsCograph.subset hQ'
      (remainder_union_foreign_cycle_subset N hj hi x))

lemma adj_of_mem_rowAt (x a : V) (ha : a ∈ rowAt N x) : G.Adj x a :=
  ((mem_rowProfile_iff (G := G)).1 (by simpa [rowAt] using ha)).2

lemma mem_ownSupport_of_own_cycle {j t : Fin F.card} (hj : j ≠ N.core)
    (htOwn : t ∈ N.own j hj) {y : V} (hy : y ∈ (F.getCycle t).support) :
    y ∈ ownSupport N hj :=
  (CycleFactor.mem_selectedSupport (F := F)).2 ⟨t, htOwn, hy⟩

lemma not_escape_of_own_cycle_edge {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t : Fin F.card} (htOwn : t ∈ N.own j hj)
    {x z : V} (hxC : x ∈ (F.getCycle t).support) (hzC : z ∈ (F.getCycle t).support)
    (hedge : (F.getCycle t).succAt hxC = z ∨ (F.getCycle t).succAt hzC = x)
    {v : V} (hvAz : v ∈ rowAt N z) (hvT : v ∉ ownCut N hj x) : False := by
  have hx : x ∈ ownSupport N hj := mem_ownSupport_of_own_cycle N hj htOwn hxC
  have hz : z ∈ ownSupport N hj := mem_ownSupport_of_own_cycle N hj htOwn hzC
  have hvF : v ∈ ineligibleSet G (coreSupport N \ rowAt N x) :=
    escape_row_subset_old_ineligible N hj hx hz (mem_sdiff.2 ⟨hvAz, hvT⟩)
  have hvE : v ∈ eligibleSet G (extendedHost N hj \ rowAt N x) :=
    escape_row_subset_new_eligible N hj hz (mem_sdiff.2 ⟨hvAz, hvT⟩)
  have Hloc := localityHyp_at N hj hpat hx
  have hvE' : v ∈ eligibleSet G
      (unionJ (coreSupport N \ rowAt N x) F.getCycle (N.foreign j hj)) := by
    simpa [unionJ_eq_host_remainder N hj x] using hvE
  obtain ⟨i, hi, hw⟩ :=
    exists_single_release_eq F.getCycle Hloc hvF hvE'
  have hpL := pathCoverNumber_remainder_eq_row N hj hx
  rcases hw with hstrict | ⟨heq, hvEi⟩
  · have hsi : pathCoverNumber G
        ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) <
          (rowAt N x).card := by
      simpa [hpL] using hstrict
    exact not_strict_saving_located_foreign N hj hpat hmin hx hi hsi
  · obtain ⟨ht, hgate⟩ := (N.hOwnMem j hj t).1 htOwn
    have hi' : i ≠ N.core := ((N.hForeignMem j hj i).1 hi).1
    have hti : t ≠ i := own_index_ne_foreign N hj htOwn hi
    have hHD : Disjoint (coreSupport N) (F.getCycle i).support := by
      simpa [coreSupport] using F.disjoint_getCycle hi'.symm
    have hHQ : Disjoint (coreSupport N) (F.getCycle t).support := by
      simpa [coreSupport] using F.disjoint_getCycle ht.symm
    have hDQ : Disjoint (F.getCycle i).support (F.getCycle t).support :=
      F.disjoint_getCycle hti.symm
    have hAsub : rowAt N x ⊆ coreSupport N := rowAt_subset_core N x
    have hAne : (rowAt N x).Nonempty := rowAt_nonempty N hj hx
    have hAx : ∀ a ∈ rowAt N x, G.Adj a x :=
      fun a ha => (adj_of_mem_rowAt N x a ha).symm
    have hK0 : IsCograph G (coreSupport N \ rowAt N x) :=
      isCograph_old_remainder N hj hx
    have hpK0 : pathCoverNumber G (coreSupport N \ rowAt N x) = (rowAt N x).card :=
      hpL
    have hJ : IsCograph G
        ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) :=
      isCograph_remainder_union_foreign N hj hpat hx hi
    have hpJ : pathCoverNumber G
        ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) =
          (rowAt N x).card := by
      simpa [hpL] using heq
    have hzh : G.Adj z v := adj_of_mem_rowAt N z v hvAz
    obtain ⟨γ, hγ⟩ :=
      Cograph.exists_released_three_cycle
        (F.getCycle N.core) (F.getCycle i) (F.getCycle t)
        (by simp [coreSupport]) rfl rfl hHD hHQ hDQ hAsub hAne hxC hzC hAx
        hK0 hpK0 hJ hpJ hvF hvEi hzh hxC hzC hedge
    have hspan :
        γ.support = F.selectedSupport ({N.core, i, t} : Finset (Fin F.card)) :=
      support_union_eq_selected_triple (i := N.core) (k := i) (t := t) γ
        (by simpa [coreSupport] using hγ)
    have h3 : 2 ≤ ({N.core, i, t} : Finset (Fin F.card)).card := by
      have hcard := card_selected_triple (i := N.core) (j := i) (k := t)
        hi'.symm ht.symm hti.symm
      omega
    exact CycleFactor.not_exists_merge_of_min F hmin
      ({N.core, i, t} : Finset (Fin F.card)) h3 γ hspan

lemma rowAt_subset_ownCut_of_own_cycle_edge {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t : Fin F.card} (htOwn : t ∈ N.own j hj)
    {x z : V} (hxC : x ∈ (F.getCycle t).support) (hzC : z ∈ (F.getCycle t).support)
    (hedge : (F.getCycle t).succAt hxC = z ∨ (F.getCycle t).succAt hzC = x) :
    rowAt N z ⊆ ownCut N hj x := by
  intro v hv
  by_contra hvT
  exact not_escape_of_own_cycle_edge N hj hpat hmin htOwn hxC hzC hedge hv hvT

lemma cuts_eq_of_own_cycle_edge {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t : Fin F.card} (htOwn : t ∈ N.own j hj)
    {x z : V} (hxC : x ∈ (F.getCycle t).support) (hzC : z ∈ (F.getCycle t).support)
    (hedge : (F.getCycle t).succAt hxC = z ∨ (F.getCycle t).succAt hzC = x) :
    cutDelta N hj x = cutDelta N hj z ∧ ownCut N hj x = ownCut N hj z := by
  have hx : x ∈ ownSupport N hj := mem_ownSupport_of_own_cycle N hj htOwn hxC
  have hz : z ∈ ownSupport N hj := mem_ownSupport_of_own_cycle N hj htOwn hzC
  have hAz : rowAt N z ⊆ ownCut N hj x :=
    rowAt_subset_ownCut_of_own_cycle_edge N hj hpat hmin htOwn hxC hzC hedge
  have hAx : rowAt N x ⊆ ownCut N hj z :=
    rowAt_subset_ownCut_of_own_cycle_edge N hj hpat hmin htOwn hzC hxC (Or.symm hedge)
  exact cuts_eq_of_mutual_row_containment N hj hpat hx hz hAz hAx

lemma cuts_eq_of_getVert_from_start {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t : Fin F.card} (htOwn : t ∈ N.own j hj)
    {k : ℕ} (hk : k < (F.getCycle t).walk.length) :
    cutDelta N hj (F.getCycle t).start =
      cutDelta N hj ((F.getCycle t).walk.getVert k) ∧
        ownCut N hj (F.getCycle t).start =
          ownCut N hj ((F.getCycle t).walk.getVert k) := by
  induction k with
  | zero =>
    simp [Walk.getVert_zero]
  | succ k ih =>
    have hk' : k < (F.getCycle t).walk.length := Nat.lt_of_succ_lt hk
    have ⟨hδ, hT⟩ := ih hk'
    have hedge :
        (F.getCycle t).succAt (getVert_mem_cycle_support (F.getCycle t) k) =
          (F.getCycle t).walk.getVert (k + 1) :=
      succAt_eq_getVert_succ (F.getCycle t) hk'
    have ⟨hδ2, hT2⟩ :=
      cuts_eq_of_own_cycle_edge N hj hpat hmin htOwn
        (getVert_mem_cycle_support (F.getCycle t) k)
        (getVert_mem_cycle_support (F.getCycle t) (k + 1))
        (Or.inl hedge)
    exact ⟨hδ.trans hδ2, hT.trans hT2⟩

lemma cuts_eq_of_mem_own_cycle {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t : Fin F.card} (htOwn : t ∈ N.own j hj)
    {x y : V} (hx : x ∈ (F.getCycle t).support) (hy : y ∈ (F.getCycle t).support) :
    cutDelta N hj x = cutDelta N hj y ∧ ownCut N hj x = ownCut N hj y := by
  obtain ⟨ix, hix, hixEq⟩ := exists_getVert_lt_length_of_mem_support (F.getCycle t) hx
  obtain ⟨iy, hiy, hiyEq⟩ := exists_getVert_lt_length_of_mem_support (F.getCycle t) hy
  have hx0 := cuts_eq_of_getVert_from_start N hj hpat hmin htOwn hix
  have hy0 := cuts_eq_of_getVert_from_start N hj hpat hmin htOwn hiy
  rw [hixEq] at hx0
  rw [hiyEq] at hy0
  exact ⟨hx0.1.symm.trans hy0.1, hx0.2.symm.trans hy0.2⟩

lemma rowAt_subset_ownCut_of_mem_own_cycle {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t : Fin F.card} (htOwn : t ∈ N.own j hj)
    {x y : V} (hx : x ∈ (F.getCycle t).support) (hy : y ∈ (F.getCycle t).support) :
    rowAt N y ⊆ ownCut N hj x := by
  have hz : y ∈ ownSupport N hj := mem_ownSupport_of_own_cycle N hj htOwn hy
  have hTy : rowAt N y ⊆ ownCut N hj y := rowAt_subset_ownCut N hj y
  have hEq := cuts_eq_of_mem_own_cycle N hj hpat hmin htOwn hx hy
  simpa [hEq.2] using hTy

/-- Nonnegative integer profile, attaining container, and constancy on
the specified own factor cycle of `x`. -/
theorem extendedCuts_on_own_cycle {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x : V} (hx : x ∈ ownSupport N hj)
    {t : Fin F.card} (htOwn : t ∈ N.own j hj)
    (hxt : x ∈ (F.getCycle t).support) :
    0 ≤ cutDelta N hj x ∧
      ownCut N hj x ⊆ extendedHost N hj ∧
        ((componentCount G (extendedHost N hj \ ownCut N hj x) : ℤ) -
          ((ownCut N hj x).card : ℤ) = cutDelta N hj x) ∧
          (∀ y ∈ (F.getCycle t).support,
            cutDelta N hj y = cutDelta N hj x ∧
              ownCut N hj y = ownCut N hj x ∧
                rowAt N y ⊆ ownCut N hj x) := by
  refine ⟨cutDelta_nonneg N hj hpat hmin hx, ownCut_subset_host N hj x,
    ownCut_attains N hj hpat hx, ?_⟩
  intro y hy
  have hEq := cuts_eq_of_mem_own_cycle N hj hpat hmin htOwn hxt hy
  exact ⟨hEq.1.symm, hEq.2.symm,
    rowAt_subset_ownCut_of_mem_own_cycle N hj hpat hmin htOwn hxt hy⟩

lemma card_selected_quad {i j k l : Fin F.card}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ({i, j, k, l} : Finset (Fin F.card)).card = 4 := by
  have hi : i ∉ ({j, k, l} : Finset (Fin F.card)) := by simp [hij, hik, hil]
  have hj : j ∉ ({k, l} : Finset (Fin F.card)) := by simp [hjk, hjl]
  have hk : k ∉ ({l} : Finset (Fin F.card)) := by simp [hkl]
  rw [card_insert_of_notMem hi, card_insert_of_notMem hj, card_insert_of_notMem hk,
    card_singleton]

lemma CycleFactor.selectedSupport_quad (i j k l : Fin F.card) :
    F.selectedSupport {i, j, k, l} =
      (F.getCycle i).support ∪ (F.getCycle j).support ∪
        (F.getCycle k).support ∪ (F.getCycle l).support := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hx
    have ht' : t = i ∨ t = j ∨ t = k ∨ t = l := by simpa using ht
    rcases ht' with rfl | rfl | rfl | rfl
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_union.2 (Or.inl hxt)))))
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_union.2 (Or.inr hxt)))))
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr hxt)))
    · exact mem_union.2 (Or.inr hxt)
  · intro hx
    rw [CycleFactor.mem_selectedSupport]
    rcases mem_union.1 hx with h | hl
    · rcases mem_union.1 h with h' | hk
      · rcases mem_union.1 h' with hi | hj
        · exact ⟨i, by simp, hi⟩
        · exact ⟨j, by simp, hj⟩
      · exact ⟨k, by simp, hk⟩
    · exact ⟨l, by simp, hl⟩

lemma support_union_eq_selected_quad {i j k l : Fin F.card} (C : GraphCycle G)
    (hC : C.support =
      (F.getCycle i).support ∪ (F.getCycle j).support ∪
        (F.getCycle k).support ∪ (F.getCycle l).support) :
    C.support = F.selectedSupport ({i, j, k, l} : Finset (Fin F.card)) := by
  rw [hC, CycleFactor.selectedSupport_quad]

lemma not_escape_of_own_cross_edge {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t s : Fin F.card} (htOwn : t ∈ N.own j hj) (hsOwn : s ∈ N.own j hj)
    (hts : t ≠ s)
    {x z : V} (hxC : x ∈ (F.getCycle t).support) (hzC : z ∈ (F.getCycle s).support)
    (hxz : G.Adj x z)
    {v : V}
    (hvAz' : v ∈ rowAt N ((F.getCycle s).succAt hzC))
    (hvT : v ∉ ownCut N hj ((F.getCycle t).succAt hxC)) : False := by
  set x' := (F.getCycle t).succAt hxC
  set z' := (F.getCycle s).succAt hzC
  have hx'C : x' ∈ (F.getCycle t).support :=
    GraphCycle.succAt_mem_support (F.getCycle t) hxC
  have hz'C : z' ∈ (F.getCycle s).support :=
    GraphCycle.succAt_mem_support (F.getCycle s) hzC
  have hx' : x' ∈ ownSupport N hj := mem_ownSupport_of_own_cycle N hj htOwn hx'C
  have hz' : z' ∈ ownSupport N hj := mem_ownSupport_of_own_cycle N hj hsOwn hz'C
  have hvF : v ∈ ineligibleSet G (coreSupport N \ rowAt N x') :=
    escape_row_subset_old_ineligible N hj hx' hz' (mem_sdiff.2 ⟨hvAz', hvT⟩)
  have hvE : v ∈ eligibleSet G (extendedHost N hj \ rowAt N x') :=
    escape_row_subset_new_eligible N hj hz' (mem_sdiff.2 ⟨hvAz', hvT⟩)
  have Hloc := localityHyp_at N hj hpat hx'
  have hvE' : v ∈ eligibleSet G
      (unionJ (coreSupport N \ rowAt N x') F.getCycle (N.foreign j hj)) := by
    simpa [unionJ_eq_host_remainder N hj x'] using hvE
  obtain ⟨i, hi, hw⟩ :=
    exists_single_release_eq F.getCycle Hloc hvF hvE'
  have hpL := pathCoverNumber_remainder_eq_row N hj hx'
  rcases hw with hstrict | ⟨heq, hvEi⟩
  · have hsi : pathCoverNumber G
        ((coreSupport N \ rowAt N x') ∪ (F.getCycle i).support) <
          (rowAt N x').card := by
      simpa [hpL] using hstrict
    exact not_strict_saving_located_foreign N hj hpat hmin hx' hi hsi
  · have ht : t ≠ N.core := ((N.hOwnMem j hj t).1 htOwn).1
    have hs : s ≠ N.core := ((N.hOwnMem j hj s).1 hsOwn).1
    have hi' : i ≠ N.core := ((N.hForeignMem j hj i).1 hi).1
    have hti : t ≠ i := own_index_ne_foreign N hj htOwn hi
    have hsi : s ≠ i := own_index_ne_foreign N hj hsOwn hi
    have hHD : Disjoint (F.getCycle N.core).support (F.getCycle i).support :=
      F.disjoint_getCycle hi'.symm
    have hHX : Disjoint (F.getCycle N.core).support (F.getCycle t).support :=
      F.disjoint_getCycle ht.symm
    have hHZ : Disjoint (F.getCycle N.core).support (F.getCycle s).support :=
      F.disjoint_getCycle hs.symm
    have hDX : Disjoint (F.getCycle i).support (F.getCycle t).support :=
      F.disjoint_getCycle hti.symm
    have hDZ : Disjoint (F.getCycle i).support (F.getCycle s).support :=
      F.disjoint_getCycle hsi.symm
    have hXZ : Disjoint (F.getCycle t).support (F.getCycle s).support :=
      F.disjoint_getCycle hts
    have hAsub : rowAt N x' ⊆ coreSupport N := rowAt_subset_core N x'
    have hAne : (rowAt N x').Nonempty := rowAt_nonempty N hj hx'
    have hK0 : IsCograph G (coreSupport N \ rowAt N x') :=
      isCograph_old_remainder N hj hx'
    have hJ : IsCograph G
        ((coreSupport N \ rowAt N x') ∪ (F.getCycle i).support) :=
      isCograph_remainder_union_foreign N hj hpat hx' hi
    have hpJ : pathCoverNumber G
        ((coreSupport N \ rowAt N x') ∪ (F.getCycle i).support) =
          (rowAt N x').card := by
      simpa [hpL] using heq
    obtain ⟨P, hPsup, hPst, hPfin, _, _⟩ :=
      Cograph.exists_released_absorption
        (F.getCycle N.core) (F.getCycle i)
        (by simp [coreSupport]) rfl hHD hAsub hAne hK0 hpL hJ hpJ hvF hvEi
    have hsP : G.Adj x' P.start := adj_of_mem_rowAt N x' P.start hPst
    have hfP : G.Adj P.finish z' := by
      have : P.finish = v := hPfin
      simpa [this] using (adj_of_mem_rowAt N z' v hvAz').symm
    have hsH : P.start ∈ (F.getCycle N.core).support := by
      have : P.start ∈ rowAt N x' := hPst
      simpa [coreSupport] using rowAt_subset_core N x' this
    have hfH : P.finish ∈ (F.getCycle N.core).support := by
      have hvK : v ∈ coreSupport N \ rowAt N x' :=
        ineligibleSet_subset (G := G) _ hvF
      simpa [hPfin, coreSupport] using (mem_sdiff.1 hvK).1
    obtain ⟨γ, hγ⟩ :=
      exists_cycle_of_four_block_path
        (F.getCycle N.core) (F.getCycle i) (F.getCycle t) (F.getCycle s)
        hHD hHX hHZ hDX hDZ hXZ hxC hx'C hzC hz'C
        (Or.inl rfl) (Or.inl rfl) hxz P
        (by simpa [coreSupport] using hPsup) hsH hfH hsP hfP
    have hspan :
        γ.support =
          F.selectedSupport ({N.core, i, t, s} : Finset (Fin F.card)) :=
      support_union_eq_selected_quad (i := N.core) (j := i) (k := t) (l := s) γ
        (by simpa [coreSupport] using hγ)
    have h4 : 2 ≤ ({N.core, i, t, s} : Finset (Fin F.card)).card := by
      have hcard := card_selected_quad
        (i := N.core) (j := i) (k := t) (l := s)
        hi'.symm ht.symm hs.symm hti.symm hsi.symm hts
      omega
    exact CycleFactor.not_exists_merge_of_min F hmin
      ({N.core, i, t, s} : Finset (Fin F.card)) h4 γ hspan

lemma rowAt_subset_ownCut_of_own_cross_edge {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t s : Fin F.card} (htOwn : t ∈ N.own j hj) (hsOwn : s ∈ N.own j hj)
    (hts : t ≠ s)
    {x z : V} (hxC : x ∈ (F.getCycle t).support) (hzC : z ∈ (F.getCycle s).support)
    (hxz : G.Adj x z) :
    rowAt N ((F.getCycle s).succAt hzC) ⊆
      ownCut N hj ((F.getCycle t).succAt hxC) := by
  intro v hv
  by_contra hvT
  exact not_escape_of_own_cross_edge N hj hpat hmin htOwn hsOwn hts hxC hzC hxz hv hvT

lemma cuts_eq_of_own_cross_edge {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {t s : Fin F.card} (htOwn : t ∈ N.own j hj) (hsOwn : s ∈ N.own j hj)
    (hts : t ≠ s)
    {x z : V} (hxC : x ∈ (F.getCycle t).support) (hzC : z ∈ (F.getCycle s).support)
    (hxz : G.Adj x z) :
    cutDelta N hj ((F.getCycle t).succAt hxC) =
      cutDelta N hj ((F.getCycle s).succAt hzC) ∧
        ownCut N hj ((F.getCycle t).succAt hxC) =
          ownCut N hj ((F.getCycle s).succAt hzC) := by
  have hx'C := GraphCycle.succAt_mem_support (F.getCycle t) hxC
  have hz'C := GraphCycle.succAt_mem_support (F.getCycle s) hzC
  have hx' := mem_ownSupport_of_own_cycle N hj htOwn hx'C
  have hz' := mem_ownSupport_of_own_cycle N hj hsOwn hz'C
  have hAz :=
    rowAt_subset_ownCut_of_own_cross_edge N hj hpat hmin htOwn hsOwn hts hxC hzC hxz
  have hAx :=
    rowAt_subset_ownCut_of_own_cross_edge N hj hpat hmin hsOwn htOwn hts.symm
      hzC hxC hxz.symm
  exact cuts_eq_of_mutual_row_containment N hj hpat hx' hz' hAz hAx

lemma cuts_eq_of_own_adj {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x z : V} (hx : x ∈ ownSupport N hj) (hz : z ∈ ownSupport N hj)
    (hxz : G.Adj x z) :
    cutDelta N hj x = cutDelta N hj z ∧ ownCut N hj x = ownCut N hj z := by
  obtain ⟨t, ht, htOwn, hxt, _⟩ := exists_own_index N hj hx
  obtain ⟨s, hs, hsOwn, hzs, _⟩ := exists_own_index N hj hz
  by_cases hts : t = s
  · subst hts
    exact cuts_eq_of_mem_own_cycle N hj hpat hmin htOwn hxt hzs
  · have hx'C := GraphCycle.succAt_mem_support (F.getCycle t) hxt
    have hz'C := GraphCycle.succAt_mem_support (F.getCycle s) hzs
    have hxx' :=
      cuts_eq_of_own_cycle_edge N hj hpat hmin htOwn hxt hx'C (Or.inl rfl)
    have hzz' :=
      cuts_eq_of_own_cycle_edge N hj hpat hmin hsOwn hzs hz'C (Or.inl rfl)
    have hx'z' :=
      cuts_eq_of_own_cross_edge N hj hpat hmin htOwn hsOwn hts hxt hzs hxz
    exact ⟨hxx'.1.trans (hx'z'.1.trans hzz'.1.symm),
      hxx'.2.trans (hx'z'.2.trans hzz'.2.symm)⟩

lemma cuts_eq_of_own_walk {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x y : V} (hx : x ∈ ownSupport N hj)
    (p : G.Walk x y)
    (hsupp : ∀ v ∈ p.support, v ∈ ownSupport N hj) :
    cutDelta N hj x = cutDelta N hj y ∧ ownCut N hj x = ownCut N hj y := by
  refine p.rec (motive := fun u w q =>
      u ∈ ownSupport N hj →
        (∀ v ∈ q.support, v ∈ ownSupport N hj) →
          cutDelta N hj u = cutDelta N hj w ∧
            ownCut N hj u = ownCut N hj w) ?_ ?_ hx hsupp
  · intro u hu _hs
    exact ⟨rfl, rfl⟩
  · intro u v w hadj q ih hu hsupp'
    have hv : v ∈ ownSupport N hj :=
      hsupp' v (by
        have : v ∈ q.support := by
          simpa [Walk.getVert_zero] using Walk.getVert_mem_support q 0
        simpa [Walk.support_cons] using Or.inr this)
    have hxz := cuts_eq_of_own_adj N hj hpat hmin hu hv hadj
    have htail : ∀ z ∈ q.support, z ∈ ownSupport N hj := fun z hz =>
      hsupp' z (by
        simp [Walk.support_cons]
        exact Or.inr hz)
    have hy := ih hv htail
    exact ⟨hxz.1.trans hy.1, hxz.2.trans hy.2⟩

/-- Manuscript `prop:extended-cuts` on one own group: nonnegative integer
profile, attaining container inside the host, and constancy of `δ` and
`T` along every original walk in the induced own support, hence on each
induced connected component. Every own-component vertex has its core row
contained in the common container. -/
theorem extendedCuts {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x : V} (hx : x ∈ ownSupport N hj) :
    0 ≤ cutDelta N hj x ∧
      ownCut N hj x ⊆ extendedHost N hj ∧
        ((componentCount G (extendedHost N hj \ ownCut N hj x) : ℤ) -
          ((ownCut N hj x).card : ℤ) = cutDelta N hj x) ∧
          (∀ y, y ∈ ownSupport N hj →
            (∃ p : G.Walk x y, ∀ v ∈ p.support, v ∈ ownSupport N hj) →
              cutDelta N hj y = cutDelta N hj x ∧
                ownCut N hj y = ownCut N hj x ∧
                  rowAt N y ⊆ ownCut N hj x) := by
  refine ⟨cutDelta_nonneg N hj hpat hmin hx, ownCut_subset_host N hj x,
    ownCut_attains N hj hpat hx, ?_⟩
  intro y hy ⟨p, hp⟩
  have hEq := cuts_eq_of_own_walk N hj hpat hmin hx p hp
  exact ⟨hEq.1.symm, hEq.2.symm, by
    have : rowAt N y ⊆ ownCut N hj y := rowAt_subset_ownCut N hj y
    simpa [hEq.2] using this⟩

end Nikoghosyan

