/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.ExtendedCuts
import Nikoghosyan.Absorption.BoundarySupport
import Nikoghosyan.Cograph.IneligibleDeletion
import Nikoghosyan.InducedCutTransport

/-!
# Manuscript `lem:nonadjacent`

Same-own-group nonadjacent vertices `x, z ∈ B` satisfy `A_z ⊆ T_x`.
The `x = z` case is definitional row inclusion. Each actual foreign factor
cycle `D_i` has `p((H \ A_x) ∪ D_i) = |A_x|`, every old released endpoint
misses `D_i` by the core gate of `D_i`, and a single equal-count old
release adjacent to a nonadjacent `z` induces a forbidden `P4 ∪ P1`.
Full-R escape localises by `exists_single_release_eq`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

open PathCover
open GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

variable {F : CycleFactor G} (N : CanonicalNormalForm F)

/-! Cut notation (`coreSupport`, `rowAt`, `ownCut`, `localityHyp_at`, `same_own_row_subset_or_escape`, …) is imported from `Nikoghosyan.ExtendedCuts`. The lemmas below are the manuscript `lem:nonadjacent` package: exact single-foreign count, universal old-released miss, and P4∪P1 exclusion. -/

lemma pathCoverNumber_union_foreign_cycle_le {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G) {x : V} (hx : x ∈ ownSupport N hj)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj) :
    pathCoverNumber G
        ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) ≤
      pathCoverNumber G (coreSupport N \ rowAt N x) :=
  pathCoverNumber_union_cycle_le F.getCycle (localityHyp_at N hj hpat hx) hi

/-- Exact single-cycle count: append gives `≤`, a strict saving merges three
blocks of a globally minimum factor. -/
lemma pathCoverNumber_union_foreign_cycle_eq {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x : V} (hx : x ∈ ownSupport N hj)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj) :
    pathCoverNumber G
        ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) =
      (rowAt N x).card := by
  have hpL := pathCoverNumber_remainder_eq_row N hj hx
  have hle := pathCoverNumber_union_foreign_cycle_le N hj hpat hx hi
  have hle' : pathCoverNumber G
      ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support) ≤
    (rowAt N x).card := by simpa [hpL] using hle
  refine le_antisymm hle' ?_
  by_contra hlt
  exact not_strict_saving_located_foreign N hj hpat hmin hx hi
    (lt_of_not_ge hlt)

lemma foreign_index_ne_core {j : Fin F.card} (hj : j ≠ N.core)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj) :
    i ≠ N.core :=
  ((N.hForeignMem j hj i).1 hi).1

lemma disjoint_core_foreign_cycle {j : Fin F.card} (hj : j ≠ N.core)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj) :
    Disjoint (coreSupport N) (F.getCycle i).support :=
  F.disjoint_getCycle (foreign_index_ne_core N hj hi).symm

/-- Foreign-gate identity: `c((H ∪ D_i) \ T_{D_i}) = |T_{D_i}| + 1`. -/
lemma componentCount_core_union_cycle_sdiff_gate {j : Fin F.card}
    (hj : j ≠ N.core) {i : Fin F.card} (hi : i ∈ N.foreign j hj) :
    componentCount G
        ((coreSupport N ∪ (F.getCycle i).support) \
          N.gateOf i (foreign_index_ne_core N hj hi)) =
      (N.gateOf i (foreign_index_ne_core N hj hi)).card + 1 := by
  set TD := N.gateOf i (foreign_index_ne_core N hj hi)
  have hT : Cograph.Tight (G := G) (coreSupport N) TD := by
    simpa [coreSupport, TD] using N.hGateTight i (foreign_index_ne_core N hj hi)
  have hTsub : TD ⊆ coreSupport N := hT.1
  have hdisj : Disjoint (coreSupport N) (F.getCycle i).support :=
    disjoint_core_foreign_cycle N hj hi
  have hEq :
      (coreSupport N ∪ (F.getCycle i).support) \ TD =
        (coreSupport N \ TD) ∪ (F.getCycle i).support := by
    ext z
    constructor
    · intro hz
      have hzU : z ∈ coreSupport N ∪ (F.getCycle i).support := (mem_sdiff.1 hz).1
      have hzT : z ∉ TD := (mem_sdiff.1 hz).2
      rcases mem_union.1 hzU with hzH | hzD
      · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzH, hzT⟩))
      · exact mem_union.2 (Or.inr hzD)
    · intro hz
      rcases mem_union.1 hz with hzH | hzD
      · exact mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hzH).1),
          (mem_sdiff.1 hzH).2⟩
      · refine mem_sdiff.2 ⟨mem_union.2 (Or.inr hzD), ?_⟩
        intro hzT
        exact Finset.disjoint_left.1 hdisj (hTsub hzT) hzD
  have hnocross :
      ∀ a ∈ coreSupport N \ TD, ∀ b ∈ (F.getCycle i).support, ¬ G.Adj a b := by
    intro a ha b hb hab
    have haH : a ∈ coreSupport N := (mem_sdiff.1 ha).1
    have haT : a ∉ TD := (mem_sdiff.1 ha).2
    have : a ∈ TD := by
      simpa [TD, coreSupport] using
        N.hGateAttach i (foreign_index_ne_core N hj hi) a
          (by simpa [coreSupport] using haH) b hb hab
    exact haT this
  have hdisjRem : Disjoint (coreSupport N \ TD) (F.getCycle i).support :=
    Disjoint.mono_left sdiff_subset hdisj
  rw [hEq, Cograph.componentCount_union_of_no_cross hdisjRem hnocross,
    Cograph.Tight.eq_card (G := G) hT, componentCount_cycle_eq_one (F.getCycle i)]

/-- Every old released vertex of a single foreign join misses that cycle. -/
lemma released_old_misses_foreign_cycle {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x r : V} (hx : x ∈ ownSupport N hj)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj)
    (hrF : r ∈ ineligibleSet G (coreSupport N \ rowAt N x))
    (hrE : r ∈ eligibleSet G
      ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support)) :
    ∀ d ∈ (F.getCycle i).support, ¬ G.Adj r d := by
  set H := coreSupport N
  set A := rowAt N x
  set D := (F.getCycle i).support
  set L := H \ A
  have hi0 : i ≠ N.core := foreign_index_ne_core N hj hi
  set TD := N.gateOf i hi0
  have hdisjHD : Disjoint H D := disjoint_core_foreign_cycle N hj hi
  have hA : A ⊆ H := rowAt_subset_core N x
  have hAne : A.Nonempty := rowAt_nonempty N hj hx
  have hK0c : IsCograph G L := isCograph_old_remainder N hj hx
  have hKc : IsCograph G (L ∪ D) :=
    isCograph_remainder_union_foreign N hj hpat hx hi
  have hpK0 : pathCoverNumber G L = A.card :=
    pathCoverNumber_remainder_eq_row N hj hx
  have hpK : pathCoverNumber G (L ∪ D) = A.card :=
    pathCoverNumber_union_foreign_cycle_eq N hj hpat hmin hx hi
  obtain ⟨p, hpsup, hstartA, hfin, hne, _hprot⟩ :=
    Cograph.exists_released_absorption (F.getCycle N.core) (F.getCycle i)
      (by simp [H, coreSupport]) (by simp [D])
      hdisjHD hA hAne hK0c hpK0 hKc hpK hrF hrE
  have hT : Cograph.Tight (G := G) H TD := by
    simpa [H, TD, coreSupport] using N.hGateTight i hi0
  have hTsubH : TD ⊆ H := hT.1
  have hTsub' : TD ⊆ p.support := by
    intro t ht
    have htH : t ∈ H := hTsubH ht
    have : t ∈ H ∪ D := mem_union.2 (Or.inl htH)
    simpa [hpsup] using this
  have hc := componentCount_core_union_cycle_sdiff_gate N hj hi
  have hcount :
      componentCount G (p.support \ TD) = TD.card + 1 := by
    simpa [hpsup, H, D, TD] using hc
  have hnotend : ¬ (p.start ∈ TD ∨ p.finish ∈ TD) := by
    intro hends
    rcases hends with hs | hf
    · have hle :=
        componentCount_path_sdiff_le_of_endpoint p hTsub' hs (Or.inl rfl)
      have hle' : TD.card + 1 ≤ TD.card := by simpa [hcount] using hle
      exact Nat.not_succ_le_self TD.card hle'
    · have hle :=
        componentCount_path_sdiff_le_of_endpoint p hTsub' hf (Or.inr rfl)
      have hle' : TD.card + 1 ≤ TD.card := by simpa [hcount] using hle
      exact Nat.not_succ_le_self TD.card hle'
  have hrH : r ∈ H := by
    have hrL : r ∈ L := (mem_ineligibleSet_iff (G := G)).1 hrF |>.1
    exact (mem_sdiff.1 hrL).1
  have hrnT : r ∉ TD := by
    intro hrT
    exact hnotend (Or.inr (by simpa [hfin] using hrT))
  intro d hd hadj
  have : r ∈ TD := by
    simpa [TD, H, coreSupport] using
      N.hGateAttach i hi0 r (by simpa [H, coreSupport] using hrH) d hd hadj
  exact hrnT this

lemma Eligible.union_disjoint_no_cross {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x : V} (hxA : x ∈ A) (hE : Eligible G A x) :
    Eligible G (A ∪ B) x := by
  obtain ⟨pcA, hmin, p, hp, hend⟩ := hE
  obtain ⟨pcB, hB⟩ := exists_min_pathCover (G := G) B
  let pc := Cograph.PathCover.unionDisjoint hdisj pcA pcB
  have hcard : pc.card = pathCoverNumber G (A ∪ B) := by
    rw [Cograph.PathCover.unionDisjoint_card hdisj pcA pcB, hmin, hB,
      Cograph.pathCoverNumber_disjoint_union hdisj hnocross]
  refine ⟨pc, hcard, p, ?_, hend⟩
  exact List.mem_append.2 (Or.inl hp)

lemma Eligible.of_union_disjoint_no_cross_left {A B : Finset V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x : V} (hxA : x ∈ A) (hE : Eligible G (A ∪ B) x) :
    Eligible G A x := by
  obtain ⟨pc, hmin, p, hp, hend⟩ := hE
  have hsupp : p.support ⊆ A ∪ B := pc.support_subset hp
  have hstartAB : p.start ∈ A ∨ p.start ∈ B := by
    have : p.start ∈ A ∪ B := hsupp p.start_mem_support
    simpa [mem_union] using this
  have hstartA : p.start ∈ A := by
    rcases hstartAB with hA | hB
    · exact hA
    · have : p.support ⊆ B :=
        Cograph.GraphPath.support_subset_of_no_cross'
          (A := A) (B := B) hnocross p hB hsupp
      have hxB : x ∈ B := by
        rcases hend with rfl | rfl
        · exact this p.start_mem_support
        · exact this p.finish_mem_support
      exact (Finset.disjoint_left.1 hdisj hxA hxB).elim
  have hpA : p ∈ (Cograph.PathCover.splitLeft hdisj hnocross pc).paths :=
    List.mem_filter.2 ⟨hp, decide_eq_true hstartA⟩
  have hcardA :
      (Cograph.PathCover.splitLeft hdisj hnocross pc).card =
        pathCoverNumber G A :=
    Cograph.splitLeft_card_eq_of_min hdisj hnocross pc hmin
  exact ⟨Cograph.PathCover.splitLeft hdisj hnocross pc, hcardA, p, hpA, hend⟩

lemma exists_middle_of_connected_cograph {U : Finset V} {h d : V}
    (_hUne : U.Nonempty)
    (hconn : (G.induce (U : Set V)).Connected)
    (hCog : IsCograph G U)
    (hh : h ∈ U) (hd : d ∈ U) (hne : h ≠ d) (hnadj : ¬ G.Adj h d) :
    ∃ u, u ∈ U ∧ G.Adj h u ∧ G.Adj u d := by
  have hOn : Cograph.IsCographOn G (U : Set V) :=
    (Cograph.isCographOn_iff_isCograph (G := G)).2 (Cograph.isCograph_iff.mpr hCog)
  have hCG : Cograph.IsCographGraph (G.induce (U : Set V)) :=
    (Cograph.isCographOn_iff_isCographGraph_induce (s := (U : Set V))).1 hOn
  let h' : (U : Set V) := ⟨h, hh⟩
  let d' : (U : Set V) := ⟨d, hd⟩
  have hdist := Cograph.dist_le_two_of_connected_cograph hconn hCG h' d'
  have hne' : h' ≠ d' := fun hst => hne (congrArg Subtype.val hst)
  have hnadj' : ¬ (G.induce (U : Set V)).Adj h' d' := by
    simpa [induce_adj] using hnadj
  have hR : (G.induce (U : Set V)).Reachable h' d' := hconn h' d'
  obtain ⟨p, _hpPath, hpLen⟩ := hR.exists_path_of_dist
  have hlen_le : p.length ≤ 2 := by
    simpa [hpLen] using hdist
  have hpos : 0 < p.length := by
    rw [Nat.pos_iff_ne_zero]
    intro hz
    have : h' = d' := by
      have h0 : p.getVert 0 = p.getVert p.length := by
        simp [hz, Walk.getVert_zero, Walk.getVert_length]
      simpa [Walk.getVert_zero, Walk.getVert_length] using h0
    exact hne' this
  have hne1 : p.length ≠ 1 := by
    intro h1
    have hlt : 0 < p.length := by omega
    have hadj := p.adj_getVert_succ hlt
    have : (G.induce (U : Set V)).Adj h' d' := by
      have h0 : p.getVert 0 = h' := by simp [Walk.getVert_zero]
      have hlen1 : p.getVert p.length = d' := Walk.getVert_length p
      have h1v : p.getVert 1 = d' := by simpa [h1] using hlen1
      simpa [h0, h1v] using hadj
    exact hnadj' this
  have h2 : p.length = 2 := by omega
  have hlt0 : 0 < p.length := by omega
  have hlt1 : 1 < p.length := by omega
  have hadj01 := p.adj_getVert_succ hlt0
  have hadj12 := p.adj_getVert_succ hlt1
  refine ⟨(p.getVert 1).1, (p.getVert 1).2, ?_, ?_⟩
  · have h0 : p.getVert 0 = h' := by simp [Walk.getVert_zero]
    simpa [induce_adj, h0] using hadj01
  · have hlen2 : p.getVert p.length = d' := Walk.getVert_length p
    have h2v : p.getVert 2 = d' := by simpa [h2] using hlen2
    simpa [induce_adj, h2v] using hadj12

/-- A single equal-count old release adjacent to a nonadjacent same-own
vertex induces a forbidden `P4 ∪ P1`. -/
lemma false_of_nonadjacent_sees_single_foreign_release
    {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x z h : V} (hx : x ∈ ownSupport N hj) (hz' : z ∈ ownSupport N hj)
    (hnadj : ¬ G.Adj x z) (hxz : x ≠ z)
    {i : Fin F.card} (hi : i ∈ N.foreign j hj)
    (hhAz : h ∈ rowAt N z)
    (hhF : h ∈ ineligibleSet G (coreSupport N \ rowAt N x))
    (hhE : h ∈ eligibleSet G
      ((coreSupport N \ rowAt N x) ∪ (F.getCycle i).support)) :
    False := by
  set H := coreSupport N
  set A := rowAt N x
  set D := (F.getCycle i).support
  set L := H \ A
  set J := L ∪ D
  have hmiss : ∀ d ∈ D, ¬ G.Adj h d :=
    released_old_misses_foreign_cycle N hj hpat hmin hx hi hhF hhE
  have hhL : h ∈ L := (mem_ineligibleSet_iff (G := G)).1 hhF |>.1
  have hhH : h ∈ H := (mem_sdiff.1 hhL).1
  have hhA : h ∉ A := (mem_sdiff.1 hhL).2
  have hCsubL : (ineligibleSet G L ∩ ineligibleSet G J) ⊆ ineligibleSet G L :=
    inter_subset_left
  have hCsubJ : (ineligibleSet G L ∩ ineligibleSet G J) ⊆ ineligibleSet G J :=
    inter_subset_right
  set C := ineligibleSet G L ∩ ineligibleSet G J
  have hKc : IsCograph G J :=
    isCograph_remainder_union_foreign N hj hpat hx hi
  have hK0c : IsCograph G L := isCograph_old_remainder N hj hx
  have hdelJ := Cograph.ineligible_deletion_sdiff_of_canonical (G := G) hKc hCsubJ
  have hdelL := Cograph.ineligible_deletion_sdiff_of_canonical (G := G) hK0c hCsubL
  have hhEJ : h ∈ eligibleSet G J := hhE
  have hhC : h ∉ C := by
    intro hC
    have : h ∈ ineligibleSet G J := (mem_inter.1 hC).2
    exact Finset.disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) J)
      hhEJ this
  have hhJC : h ∈ J \ C := mem_sdiff.2 ⟨mem_union.2 (Or.inl hhL), hhC⟩
  have hDsub : D ⊆ J := subset_union_right
  have hDC : Disjoint D C := by
    refine disjoint_left.2 ?_
    intro d hd hdC
    have hdL : d ∈ L :=
      ineligibleSet_subset (G := G) L ((mem_inter.1 hdC).1)
    exact Finset.disjoint_left.1
      (disjoint_remainder_foreign_cycle N hj hi x) hdL hd
  have hDJC : D ⊆ J \ C := by
    intro d hd
    exact mem_sdiff.2 ⟨hDsub hd, fun hC => (disjoint_left.1 hDC) hd hC⟩
  have hDne : D.Nonempty := (F.getCycle i).support_nonempty
  have hDconn : (G.induce (D : Set V)).Connected := by
    simpa [D] using Cograph.connected_of_cycle (F.getCycle i)
  obtain ⟨U, hUsub, hDU, hUne, hUconn, hnocrossU⟩ :=
    Cograph.exists_block_containing (K := J \ C) hDJC hDne hDconn
  have hUCog : IsCograph G U :=
    Cograph.isCograph_iff.mp
      (Cograph.isCograph_mono
        (Cograph.isCograph_mono (Cograph.isCograph_iff.mpr hKc) sdiff_subset)
        hUsub)
  have hhU : h ∈ U := by
    by_contra hhU
    have hhW : h ∈ (J \ C) \ U := mem_sdiff.2 ⟨hhJC, hhU⟩
    set W := (J \ C) \ U
    have hdisjUW : Disjoint U W := disjoint_sdiff
    have hcover : U ∪ W = J \ C := union_sdiff_of_subset hUsub
    have hnocross : ∀ a ∈ U, ∀ b ∈ W, ¬ G.Adj a b := hnocrossU
    have hhEJC : Eligible G (J \ C) h := by
      have : h ∈ eligibleSet G (J \ C) := by
        have hEq := hdelJ.2.1
        simpa [hEq] using hhEJ
      exact (mem_eligibleSet_iff (G := G)).1 this |>.2
    have hEW : Eligible G W h :=
      Eligible.of_union_disjoint_no_cross_left (A := W) (B := U)
        (Disjoint.symm (by simpa [W] using hdisjUW))
        (fun a ha b hb hab => hnocrossU b hb a ha hab.symm)
        (by simpa [W] using hhW)
        (by simpa [hcover, Finset.union_comm] using hhEJC)
    -- old eligible neighbour of D lies in U ∩ (L \ C)
    obtain ⟨d0, hd0⟩ := hDne
    have hd0R : d0 ∈ foreignSupport N hj :=
      (CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hi, hd0⟩
    obtain ⟨u0, hu0E, hadj0⟩ := foreign_meets_old_eligible N hj hpat hx hd0R
    have hu0L : u0 ∈ L := (mem_eligibleSet_iff (G := G)).1 hu0E |>.1
    have hu0C : u0 ∉ C := by
      intro huC
      have : u0 ∈ ineligibleSet G L := (mem_inter.1 huC).1
      exact Finset.disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) L)
        hu0E this
    have hu0JC : u0 ∈ J \ C :=
      mem_sdiff.2 ⟨mem_union.2 (Or.inl hu0L), hu0C⟩
    have hu0U : u0 ∈ U := by
      by_contra hu0nU
      have hu0W : u0 ∈ W := mem_sdiff.2 ⟨hu0JC, hu0nU⟩
      exact hnocrossU d0 (hDU hd0) u0 hu0W hadj0
    have hUL : U ∩ (L \ C) = U \ D := by
      ext y
      constructor
      · intro hy
        have hyU : y ∈ U := (mem_inter.1 hy).1
        have hyL : y ∈ L \ C := (mem_inter.1 hy).2
        have hyD : y ∉ D := by
          intro hyD
          exact Finset.disjoint_left.1
            (disjoint_remainder_foreign_cycle N hj hi x)
            (mem_sdiff.1 hyL).1 hyD
        exact mem_sdiff.2 ⟨hyU, hyD⟩
      · intro hy
        have hyU : y ∈ U := (mem_sdiff.1 hy).1
        have hyD : y ∉ D := (mem_sdiff.1 hy).2
        have hyJC : y ∈ J \ C := hUsub hyU
        have hyJ : y ∈ J := (mem_sdiff.1 hyJC).1
        have hyC : y ∉ C := (mem_sdiff.1 hyJC).2
        have hyL : y ∈ L := (mem_union.1 hyJ).resolve_right hyD
        exact mem_inter.2 ⟨hyU, mem_sdiff.2 ⟨hyL, hyC⟩⟩
    have hLsplit : (U \ D) ∪ W = L \ C := by
      ext y
      constructor
      · intro hy
        rcases mem_union.1 hy with hyU | hyW
        · have hy' : y ∈ U ∩ (L \ C) := by
            simpa [hUL] using hyU
          exact (mem_inter.1 hy').2
        · have hyJC : y ∈ J \ C := (mem_sdiff.1 hyW).1
          have hyU : y ∉ U := (mem_sdiff.1 hyW).2
          have hyJ : y ∈ J := (mem_sdiff.1 hyJC).1
          have hyC : y ∉ C := (mem_sdiff.1 hyJC).2
          have hyD : y ∉ D := by
            intro hyD
            exact hyU (hDU hyD)
          exact mem_sdiff.2 ⟨(mem_union.1 hyJ).resolve_right hyD, hyC⟩
      · intro hy
        have hyL : y ∈ L := (mem_sdiff.1 hy).1
        have hyC : y ∉ C := (mem_sdiff.1 hy).2
        have hyJC : y ∈ J \ C :=
          mem_sdiff.2 ⟨mem_union.2 (Or.inl hyL), hyC⟩
        by_cases hyU : y ∈ U
        · have hyD : y ∉ D := by
            intro hyD
            exact Finset.disjoint_left.1
              (disjoint_remainder_foreign_cycle N hj hi x) hyL hyD
          exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hyU, hyD⟩))
        · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hyJC, hyU⟩))
    have hdisjLW : Disjoint (U \ D) W :=
      Disjoint.mono_left sdiff_subset (by simpa [W] using hdisjUW)
    have hnocrossLW : ∀ a ∈ U \ D, ∀ b ∈ W, ¬ G.Adj a b :=
      fun a ha b hb => hnocrossU a (mem_sdiff.1 ha).1 b hb
    have hELC : Eligible G (L \ C) h := by
      have hE' :
          Eligible G (W ∪ (U \ D)) h :=
        Eligible.union_disjoint_no_cross (A := W) (B := U \ D)
          (Disjoint.symm hdisjLW)
          (fun a ha b hb hab => hnocrossLW b hb a ha hab.symm)
          (by simpa [W] using hhW) hEW
      have hEq : W ∪ (U \ D) = L \ C := by
        rw [union_comm]
        exact hLsplit
      simpa [hEq] using hE'
    have hEL : h ∈ eligibleSet G L := by
      have hEq := hdelL.2.1
      have : h ∈ eligibleSet G (L \ C) :=
        (mem_eligibleSet_iff (G := G)).2 ⟨mem_sdiff.2 ⟨hhL, hhC⟩, hELC⟩
      simpa [hEq] using this
    exact Finset.disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) L)
      hEL hhF
  obtain ⟨d, hdD⟩ := hDne
  have hdU : d ∈ U := hDU hdD
  have hne_hd : h ≠ d := by
    intro hhd
    have hdL : d ∈ L := by simpa [hhd] using hhL
    exact Finset.disjoint_left.1
      (disjoint_remainder_foreign_cycle N hj hi x) hdL hdD
  have hnadj_hd : ¬ G.Adj h d := hmiss d hdD
  obtain ⟨u, huU, hadj_hu, hadj_ud⟩ :=
    exists_middle_of_connected_cograph hUne hUconn hUCog hhU hdU hne_hd hnadj_hd
  have huD : u ∉ D := by
    intro huD
    exact hmiss u huD hadj_hu
  have huJC : u ∈ J \ C := hUsub huU
  have huJ : u ∈ J := (mem_sdiff.1 huJC).1
  have huC : u ∉ C := (mem_sdiff.1 huJC).2
  have huL : u ∈ L := (mem_union.1 huJ).resolve_right huD
  have huE : u ∈ eligibleSet G L := by
    by_contra huF
    have huIn : u ∈ ineligibleSet G L :=
      (mem_ineligibleSet_iff (G := G)).2 ⟨huL, fun hE =>
        huF ((mem_eligibleSet_iff (G := G)).2 ⟨huL, hE⟩)⟩
    have huEJ : u ∈ eligibleSet G J := by
      by_contra huFJ
      have : u ∈ ineligibleSet G J :=
        (mem_ineligibleSet_iff (G := G)).2 ⟨huJ, fun hE =>
          huFJ ((mem_eligibleSet_iff (G := G)).2 ⟨huJ, hE⟩)⟩
      exact huC (mem_inter.2 ⟨huIn, this⟩)
    exact released_old_misses_foreign_cycle N hj hpat hmin hx hi
      huIn huEJ d hdD hadj_ud
  have huS : u ∉
      Cograph.canonicalContainer (G := G) H A := by
    have huEL : Eligible G L u := (mem_eligibleSet_iff (G := G)).1 huE |>.2
    intro huCan
    have : u ∈ A ∪ ineligibleSet G L := by
      simpa [Cograph.canonicalContainer_eq, H, A, L] using huCan
    rcases mem_union.1 this with huA | huF
    · exact (mem_sdiff.1 huL).2 huA
    · exact ((mem_ineligibleSet_iff (G := G)).1 huF).2 huEL
  have hnadj_zu : ¬ G.Adj z u := by
    intro hzu
    have hzH : u ∈ rowAt N z :=
      (mem_rowProfile_iff (G := G)).2 ⟨(mem_sdiff.1 huL).1, hzu⟩
    have : u ∈ Cograph.canonicalContainer (G := G) H A :=
      same_own_row_subset_old_canonical N hj hx hz' hzH
    exact huS this
  have hnadj_zd : ¬ G.Adj z d := by
    intro hzd
    have hzR : d ∈ foreignSupport N hj :=
      (CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hi, hdD⟩
    exact anticomplete_own_foreign N hj hz' hzR hzd
  have hadj_zh : G.Adj z h := (mem_rowProfile_iff (G := G)).1 hhAz |>.2
  have hne_zh : z ≠ h := hadj_zh.ne
  have hne_hu : h ≠ u := hadj_hu.ne
  have hne_ud : u ≠ d := hadj_ud.ne
  have hne_zu : z ≠ u := by
    intro hzu
    have : u ∈ ownSupport N hj := by simpa [hzu] using hz'
    exact not_mem_core_of_own N hj this (mem_sdiff.1 huL).1
  have hne_zd : z ≠ d := by
    intro hzd
    have : d ∈ ownSupport N hj := by simpa [hzd] using hz'
    have hdR : d ∈ foreignSupport N hj :=
      (CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hi, hdD⟩
    exact not_mem_foreign_of_own N hj this hdR
  have hp4 : InducedP4 G z h u d :=
    ⟨hne_zh, hne_zu, hne_zd, hne_hu, hne_hd, hne_ud,
      hadj_zh, hadj_hu, hadj_ud, hnadj_zu, hnadj_zd, hnadj_hd⟩
  have hxH : x ∉ H := not_mem_core_of_own N hj hx
  have hne_xh : x ≠ h := fun hxh => hxH (by simpa [hxh] using hhH)
  have hne_xu : x ≠ u := fun hxu => hxH (by simpa [hxu] using (mem_sdiff.1 huL).1)
  have hne_xd : x ≠ d := by
    intro hxd
    have hdR : d ∈ foreignSupport N hj :=
      (CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hi, hdD⟩
    exact not_mem_foreign_of_own N hj (by simpa [hxd] using hx) hdR
  have hnadj_xh : ¬ G.Adj x h := by
    intro hxh
    exact hhA ((mem_rowProfile_iff (G := G)).2 ⟨hhH, hxh⟩)
  have hnadj_xu : ¬ G.Adj x u := by
    intro hxu
    exact (mem_sdiff.1 huL).2 ((mem_rowProfile_iff (G := G)).2
      ⟨(mem_sdiff.1 huL).1, hxu⟩)
  have hnadj_xd : ¬ G.Adj x d := by
    intro hxd
    have hdR : d ∈ foreignSupport N hj :=
      (CycleFactor.mem_selectedSupport (F := F)).2 ⟨i, hi, hdD⟩
    exact anticomplete_own_foreign N hj hx hdR hxd
  have hmeet := hpat hp4 hxz hne_xh hne_xu hne_xd
  rcases hmeet with h1 | h2 | h3 | h4
  · exact hnadj h1
  · exact hnadj_xh h2
  · exact hnadj_xu h3
  · exact hnadj_xd h4

/-- Manuscript `lem:nonadjacent`: nonadjacent same-own-group vertices
satisfy `A_z ⊆ T_x`. The `x = z` case is definitional row inclusion.
An escaping neighbour of `z` is an old released vertex of `H \ A_x` that
is new-eligible in `Q \ A_x`; locality release supplies a single foreign
cycle which either strictly saves (contradicting a minimum factor) or
equal-releases that vertex (inducing a forbidden `P4 ∪ P1`). -/
theorem nonadjacent_rows_subset_ownCut
    {j : Fin F.card} (hj : j ≠ N.core)
    (hpat : NoInducedP4UnionP1 G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {x z : V} (hx : x ∈ ownSupport N hj) (hz : z ∈ ownSupport N hj)
    (hnadj : ¬ G.Adj x z) :
    rowAt N z ⊆ ownCut N hj x := by
  by_cases hxz : x = z
  · subst hxz
    exact rowAt_subset_ownCut N hj x
  rcases same_own_row_subset_or_escape N hj hx hz with hsub | hexc
  · exact hsub
  · obtain ⟨h, hhAz, hhF, hhE⟩ := hexc
    have hhE' : h ∈ eligibleSet G
        (unionJ (coreSupport N \ rowAt N x) F.getCycle (N.foreign j hj)) := by
      simpa [unionJ_eq_host_remainder N hj x] using hhE
    obtain ⟨i, hi, hw⟩ :=
      exists_single_release_eq F.getCycle (localityHyp_at N hj hpat hx) hhF hhE'
    have hpL := pathCoverNumber_remainder_eq_row N hj hx
    rcases hw with hstrict | ⟨_, hhEi⟩
    · exact (not_strict_saving_located_foreign N hj hpat hmin hx hi
        (by simpa [hpL] using hstrict)).elim
    · exact (false_of_nonadjacent_sees_single_foreign_release N hj hpat hmin
        hx hz hnadj hxz hi hhAz hhF hhEi).elim

end Nikoghosyan
