/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.Compatibility
import Nikoghosyan.Cograph.EndpointCuts

/-!
# Common-ineligible deletion

For an induced cograph carrier `U` and `f ∈ F(U)`,
`p(U.erase f) = p(U)+1`, `E(U.erase f) = E(U)`, and
`F(U.erase f) = F(U).erase f`. The generic helper takes the already
proved numerical F-cut as a hypothesis; the cograph specializations
import that identity rather than leaving it as an unproved premise.
Iteration over an arbitrary `C ⊆ F(U)` follows from the exact `F`
equality after each single deletion.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma eligibleSet_eq_sdiff_ineligible (U : Finset V) :
    eligibleSet G U = U \ ineligibleSet G U := by
  ext x
  constructor
  · intro hx
    rw [mem_eligibleSet_iff] at hx
    refine mem_sdiff.2 ⟨hx.1, ?_⟩
    intro hF
    exact (mem_ineligibleSet_iff (G := G)).1 hF |>.2 hx.2
  · intro hx
    have hxU : x ∈ U := (mem_sdiff.1 hx).1
    have hnotF : x ∉ ineligibleSet G U := (mem_sdiff.1 hx).2
    have hE : Eligible G U x := by
      have h := (mem_ineligibleSet_iff (G := G) (U := U) (x := x)).not
      simp only [not_and, Classical.not_not] at h
      exact h.mp hnotF hxU
    exact (mem_eligibleSet_iff (G := G)).2 ⟨hxU, hE⟩

lemma sdiff_erase_eq_sdiff_of_mem {s t : Finset V} {a : V} (ha : a ∈ t) :
    s.erase a \ t.erase a = s \ t := by
  ext x
  constructor
  · intro hx
    have hxL := mem_sdiff.1 hx
    have hxse := mem_erase.1 hxL.1
    refine mem_sdiff.2 ⟨hxse.2, ?_⟩
    intro hxt
    exact hxL.2 (mem_erase.2 ⟨hxse.1, hxt⟩)
  · intro hx
    have hxs : x ∈ s := (mem_sdiff.1 hx).1
    have hxt : x ∉ t := (mem_sdiff.1 hx).2
    have hne : x ≠ a := fun h => hxt (h ▸ ha)
    exact mem_sdiff.2 ⟨mem_erase.2 ⟨hne, hxs⟩, fun h => hxt (mem_erase.1 h).2⟩

lemma erase_sdiff_comm (s t : Finset V) (a : V) :
    s.erase a \ t = (s \ t).erase a := by
  ext x
  constructor
  · intro hx
    have hxL := mem_sdiff.1 hx
    have hxse := mem_erase.1 hxL.1
    exact mem_erase.2 ⟨hxse.1, mem_sdiff.2 ⟨hxse.2, hxL.2⟩⟩
  · intro hx
    have hxL := mem_erase.1 hx
    have hxs := mem_sdiff.1 hxL.2
    exact mem_sdiff.2 ⟨mem_erase.2 ⟨hxL.1, hxs.1⟩, hxs.2⟩

lemma subset_erase_ineligible {U : Finset V} {f : V} :
    (ineligibleSet G U).erase f ⊆ U.erase f := by
  intro x hx
  have hxF := mem_erase.1 hx
  exact mem_erase.2 ⟨hxF.1, ineligibleSet_subset (G := G) U hxF.2⟩

/-- Generic single-vertex common-F deletion, conditional on the numerical
F-cut identity of the original carrier. -/
lemma ineligible_deletion_erase {U : Finset V} {f : V}
    (hf : f ∈ ineligibleSet G U)
    (hfcut : componentCount G (U \ ineligibleSet G U) =
      (ineligibleSet G U).card + pathCoverNumber G U) :
    pathCoverNumber G (U.erase f) = pathCoverNumber G U + 1 ∧
    eligibleSet G (U.erase f) = eligibleSet G U ∧
    ineligibleSet G (U.erase f) = (ineligibleSet G U).erase f ∧
    componentCount G ((U.erase f) \ ineligibleSet G (U.erase f)) =
      (ineligibleSet G (U.erase f)).card + pathCoverNumber G (U.erase f) := by
  have hfU : f ∈ U := ineligibleSet_subset (G := G) U hf
  have hnotE : ¬ Eligible G U f := (mem_ineligibleSet_iff (G := G)).1 hf |>.2
  have hXsub : (ineligibleSet G U).erase f ⊆ U.erase f :=
    subset_erase_ineligible (U := U) (f := f)
  have hrem :
      U.erase f \ (ineligibleSet G U).erase f = U \ ineligibleSet G U :=
    sdiff_erase_eq_sdiff_of_mem hf
  have hcardX :
      ((ineligibleSet G U).erase f).card = (ineligibleSet G U).card - 1 :=
    card_erase_of_mem hf
  have hposF : 1 ≤ (ineligibleSet G U).card :=
    Nat.succ_le_of_lt (card_pos.2 ⟨f, hf⟩)
  have hcut' :=
    componentCount_sdiff_le (G := G) (U.erase f)
      ((ineligibleSet G U).erase f) hXsub
  have hp_ge : pathCoverNumber G U + 1 ≤ pathCoverNumber G (U.erase f) := by
    have : componentCount G (U.erase f \ (ineligibleSet G U).erase f) =
        (ineligibleSet G U).card + pathCoverNumber G U := by
      simpa [hrem] using hfcut
    omega
  have hp_le := pathCoverNumber_erase_le (G := G) U f
  have hp : pathCoverNumber G (U.erase f) = pathCoverNumber G U + 1 :=
    le_antisymm hp_le hp_ge
  have hEsub : eligibleSet G U ⊆ eligibleSet G (U.erase f) := by
    intro x hx
    rw [mem_eligibleSet_iff] at hx
    have hxf : x ≠ f := fun h => hnotE (h ▸ hx.2)
    obtain ⟨pc, hpc, p, hpP, hxend⟩ := hx.2
    have hend : pc.IsEndpoint x := ⟨p, hpP, hxend⟩
    have hend' : (pc.deleteVertex f).IsEndpoint x :=
      PathCover.IsEndpoint_deleteVertex pc hend hxf
    have hcard := pc.card_deleteVertex_le f
    have hmin : (pc.deleteVertex f).card = pathCoverNumber G (U.erase f) := by
      have hle := pathCoverNumber_le (G := G) (pc.deleteVertex f)
      omega
    obtain ⟨q, hq, hxq⟩ := hend'
    exact (mem_eligibleSet_iff (G := G)).2
      ⟨mem_erase.2 ⟨hxf, hx.1⟩, ⟨pc.deleteVertex f, hmin, q, hq, hxq⟩⟩
  have hXatt :
      componentCount G (U.erase f \ (ineligibleSet G U).erase f) =
        pathCoverNumber G (U.erase f) + ((ineligibleSet G U).erase f).card := by
    have : componentCount G (U.erase f \ (ineligibleSet G U).erase f) =
        (ineligibleSet G U).card + pathCoverNumber G U := by
      simpa [hrem] using hfcut
    omega
  have hXinc :
      (ineligibleSet G U).erase f ⊆ ineligibleSet G (U.erase f) :=
    eq_cut_bound_imp_subset_ineligible hXsub hXatt
  have hErev : eligibleSet G (U.erase f) ⊆ eligibleSet G U := by
    intro x hx
    have hxU' : x ∈ U.erase f := eligibleSet_subset (G := G) (U.erase f) hx
    have hnotF' : x ∉ ineligibleSet G (U.erase f) :=
      disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) (U.erase f)) hx
    have hx_notX : x ∉ (ineligibleSet G U).erase f := fun h => hnotF' (hXinc h)
    have hxE : x ∈ U.erase f \ (ineligibleSet G U).erase f :=
      mem_sdiff.2 ⟨hxU', hx_notX⟩
    have hxold : x ∈ U \ ineligibleSet G U := by rwa [hrem] at hxE
    rw [eligibleSet_eq_sdiff_ineligible]
    exact hxold
  have hE : eligibleSet G (U.erase f) = eligibleSet G U :=
    Subset.antisymm hErev hEsub
  have hF : ineligibleSet G (U.erase f) = (ineligibleSet G U).erase f := by
    have hEerase : f ∉ eligibleSet G U := by
      intro h
      exact hnotE ((mem_eligibleSet_iff (G := G)).1 h).2
    ext x
    constructor
    · intro hx
      rw [mem_ineligibleSet_iff] at hx
      have hxU' := hx.1
      have hxne : x ≠ f := (mem_erase.1 hxU').1
      have hxU : x ∈ U := (mem_erase.1 hxU').2
      refine mem_erase.2 ⟨hxne, ?_⟩
      rw [mem_ineligibleSet_iff]
      refine ⟨hxU, ?_⟩
      intro hEU
      have hxEold : x ∈ eligibleSet G U :=
        (mem_eligibleSet_iff (G := G)).2 ⟨hxU, hEU⟩
      have hxEnew : x ∈ eligibleSet G (U.erase f) := by rwa [← hE] at hxEold
      exact hx.2 ((mem_eligibleSet_iff (G := G)).1 hxEnew).2
    · intro hx
      have hxF := mem_erase.1 hx
      rw [mem_ineligibleSet_iff]
      refine ⟨mem_erase.2 ⟨hxF.1, ineligibleSet_subset (G := G) U hxF.2⟩, ?_⟩
      intro hE'
      have : x ∈ eligibleSet G (U.erase f) :=
        (mem_eligibleSet_iff (G := G)).2 ⟨mem_erase.2 ⟨hxF.1,
          ineligibleSet_subset (G := G) U hxF.2⟩, hE'⟩
      have : x ∈ eligibleSet G U := by rwa [hE] at this
      exact (mem_ineligibleSet_iff (G := G)).1 hxF.2 |>.2
        ((mem_eligibleSet_iff (G := G)).1 this).2
  have hfcut' :
      componentCount G ((U.erase f) \ ineligibleSet G (U.erase f)) =
        (ineligibleSet G (U.erase f)).card + pathCoverNumber G (U.erase f) := by
    have hrem' :
        (U.erase f) \ ineligibleSet G (U.erase f) = U \ ineligibleSet G U := by
      rw [hF, hrem]
    have hcard' :
        (ineligibleSet G (U.erase f)).card = (ineligibleSet G U).card - 1 := by
      rw [hF, hcardX]
    rw [hrem', hfcut, hcard', hp]
    omega
  exact ⟨hp, hE, hF, hfcut'⟩

/-- Iterate common-F deletion over an arbitrary subset of the original
ineligible set. The exact `F` equality after each step places the remaining
deleted vertices in the new ineligible set. -/
lemma ineligible_deletion_sdiff {U C : Finset V}
    (hC : C ⊆ ineligibleSet G U)
    (hfcut : componentCount G (U \ ineligibleSet G U) =
      (ineligibleSet G U).card + pathCoverNumber G U) :
    pathCoverNumber G (U \ C) = pathCoverNumber G U + C.card ∧
    eligibleSet G (U \ C) = eligibleSet G U ∧
    ineligibleSet G (U \ C) = ineligibleSet G U \ C ∧
    componentCount G ((U \ C) \ ineligibleSet G (U \ C)) =
      (ineligibleSet G (U \ C)).card + pathCoverNumber G (U \ C) := by
  induction C using Finset.induction generalizing U with
  | empty =>
    simp [hfcut]
  | insert f C hfC ih =>
    have hf : f ∈ ineligibleSet G U := hC (mem_insert_self f C)
    have hCsub : C ⊆ ineligibleSet G U := fun x hx =>
      hC (mem_insert_of_mem hx)
    have hsingle := ineligible_deletion_erase hf hfcut
    have hCnew : C ⊆ ineligibleSet G (U.erase f) := by
      intro x hx
      have hxne : x ≠ f := fun h => hfC (h ▸ hx)
      have hxF : x ∈ ineligibleSet G U := hCsub hx
      rw [hsingle.2.2.1]
      exact mem_erase.2 ⟨hxne, hxF⟩
    obtain ⟨hpC, hEC, hFC, hfcutC⟩ :=
      ih (U := U.erase f) hCnew hsingle.2.2.2
    have hEq : U \ insert f C = U.erase f \ C := by
      rw [sdiff_insert, erase_sdiff_comm]
    have hcard : (insert f C).card = C.card + 1 := card_insert_of_notMem hfC
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hEq, hpC, hsingle.1, hcard]
      omega
    · rw [hEq, hEC, hsingle.2.1]
    · rw [hEq, hFC, hsingle.2.2.1, sdiff_insert, erase_sdiff_comm]
    · rw [hEq]
      simpa using hfcutC

lemma ineligible_deletion_erase_of_cotreeOn {U : Finset V} {f : V}
    (hU : CotreeOn G U) (hf : f ∈ ineligibleSet G U) :
    pathCoverNumber G (U.erase f) = pathCoverNumber G U + 1 ∧
    eligibleSet G (U.erase f) = eligibleSet G U ∧
    ineligibleSet G (U.erase f) = (ineligibleSet G U).erase f :=
  let h := ineligible_deletion_erase hf (componentCount_sdiff_ineligibleSet_eq hU)
  ⟨h.1, h.2.1, h.2.2.1⟩

lemma ineligible_deletion_sdiff_of_cotreeOn {U C : Finset V}
    (hU : CotreeOn G U) (hC : C ⊆ ineligibleSet G U) :
    pathCoverNumber G (U \ C) = pathCoverNumber G U + C.card ∧
    eligibleSet G (U \ C) = eligibleSet G U ∧
    ineligibleSet G (U \ C) = ineligibleSet G U \ C :=
  let h := ineligible_deletion_sdiff hC (componentCount_sdiff_ineligibleSet_eq hU)
  ⟨h.1, h.2.1, h.2.2.1⟩

lemma ineligible_deletion_erase_of_isCograph {U : Finset V} {f : V}
    (hU : IsCograph G U) (hf : f ∈ ineligibleSet G U) :
    pathCoverNumber G (U.erase f) = pathCoverNumber G U + 1 ∧
    eligibleSet G (U.erase f) = eligibleSet G U ∧
    ineligibleSet G (U.erase f) = (ineligibleSet G U).erase f :=
  ineligible_deletion_erase_of_cotreeOn (cotreeOn_of_isCograph hU) hf

lemma ineligible_deletion_sdiff_of_isCograph {U C : Finset V}
    (hU : IsCograph G U) (hC : C ⊆ ineligibleSet G U) :
    pathCoverNumber G (U \ C) = pathCoverNumber G U + C.card ∧
    eligibleSet G (U \ C) = eligibleSet G U ∧
    ineligibleSet G (U \ C) = ineligibleSet G U \ C :=
  ineligible_deletion_sdiff_of_cotreeOn (cotreeOn_of_isCograph hU) hC

/-- Canonical flattened `Nikoghosyan.IsCograph` specialization. -/
lemma ineligible_deletion_erase_of_canonical {U : Finset V} {f : V}
    (hU : Nikoghosyan.IsCograph G U) (hf : f ∈ ineligibleSet G U) :
    pathCoverNumber G (U.erase f) = pathCoverNumber G U + 1 ∧
    eligibleSet G (U.erase f) = eligibleSet G U ∧
    ineligibleSet G (U.erase f) = (ineligibleSet G U).erase f :=
  ineligible_deletion_erase_of_isCograph (isCograph_iff.2 hU) hf

lemma ineligible_deletion_sdiff_of_canonical {U C : Finset V}
    (hU : Nikoghosyan.IsCograph G U) (hC : C ⊆ ineligibleSet G U) :
    pathCoverNumber G (U \ C) = pathCoverNumber G U + C.card ∧
    eligibleSet G (U \ C) = eligibleSet G U ∧
    ineligibleSet G (U \ C) = ineligibleSet G U \ C :=
  ineligible_deletion_sdiff_of_isCograph (isCograph_iff.2 hU) hC

end Cograph
end Nikoghosyan
