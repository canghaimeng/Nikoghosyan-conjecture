/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.FactorAuxiliaryClosure
import Nikoghosyan.Cograph.HamiltonBalanced

/-!
Phase 10, item 1: actual `GlobalPortData` for cograph blocks of a real
original-edge cycle factor.

The global port of a vertex `x` is the R-incompatible class of `x` inside
the unique factor cycle that contains `x`. Original membership in block
`i` rewrites the index by `BlockPartition.index_eq`. Distinct classes on
the same block are realised by the checked Hamiltonian-cograph port
theorem, then oriented to the requested original endpoints.

No supplied port realisation, class-cut, or extension premise is used.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Global port of an original vertex: the R-incompatible class of that
vertex inside the unique factor cycle that contains it. The common port
type is `Finset V`. -/
noncomputable def factorPort (F : CycleFactor G) (x : V) : Finset V :=
  Cograph.rNonadjClass (G := G) (F.getCycle (F.partition.index x)).support x

lemma factorPort_eq_of_mem (F : CycleFactor G) {i : Fin F.card} {x : V}
    (hx : x ∈ (F.getCycle i).support) :
    factorPort F x =
      Cograph.rNonadjClass (G := G) (F.getCycle i).support x := by
  have hi : F.partition.index x = i := F.partition.index_eq hx
  unfold factorPort
  rw [hi]

lemma factorPort_eq_of_mem_block (F : CycleFactor G) {i : Fin F.card} {x : V}
    (hx : x ∈ F.partition.blocks i) :
    factorPort F x =
      Cograph.rNonadjClass (G := G) (F.getCycle i).support x :=
  factorPort_eq_of_mem F (by simpa [CycleFactor.partition] using hx)

/-- Orient a spanning-path compatibility witness so that the path runs
from the requested start to the requested finish. -/
lemma exists_oriented_spanning_of_compatible {U : Finset V} {x y : V}
    (h : SpanningPathCompatible (G := G) U x y) :
    ∃ p : GraphPath G, p.start = x ∧ p.finish = y ∧ p.support = U := by
  obtain ⟨_, p, hp, hends⟩ := h
  rcases hends with hxy | hyx
  · exact ⟨p, hxy.1, hxy.2, hp⟩
  · refine ⟨p.reverse, ?_, ?_, by simp [hp]⟩
    · simp [GraphPath.reverse, hyx.2]
    · simp [GraphPath.reverse, hyx.1]

lemma factor_block_balanced (F : CycleFactor G)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    (i : Fin F.card) :
    Cograph.IsBalancedEndpoints (G := G) (F.getCycle i).support :=
  (Cograph.hamiltonian_cograph_port_canonical (hcog i) (F.getCycle i) rfl).2.1

/-- Distinct actual R-classes on a cograph factor block are realised by an
original spanning path of that block, oriented to the requested ends. -/
lemma exists_spanning_of_factor_ports (F : CycleFactor G)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    {i : Fin F.card} {x y : V}
    (hx : x ∈ (F.getCycle i).support) (hy : y ∈ (F.getCycle i).support)
    (hp : factorPort F x ≠ factorPort F y) :
    ∃ p : GraphPath G,
      p.start = x ∧ p.finish = y ∧ p.support = (F.getCycle i).support := by
  have hxQ := factorPort_eq_of_mem F hx
  have hyQ := factorPort_eq_of_mem F hy
  have hne :
      Cograph.rNonadjClass (G := G) (F.getCycle i).support x ≠
        Cograph.rNonadjClass (G := G) (F.getCycle i).support y := by
    simpa [hxQ, hyQ] using hp
  have hR :
      SpanningPathCompatible (G := G) (F.getCycle i).support x y :=
    Cograph.spanningPath_of_distinct_classes
      (factor_block_balanced F hcog i) hx hy hne
  exact exists_oriented_spanning_of_compatible hR

/-- Actual `GlobalPortData` of a cycle factor whose blocks are cographs.
The colouring of the physical-cross-edge auxiliary graph uses this same
global port map. -/
noncomputable def globalPortData_of_cograph_factor (F : CycleFactor G)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support) :
    GlobalPortData (G := G) F.partition (Finset V) where
  port := factorPort F
  realize := by
    intro i x y hx hy hp
    have hx' : x ∈ (F.getCycle i).support := by
      simpa [CycleFactor.partition] using hx
    have hy' : y ∈ (F.getCycle i).support := by
      simpa [CycleFactor.partition] using hy
    simpa [CycleFactor.partition] using
      exists_spanning_of_factor_ports F hcog hx' hy' hp

lemma globalPortData_port_eq (F : CycleFactor G)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support) :
    (globalPortData_of_cograph_factor F hcog).port = factorPort F :=
  rfl

/-- Actual class-cut of a cograph factor block: deleting the R-class of
an original vertex of the block leaves exactly that many components. -/
lemma factor_block_partCut (F : CycleFactor G)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    {i : Fin F.card} {x : V} (hx : x ∈ (F.getCycle i).support) :
    componentCount G
        ((F.getCycle i).support \ factorPort F x) =
      (factorPort F x).card := by
  have hbal := factor_block_balanced F hcog i
  have hcut := Cograph.partCut_of_balanced (G := G) hbal hx
  simpa [factorPort_eq_of_mem F hx] using hcut

lemma factorPort_mem_self (F : CycleFactor G) {x : V} :
    x ∈ factorPort F x := by
  have hx : x ∈ (F.getCycle (F.partition.index x)).support := by
    simpa [CycleFactor.partition] using F.partition.mem_index x
  simpa [factorPort] using
    Cograph.mem_rNonadjClass_self (G := G) hx

lemma factorPort_subset_block (F : CycleFactor G) {i : Fin F.card} {x : V}
    (hx : x ∈ (F.getCycle i).support) :
    factorPort F x ⊆ (F.getCycle i).support := by
  simpa [factorPort_eq_of_mem F hx] using
    Cograph.rNonadjClass_subset (G := G) (F.getCycle i).support x

end Nikoghosyan
