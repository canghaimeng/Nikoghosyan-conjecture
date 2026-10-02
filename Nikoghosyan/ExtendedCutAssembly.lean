/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.CycleAssembly
import Nikoghosyan.CycleIncidences
import Nikoghosyan.Locality

/-!
# Four-block original-path assembler

Internal given-path operator for manuscript `prop:extended-cuts` cross
edges. Given an actual original path `P` on `H ∪ D` whose ends are old
core vertices neighbouring specified own-cycle vertices `x'` and `z'`,
together with the physical factor edges `xx'` and `zz'` and the original
cross edge `xz`, open both own cycles at those edges and splice `P`
between them, then close through `xz`.

This is not a callback theorem and is not the paper proposition. Ends of
`P` are required to lie in the old core support `H`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Open a specified original cycle along a prescribed cycle edge `uv`,
producing a spanning original path from `u` to `v`. -/
noncomputable def openAlong (c : GraphCycle G) {u v : V}
    (hu : u ∈ c.support) (hv : v ∈ c.support)
    (hedge : c.succAt hu = v ∨ c.succAt hv = u) : GraphPath G :=
  if h : c.succAt hu = v then (c.openAt hu).reverse else c.openAt hv

lemma openAlong_start (c : GraphCycle G) {u v : V}
    (hu : u ∈ c.support) (hv : v ∈ c.support)
    (hedge : c.succAt hu = v ∨ c.succAt hv = u) :
    (openAlong c hu hv hedge).start = u := by
  by_cases h : c.succAt hu = v
  · simp [openAlong, h, GraphPath.reverse]
    exact GraphCycle.openAt_finish c hu
  · have : c.succAt hv = u := hedge.resolve_left h
    simp [openAlong, h]
    exact (GraphCycle.openAt_start c hv).trans this

lemma openAlong_finish (c : GraphCycle G) {u v : V}
    (hu : u ∈ c.support) (hv : v ∈ c.support)
    (hedge : c.succAt hu = v ∨ c.succAt hv = u) :
    (openAlong c hu hv hedge).finish = v := by
  by_cases h : c.succAt hu = v
  · simp [openAlong, h, GraphPath.reverse]
    exact (GraphCycle.openAt_start c hu).trans h
  · simp [openAlong, h]
    exact GraphCycle.openAt_finish c hv

lemma openAlong_support (c : GraphCycle G) {u v : V}
    (hu : u ∈ c.support) (hv : v ∈ c.support)
    (hedge : c.succAt hu = v ∨ c.succAt hv = u) :
    (openAlong c hu hv hedge).support = c.support := by
  by_cases h : c.succAt hu = v
  · simpa [openAlong, h, GraphPath.support_reverse] using c.openAt_support hu
  · simpa [openAlong, h] using c.openAt_support hv

/-- Given-path four-block assembly. Ends of `P` lie in the old core `H`. -/
theorem exists_cycle_of_four_block_path
    (cH cD cX cZ : GraphCycle G)
    (_hHD : Disjoint cH.support cD.support)
    (hHX : Disjoint cH.support cX.support)
    (hHZ : Disjoint cH.support cZ.support)
    (hDX : Disjoint cD.support cX.support)
    (hDZ : Disjoint cD.support cZ.support)
    (hXZ : Disjoint cX.support cZ.support)
    {x x' z z' : V}
    (hx : x ∈ cX.support) (hx' : x' ∈ cX.support)
    (hz : z ∈ cZ.support) (hz' : z' ∈ cZ.support)
    (hedgeX : cX.succAt hx = x' ∨ cX.succAt hx' = x)
    (hedgeZ : cZ.succAt hz = z' ∨ cZ.succAt hz' = z)
    (hxz : G.Adj x z)
    (P : GraphPath G)
    (hp : P.support = cH.support ∪ cD.support)
    (_hsH : P.start ∈ cH.support) (_hfH : P.finish ∈ cH.support)
    (hs : G.Adj x' P.start) (hf : G.Adj P.finish z') :
    ∃ γ : GraphCycle G,
      γ.support =
        cH.support ∪ cD.support ∪ cX.support ∪ cZ.support := by
  let Qx := openAlong cX hx hx' hedgeX
  let Qz := openAlong cZ hz' hz (Or.symm hedgeZ)
  have hQxst : Qx.start = x := openAlong_start cX hx hx' hedgeX
  have hQxfn : Qx.finish = x' := openAlong_finish cX hx hx' hedgeX
  have hQxsup : Qx.support = cX.support :=
    openAlong_support cX hx hx' hedgeX
  have hQzst : Qz.start = z' := openAlong_start cZ hz' hz (Or.symm hedgeZ)
  have hQzfn : Qz.finish = z := openAlong_finish cZ hz' hz (Or.symm hedgeZ)
  have hQzsup : Qz.support = cZ.support :=
    openAlong_support cZ hz' hz (Or.symm hedgeZ)
  have hadj1 : G.Adj Qx.finish P.start := by
    rw [hQxfn]
    exact hs
  have hadj2 : G.Adj P.finish Qz.start := by
    rw [hQzst]
    exact hf
  have hd1 : Disjoint Qx.support P.support := by
    rw [hQxsup, hp]
    exact disjoint_union_right.2 ⟨hHX.symm, hDX.symm⟩
  have hd2 : Disjoint (Qx.support ∪ P.support) Qz.support := by
    rw [hQxsup, hp, hQzsup]
    refine disjoint_left.2 ?_
    intro a ha haZ
    rcases mem_union.1 ha with haX | haP
    · exact disjoint_left.1 hXZ haX haZ
    · rcases mem_union.1 haP with haH | haD
      · exact disjoint_left.1 hHZ haH haZ
      · exact disjoint_left.1 hDZ haD haZ
  obtain ⟨R, hRsup, hRst, hRfn⟩ :=
    exists_splice_three Qx P Qz hadj1 hadj2 hd1 hd2
  have hRstart : R.start = x := hRst.trans hQxst
  have hRfinish : R.finish = z := hRfn.trans hQzfn
  have hadjClose : G.Adj R.finish R.start := by
    rw [hRfinish, hRstart]
    exact hxz.symm
  have h3 : 3 ≤ R.support.card := by
    have hxcard := cX.three_le_card_support
    have : cX.support ⊆ R.support := by
      intro a ha
      rw [hRsup, hQxsup]
      exact mem_union.2 (Or.inl (mem_union.2 (Or.inl ha)))
    exact le_trans hxcard (card_le_card this)
  refine ⟨R.toCycle hadjClose h3, ?_⟩
  rw [GraphPath.support_toCycle, hRsup, hQxsup, hp, hQzsup]
  ac_rfl

end Nikoghosyan
