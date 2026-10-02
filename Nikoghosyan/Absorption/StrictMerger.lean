/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Absorption.RootedRestoration
import Nikoghosyan.Absorption.Strict

/-!
# Manuscript `abs:cor:strict-merger`

Setup lemmas for the three-block strict merger, restoration from an
actual original `A`-ended spanning `H ∪ D` path, and the unconditional
existence theorem obtained by composing `exists_strict_absorption` with
that restoration. No `A`-to-`A` path is assumed in the final statement.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma k0_cograph_of_xrow
    (hpat : NoInducedP4UnionP1 G)
    {H X : Finset V} (hHX : Disjoint H X) {x : V} (hx : x ∈ X) :
    IsCograph G (H \ rowProfile (G := G) H x) :=
  xrow_cograph_complement_of_host hpat hHX hx

lemma pathCoverNumber_k0_of_saturated {H : Finset V} {x : V}
    (hSat : Cograph.Saturated (G := G) H (rowProfile (G := G) H x)) :
    pathCoverNumber G (H \ rowProfile (G := G) H x) =
      (rowProfile (G := G) H x).card :=
  hSat

lemma eligibleSet_eq_sdiff_canonicalContainer {U A : Finset V}
    (_hA : A ⊆ U) :
    eligibleSet G (U \ A) = U \ Cograph.canonicalContainer (G := G) U A := by
  ext z
  constructor
  · intro hz
    have hz' := (mem_eligibleSet_iff (G := G)).1 hz
    have hzU : z ∈ U := (mem_sdiff.1 hz'.1).1
    have hzA : z ∉ A := (mem_sdiff.1 hz'.1).2
    refine mem_sdiff.2 ⟨hzU, ?_⟩
    intro hzS
    have hzAF : z ∈ A ∪ ineligibleSet G (U \ A) := by
      simpa [Cograph.canonicalContainer_eq] using hzS
    rcases mem_union.1 hzAF with hzA' | hzF
    · exact hzA hzA'
    · exact (mem_ineligibleSet_iff (G := G)).1 hzF |>.2 hz'.2
  · intro hz
    have hzU : z ∈ U := (mem_sdiff.1 hz).1
    have hzS : z ∉ Cograph.canonicalContainer (G := G) U A :=
      (mem_sdiff.1 hz).2
    have hzA : z ∉ A := fun h =>
      hzS (Cograph.mem_canonicalContainer_of_mem_A h)
    have hzK : z ∈ U \ A := mem_sdiff.2 ⟨hzU, hzA⟩
    have hE : Eligible G (U \ A) z := by
      by_contra hnot
      exact hzS (by
        simpa [Cograph.canonicalContainer_eq] using
          mem_union.2 (Or.inr ((mem_ineligibleSet_iff (G := G)).2 ⟨hzK, hnot⟩)))
    exact (mem_eligibleSet_iff (G := G)).2 ⟨hzK, hE⟩

lemma drow_not_subset_S
    (hpat : NoInducedP4UnionP1 G)
    (cH : GraphCycle G) {X : Finset V}
    (hHX : Disjoint cH.support X)
    (hHnc : ¬ IsCograph G cH.support)
    {T S : Finset V} {d x : V}
    (hDrow : (rowProfile (G := G) cH.support d).Nonempty ∧
      IsCograph G (cH.support \ rowProfile (G := G) cH.support d) ∧
        Cograph.Saturated (G := G) cH.support
          (rowProfile (G := G) cH.support d) ∧
          Cograph.canonicalContainer (G := G) cH.support
              (rowProfile (G := G) cH.support d) = T)
    (hx : x ∈ X)
    (hXsat : Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support x))
    (hXgate : Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support x) = S)
    (hST : S ≠ T) :
    ¬ rowProfile (G := G) cH.support d ⊆ S := by
  intro hsub
  set H := cH.support
  set A := rowProfile (G := G) H x
  set C := rowProfile (G := G) H d
  have hAne := xrow_nonempty_of_noncograph_host hpat hHX hHnc hx
  have hKA := xrow_cograph_complement_of_host hpat hHX hx
  have hCne := hDrow.1
  have hKC := hDrow.2.1
  have hSatC := hDrow.2.2.1
  have hgateC := hDrow.2.2.2
  have hAsub : A ⊆ H := rowProfile_subset (G := G) H x
  have hCsub : C ⊆ H := rowProfile_subset (G := G) H d
  have hTgt : Cograph.Tight (G := G) H S := by
    have :=
      (Cograph.canonical_saturated_container_spec_of_canonical
        (G := G) hAsub hAne hKA hXsat).1
    simpa [hXgate] using this
  have hAS : A ⊆ S := by
    intro z hz
    have hzS :=
      Cograph.mem_canonicalContainer_of_mem_A (G := G) (U := H) (A := A) hz
    simpa [hXgate] using hzS
  have hno : ∀ a ∈ A, ∀ b ∈ C, ¬ SpanningPathCompatible (G := G) H a b := by
    intro a ha b hb
    exact no_spanning_both_in_tight cH rfl hTgt (hAS ha) (hsub hb)
  have hinc :=
    Cograph.incompatible_saturated_profiles (G := G) cH rfl hAsub hAne hKA
      hCsub hCne hKC (Or.inl hXsat) hno
  have heq : S = T := hXgate.symm.trans (hinc.2.2.2.trans hgateC)
  exact hST heq

lemma drow_meets_eligible_of_distinct_gates
    (hpat : NoInducedP4UnionP1 G)
    (cH : GraphCycle G) {X : Finset V}
    (hHX : Disjoint cH.support X)
    (hHnc : ¬ IsCograph G cH.support)
    {T S : Finset V} {d x : V}
    (hDrow : (rowProfile (G := G) cH.support d).Nonempty ∧
      IsCograph G (cH.support \ rowProfile (G := G) cH.support d) ∧
        Cograph.Saturated (G := G) cH.support
          (rowProfile (G := G) cH.support d) ∧
          Cograph.canonicalContainer (G := G) cH.support
              (rowProfile (G := G) cH.support d) = T)
    (hx : x ∈ X)
    (hXsat : Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support x))
    (hXgate : Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support x) = S)
    (hST : S ≠ T) :
    ∃ u ∈ eligibleSet G (cH.support \ rowProfile (G := G) cH.support x),
      G.Adj d u := by
  have hnot :=
    drow_not_subset_S hpat cH hHX hHnc hDrow hx hXsat hXgate hST
  obtain ⟨u, huC, huS⟩ : ∃ u ∈ rowProfile (G := G) cH.support d, u ∉ S := by
    by_contra hnone
    apply hnot
    intro z hz
    by_contra hzS
    exact hnone ⟨z, hz, hzS⟩
  have hu' := (mem_rowProfile_iff (G := G)).1 huC
  have hAsub : rowProfile (G := G) cH.support x ⊆ cH.support :=
    rowProfile_subset (G := G) cH.support x
  have huE : u ∈ eligibleSet G
      (cH.support \ rowProfile (G := G) cH.support x) := by
    have : u ∈
        cH.support \
          Cograph.canonicalContainer (G := G) cH.support
            (rowProfile (G := G) cH.support x) :=
      mem_sdiff.2 ⟨hu'.1, by simpa [hXgate] using huS⟩
    simpa [eligibleSet_eq_sdiff_canonicalContainer hAsub] using this
  exact ⟨u, huE, hu'.2⟩

lemma isCograph_K_of_anticomplete_x
    (hpat : NoInducedP4UnionP1 G)
    {H D : Finset V} {x : V}
    (hxH : x ∉ H) (hxD : x ∉ D)
    (hanti : ∀ d ∈ D, ¬ G.Adj x d) :
    IsCograph G ((H \ rowProfile (G := G) H x) ∪ D) := by
  intro a b c d ha hb hc hd hp
  have nAdj {z : V}
      (hz : z ∈ (H \ rowProfile (G := G) H x) ∪ D) : ¬ G.Adj x z := by
    rcases mem_union.1 hz with hzH | hzD
    · have hzrow : z ∉ rowProfile (G := G) H x := (mem_sdiff.1 hzH).2
      intro hadj
      exact hzrow ((mem_rowProfile_iff (G := G)).2 ⟨(mem_sdiff.1 hzH).1, hadj⟩)
    · exact hanti z hzD
  have hne {z : V}
      (hz : z ∈ (H \ rowProfile (G := G) H x) ∪ D) : x ≠ z := by
    intro h
    rcases mem_union.1 hz with hzH | hzD
    · exact hxH (h ▸ (mem_sdiff.1 hzH).1)
    · exact hxD (h ▸ hzD)
  have : ¬ (G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d) := by
    simp [nAdj ha, nAdj hb, nAdj hc, nAdj hd]
  exact this <|
    hpat hp (hne ha) (hne hb) (hne hc) (hne hd)

/-- Close an actual original `A`-ended spanning `H ∪ D` path through `x`
and restore the remaining `X` vertices. This is the composition half of
`abs:cor:strict-merger`. -/
theorem exists_cycle_of_strict_merger_of_AA_path
    (hpat : NoInducedP4UnionP1 G)
    (cH cD cX : GraphCycle G)
    (hHD : Disjoint cH.support cD.support)
    (hHX : Disjoint cH.support cX.support)
    (hDX : Disjoint cD.support cX.support)
    (hHnc : ¬ IsCograph G cH.support)
    {T S : Finset V}
    (hDrows : ∀ d ∈ cD.support,
      (rowProfile (G := G) cH.support d).Nonempty ∧
        IsCograph G (cH.support \ rowProfile (G := G) cH.support d) ∧
          Cograph.Saturated (G := G) cH.support
            (rowProfile (G := G) cH.support d) ∧
            Cograph.canonicalContainer (G := G) cH.support
                (rowProfile (G := G) cH.support d) = T)
    (hXsat : ∀ y ∈ cX.support,
      Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support y) ∧
        Cograph.canonicalContainer (G := G) cH.support
            (rowProfile (G := G) cH.support y) = S)
    (hST : S ≠ T)
    {x : V} (hx : x ∈ cX.support)
    (_hanti : ∀ d ∈ cD.support, ¬ G.Adj x d)
    (p : GraphPath G)
    (hp : p.support = cH.support ∪ cD.support)
    (hs : p.start ∈ rowProfile (G := G) cH.support x)
    (hf : p.finish ∈ rowProfile (G := G) cH.support x)
    (hne : p.start ≠ p.finish) :
    ∃ γ : GraphCycle G,
      γ.support = cH.support ∪ cD.support ∪ cX.support := by
  have hxH : x ∉ cH.support := disjoint_right.1 hHX hx
  have hxD : x ∉ cD.support := disjoint_right.1 hDX hx
  have hxP : x ∉ p.support := by
    intro hx'
    have hxQ : x ∈ cH.support ∪ cD.support := by simpa [hp] using hx'
    exact (mem_union.1 hxQ).elim hxH hxD
  have hadjs : G.Adj x p.start := (mem_rowProfile_iff (G := G)).1 hs |>.2
  have hadjf : G.Adj p.finish x :=
    ((mem_rowProfile_iff (G := G)).1 hf |>.2).symm
  obtain ⟨c0, hc0, _, _⟩ :=
    exists_graphCycle_insert p hadjs hadjf hxP hne
  have hc0' : c0.support = cH.support ∪ cD.support ∪ {x} := by
    rw [hc0, hp, insert_eq, union_comm, union_assoc]
  exact exists_cycle_of_rooted_prefix_restoration hpat cH cD cX
    hHD hHX hDX hHnc hDrows hXsat hST c0 hx hc0'

/-- Manuscript `abs:cor:strict-merger`. From a strict saving
`p(K₀ ∪ D) < |A|` at a vertex `x ∈ X` anticomplete to `D`, produce an
actual original cycle on `H ∪ D ∪ X`. The `A`-ended spanning path of
`H ∪ D` is derived, not assumed. -/
theorem exists_cycle_of_strict_merger
    (hpat : NoInducedP4UnionP1 G)
    (cH cD cX : GraphCycle G)
    (hHD : Disjoint cH.support cD.support)
    (hHX : Disjoint cH.support cX.support)
    (hDX : Disjoint cD.support cX.support)
    (hHnc : ¬ IsCograph G cH.support)
    {T S : Finset V}
    (hDrows : ∀ d ∈ cD.support,
      (rowProfile (G := G) cH.support d).Nonempty ∧
        IsCograph G (cH.support \ rowProfile (G := G) cH.support d) ∧
          Cograph.Saturated (G := G) cH.support
            (rowProfile (G := G) cH.support d) ∧
            Cograph.canonicalContainer (G := G) cH.support
                (rowProfile (G := G) cH.support d) = T)
    (hXsat : ∀ y ∈ cX.support,
      Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support y) ∧
        Cograph.canonicalContainer (G := G) cH.support
            (rowProfile (G := G) cH.support y) = S)
    (hST : S ≠ T)
    {x : V} (hx : x ∈ cX.support)
    (hanti : ∀ d ∈ cD.support, ¬ G.Adj x d)
    (hpK : pathCoverNumber G
        ((cH.support \ rowProfile (G := G) cH.support x) ∪ cD.support) <
      (rowProfile (G := G) cH.support x).card) :
    ∃ γ : GraphCycle G,
      γ.support = cH.support ∪ cD.support ∪ cX.support := by
  set H := cH.support
  set D := cD.support
  set A := rowProfile (G := G) H x
  have hAsub : A ⊆ H := rowProfile_subset (G := G) H x
  have hAne : A.Nonempty :=
    xrow_nonempty_of_noncograph_host hpat hHX hHnc hx
  have hK0 : IsCograph G (H \ A) := k0_cograph_of_xrow hpat hHX hx
  have hpK0 : pathCoverNumber G (H \ A) = A.card :=
    pathCoverNumber_k0_of_saturated (hXsat x hx).1
  have hxH : x ∉ H := disjoint_right.1 hHX hx
  have hxD : x ∉ D := disjoint_right.1 hDX hx
  have hK : IsCograph G ((H \ A) ∪ D) :=
    isCograph_K_of_anticomplete_x hpat hxH hxD hanti
  have hE : ∀ d ∈ D, ∃ u ∈ eligibleSet G (H \ A), G.Adj d u := by
    intro d hd
    exact drow_meets_eligible_of_distinct_gates hpat cH hHX hHnc
      (hDrows d hd) hx (hXsat x hx).1 (hXsat x hx).2 hST
  obtain ⟨p, hp, hs, hf, hne, _⟩ :=
    Cograph.exists_strict_absorption (H := H) (D := D) (A := A)
      cH cD rfl rfl hHD hAsub hAne hK0 hpK0 hK hE hpK
  exact exists_cycle_of_strict_merger_of_AA_path hpat cH cD cX
    hHD hHX hDX hHnc hDrows hXsat hST hx hanti p hp hs hf hne

end Nikoghosyan
