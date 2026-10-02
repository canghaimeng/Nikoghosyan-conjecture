/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.InsertionCompletion
import Nikoghosyan.Cograph.ProfileEndpoints
import Nikoghosyan.Cograph.HamiltonBalanced

/-!
# Manuscript `abs:thm:prefix-restoration`

Actual pairwise-disjoint original cycles `cH`, `cD`, `cX` in an
induced-`(P₄ ∪ P₁)`-free host, with `H` a noncograph. Every `D`-row is
nonempty, cograph-complement, saturated, and has common canonical gate
`T`. Every `X`-row is saturated with canonical gate `S ≠ T`. Given an
actual original cycle on `H ∪ D ∪ {x}` for one `x ∈ X`, restore an
actual original cycle on `H ∪ D ∪ X`.

No ambient `OneTough`, prefix-toughness callback, insertion-path witness,
or supplied `NoTightContainer` hypothesis. `Absorption.Strict` is not
imported.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Shared-vertex component bound -/

lemma componentCount_union_le_sub_one_of_adj {A B : Finset V}
    (_hdisj : Disjoint A B) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) (hadj : G.Adj a b) :
    componentCount G (A ∪ B) + 1 ≤
      componentCount G A + componentCount G B := by
  let f : (G.induce (A : Set V)).ConnectedComponent ⊕
        (G.induce (B : Set V)).ConnectedComponent →
      (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent
    | .inl C => C.map (induceIncl G (subset_union_left (s₁ := A)))
    | .inr C => C.map (induceIncl G (subset_union_right (s₁ := A)))
  have hf : Surjective f := by
    intro C
    refine C.ind fun z => ?_
    rcases mem_union.mp z.property with hA | hB
    · refine ⟨.inl ((G.induce (A : Set V)).connectedComponentMk ⟨z.val, hA⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
    · refine ⟨.inr ((G.induce (B : Set V)).connectedComponentMk ⟨z.val, hB⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
  have hnotinj : ¬ Injective f := by
    intro hinj
    let Ca := (G.induce (A : Set V)).connectedComponentMk ⟨a, ha⟩
    let Cb := (G.induce (B : Set V)).connectedComponentMk ⟨b, hb⟩
    have hmap : f (.inl Ca) = f (.inr Cb) := by
      apply ConnectedComponent.sound
      have ha' :
          induceIncl G (subset_union_left (s₁ := A) (s₂ := B)) ⟨a, ha⟩ =
            ⟨a, mem_union.2 (Or.inl ha)⟩ := rfl
      have hb' :
          induceIncl G (subset_union_right (s₁ := A) (s₂ := B)) ⟨b, hb⟩ =
            ⟨b, mem_union.2 (Or.inr hb)⟩ := rfl
      refine Adj.reachable ?_
      rw [ha', hb']
      exact (SimpleGraph.induce_adj (G := G)).2 hadj
    exact Sum.inl_ne_inr (hinj hmap)
  haveI : Fintype (G.induce (A : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce (B : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  have hlt :
      Fintype.card ((G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent) <
        Fintype.card
          ((G.induce (A : Set V)).ConnectedComponent ⊕
            (G.induce (B : Set V)).ConnectedComponent) :=
    Fintype.card_lt_of_surjective_not_injective f hf hnotinj
  simpa [componentCount, Nat.card_sum, Nat.card_eq_fintype_card] using
    Nat.succ_le_of_lt hlt

lemma componentCount_union_le_sub_one_of_mem {A B : Finset V} {x : V}
    (hxA : x ∈ A) (hxB : x ∈ B) :
    componentCount G (A ∪ B) + 1 ≤
      componentCount G A + componentCount G B := by
  let f : (G.induce (A : Set V)).ConnectedComponent ⊕
        (G.induce (B : Set V)).ConnectedComponent →
      (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent
    | .inl C => C.map (induceIncl G (subset_union_left (s₁ := A)))
    | .inr C => C.map (induceIncl G (subset_union_right (s₁ := A)))
  have hf : Surjective f := by
    intro C
    refine C.ind fun z => ?_
    rcases mem_union.mp z.property with hA | hB
    · refine ⟨.inl ((G.induce (A : Set V)).connectedComponentMk ⟨z.val, hA⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
    · refine ⟨.inr ((G.induce (B : Set V)).connectedComponentMk ⟨z.val, hB⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
  have hnotinj : ¬ Injective f := by
    intro hinj
    let Ca := (G.induce (A : Set V)).connectedComponentMk ⟨x, hxA⟩
    let Cb := (G.induce (B : Set V)).connectedComponentMk ⟨x, hxB⟩
    have hmap : f (.inl Ca) = f (.inr Cb) := by
      apply ConnectedComponent.sound
      exact Reachable.rfl
    exact Sum.inl_ne_inr (hinj hmap)
  haveI : Fintype (G.induce (A : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce (B : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  have hlt :
      Fintype.card ((G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent) <
        Fintype.card
          ((G.induce (A : Set V)).ConnectedComponent ⊕
            (G.induce (B : Set V)).ConnectedComponent) :=
    Fintype.card_lt_of_surjective_not_injective f hf hnotinj
  simpa [componentCount, Nat.card_sum, Nat.card_eq_fintype_card] using
    Nat.succ_le_of_lt hlt

/-! ### Cycle toughness and two-cycle base -/

lemma OneToughOn_of_cycle (c : GraphCycle G) : OneToughOn G c.support := by
  intro S hS h2
  have hSne : S.Nonempty := by
    by_contra hempty
    have hSemp : S = ∅ := not_nonempty_iff_eq_empty.1 hempty
    have : componentCount G (c.support \ S) = 1 := by
      simpa [hSemp] using componentCount_cycle_eq_one c
    omega
  exact componentCount_cycle_sdiff_le c hS hSne

lemma componentCount_union_cycles_of_row {cH cD : GraphCycle G}
    (hrow : ∀ d ∈ cD.support,
      (rowProfile (G := G) cH.support d).Nonempty) :
    componentCount G (cH.support ∪ cD.support) = 1 := by
  have hadj : ∀ d ∈ cD.support, ∃ u ∈ cH.support, G.Adj d u := by
    intro d hd
    obtain ⟨u, hu⟩ := hrow d hd
    have hu' := (mem_rowProfile_iff (G := G)).1 hu
    exact ⟨u, hu'.1, hu'.2⟩
  have hle :=
    componentCount_union_le_of_adj (U := cH.support) (W := cD.support) hadj
  haveI : Nonempty ((cH.support ∪ cD.support : Finset V) : Set V) :=
    ⟨⟨cH.start, mem_union.2 (Or.inl cH.start_mem_support)⟩⟩
  have hpos : 0 < componentCount G (cH.support ∪ cD.support) := Nat.card_pos
  have hH : componentCount G cH.support = 1 := componentCount_cycle_eq_one cH
  omega

/-! ### Derived X-row nonempty / cograph remainder -/

lemma xrow_nonempty_of_noncograph_host
    (hpat : NoInducedP4UnionP1 G)
    {H X : Finset V} (hHX : Disjoint H X)
    (hHnc : ¬ IsCograph G H) {y : V} (hy : y ∈ X) :
    (rowProfile (G := G) H y).Nonempty := by
  by_contra hempty
  have hnone : ∀ h ∈ H, ¬ G.Adj y h := by
    intro h hh hadj
    exact hempty ⟨h, (mem_rowProfile_iff (G := G)).2 ⟨hh, hadj⟩⟩
  have hHnc' : ∃ a b c d : V,
      a ∈ H ∧ b ∈ H ∧ c ∈ H ∧ d ∈ H ∧ InducedP4 G a b c d := by
    by_contra hnone'
    apply hHnc
    intro a b c d ha hb hc hd hp
    exact hnone' ⟨a, b, c, d, ha, hb, hc, hd, hp⟩
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hp⟩ := hHnc'
  have hyH : y ∉ H := disjoint_right.1 hHX hy
  have hne {z : V} (hz : z ∈ H) : y ≠ z := fun h => hyH (h ▸ hz)
  have := hpat hp (hne ha) (hne hb) (hne hc) (hne hd)
  rcases this with h | h | h | h
  · exact hnone a ha h
  · exact hnone b hb h
  · exact hnone c hc h
  · exact hnone d hd h

lemma xrow_cograph_complement_of_host
    (hpat : NoInducedP4UnionP1 G)
    {H X : Finset V} (hHX : Disjoint H X) {y : V} (hy : y ∈ X) :
    IsCograph G (H \ rowProfile (G := G) H y) :=
  isCograph_sdiff_rowProfile (H := H) (R := X) hHX hy
    (fun _ _ _ _ _ _ _ _ _ _ hp hxa hxb hxc hxd =>
      hpat hp hxa hxb hxc hxd)

/-! ### Distinct-gate rows meet `H \ T` -/

lemma no_spanning_both_in_tight {U T : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hT : Cograph.Tight (G := G) U T) {a b : V}
    (ha : a ∈ T) (hb : b ∈ T) :
    ¬ SpanningPathCompatible (G := G) U a b := by
  intro hR
  have hS : T ⊆ U := hT.1
  have hxy : a ≠ b := hR.1
  have hle :=
    Cograph.componentCount_sdiff_le_of_both_endpoints (G := G) (U := U)
      (S := T) hS ha hb hxy (by simpa [hc] using hR)
  have hpos : 1 ≤ T.card := Nat.succ_le_of_lt (card_pos.2 ⟨a, ha⟩)
  have heq : componentCount G (U \ T) = T.card := hT.2
  omega

lemma drow_subset_gate {H : Finset V} {d : V} {T : Finset V}
    (hCsub : rowProfile (G := G) H d ⊆ H)
    (hCne : (rowProfile (G := G) H d).Nonempty)
    (hKC : IsCograph G (H \ rowProfile (G := G) H d))
    (hSatC : Cograph.Saturated (G := G) H (rowProfile (G := G) H d))
    (hgateC : Cograph.canonicalContainer (G := G) H
        (rowProfile (G := G) H d) = T) :
    rowProfile (G := G) H d ⊆ T := by
  intro z hz
  have : z ∈ Cograph.canonicalContainer (G := G) H
      (rowProfile (G := G) H d) :=
    Cograph.mem_canonicalContainer_of_mem_A (U := H)
      (A := rowProfile (G := G) H d) hz
  simpa [hgateC] using this

lemma xrow_not_subset_T
    (hpat : NoInducedP4UnionP1 G)
    (cH : GraphCycle G) {X : Finset V}
    (hHX : Disjoint cH.support X)
    (hHnc : ¬ IsCograph G cH.support)
    {T S : Finset V} {d y : V}
    (hDrow : (rowProfile (G := G) cH.support d).Nonempty ∧
      IsCograph G (cH.support \ rowProfile (G := G) cH.support d) ∧
        Cograph.Saturated (G := G) cH.support
          (rowProfile (G := G) cH.support d) ∧
          Cograph.canonicalContainer (G := G) cH.support
              (rowProfile (G := G) cH.support d) = T)
    (hy : y ∈ X)
    (hXsat : Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support y))
    (hXgate : Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support y) = S)
    (hST : S ≠ T) :
    ¬ rowProfile (G := G) cH.support y ⊆ T := by
  intro hsub
  set H := cH.support
  set A := rowProfile (G := G) H y
  set C := rowProfile (G := G) H d
  have hAne := xrow_nonempty_of_noncograph_host hpat hHX hHnc hy
  have hKA := xrow_cograph_complement_of_host hpat hHX hy
  have hCne := hDrow.1
  have hKC := hDrow.2.1
  have hSatC := hDrow.2.2.1
  have hgateC := hDrow.2.2.2
  have hAsub : A ⊆ H := rowProfile_subset (G := G) H y
  have hCsub : C ⊆ H := rowProfile_subset (G := G) H d
  have hTgt : Cograph.Tight (G := G) H T := by
    have :=
      (Cograph.canonical_saturated_container_spec_of_canonical
        (G := G) hCsub hCne hKC hSatC).1
    simpa [hgateC] using this
  have hCT : C ⊆ T :=
    drow_subset_gate hCsub hCne hKC hSatC hgateC
  have hno : ∀ a ∈ A, ∀ b ∈ C, ¬ SpanningPathCompatible (G := G) H a b := by
    intro a ha b hb
    exact no_spanning_both_in_tight cH rfl hTgt (hsub ha) (hCT hb)
  have hinc :=
    Cograph.incompatible_saturated_profiles (G := G) cH rfl hAsub hAne hKA
      hCsub hCne hKC (Or.inr hSatC) hno
  have heq : S = T :=
    hXgate.symm.trans (hinc.2.2.2.trans hgateC)
  exact hST heq

lemma xrow_meets_H_sdiff_T
    (hpat : NoInducedP4UnionP1 G)
    (cH : GraphCycle G) {X : Finset V}
    (hHX : Disjoint cH.support X)
    (hHnc : ¬ IsCograph G cH.support)
    {T S : Finset V} {d y : V}
    (hDrow : (rowProfile (G := G) cH.support d).Nonempty ∧
      IsCograph G (cH.support \ rowProfile (G := G) cH.support d) ∧
        Cograph.Saturated (G := G) cH.support
          (rowProfile (G := G) cH.support d) ∧
          Cograph.canonicalContainer (G := G) cH.support
              (rowProfile (G := G) cH.support d) = T)
    (hy : y ∈ X)
    (hXsat : Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support y))
    (hXgate : Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support y) = S)
    (hST : S ≠ T) :
    ∃ u ∈ rowProfile (G := G) cH.support y, u ∉ T := by
  have hnot :=
    xrow_not_subset_T hpat cH hHX hHnc hDrow hy hXsat hXgate hST
  by_contra hnone
  apply hnot
  intro z hz
  by_contra hzT
  exact hnone ⟨z, hz, hzT⟩

/-! ### Prefix 1-toughness on `Q ∪ R` -/

lemma oneToughOn_Q_union_prefix
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
    (c0 : GraphCycle G) {x : V} (hx : x ∈ cX.support)
    (hc0 : c0.support = cH.support ∪ cD.support ∪ {x})
    (r : GraphPath G) (hr : r.support = cX.support) (hst : r.start = x)
    {n : ℕ} (hn : n ≤ r.walk.length) :
    OneToughOn G
      (cH.support ∪ cD.support ∪ (r.prefixTake n).support) := by
  intro ST hST' h2
  set H := cH.support
  set D := cD.support
  set Q := H ∪ D
  set R := (r.prefixTake n).support
  set U := ST ∩ Q
  set W := ST ∩ R
  have hQR : Disjoint Q R := by
    refine disjoint_left.2 ?_
    intro z hzQ hzR
    have hzX : z ∈ cX.support := by
      simpa [hr] using r.support_prefixTake_subset n hzR
    rcases mem_union.1 hzQ with hzH | hzD
    · exact disjoint_left.1 hHX hzH hzX
    · exact disjoint_left.1 hDX hzD hzX
  have hU : U ⊆ Q := inter_subset_right
  have hW : W ⊆ R := inter_subset_right
  have hcard : ST.card = U.card + W.card := by
    have hSTQ : ST ⊆ Q ∪ R := by
      intro z hz
      have := hST' hz
      simpa [union_assoc] using this
    simpa [U, W] using card_cut_split hQR hSTQ
  have hrem : (Q ∪ R) \ ST = (Q \ U) ∪ (R \ W) := by
    have hSTQ : ST ⊆ Q ∪ R := by
      intro z hz
      have := hST' hz
      simpa [union_assoc] using this
    nth_rw 1 [inter_union_eq_of_subset_union hSTQ]
    exact union_sdiff_of_disjoint hQR hU hW
  have hJ : Q ∪ R = H ∪ D ∪ R := by simp [Q, union_assoc]
  rw [← hJ, hrem] at h2 ⊢
  rw [hcard]
  have hxQ : x ∉ Q := by
    intro hxQ'
    rcases mem_union.1 hxQ' with hxH | hxD
    · exact disjoint_left.1 hHX hxH hx
    · exact disjoint_left.1 hDX hxD hx
  have hxR : x ∈ R := by
    have hst' : (r.prefixTake n).start = x :=
      (GraphPath.start_prefixTake r n).trans hst
    simpa [hst'] using (r.prefixTake n).start_mem_support
  have hDne : D.Nonempty := cD.support_nonempty
  obtain ⟨d0, hd0⟩ := hDne
  have hDrow0 := hDrows d0 hd0
  have hXrow : ∀ y ∈ R,
      (rowProfile (G := G) H y).Nonempty ∧
        ∃ u ∈ rowProfile (G := G) H y, u ∉ T := by
    intro y hy
    have hyX : y ∈ cX.support := by
      simpa [hr] using r.support_prefixTake_subset n hy
    have hsat := hXsat y hyX
    refine ⟨xrow_nonempty_of_noncograph_host hpat hHX hHnc hyX, ?_⟩
    exact xrow_meets_H_sdiff_T hpat cH hHX hHnc hDrow0 hyX hsat.1 hsat.2 hST
  have hQconn : componentCount G Q = 1 :=
    componentCount_union_cycles_of_row (cH := cH) (cD := cD)
      (fun d hd => (hDrows d hd).1)
  have hRpath : R = (r.prefixTake n).support := rfl
  by_cases hxW : x ∈ W
  · have hWne : W.Nonempty := ⟨x, hxW⟩
    have hpath : componentCount G (R \ W) ≤ W.card :=
      componentCount_path_sdiff_le_of_endpoint (r.prefixTake n) hW
        (x := x) hxW
        (Or.inl ((hst.symm).trans (GraphPath.start_prefixTake r n).symm))
    set UH := U ∩ H
    set UD := U ∩ D
    have hUcard : U.card = UH.card + UD.card := by
      have hUD : Disjoint H D := hHD
      have hUsub : U ⊆ H ∪ D := hU
      simpa [UH, UD, Q] using card_cut_split hUD (by
        intro z hz; simpa [Q] using hU hz)
    have hQrem : Q \ U = (H \ UH) ∪ (D \ UD) := by
      have : U = UH ∪ UD := by
        simpa [UH, UD, Q] using
          inter_union_eq_of_subset_union (H := H) (R := D) (ST := U)
            (by intro z hz; simpa [Q] using hU hz)
      have hdisj : Disjoint H D := hHD
      have hUH : UH ⊆ H := inter_subset_right
      have hUD' : UD ⊆ D := inter_subset_right
      simpa [this] using
        union_sdiff_of_disjoint (H := H) (R := D) (S := UH) (T := UD)
          hdisj hUH hUD'
    by_cases hUHne : UH.Nonempty
    · by_cases hUDne : UD.Nonempty
      · have hHle : componentCount G (H \ UH) ≤ UH.card :=
          componentCount_cycle_sdiff_le cH (inter_subset_right) hUHne
        have hDle : componentCount G (D \ UD) ≤ UD.card :=
          componentCount_cycle_sdiff_le cD (inter_subset_right) hUDne
        have hbase :=
          componentCount_union_le (G := G) (H \ UH) (D \ UD)
        have htot :=
          componentCount_union_le (G := G) ((H \ UH) ∪ (D \ UD)) (R \ W)
        have : (Q \ U) ∪ (R \ W) = ((H \ UH) ∪ (D \ UD)) ∪ (R \ W) := by
          simp [hQrem]
        rw [this]
        omega
      · -- `UD = ∅`, so `U ⊆ H` and `D` is intact.
        have hUDemp : UD = ∅ := not_nonempty_iff_eq_empty.1 hUDne
        have hUsubH : U ⊆ H := by
          intro z hz
          have hzQ : z ∈ Q := hU hz
          rcases mem_union.1 hzQ with hzH | hzD
          · exact hzH
          · have : z ∈ UD := mem_inter.2 ⟨hz, hzD⟩
            simp [hUDemp] at this
        have hUHU : UH = U := by
          ext z
          constructor
          · intro hz; exact (mem_inter.1 hz).1
          · intro hz; exact mem_inter.2 ⟨hz, hUsubH hz⟩
        have hHle : componentCount G (H \ UH) ≤ UH.card :=
          componentCount_cycle_sdiff_le cH (by simpa [hUHU] using hUsubH)
            (by simpa [hUHU] using hUHne)
        have hD1 : componentCount G D = 1 := componentCount_cycle_eq_one cD
        by_cases hex : ∃ a ∈ H \ UH, ∃ b ∈ D, G.Adj a b
        · obtain ⟨a, ha, b, hb, hadj⟩ := hex
          have hdisjHD : Disjoint (H \ UH) D :=
            hHD.mono sdiff_subset Subset.rfl
          have hbase : componentCount G ((H \ UH) ∪ D) ≤ UH.card := by
            have hle :=
              componentCount_union_le_sub_one_of_adj hdisjHD ha hb hadj
            omega
          have htot :=
            componentCount_union_le (G := G) ((H \ UH) ∪ D) (R \ W)
          have : (Q \ U) ∪ (R \ W) = ((H \ UH) ∪ D) ∪ (R \ W) := by
            simp [hQrem, hUDemp]
          rw [this]
          omega
        · -- No D–(H\UH) edge: every D-row lies in `UH`.
          push Not at hex
          have hCrow : rowProfile (G := G) H d0 ⊆ UH := by
            intro z hz
            have hzH : z ∈ H := (mem_rowProfile_iff (G := G)).1 hz |>.1
            have hadj : G.Adj d0 z := (mem_rowProfile_iff (G := G)).1 hz |>.2
            by_contra hzU
            exact hex z (mem_sdiff.2 ⟨hzH, hzU⟩) d0 hd0 hadj.symm
          have hbase :
              componentCount G ((H \ UH) ∪ D) ≤ UH.card + 1 := by
            have hsum := componentCount_union_le (G := G) (H \ UH) D
            omega
          by_cases htight : componentCount G (H \ UH) = UH.card
          · have hTgtU : Cograph.Tight (G := G) H UH :=
              ⟨by simpa [hUHU] using hUsubH, htight⟩
            have hCsub : rowProfile (G := G) H d0 ⊆ H :=
              rowProfile_subset (G := G) H d0
            have hspec :=
              Cograph.canonical_saturated_container_spec_of_canonical
                (G := G) hCsub hDrow0.1 hDrow0.2.1 hDrow0.2.2.1
            have hUsubT : UH ⊆ T := by
              have hle := hspec.2.2 UH hTgtU (fun z hz => hCrow hz)
              simpa [H, hDrow0.2.2.2] using hle
            have hadjR : ∀ z ∈ R \ W, ∃ u ∈ H \ UH, G.Adj z u := by
              intro z hz
              obtain ⟨_, ⟨u, hu, huT⟩⟩ := hXrow z (mem_sdiff.1 hz).1
              have hu' := (mem_rowProfile_iff (G := G)).1 hu
              have huU : u ∉ UH := fun h => huT (hUsubT h)
              exact ⟨u, mem_sdiff.2 ⟨hu'.1, huU⟩, hu'.2⟩
            have hpref :
                componentCount G (((H \ UH) ∪ D) ∪ (R \ W)) ≤
                  componentCount G ((H \ UH) ∪ D) :=
              componentCount_union_le_of_adj
                (U := (H \ UH) ∪ D) (W := R \ W)
                (fun z hz => by
                  obtain ⟨u, hu, hadj⟩ := hadjR z hz
                  exact ⟨u, mem_union.2 (Or.inl hu), hadj⟩)
            have : (Q \ U) ∪ (R \ W) = ((H \ UH) ∪ D) ∪ (R \ W) := by
              simp [hQrem, hUDemp]
            rw [this]
            have hWpos : 1 ≤ W.card := Nat.succ_le_of_lt (card_pos.2 hWne)
            omega
          · have hlt : componentCount G (H \ UH) + 1 ≤ UH.card := by omega
            have hsum := componentCount_union_le (G := G) (H \ UH) D
            have hbase' : componentCount G ((H \ UH) ∪ D) ≤ UH.card := by
              omega
            have htot :=
              componentCount_union_le (G := G) ((H \ UH) ∪ D) (R \ W)
            have : (Q \ U) ∪ (R \ W) = ((H \ UH) ∪ D) ∪ (R \ W) := by
              simp [hQrem, hUDemp]
            rw [this]
            omega

    · -- `UH = ∅`: intact `H` joins every surviving D- and prefix vertex.
      have hUHemp : UH = ∅ := not_nonempty_iff_eq_empty.1 hUHne
      have hHrem : H \ UH = H := by simp [hUHemp]
      have hadjD : ∀ z ∈ D \ UD, ∃ u ∈ H, G.Adj z u := by
        intro z hz
        have hzD : z ∈ D := (mem_sdiff.1 hz).1
        obtain ⟨u, hu⟩ := (hDrows z hzD).1
        have hu' := (mem_rowProfile_iff (G := G)).1 hu
        exact ⟨u, hu'.1, hu'.2⟩
      have hadjR : ∀ z ∈ R \ W, ∃ u ∈ H, G.Adj z u := by
        intro z hz
        obtain ⟨hAne, ⟨u, hu, _⟩⟩ := hXrow z (mem_sdiff.1 hz).1
        have hu' := (mem_rowProfile_iff (G := G)).1 hu
        exact ⟨u, hu'.1, hu'.2⟩
      have hbase : componentCount G (H ∪ (D \ UD)) ≤ 1 := by
        have hH1 : componentCount G H = 1 := componentCount_cycle_eq_one cH
        exact (componentCount_union_le_of_adj (U := H) (W := D \ UD) hadjD).trans
          (le_of_eq hH1)
      have htot :
          componentCount G (H ∪ ((D \ UD) ∪ (R \ W))) ≤ 1 := by
        have hadj :
            ∀ z ∈ (D \ UD) ∪ (R \ W), ∃ u ∈ H, G.Adj z u := by
          intro z hz
          rcases mem_union.1 hz with hD' | hR'
          · exact hadjD z hD'
          · exact hadjR z hR'
        have hH1 : componentCount G H = 1 := componentCount_cycle_eq_one cH
        exact (componentCount_union_le_of_adj
            (U := H) (W := (D \ UD) ∪ (R \ W)) hadj).trans (le_of_eq hH1)
      have hrest : (Q \ U) ∪ (R \ W) = H ∪ ((D \ UD) ∪ (R \ W)) := by
        simp [hQrem, hHrem, union_assoc]
      have : componentCount G ((Q \ U) ∪ (R \ W)) ≤ 1 := by
        rw [hrest]
        exact htot
      omega
  · -- `x ∉ W`.
    have hxPref : x ∈ R \ W := mem_sdiff.2 ⟨hxR, hxW⟩
    by_cases hUemp : U = ∅
    · have hQU : Q \ U = Q := by simp [hUemp]
      have hadjR : ∀ z ∈ R \ W, ∃ u ∈ Q, G.Adj z u := by
        intro z hz
        obtain ⟨hAne, ⟨u, hu, _⟩⟩ := hXrow z (mem_sdiff.1 hz).1
        have hu' := (mem_rowProfile_iff (G := G)).1 hu
        exact ⟨u, mem_union.2 (Or.inl hu'.1), hu'.2⟩
      have hle :=
        componentCount_union_le_of_adj (U := Q) (W := R \ W) hadjR
      have hQUeq : (Q \ U) ∪ (R \ W) = Q ∪ (R \ W) := by simp [hQU]
      have : componentCount G ((Q \ U) ∪ (R \ W)) ≤ 1 := by
        rw [hQUeq]
        exact hle.trans (le_of_eq hQconn)
      omega
    · have hUne : U.Nonempty := (nonempty_iff_ne_empty (s := U)).2 hUemp
      have hxU : x ∉ U := fun hxU => hxQ (hU hxU)
      have hUsub : U ⊆ c0.support := by
        intro z hz
        have hzQ : z ∈ Q := hU hz
        have : z ∈ Q ∪ {x} := mem_union.2 (Or.inl hzQ)
        simpa [hc0] using this
      have hcle : componentCount G (c0.support \ U) ≤ U.card :=
        componentCount_cycle_sdiff_le c0 hUsub hUne
      have hBase : c0.support \ U = (Q \ U) ∪ {x} := by
        have hsup : c0.support = insert x Q := by
          rw [hc0, insert_eq, union_comm]
        have hxU' : x ∉ U := hxU
        ext z
        constructor
        · intro hz
          have hz' := mem_sdiff.1 hz
          have hzins : z ∈ insert x Q := by simpa [hsup] using hz'.1
          rcases mem_insert.1 hzins with hzx | hzQ
          · exact mem_union.2 (Or.inr (by simpa [hzx] using mem_singleton_self z))
          · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzQ, hz'.2⟩))
        · intro hz
          rcases mem_union.1 hz with hQU | hxsing
          · exact mem_sdiff.2 ⟨by
              have : z ∈ insert x Q :=
                mem_insert_of_mem (mem_sdiff.1 hQU).1
              simpa [hsup] using this, (mem_sdiff.1 hQU).2⟩
          · have hzX : z = x := mem_singleton.1 hxsing
            subst hzX
            exact mem_sdiff.2 ⟨by
              simpa [hsup] using mem_insert_self x Q, hxU'⟩
      have hxBase : x ∈ c0.support \ U := by
        simp [hBase]
      have hpath : componentCount G (R \ W) ≤ W.card + 1 :=
        componentCount_path_sdiff_le (r.prefixTake n) hW
      have hinter : x ∈ (c0.support \ U) ∩ (R \ W) :=
        mem_inter.2 ⟨hxBase, hxPref⟩
      have hmerge :=
        componentCount_union_le_sub_one_of_mem (G := G)
          (A := c0.support \ U) (B := R \ W) (x := x)
          hxBase hxPref
      have hcup : (Q \ U) ∪ (R \ W) = (c0.support \ U) ∪ (R \ W) := by
        rw [hBase, union_assoc]
        have : ({x} : Finset V) ∪ (R \ W) = R \ W :=
          union_eq_right.2 (singleton_subset_iff.2 hxPref)
        rw [this]
      rw [hcup]
      omega

/-! ### Finite insertion of the remaining physical prefix -/

lemma exists_cycle_of_rooted_prefixTake
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
    (c0 : GraphCycle G) {x : V} (hx : x ∈ cX.support)
    (hc0 : c0.support = cH.support ∪ cD.support ∪ {x})
    (r : GraphPath G) (hr : r.support = cX.support) (hst : r.start = x)
    (n : ℕ) (hn : n ≤ r.walk.length) :
    ∃ γ : GraphCycle G,
      γ.support = cH.support ∪ cD.support ∪ (r.prefixTake n).support := by
  induction n with
  | zero =>
    refine ⟨c0, ?_⟩
    rw [hc0, r.support_prefixTake_zero, hst]
  | succ n ih =>
    have hn0 : n ≤ r.walk.length := Nat.le_of_succ_le hn
    have hnlt : n < r.walk.length := Nat.lt_of_succ_le hn
    obtain ⟨γ, hγ⟩ := ih hn0
    set y := r.walk.getVert (n + 1)
    have hyX : y ∈ cX.support := by
      simpa [hr] using r.getVert_mem_path_support (n + 1)
    have hyH : y ∉ cH.support := disjoint_right.1 hHX hyX
    have hyD : y ∉ cD.support := disjoint_right.1 hDX hyX
    have hyQ : y ∉ cH.support ∪ cD.support := fun h =>
      (mem_union.1 h).elim hyH hyD
    have hyP : y ∉ (r.prefixTake n).support :=
      r.next_not_mem_prefixTake hnlt
    have hy : y ∉ γ.support := by
      rw [hγ]
      exact fun h => (mem_union.1 h).elim hyQ hyP
    have hinsert :
        insert y γ.support =
          cH.support ∪ cD.support ∪ (r.prefixTake (n + 1)).support := by
      rw [hγ, insert_union_right, r.support_prefixTake_succ hnlt]
    have hJ : OneToughOn G (insert y γ.support) := by
      rw [hinsert]
      exact oneToughOn_Q_union_prefix hpat cH cD cX hHD hHX hDX hHnc
        hDrows hXsat hST c0 hx hc0 r hr hst hn
    have hOn :
        NoInducedP4UnionP1On G (insert y γ.support) :=
      NoInducedP4UnionP1On.of_global hpat _
    have hK : IsCograph G
        (γ.support \ rowProfile (G := G) γ.support y) :=
      isCograph_current_remainder γ hy hOn
    obtain ⟨γ', hγ', _⟩ :=
      exists_original_cycle_of_vertex_insertion γ hy hJ hK
    refine ⟨γ', ?_⟩
    simpa [hinsert] using hγ'

/-- Manuscript `abs:thm:prefix-restoration`. -/
theorem exists_cycle_of_rooted_prefix_restoration
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
    (c0 : GraphCycle G) {x : V} (hx : x ∈ cX.support)
    (hc0 : c0.support = cH.support ∪ cD.support ∪ {x}) :
    ∃ γ : GraphCycle G,
      γ.support = cH.support ∪ cD.support ∪ cX.support := by
  obtain ⟨r, hr, hst, _⟩ := Cograph.exists_spanning_path_from cX hx
  obtain ⟨γ, hγ⟩ :=
    exists_cycle_of_rooted_prefixTake hpat cH cD cX hHD hHX hDX hHnc
      hDrows hXsat hST c0 hx hc0 r hr hst r.walk.length le_rfl
  refine ⟨γ, ?_⟩
  simpa [hr, r.support_prefixTake_length] using hγ

end Nikoghosyan

