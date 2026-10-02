/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.DistinctPath

/-!
# D-nonadjacent classes and actual part-cut certificates

For `x ∈ E(U)`, the D-nonadjacent class is
`P_x = { y ∈ E(U) | ¬ DistinctPathCompatible U x y }`.
`D` remains the existential common-minimum-cover relation. On a cotree
carrier, the classes are the parts of the complete-multipartite graph of
`D` on `E(U)`, and each part has an actual cut `S ⊆ F(U)` with
`c(U \ S) = |S| + p(U)` whose remainder has one induced component
containing `(F(U) ∪ P_x) \ S` in the original vertex set.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The D-nonadjacent class of an eligible vertex, as a finset of original
vertices. Ambient vertices outside `E(U)` are excluded. -/
noncomputable def dNonadjClass (U : Finset V) (x : V) : Finset V :=
  (eligibleSet G U).filter
    fun y => ¬ DistinctPathCompatible (G := G) U x y

lemma mem_dNonadjClass_iff {U : Finset V} {x y : V} :
    y ∈ dNonadjClass (G := G) U x ↔
      y ∈ eligibleSet G U ∧ ¬ DistinctPathCompatible (G := G) U x y := by
  simp [dNonadjClass]

lemma dNonadjClass_subset_eligible (U : Finset V) (x : V) :
    dNonadjClass (G := G) U x ⊆ eligibleSet G U :=
  filter_subset _ _

lemma not_DistinctPathCompatible_self (U : Finset V) (x : V) :
    ¬ DistinctPathCompatible (G := G) U x x := fun h => h.1 rfl

lemma mem_dNonadjClass_self {U : Finset V} {x : V}
    (hx : x ∈ eligibleSet G U) :
    x ∈ dNonadjClass (G := G) U x :=
  mem_dNonadjClass_iff.2 ⟨hx, not_DistinctPathCompatible_self (G := G) U x⟩

lemma dNonadjClass_symm {U : Finset V} {x y : V}
    (hx : x ∈ eligibleSet G U)
    (h : y ∈ dNonadjClass (G := G) U x) :
    x ∈ dNonadjClass (G := G) U y := by
  have hy := mem_dNonadjClass_iff.1 h
  exact mem_dNonadjClass_iff.2 ⟨hx, fun hD => hy.2 (DistinctPathCompatible.symm hD)⟩

lemma dNonadjClass_trans {U : Finset V} (hU : CotreeOn G U) {x y z : V}
    (hx : x ∈ eligibleSet G U) (hy : y ∈ eligibleSet G U)
    (hz : z ∈ eligibleSet G U)
    (hxy : y ∈ dNonadjClass (G := G) U x)
    (hyz : z ∈ dNonadjClass (G := G) U y) :
    z ∈ dNonadjClass (G := G) U x := by
  have hxy' := (mem_dNonadjClass_iff.1 hxy).2
  have hyz' := (mem_dNonadjClass_iff.1 hyz).2
  exact mem_dNonadjClass_iff.2
    ⟨hz, not_DistinctPathCompatible_trans_of_cotreeOn hU hx hy hz hxy' hyz'⟩

lemma dNonadjClass_eq_eligible_of_le_one {U : Finset V} {x : V}
    (hp : pathCoverNumber G U ≤ 1) (hx : x ∈ eligibleSet G U) :
    dNonadjClass (G := G) U x = eligibleSet G U := by
  ext y
  constructor
  · intro hy
    exact (mem_dNonadjClass_iff.1 hy).1
  · intro hy
    exact mem_dNonadjClass_iff.2
      ⟨hy, not_DistinctPathCompatible_of_le_one (G := G) hp⟩

lemma dNonadjClass_disjoint_union_left {A B : Finset V} {x : V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hx : x ∈ eligibleSet G A) :
    dNonadjClass (G := G) (A ∪ B) x = dNonadjClass (G := G) A x := by
  have hEU := eligibleSet_disjoint_union (G := G) hdisj hnocross
  ext y
  constructor
  · intro hy
    have hyU := mem_dNonadjClass_iff.1 hy
    have hyE : y ∈ eligibleSet G A ∪ eligibleSet G B := by
      rw [← hEU]; exact hyU.1
    rcases mem_union.1 hyE with hyA | hyB
    · refine mem_dNonadjClass_iff.2 ⟨hyA, ?_⟩
      intro hD
      exact hyU.2 (DistinctPathCompatible_union_left hdisj hnocross hD)
    · exact (hyU.2 (DistinctPathCompatible_union_cross hdisj hnocross
        (eligible_mem_of_mem_eligibleSet hx)
        (eligible_mem_of_mem_eligibleSet hyB))).elim
  · intro hy
    have hyA := mem_dNonadjClass_iff.1 hy
    have hyU : y ∈ eligibleSet G (A ∪ B) := by
      rw [hEU]; exact mem_union.2 (Or.inl hyA.1)
    refine mem_dNonadjClass_iff.2 ⟨hyU, ?_⟩
    intro hD
    exact hyA.2 (DistinctPathCompatible_union_of_left hdisj hnocross
      (eligibleSet_subset (G := G) A hx)
      (eligibleSet_subset (G := G) A hyA.1) hD)

lemma dNonadjClass_disjoint_union_right {A B : Finset V} {x : V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hx : x ∈ eligibleSet G B) :
    dNonadjClass (G := G) (A ∪ B) x = dNonadjClass (G := G) B x := by
  have hdisj' : Disjoint B A := hdisj.symm
  have hnocross' : ∀ b ∈ B, ∀ a ∈ A, ¬ G.Adj b a := fun b hb a ha hab =>
    hnocross a ha b hb hab.symm
  have h := dNonadjClass_disjoint_union_left (G := G) hdisj' hnocross' hx
  simpa [union_comm] using h

lemma dNonadjClass_complete_join_dominant {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hq : 2 ≤ pathCoverNumber G (A ∪ B))
    (hx : x ∈ eligibleSet G A) :
    dNonadjClass (G := G) (A ∪ B) x = dNonadjClass (G := G) A x := by
  have hE := eligibleSet_complete_join_dominant hAne hBne hAB hdom
  ext y
  constructor
  · intro hy
    have hyU := mem_dNonadjClass_iff.1 hy
    have hyA : y ∈ eligibleSet G A := by rw [← hE]; exact hyU.1
    refine mem_dNonadjClass_iff.2 ⟨hyA, ?_⟩
    intro hD
    exact hyU.2
      ((DistinctPathCompatible_complete_join_dominant_iff
        hAne hBne hAB hdom hq).2 hD)
  · intro hy
    have hyA := mem_dNonadjClass_iff.1 hy
    have hyU : y ∈ eligibleSet G (A ∪ B) := by rw [hE]; exact hyA.1
    refine mem_dNonadjClass_iff.2 ⟨hyU, ?_⟩
    intro hD
    exact hyA.2
      ((DistinctPathCompatible_complete_join_dominant_iff
        hAne hBne hAB hdom hq).1 hD)

/-- Pairwise reachability of `W` inside the induced subgraph on `U`. -/
def InOneComponent (U W : Finset V) : Prop :=
  ∃ hW : W ⊆ U,
    ∀ {a b : V} (ha : a ∈ W) (hb : b ∈ W),
      (G.induce (U : Set V)).Reachable ⟨a, hW ha⟩ ⟨b, hW hb⟩

lemma inOneComponent_mono {A B W : Finset V}
    (hAB : A ⊆ B) (h : InOneComponent (G := G) A W) :
    InOneComponent (G := G) B W := by
  obtain ⟨hW, hreach⟩ := h
  refine ⟨hW.trans hAB, ?_⟩
  intro a b ha hb
  exact (hreach ha hb).map (induceIncl G hAB)

lemma reachable_of_mem_graphPath {U : Finset V} (p : GraphPath G)
    (hsub : p.support ⊆ U) {x y : V}
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    (G.induce (U : Set V)).Reachable ⟨x, hsub hx⟩ ⟨y, hsub hy⟩ := by
  have hxw : x ∈ p.walk.support := GraphPath.mem_walk_support.1 hx
  have hyw : y ∈ p.walk.support := GraphPath.mem_walk_support.1 hy
  have hstartx :
      (G.induce (U : Set V)).Reachable
        ⟨p.start, hsub p.start_mem_support⟩ ⟨x, hsub hx⟩ := by
    let w := p.walk.takeUntil x hxw
    have hwU : ∀ a ∈ w.support, a ∈ (U : Set V) := fun a ha =>
      hsub (List.mem_toFinset.2
        (Walk.support_takeUntil_subset_support p.walk hxw ha))
    exact ⟨w.induce (U : Set V) hwU⟩
  have hstarty :
      (G.induce (U : Set V)).Reachable
        ⟨p.start, hsub p.start_mem_support⟩ ⟨y, hsub hy⟩ := by
    let w := p.walk.takeUntil y hyw
    have hwU : ∀ a ∈ w.support, a ∈ (U : Set V) := fun a ha =>
      hsub (List.mem_toFinset.2
        (Walk.support_takeUntil_subset_support p.walk hyw ha))
    exact ⟨w.induce (U : Set V) hwU⟩
  exact hstartx.symm.trans hstarty

lemma exists_spanning_path_of_pathCoverNumber_eq_one {U : Finset V}
    (h : pathCoverNumber G U = 1) :
    ∃ p : GraphPath G, p.support = U := by
  obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
  have hlen : pc.paths.length = 1 := by
    simpa [PathCover.card] using hpc.trans h
  match hps : pc.paths with
  | [] =>
    simp [hps] at hlen
  | [p] =>
    refine ⟨p, ?_⟩
    ext x
    constructor
    · intro hx
      exact pc.support_subset (by simp [hps]) hx
    · intro hx
      obtain ⟨q, hq, hxq⟩ := (pc.mem_iff x).1 hx
      simp [hps] at hq
      simpa [hq] using hxq
  | _ :: _ :: _ =>
    have : 2 ≤ pc.paths.length := by simp [hps]
    omega

lemma connected_of_spanning_path {U : Finset V}
    (p : GraphPath G) (hp : p.support = U) :
    (G.induce (U : Set V)).Connected := by
  have hne : U.Nonempty := by
    rw [← hp]; exact p.support_nonempty
  haveI : Nonempty (U : Set V) := hne.to_subtype
  refine (connected_iff _).2 ⟨?_, inferInstance⟩
  intro a b
  have ha : a.val ∈ p.support := by simpa [hp] using a.property
  have hb : b.val ∈ p.support := by simpa [hp] using b.property
  have hsub : p.support ⊆ U := by simp [hp]
  have hR := reachable_of_mem_graphPath (U := U) p hsub ha hb
  have ha' : (⟨a.val, hsub ha⟩ : (U : Set V)) = a := Subtype.ext rfl
  have hb' : (⟨b.val, hsub hb⟩ : (U : Set V)) = b := Subtype.ext rfl
  simpa [ha', hb'] using hR

lemma inOneComponent_of_connected {U W : Finset V}
    (hW : W ⊆ U) (hU : U.Nonempty)
    (hc : (G.induce (U : Set V)).Connected) :
    InOneComponent (G := G) U W := by
  refine ⟨hW, ?_⟩
  intro a b ha hb
  haveI : Nonempty (U : Set V) := hU.to_subtype
  have hpre : (G.induce (U : Set V)).Preconnected :=
    ((connected_iff (G.induce (U : Set V))).1 hc).1
  exact hpre ⟨a, hW ha⟩ ⟨b, hW hb⟩

lemma one_le_pathCoverNumber_of_mem_eligible {U : Finset V} {x : V}
    (hx : x ∈ eligibleSet G U) :
    1 ≤ pathCoverNumber G U :=
  one_le_pathCoverNumber_of_nonempty (G := G)
    ⟨x, eligibleSet_subset (G := G) U hx⟩

lemma sdiff_union_right_ineligible {A B S : Finset V}
    (hdisj : Disjoint A B) (hS : S ⊆ A) :
    (A ∪ B) \ (S ∪ ineligibleSet G B) =
      (A \ S) ∪ (B \ ineligibleSet G B) := by
  ext z
  constructor
  · intro hz
    have hzU : z ∈ A ∪ B := (mem_sdiff.1 hz).1
    have hzN : z ∉ S ∪ ineligibleSet G B := (mem_sdiff.1 hz).2
    rcases mem_union.1 hzU with hzA | hzB
    · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzA, fun hS' =>
        hzN (mem_union.2 (Or.inl hS'))⟩))
    · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hzB, fun hF =>
        hzN (mem_union.2 (Or.inr hF))⟩))
  · intro hz
    rcases mem_union.1 hz with hzA | hzB
    · have hzA' : z ∈ A := (mem_sdiff.1 hzA).1
      have hzS : z ∉ S := (mem_sdiff.1 hzA).2
      refine mem_sdiff.2 ⟨mem_union.2 (Or.inl hzA'), ?_⟩
      intro h
      rcases mem_union.1 h with hS | hF
      · exact hzS hS
      · exact Finset.disjoint_left.1 hdisj hzA'
          (ineligibleSet_subset (G := G) B hF)
    · have hzB' : z ∈ B := (mem_sdiff.1 hzB).1
      have hzF : z ∉ ineligibleSet G B := (mem_sdiff.1 hzB).2
      refine mem_sdiff.2 ⟨mem_union.2 (Or.inr hzB'), ?_⟩
      intro h
      rcases mem_union.1 h with hSz | hF
      · exact Finset.disjoint_left.1 hdisj (hS hSz) hzB'
      · exact hzF hF

lemma part_remainder_union_left {A B S : Finset V} {x : V}
    (hdisj : Disjoint A B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hS : S ⊆ ineligibleSet G A)
    (hx : x ∈ eligibleSet G A) :
    (ineligibleSet G (A ∪ B) ∪ dNonadjClass (G := G) (A ∪ B) x) \
        (S ∪ ineligibleSet G B) =
      (ineligibleSet G A ∪ dNonadjClass (G := G) A x) \ S := by
  have hF := ineligibleSet_disjoint_union (G := G) hdisj hnocross
  have hP := dNonadjClass_disjoint_union_left (G := G) hdisj hnocross hx
  have hPA : dNonadjClass (G := G) A x ⊆ A :=
    (dNonadjClass_subset_eligible (G := G) A x).trans
      (eligibleSet_subset (G := G) A)
  ext z
  constructor
  · intro hz
    have hzL := mem_sdiff.1 hz
    have hzN : z ∉ S ∪ ineligibleSet G B := hzL.2
    have hzS : z ∉ S := fun h => hzN (mem_union.2 (Or.inl h))
    have hzFB : z ∉ ineligibleSet G B := fun h => hzN (mem_union.2 (Or.inr h))
    rcases mem_union.1 hzL.1 with hzF | hzP
    · have hzF' : z ∈ ineligibleSet G A ∪ ineligibleSet G B := by rwa [hF] at hzF
      rcases mem_union.1 hzF' with hzA | hzB
      · exact mem_sdiff.2 ⟨mem_union.2 (Or.inl hzA), hzS⟩
      · exact (hzFB hzB).elim
    · have hzP' : z ∈ dNonadjClass (G := G) A x := by rwa [hP] at hzP
      exact mem_sdiff.2 ⟨mem_union.2 (Or.inr hzP'), hzS⟩
  · intro hz
    have hzL := mem_sdiff.1 hz
    have hzS : z ∉ S := hzL.2
    refine mem_sdiff.2 ⟨?_, ?_⟩
    · rcases mem_union.1 hzL.1 with hzA | hzP
      · rw [hF]; exact mem_union.2 (Or.inl (mem_union.2 (Or.inl hzA)))
      · rw [hP]; exact mem_union.2 (Or.inr hzP)
    · intro h
      rcases mem_union.1 h with hS | hF
      · exact hzS hS
      · rcases mem_union.1 hzL.1 with hzA | hzP
        · exact Finset.disjoint_left.1 hdisj
            (ineligibleSet_subset (G := G) A hzA)
            (ineligibleSet_subset (G := G) B hF)
        · exact Finset.disjoint_left.1 hdisj (hPA hzP)
            (ineligibleSet_subset (G := G) B hF)

lemma sdiff_union_dominant {A B S : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hS : S ⊆ A) :
    (A ∪ B) \ (B ∪ S) = A \ S := by
  have hdisj := disjoint_of_completeBetween hAB
  ext z
  constructor
  · intro hz
    have hzU : z ∈ A ∪ B := (mem_sdiff.1 hz).1
    have hzN : z ∉ B ∪ S := (mem_sdiff.1 hz).2
    have hzB : z ∉ B := fun h => hzN (mem_union.2 (Or.inl h))
    have hzS : z ∉ S := fun h => hzN (mem_union.2 (Or.inr h))
    have hzA : z ∈ A := (mem_union.1 hzU).resolve_right hzB
    exact mem_sdiff.2 ⟨hzA, hzS⟩
  · intro hz
    have hzA : z ∈ A := (mem_sdiff.1 hz).1
    have hzS : z ∉ S := (mem_sdiff.1 hz).2
    refine mem_sdiff.2 ⟨mem_union.2 (Or.inl hzA), ?_⟩
    intro h
    rcases mem_union.1 h with hzB | hS
    · exact Finset.disjoint_left.1 hdisj hzA hzB
    · exact hzS hS

lemma part_remainder_dominant {A B S : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hq : 2 ≤ pathCoverNumber G (A ∪ B))
    (hS : S ⊆ ineligibleSet G A)
    (hx : x ∈ eligibleSet G A) :
    (ineligibleSet G (A ∪ B) ∪ dNonadjClass (G := G) (A ∪ B) x) \ (B ∪ S) =
      (ineligibleSet G A ∪ dNonadjClass (G := G) A x) \ S := by
  have hF := ineligibleSet_complete_join_dominant hAne hBne hAB hdom
  have hP := dNonadjClass_complete_join_dominant hAne hBne hAB hdom hq hx
  have hdisj := disjoint_of_completeBetween hAB
  have hPA : dNonadjClass (G := G) A x ⊆ A :=
    (dNonadjClass_subset_eligible (G := G) A x).trans
      (eligibleSet_subset (G := G) A)
  ext z
  constructor
  · intro hz
    have hzL := mem_sdiff.1 hz
    have hzN : z ∉ B ∪ S := hzL.2
    have hzB : z ∉ B := fun h => hzN (mem_union.2 (Or.inl h))
    have hzS : z ∉ S := fun h => hzN (mem_union.2 (Or.inr h))
    rcases mem_union.1 hzL.1 with hzF | hzP
    · have hzF' : z ∈ B ∪ ineligibleSet G A := by rwa [hF] at hzF
      rcases mem_union.1 hzF' with hzB' | hzA
      · exact (hzB hzB').elim
      · exact mem_sdiff.2 ⟨mem_union.2 (Or.inl hzA), hzS⟩
    · have hzP' : z ∈ dNonadjClass (G := G) A x := by rwa [hP] at hzP
      exact mem_sdiff.2 ⟨mem_union.2 (Or.inr hzP'), hzS⟩
  · intro hz
    have hzL := mem_sdiff.1 hz
    have hzS : z ∉ S := hzL.2
    refine mem_sdiff.2 ⟨?_, ?_⟩
    · rcases mem_union.1 hzL.1 with hzA | hzP
      · rw [hF]; exact mem_union.2 (Or.inl (mem_union.2 (Or.inr hzA)))
      · rw [hP]; exact mem_union.2 (Or.inr hzP)
    · intro h
      rcases mem_union.1 h with hzB | hS
      · rcases mem_union.1 hzL.1 with hzA | hzP
        · exact Finset.disjoint_left.1 hdisj
            (ineligibleSet_subset (G := G) A hzA) hzB
        · exact Finset.disjoint_left.1 hdisj (hPA hzP) hzB
      · exact hzS hS

/-- If `p(U)=1`, the empty cut is a part-cut for the unique D-class `E(U)`. -/
lemma exists_partCut_of_eq_one {U : Finset V} {x : V}
    (hx : x ∈ eligibleSet G U) (hp : pathCoverNumber G U = 1) :
    ∃ S, S ⊆ ineligibleSet G U ∧
      componentCount G (U \ S) = S.card + pathCoverNumber G U ∧
      InOneComponent (G := G) (U \ S)
        ((ineligibleSet G U ∪ dNonadjClass (G := G) U x) \ S) := by
  refine ⟨∅, empty_subset _, ?_, ?_⟩
  · simp [hp]
    obtain ⟨p, hpU⟩ := exists_spanning_path_of_pathCoverNumber_eq_one (G := G) hp
    have hc := connected_of_spanning_path p hpU
    have hne : U.Nonempty := ⟨x, eligibleSet_subset (G := G) U hx⟩
    exact componentCount_eq_one_of_connected hne hc
  · obtain ⟨p, hpU⟩ := exists_spanning_path_of_pathCoverNumber_eq_one (G := G) hp
    have hW :
        (ineligibleSet G U ∪ dNonadjClass (G := G) U x) \ ∅ = U := by
      have hP := dNonadjClass_eq_eligible_of_le_one (G := G)
        (by omega : pathCoverNumber G U ≤ 1) hx
      rw [sdiff_empty, hP, union_comm, eligibleSet_union_ineligibleSet]
    simpa [hW] using
      inOneComponent_of_connected (W := U) (subset_refl _)
        ⟨x, eligibleSet_subset (G := G) U hx⟩
        (connected_of_spanning_path p hpU)

/-- Actual part-cut certificate: an original-vertex set `S ⊆ F(U)` attaining
the generic cut bound, with `(F(U) ∪ P_x) \ S` lying in one induced
component of `U \ S`. -/
lemma exists_partCut_of_cotreeOn {U : Finset V} (hU : CotreeOn G U) {x : V}
    (hx : x ∈ eligibleSet G U) :
    ∃ S, S ⊆ ineligibleSet G U ∧
      componentCount G (U \ S) = S.card + pathCoverNumber G U ∧
      InOneComponent (G := G) (U \ S)
        ((ineligibleSet G U ∪ dNonadjClass (G := G) U x) \ S) := by
  induction hU generalizing x with
  | empty =>
    exact (notMem_empty x (eligibleSet_subset (G := G) ∅ hx)).elim
  | singleton v =>
    have hx' : x = v :=
      mem_singleton.1 ((eligibleSet_subset (G := G) {v}) hx)
    refine ⟨∅, empty_subset _, ?_, ?_⟩
    · simp [ineligibleSet_singleton, pathCoverNumber_singleton,
        componentCount_singleton]
    · have hP : dNonadjClass (G := G) {v} x = {v} := by
        have : pathCoverNumber G {v} ≤ 1 := by
          simp [pathCoverNumber_singleton]
        simpa [hx', eligibleSet_singleton] using
          dNonadjClass_eq_eligible_of_le_one (G := G) this
            (by simpa [hx'] using hx)
      have hW :
          (ineligibleSet G {v} ∪ dNonadjClass (G := G) {v} x) \ ∅ = {v} := by
        simp [ineligibleSet_singleton, hP]
      refine ⟨by simp [hW], ?_⟩
      intro a b ha hb
      simp [hW] at ha hb
      subst ha; subst hb
      exact Reachable.rfl
  | disjointUnion hdisj hnocross hA hB ihA ihB =>
    rename_i A B
    have hpU := pathCoverNumber_disjoint_union (G := G) hdisj hnocross
    by_cases hp1 : pathCoverNumber G (A ∪ B) ≤ 1
    · have hp : pathCoverNumber G (A ∪ B) = 1 :=
        le_antisymm hp1 (one_le_pathCoverNumber_of_mem_eligible hx)
      exact exists_partCut_of_eq_one hx hp
    · have hEU := eligibleSet_disjoint_union (G := G) hdisj hnocross
      have hxU : x ∈ eligibleSet G A ∪ eligibleSet G B := by rwa [← hEU]
      rcases mem_union.1 hxU with hxA | hxB
      · obtain ⟨SA, hSA, hcutA, hcompA⟩ := ihA hxA
        let S := SA ∪ ineligibleSet G B
        have hS : S ⊆ ineligibleSet G (A ∪ B) := by
          intro z hz
          have hF := ineligibleSet_disjoint_union (G := G) hdisj hnocross
          rcases mem_union.1 hz with hzA | hzB
          · exact hF ▸ mem_union.2 (Or.inl (hSA hzA))
          · exact hF ▸ mem_union.2 (Or.inr hzB)
        have hrem := sdiff_union_right_ineligible (G := G) hdisj
          (hSA.trans (ineligibleSet_subset (G := G) A))
        have hdisjRem :
            Disjoint (A \ SA) (B \ ineligibleSet G B) :=
          disjoint_of_subset_left sdiff_subset
            (disjoint_of_subset_right sdiff_subset hdisj)
        have hnocrossRem :
            ∀ a ∈ A \ SA, ∀ b ∈ B \ ineligibleSet G B, ¬ G.Adj a b :=
          fun a ha b hb =>
            hnocross a (mem_sdiff.1 ha).1 b (mem_sdiff.1 hb).1
        have hadd :=
          componentCount_union_of_no_cross hdisjRem hnocrossRem
        have hFB := componentCount_sdiff_ineligibleSet_eq hB
        have hcard : S.card = SA.card + (ineligibleSet G B).card := by
          have hdisjS :
              Disjoint SA (ineligibleSet G B) :=
            disjoint_of_subset_left (hSA.trans (ineligibleSet_subset (G := G) A))
              (disjoint_of_subset_right (ineligibleSet_subset (G := G) B) hdisj)
          exact card_union_of_disjoint hdisjS
        refine ⟨S, hS, ?_, ?_⟩
        · rw [hrem, hadd, hcutA, hFB, hcard, hpU]
          omega
        · have hW :=
            part_remainder_union_left (G := G) hdisj hnocross hSA hxA
          have hmono := inOneComponent_mono
            (A := A \ SA) (B := (A ∪ B) \ S)
            (by intro z hz; rw [hrem]; exact mem_union.2 (Or.inl hz))
            hcompA
          exact hW ▸ hmono
      · obtain ⟨SB, hSB, hcutB, hcompB⟩ := ihB hxB
        let S := SB ∪ ineligibleSet G A
        have hdisj' : Disjoint B A := hdisj.symm
        have hnocross' : ∀ b ∈ B, ∀ a ∈ A, ¬ G.Adj b a :=
          fun b hb a ha hab => hnocross a ha b hb hab.symm
        have hS : S ⊆ ineligibleSet G (A ∪ B) := by
          intro z hz
          have hF := ineligibleSet_disjoint_union (G := G) hdisj hnocross
          rcases mem_union.1 hz with hzB | hzA
          · exact hF ▸ mem_union.2 (Or.inr (hSB hzB))
          · exact hF ▸ mem_union.2 (Or.inl hzA)
        have hrem : (A ∪ B) \ S =
            (B \ SB) ∪ (A \ ineligibleSet G A) := by
          have h := sdiff_union_right_ineligible (G := G) hdisj'
            (hSB.trans (ineligibleSet_subset (G := G) B))
          simpa [union_comm, S] using h
        have hdisjRem :
            Disjoint (B \ SB) (A \ ineligibleSet G A) :=
          disjoint_of_subset_left sdiff_subset
            (disjoint_of_subset_right sdiff_subset hdisj')
        have hnocrossRem :
            ∀ b ∈ B \ SB, ∀ a ∈ A \ ineligibleSet G A, ¬ G.Adj b a :=
          fun b hb a ha =>
            hnocross' b (mem_sdiff.1 hb).1 a (mem_sdiff.1 ha).1
        have hadd :=
          componentCount_union_of_no_cross hdisjRem hnocrossRem
        have hFA := componentCount_sdiff_ineligibleSet_eq hA
        have hcard : S.card = SB.card + (ineligibleSet G A).card := by
          have hdisjS :
              Disjoint SB (ineligibleSet G A) :=
            disjoint_of_subset_left (hSB.trans (ineligibleSet_subset (G := G) B))
              (disjoint_of_subset_right (ineligibleSet_subset (G := G) A) hdisj')
          exact card_union_of_disjoint hdisjS
        refine ⟨S, hS, ?_, ?_⟩
        · rw [hrem, hadd, hcutB, hFA, hcard, hpU]
          omega
        · have hW :
              (ineligibleSet G (A ∪ B) ∪ dNonadjClass (G := G) (A ∪ B) x) \ S =
                (ineligibleSet G B ∪ dNonadjClass (G := G) B x) \ SB := by
            have h := part_remainder_union_left (G := G) hdisj' hnocross'
              hSB hxB
            simpa [union_comm, S] using h
          have hmono := inOneComponent_mono
            (A := B \ SB) (B := (A ∪ B) \ S)
            (by intro z hz; rw [hrem]; exact mem_union.2 (Or.inl hz))
            hcompB
          exact hW ▸ hmono
  | completeJoin hAne hBne hAB hA hB ihA ihB =>
    rename_i A B
    by_cases hp1 : pathCoverNumber G (A ∪ B) ≤ 1
    · have hp : pathCoverNumber G (A ∪ B) = 1 :=
        le_antisymm hp1 (one_le_pathCoverNumber_of_mem_eligible hx)
      exact exists_partCut_of_eq_one hx hp
    · have hq : 2 ≤ pathCoverNumber G (A ∪ B) := by omega
      by_cases hAdom : B.card < pathCoverNumber G A
      · have hE := eligibleSet_complete_join_dominant hAne hBne hAB hAdom
        have hxA : x ∈ eligibleSet G A := by rwa [← hE]
        obtain ⟨SA, hSA, hcutA, hcompA⟩ := ihA hxA
        let S := B ∪ SA
        have hS : S ⊆ ineligibleSet G (A ∪ B) := by
          intro z hz
          have hF := ineligibleSet_complete_join_dominant hAne hBne hAB hAdom
          rcases mem_union.1 hz with hzB | hzA
          · exact hF ▸ mem_union.2 (Or.inl hzB)
          · exact hF ▸ mem_union.2 (Or.inr (hSA hzA))
        have hrem := sdiff_union_dominant hAB
          (hSA.trans (ineligibleSet_subset (G := G) A))
        have hcard : S.card = B.card + SA.card := by
          have hdisj := disjoint_of_completeBetween hAB
          have hdisjS : Disjoint B SA :=
            disjoint_of_subset_right
              (hSA.trans (ineligibleSet_subset (G := G) A)) hdisj.symm
          exact card_union_of_disjoint hdisjS
        have hpadd := pathCoverNumber_add_card_of_dominant hAne hBne hAB hAdom
        refine ⟨S, hS, ?_, ?_⟩
        · rw [hrem, hcutA, hcard, hpadd]
          omega
        · have hW :=
            part_remainder_dominant hAne hBne hAB hAdom hq hSA hxA
          have hmono := inOneComponent_mono
            (A := A \ SA) (B := (A ∪ B) \ S)
            (by intro z hz; rw [hrem]; exact hz)
            hcompA
          exact hW ▸ hmono
      · by_cases hBdom : A.card < pathCoverNumber G B
        · have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
            fun {b} hb {a} ha => (hAB ha hb).symm
          have hqB : 2 ≤ pathCoverNumber G (B ∪ A) := by
            simpa [union_comm] using hq
          have hE : eligibleSet G (A ∪ B) = eligibleSet G B := by
            simpa [union_comm] using
              eligibleSet_complete_join_dominant hBne hAne hBA hBdom
          have hxB : x ∈ eligibleSet G B := by rwa [← hE]
          obtain ⟨SB, hSB, hcutB, hcompB⟩ := ihB hxB
          let S := A ∪ SB
          have hS : S ⊆ ineligibleSet G (A ∪ B) := by
            intro z hz
            have hF : ineligibleSet G (A ∪ B) = A ∪ ineligibleSet G B := by
              simpa [union_comm] using
                ineligibleSet_complete_join_dominant hBne hAne hBA hBdom
            rcases mem_union.1 hz with hzA | hzB
            · exact hF ▸ mem_union.2 (Or.inl hzA)
            · exact hF ▸ mem_union.2 (Or.inr (hSB hzB))
          have hrem : (A ∪ B) \ S = B \ SB := by
            have h := sdiff_union_dominant hBA
              (hSB.trans (ineligibleSet_subset (G := G) B))
            simpa [union_comm, S] using h
          have hcard : S.card = A.card + SB.card := by
            have hdisj := disjoint_of_completeBetween hBA
            have hdisjS : Disjoint A SB :=
              disjoint_of_subset_right
                (hSB.trans (ineligibleSet_subset (G := G) B)) hdisj.symm
            exact card_union_of_disjoint hdisjS
          have hpadd : pathCoverNumber G B =
              pathCoverNumber G (A ∪ B) + A.card := by
            simpa [union_comm] using
              pathCoverNumber_add_card_of_dominant hBne hAne hBA hBdom
          refine ⟨S, hS, ?_, ?_⟩
          · rw [hrem, hcutB, hcard, hpadd]
            omega
          · have hW :
                (ineligibleSet G (A ∪ B) ∪
                    dNonadjClass (G := G) (A ∪ B) x) \ S =
                  (ineligibleSet G B ∪ dNonadjClass (G := G) B x) \ SB := by
              have h := part_remainder_dominant hBne hAne hBA hBdom hqB hSB hxB
              simpa [union_comm, S] using h
            have hmono := inOneComponent_mono
              (A := B \ SB) (B := (A ∪ B) \ S)
              (by intro z hz; rw [hrem]; exact hz)
              hcompB
            exact hW ▸ hmono
        · have hpA : pathCoverNumber G A ≤ B.card := Nat.le_of_not_gt hAdom
          have hpB : pathCoverNumber G B ≤ A.card := Nat.le_of_not_gt hBdom
          have hp := pathCoverNumber_complete_join hAne hBne hAB
          have hmax :
              max 1 (max (pathCoverNumber G A - B.card)
                (pathCoverNumber G B - A.card)) = 1 := by
            simp [Nat.sub_eq_zero_of_le hpA, Nat.sub_eq_zero_of_le hpB]
          have hp1' : pathCoverNumber G (A ∪ B) = 1 := hp.trans hmax
          exact (hp1 (by omega)).elim

lemma exists_partCut_of_isCograph {U : Finset V} (hU : IsCograph G U) {x : V}
    (hx : x ∈ eligibleSet G U) :
    ∃ S, S ⊆ ineligibleSet G U ∧
      componentCount G (U \ S) = S.card + pathCoverNumber G U ∧
      InOneComponent (G := G) (U \ S)
        ((ineligibleSet G U ∪ dNonadjClass (G := G) U x) \ S) :=
  exists_partCut_of_cotreeOn (cotreeOn_of_isCograph hU) hx

lemma exists_partCut_of_canonical {U : Finset V}
    (hU : Nikoghosyan.IsCograph G U) {x : V}
    (hx : x ∈ eligibleSet G U) :
    ∃ S, S ⊆ ineligibleSet G U ∧
      componentCount G (U \ S) = S.card + pathCoverNumber G U ∧
      InOneComponent (G := G) (U \ S)
        ((ineligibleSet G U ∪ dNonadjClass (G := G) U x) \ S) :=
  exists_partCut_of_isCograph (isCograph_iff.2 hU) hx

/-- The containment witness as an actual induced connected component. -/
lemma exists_component_of_inOneComponent {U W : Finset V}
    (hWne : W.Nonempty) (h : InOneComponent (G := G) U W) :
    ∃ C : (G.induce (U : Set V)).ConnectedComponent,
      ∀ y ∈ W, ∃ hy : y ∈ U,
        (G.induce (U : Set V)).connectedComponentMk ⟨y, hy⟩ = C := by
  obtain ⟨hW, hreach⟩ := h
  obtain ⟨x, hx⟩ := hWne
  refine ⟨(G.induce (U : Set V)).connectedComponentMk ⟨x, hW hx⟩, ?_⟩
  intro y hy
  exact ⟨hW hy, ConnectedComponent.sound (hreach hy hx)⟩

lemma exists_partCut_component_of_canonical {U : Finset V}
    (hU : Nikoghosyan.IsCograph G U) {x : V}
    (hx : x ∈ eligibleSet G U) :
    ∃ S, S ⊆ ineligibleSet G U ∧
      componentCount G (U \ S) = S.card + pathCoverNumber G U ∧
      ∃ C : (G.induce ((U \ S : Finset V) : Set V)).ConnectedComponent,
        ∀ y ∈ (ineligibleSet G U ∪ dNonadjClass (G := G) U x) \ S,
          ∃ hy : y ∈ U \ S,
            (G.induce ((U \ S : Finset V) : Set V)).connectedComponentMk
              ⟨y, hy⟩ = C := by
  obtain ⟨S, hS, hcut, hcomp⟩ := exists_partCut_of_canonical hU hx
  have hWne :
      ((ineligibleSet G U ∪ dNonadjClass (G := G) U x) \ S).Nonempty := by
    refine ⟨x, mem_sdiff.2 ⟨mem_union.2 (Or.inr (mem_dNonadjClass_self hx)), ?_⟩⟩
    intro hxS
    have hxF := hS hxS
    exact (disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) U) hx) hxF
  obtain ⟨C, hC⟩ := exists_component_of_inOneComponent hWne hcomp
  exact ⟨S, hS, hcut, C, hC⟩

end Cograph
end Nikoghosyan
