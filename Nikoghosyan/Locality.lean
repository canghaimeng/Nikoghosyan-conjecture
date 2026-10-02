/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Cograph.SaturatedJoin
import Nikoghosyan.Cograph.PathCoverUnion
import Nikoghosyan.Cograph.Decomposition
import Nikoghosyan.Cograph.Profiles
import Nikoghosyan.Cograph.AlignedJoinProfile
import Nikoghosyan.Cograph.Compatibility
import Nikoghosyan.Prerequisites.TerminalRefinement

/-!
# Manuscript `loc:thm:locality`

Single-cycle witnesses for a strict path-cover saving and for endpoint
release, in a cograph union of a nonempty old block `L` with one or more
specified original Hamiltonian blocks. Edges among the new blocks are
allowed. There is no ambient `OneTough`, host cofreeness, old Hamilton
cycle, no-cross-among-new-cycles hypothesis, or inductive callback.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

open GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Family supports -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def selectedSupport (c : ι → GraphCycle G) (I : Finset ι) :
    Finset V :=
  I.biUnion fun i => (c i).support

noncomputable def unionJ (L : Finset V) (c : ι → GraphCycle G) (I : Finset ι) :
    Finset V :=
  L ∪ selectedSupport c I

lemma mem_selectedSupport {c : ι → GraphCycle G} {I : Finset ι} {x : V} :
    x ∈ selectedSupport c I ↔ ∃ i ∈ I, x ∈ (c i).support := by
  simp [selectedSupport]

lemma selectedSupport_mono {c : ι → GraphCycle G} {I J : Finset ι}
    (h : I ⊆ J) : selectedSupport c I ⊆ selectedSupport c J := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hx
  exact mem_biUnion.2 ⟨i, h hi, hxi⟩

lemma selectedSupport_subset_unionJ (L : Finset V) (c : ι → GraphCycle G)
    (I : Finset ι) : selectedSupport c I ⊆ unionJ L c I :=
  subset_union_right

lemma unionJ_mono_index (L : Finset V) (c : ι → GraphCycle G) {I J : Finset ι}
    (h : I ⊆ J) : unionJ L c I ⊆ unionJ L c J :=
  union_subset_union Subset.rfl (selectedSupport_mono h)

lemma cycle_support_subset_selected {c : ι → GraphCycle G} {I : Finset ι}
    {i : ι} (hi : i ∈ I) : (c i).support ⊆ selectedSupport c I :=
  subset_biUnion_of_mem (fun i => (c i).support) hi

lemma disjoint_selected_of_pairwise {c : ι → GraphCycle G} {L : Finset V}
    {I : Finset ι}
    (hdisjL : ∀ i ∈ I, Disjoint L (c i).support)
    {i : ι} (hi : i ∈ I) :
    Disjoint L (c i).support :=
  hdisjL i hi

/-! ### Facing a prescribed path end -/

def GraphPath.faceToFinish (p : GraphPath G) {u : V}
    (_h : u = p.start ∨ u = p.finish) : GraphPath G :=
  if hu : u = p.finish then p else p.reverse

lemma GraphPath.faceToFinish_support (p : GraphPath G) {u : V}
    (h : u = p.start ∨ u = p.finish) :
    (p.faceToFinish h).support = p.support := by
  unfold faceToFinish
  split_ifs <;> simp [GraphPath.support_reverse]

lemma GraphPath.faceToFinish_finish (p : GraphPath G) {u : V}
    (h : u = p.start ∨ u = p.finish) :
    (p.faceToFinish h).finish = u := by
  unfold faceToFinish
  split_ifs with hu
  · exact hu.symm
  · have : u = p.start := h.resolve_right hu
    simp [GraphPath.reverse, this]

def GraphPath.faceToStart (p : GraphPath G) {u : V}
    (_h : u = p.start ∨ u = p.finish) : GraphPath G :=
  if hu : u = p.start then p else p.reverse

lemma GraphPath.faceToStart_support (p : GraphPath G) {u : V}
    (h : u = p.start ∨ u = p.finish) :
    (p.faceToStart h).support = p.support := by
  unfold faceToStart
  split_ifs <;> simp [GraphPath.support_reverse]

lemma GraphPath.faceToStart_start (p : GraphPath G) {u : V}
    (h : u = p.start ∨ u = p.finish) :
    (p.faceToStart h).start = u := by
  unfold faceToStart
  split_ifs with hu
  · exact hu.symm
  · have : u = p.finish := h.resolve_left hu
    simp [GraphPath.reverse, this]

/-! ### Replace two cover paths by one spliced path -/

open PathCover
open GraphPath

noncomputable def PathCover.replaceTwo {U E : Finset V}
    (hdisj : Disjoint U E) (pc : PathCover G U)
    {p q r : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hr : r.support = p.support ∪ q.support ∪ E) :
    PathCover G (U ∪ E) where
  paths :=
    (pc.paths.filter fun s => decide (s ≠ p)).filter (fun s => decide (s ≠ q))
      ++ [r]
  disjoint := by
    refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · exact List.Pairwise.filter _ (List.Pairwise.filter _ pc.disjoint)
    · intro s hs t ht
      have ht' : t = r := List.mem_singleton.1 ht
      subst ht'
      have hs1 := List.mem_filter.1 hs
      have hs0 := List.mem_filter.1 hs1.1
      have hspc : s ∈ pc.paths := hs0.1
      have hsp : s ≠ p := of_decide_eq_true hs0.2
      have hsq : s ≠ q := of_decide_eq_true hs1.2
      have hdisjp : Disjoint s.support p.support :=
        pairwise_disjoint_of_mem pc.disjoint hspc hp hsp
      have hdisjq : Disjoint s.support q.support :=
        pairwise_disjoint_of_mem pc.disjoint hspc hq hsq
      have hsU : s.support ⊆ U := pc.support_subset hspc
      have hsE : Disjoint s.support E := hdisj.mono_left hsU
      refine disjoint_left.2 ?_
      intro x hxs hxr
      have hxrs : x ∈ p.support ∪ q.support ∪ E := by rwa [hr] at hxr
      have hx1 : x ∈ p.support ∨ x ∈ q.support ∨ x ∈ E := by
        simpa [mem_union] using hxrs
      rcases hx1 with hxp | hxq | hxE
      · exact disjoint_left.1 hdisjp hxs hxp
      · exact disjoint_left.1 hdisjq hxs hxq
      · exact disjoint_left.1 hsE hxs hxE
  mem_iff := by
    intro x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxU | hxE
      · obtain ⟨s, hs, hxs⟩ := (pc.mem_iff x).1 hxU
        by_cases hsp : s = p
        · subst hsp
          refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
          rw [hr]
          exact mem_union.2 (Or.inl (mem_union.2 (Or.inl hxs)))
        · by_cases hsq : s = q
          · subst hsq
            refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
            rw [hr]
            exact mem_union.2 (Or.inl (mem_union.2 (Or.inr hxs)))
          · refine ⟨s, List.mem_append.mpr (Or.inl ?_), hxs⟩
            exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hs, decide_eq_true hsp⟩,
              decide_eq_true hsq⟩
      · refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
        rw [hr]
        exact mem_union.2 (Or.inr hxE)
    · intro ⟨s, hs, hxs⟩
      rcases List.mem_append.1 hs with hsL | hsR
      · have hs1 := List.mem_filter.1 hsL
        have hs0 := List.mem_filter.1 hs1.1
        exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨s, hs0.1, hxs⟩))
      · have : s = r := List.mem_singleton.1 hsR
        subst this
        have hx' : x ∈ p.support ∪ q.support ∪ E := by rwa [hr] at hxs
        have hx1 : x ∈ p.support ∨ x ∈ q.support ∨ x ∈ E := by
          simpa [mem_union] using hx'
        rcases hx1 with hxp | hxq | hxE
        · exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨p, hp, hxp⟩))
        · exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨q, hq, hxq⟩))
        · exact mem_union.2 (Or.inr hxE)

lemma two_le_card_of_mem_ne {U : Finset V} (pc : PathCover G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q) :
    2 ≤ pc.card := by
  have hq' : q ∈ pc.paths.filter fun x => decide (x ≠ p) :=
    List.mem_filter.2 ⟨hq, decide_eq_true hne.symm⟩
  have hpos : 0 < (pc.paths.filter fun x => decide (x ≠ p)).length :=
    List.length_pos_of_mem hq'
  have hlen := length_filter_ne_of_mem_nodup (a := p) (l := pc.paths) hp pc.nodup_paths
  simp [PathCover.card]
  omega

lemma PathCover.replaceTwo_card {U E : Finset V}
    (hdisj : Disjoint U E) (pc : PathCover G U)
    {p q r : GraphPath G}
    (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hr : r.support = p.support ∪ q.support ∪ E) :
    (pc.replaceTwo hdisj hp hq hne hr).card = pc.card - 1 := by
  have hlen := length_filter_ne_two (a := p) (b := q) hp hq hne pc.nodup_paths
  have h2 : 2 ≤ pc.paths.length := by
    simpa [PathCover.card] using two_le_card_of_mem_ne pc hp hq hne
  simp only [replaceTwo, PathCover.card, List.length_append, List.length_cons,
    List.length_nil]
  rw [hlen]
  omega

/-! ### Distinct-path endpoints are nonadjacent -/

lemma not_adj_distinct_cover_endpoints {U : Finset V}
    (pc : PathCover G U) (hmin : pc.card = pathCoverNumber G U)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    {x y : V}
    (hx : x = p.start ∨ x = p.finish) (hy : y = q.start ∨ y = q.finish) :
    ¬ G.Adj x y := by
  intro hadj
  let p' := p.faceToFinish hx
  let q' := q.faceToStart hy
  have hp's : p'.support = p.support := p.faceToFinish_support hx
  have hq's : q'.support = q.support := q.faceToStart_support hy
  have hdisjpq : Disjoint p.support q.support :=
    pairwise_disjoint_of_mem pc.disjoint hp hq hne
  have hdisj' : Disjoint p'.support q'.support := by
    simpa [hp's, hq's] using hdisjpq
  have hadj' : G.Adj p'.finish q'.start := by
    rw [p.faceToFinish_finish hx, q.faceToStart_start hy]
    exact hadj
  let r := p'.splice q' hadj' hdisj'
  have hr : r.support = p.support ∪ q.support ∪ (∅ : Finset V) := by
    simp [r, GraphPath.support_splice, hp's, hq's]
  have hdisjE : Disjoint U (∅ : Finset V) := disjoint_empty_right _
  let pc' := pc.replaceTwo hdisjE hp hq hne hr
  have hcard : pc'.card = pc.card - 1 :=
    pc.replaceTwo_card hdisjE hp hq hne hr
  have hle : pathCoverNumber G U ≤ pc'.card := by
    have hUW : U ∪ (∅ : Finset V) = U := union_empty U
    exact (pathCoverNumber_le (G := G) (pc'.cast hUW)).trans_eq
      (by simp [PathCover.cast_card, hcard])
  have hpos := two_le_card_of_mem_ne pc hp hq hne
  omega

/-! ### Locality hypotheses -/

structure LocalityHyp (c : ι → GraphCycle G) (L : Finset V) (I : Finset ι) :
    Prop where
  I_nonempty : I.Nonempty
  L_nonempty : L.Nonempty
  disjL : ∀ i ∈ I, Disjoint L (c i).support
  pairwise : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (c i).support (c j).support
  cog : IsCograph G (unionJ L c I)
  sees : ∀ i ∈ I, ∀ d ∈ (c i).support, ∃ u ∈ eligibleSet G L, G.Adj d u

noncomputable def restrictIndex (c : ι → GraphCycle G) (I : Finset ι)
    (A : Finset V) : Finset ι :=
  I.filter fun i => (c i).support ⊆ A

lemma mem_restrictIndex {c : ι → GraphCycle G} {I : Finset ι} {A : Finset V}
    {i : ι} : i ∈ restrictIndex c I A ↔ i ∈ I ∧ (c i).support ⊆ A := by
  simp [restrictIndex]

lemma unionJ_single_subset (L : Finset V) (c : ι → GraphCycle G) {I : Finset ι}
    {i : ι} (hi : i ∈ I) : L ∪ (c i).support ⊆ unionJ L c I :=
  union_subset_union Subset.rfl (cycle_support_subset_selected hi)

lemma selectedSupport_restrict_subset (c : ι → GraphCycle G) (I : Finset ι)
    (A : Finset V) : selectedSupport c (restrictIndex c I A) ⊆ A := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hx
  have := (mem_restrictIndex (c := c) (I := I) (A := A)).1 hi
  exact this.2 hxi

/-! ### Cycle support cannot cross a no-cross cut -/

lemma GraphCycle.support_subset_of_no_cross {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (c : GraphCycle G) (hsupp : c.support ⊆ A ∪ B) :
    c.support ⊆ A ∨ c.support ⊆ B := by
  have hstart : c.start ∈ A ∪ B := hsupp c.start_mem_support
  have hwalk : ∀ y ∈ c.walk.support, y ∈ (A : Set V) ∨ y ∈ (B : Set V) := by
    intro y hy
    have : y ∈ c.support := by simpa [GraphCycle.support] using hy
    simpa [mem_union] using hsupp this
  rcases mem_union.mp hstart with hA | hB
  · refine Or.inl ?_
    intro x hx
    have hxW : x ∈ c.walk.support := by simpa [GraphCycle.support] using hx
    exact Cograph.walk_support_subset_of_no_cross
      (A := (A : Set V)) (B := (B : Set V))
      (fun a ha b hb => hnocross a ha b hb) c.walk hA hwalk x hxW
  · refine Or.inr ?_
    intro x hx
    have hxW : x ∈ c.walk.support := by simpa [GraphCycle.support] using hx
    exact Cograph.walk_support_subset_of_no_cross'
      (A := (A : Set V)) (B := (B : Set V))
      (fun a ha b hb => hnocross a ha b hb) c.walk hB hwalk x hxW

/-! ### Three-path splice -/

lemma exists_splice_three (left mid right : GraphPath G)
    (h1 : G.Adj left.finish mid.start) (h2 : G.Adj mid.finish right.start)
    (hd1 : Disjoint left.support mid.support)
    (hd2 : Disjoint (left.support ∪ mid.support) right.support) :
    ∃ r : GraphPath G,
      r.support = left.support ∪ mid.support ∪ right.support ∧
        r.start = left.start ∧ r.finish = right.finish := by
  let m := left.splice mid h1 hd1
  have hd2' : Disjoint m.support right.support := by
    simpa [m, GraphPath.support_splice] using hd2
  have h2' : G.Adj m.finish right.start := h2
  refine ⟨m.splice right h2' hd2', ?_, rfl, rfl⟩
  simp [m, GraphPath.support_splice, union_assoc]

/-! ### Single-extension upper bound `p(L ∪ D_i) ≤ p(L)` -/

lemma pathCoverNumber_union_cycle_le
    (c : ι → GraphCycle G) {L : Finset V} {I : Finset ι}
    (H : LocalityHyp c L I) {i : ι} (hi : i ∈ I) :
    pathCoverNumber G (L ∪ (c i).support) ≤ pathCoverNumber G L := by
  obtain ⟨d, hd⟩ := (c i).support_nonempty
  obtain ⟨u, huE, hadj⟩ := H.sees i hi d hd
  have hEl : Eligible G L u := (mem_eligibleSet_iff (G := G)).1 huE |>.2
  obtain ⟨pc, hmin, p, hp, huend⟩ := hEl
  let p' := p.faceToFinish huend
  have hp's : p'.support = p.support := p.faceToFinish_support huend
  have hf' : p'.finish = u := p.faceToFinish_finish huend
  let pc' := pc.replacePath_sat hp p' hp's
  have hmin' : pc'.card = pathCoverNumber G L :=
    (replacePath_sat_card pc hp p' hp's).trans hmin
  have hp'mem : p' ∈ pc'.paths := replacePath_sat_self_mem pc hp p' hp's
  obtain ⟨r0, hr0, hst, _hadjD⟩ := Cograph.exists_spanning_path_from (c i) hd
  have hrst : r0.start = d := hst
  have hdisjLD : Disjoint L (c i).support := H.disjL i hi
  have hdisjpr : Disjoint p'.support r0.support := by
    have : Disjoint p.support (c i).support :=
      hdisjLD.mono_left (pc.support_subset hp)
    simpa [hp's, hr0] using this
  have hadj' : G.Adj p'.finish r0.start := by
    rw [hf', hrst]
    exact hadj.symm
  let s := p'.splice r0 hadj' hdisjpr
  have hs : s.support = p.support ∪ (c i).support := by
    simp [s, GraphPath.support_splice, hp's, hr0]
  have hdisjRem : Disjoint (L \ p.support) (p.support ∪ (c i).support) := by
    refine disjoint_left.2 ?_
    intro x hxL hxR
    have hxnp : x ∉ p.support := (mem_sdiff.1 hxL).2
    rcases mem_union.1 hxR with hxp | hxD
    · exact hxnp hxp
    · exact Finset.disjoint_left.1 hdisjLD (mem_sdiff.1 hxL).1 hxD
  have hcastRem : L \ p'.support = L \ p.support := by rw [hp's]
  let pcRem' := (pc'.erasePath hp'mem).cast hcastRem
  let pcNew' : PathCover G (p.support ∪ (c i).support) :=
    (PathCover.ofPath s).cast hs
  let pcU := Cograph.PathCover.unionDisjoint hdisjRem pcRem' pcNew'
  have hcard : pcU.card = pc.card := by
    have h3 : pcU.card = pcRem'.card + pcNew'.card :=
      Cograph.PathCover.unionDisjoint_card hdisjRem pcRem' pcNew'
    have h4 : pcRem'.card = pc'.card - 1 := by
      rw [PathCover.cast_card]
      exact PathCover.erasePath_card pc' hp'mem
    have h5 : pcNew'.card = 1 := by
      rw [PathCover.cast_card]
      exact PathCover.ofPath_card s
    have h6 : pc'.card = pc.card := replacePath_sat_card pc hp p' hp's
    have hpos : 1 ≤ pc'.card := by
      simpa [PathCover.card] using
        (Nat.succ_le_of_lt (List.length_pos_of_mem hp'mem))
    rw [h3, h4, h5, h6]
    omega
  have hUeq : (L \ p.support) ∪ (p.support ∪ (c i).support) =
      L ∪ (c i).support := by
    ext x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxL | hxR
      · exact mem_union.2 (Or.inl (mem_sdiff.1 hxL).1)
      · rcases mem_union.1 hxR with hxp | hxD
        · exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨p, hp, hxp⟩))
        · exact mem_union.2 (Or.inr hxD)
    · intro hx
      rcases mem_union.1 hx with hL | hD
      · by_cases hxp : x ∈ p.support
        · exact mem_union.2 (Or.inr (mem_union.2 (Or.inl hxp)))
        · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hL, hxp⟩))
      · exact mem_union.2 (Or.inr (mem_union.2 (Or.inr hD)))
  let pcJ := pcU.cast hUeq
  have hle := pathCoverNumber_le (G := G) pcJ
  have hcardJ : pcJ.card = pc.card := by
    rw [PathCover.cast_card]
    exact hcard
  omega

/-! ### Alignment of a `q ≥ 2` old cover in a complete join of `J` -/

lemma endpoints_aligned_of_join {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hLsub : L ⊆ X ∪ Y)
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    (hq : 2 ≤ pc.card)
    {p0 : GraphPath G} (hp0 : p0 ∈ pc.paths)
    (hXend : p0.start ∈ X ∨ p0.finish ∈ X) :
    ∀ p ∈ pc.paths, p.start ∈ X ∧ p.finish ∈ X := by
  have hend_in (p : GraphPath G) (hp : p ∈ pc.paths) {z : V}
      (hz : z = p.start ∨ z = p.finish) : z ∈ X ∪ Y :=
    hLsub (pc.support_subset hp (by
      rcases hz with rfl | rfl
      · exact p.start_mem_support
      · exact p.finish_mem_support))
  obtain ⟨z0, hz0, hz0X⟩ : ∃ z, (z = p0.start ∨ z = p0.finish) ∧ z ∈ X := by
    rcases hXend with h | h
    · exact ⟨p0.start, Or.inl rfl, h⟩
    · exact ⟨p0.finish, Or.inr rfl, h⟩
  have hother : ∀ q ∈ pc.paths, q ≠ p0 → q.start ∈ X ∧ q.finish ∈ X := by
    intro q hq hne
    have hsX : q.start ∈ X := by
      have hAB := hend_in q hq (Or.inl rfl)
      rcases mem_union.1 hAB with hX | hY
      · exact hX
      · exact (not_adj_distinct_cover_endpoints pc hmin hp0 hq (Ne.symm hne)
          hz0 (Or.inl rfl) (hXY hz0X hY)).elim
    have hfX : q.finish ∈ X := by
      have hAB := hend_in q hq (Or.inr rfl)
      rcases mem_union.1 hAB with hX | hY
      · exact hX
      · exact (not_adj_distinct_cover_endpoints pc hmin hp0 hq (Ne.symm hne)
          hz0 (Or.inr rfl) (hXY hz0X hY)).elim
    exact ⟨hsX, hfX⟩
  have hex : ∃ q, q ∈ pc.paths ∧ q ≠ p0 := by
    obtain ⟨a, b, ha, hb, hne⟩ := PathCover.exists_two_distinct pc hq
    by_cases h : a = p0
    · refine ⟨b, hb, ?_⟩
      intro hba
      exact hne (h.trans hba.symm)
    · exact ⟨a, ha, h⟩
  obtain ⟨q, hq, hne⟩ := hex
  have hqX := hother q hq hne
  have hp0' : p0.start ∈ X ∧ p0.finish ∈ X := by
    have hsX : p0.start ∈ X := by
      have hAB := hend_in p0 hp0 (Or.inl rfl)
      rcases mem_union.1 hAB with hX | hY
      · exact hX
      · exact (not_adj_distinct_cover_endpoints pc hmin hp0 hq hne.symm
          (Or.inl rfl) (Or.inl rfl) (hXY hqX.1 hY).symm).elim
    have hfX : p0.finish ∈ X := by
      have hAB := hend_in p0 hp0 (Or.inr rfl)
      rcases mem_union.1 hAB with hX | hY
      · exact hX
      · exact (not_adj_distinct_cover_endpoints pc hmin hp0 hq hne.symm
          (Or.inr rfl) (Or.inl rfl) (hXY hqX.1 hY).symm).elim
    exact ⟨hsX, hfX⟩
  intro p hp
  by_cases hpe : p = p0
  · simpa [hpe] using hp0'
  · exact hother p hp hpe

/-! ### Restrict the family to one side of a cut of `J` -/

lemma unionJ_restrict_eq {c : ι → GraphCycle G} {L A B : Finset V} {I : Finset ι}
    (H : LocalityHyp c L I)
    (hdisj : Disjoint A B) (hunion : A ∪ B = unionJ L c I)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    unionJ (L ∩ A) c (restrictIndex c I A) = A := by
  have hLsub : L ⊆ A ∪ B := by
    rw [hunion]; exact subset_union_left
  have hsel : selectedSupport c I ⊆ A ∪ B := by
    rw [hunion]; exact subset_union_right
  have hcycle : ∀ i ∈ I, (c i).support ⊆ A ∨ (c i).support ⊆ B := by
    intro i hi
    exact GraphCycle.support_subset_of_no_cross hnocross (c i)
      ((cycle_support_subset_selected hi).trans hsel)
  ext x
  constructor
  · intro hx
    rcases mem_union.1 hx with hxL | hxS
    · exact (mem_inter.1 hxL).2
    · exact selectedSupport_restrict_subset c I A hxS
  · intro hxA
    have hxJ : x ∈ unionJ L c I := by
      rw [← hunion]
      exact mem_union.2 (Or.inl hxA)
    rcases mem_union.1 hxJ with hxL | hxS
    · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hxL, hxA⟩))
    · obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hxS
      have hsub := hcycle i hi
      have hiA : (c i).support ⊆ A := by
        rcases hsub with hA | hB
        · exact hA
        · exact (Finset.disjoint_left.1 hdisj hxA (hB hxi)).elim
      exact mem_union.2 (Or.inr (mem_biUnion.2
        ⟨i, mem_restrictIndex.2 ⟨hi, hiA⟩, hxi⟩))

lemma LocalityHyp.restrict_side (c : ι → GraphCycle G) {L A B : Finset V}
    {I : Finset ι} (H : LocalityHyp c L I)
    (hdisj : Disjoint A B) (hunion : A ∪ B = unionJ L c I)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hIA : (restrictIndex c I A).Nonempty)
    (hLA : (L ∩ A).Nonempty) :
    LocalityHyp c (L ∩ A) (restrictIndex c I A) where
  I_nonempty := hIA
  L_nonempty := hLA
  disjL := by
    intro i hi
    have hiI := (mem_restrictIndex (c := c) (I := I) (A := A)).1 hi |>.1
    exact (H.disjL i hiI).mono_left inter_subset_left
  pairwise := by
    intro i hi j hj hne
    have hiI := (mem_restrictIndex (c := c) (I := I) (A := A)).1 hi |>.1
    have hjI := (mem_restrictIndex (c := c) (I := I) (A := A)).1 hj |>.1
    exact H.pairwise i hiI j hjI hne
  cog := by
    have hJ : unionJ (L ∩ A) c (restrictIndex c I A) = A :=
      unionJ_restrict_eq H hdisj hunion hnocross
    have hAsub : A ⊆ unionJ L c I := by
      rw [← hunion]
      exact subset_union_left
    have hAcog : IsCograph G A := IsCograph.subset (G := G) H.cog hAsub
    simpa [hJ] using hAcog
  sees := by
    intro i hi d hd
    have hiI := (mem_restrictIndex (c := c) (I := I) (A := A)).1 hi |>.1
    have hsubA := (mem_restrictIndex (c := c) (I := I) (A := A)).1 hi |>.2
    obtain ⟨u, huE, hadj⟩ := H.sees i hiI d hd
    have huL : u ∈ L := eligibleSet_subset (G := G) L huE
    have huA : u ∈ A := by
      have huAB : u ∈ A ∪ B := by
        have : u ∈ unionJ L c I := mem_union.2 (Or.inl huL)
        rw [← hunion] at this
        exact this
      rcases mem_union.1 huAB with hA | hB
      · exact hA
      · exact (hnocross d (hsubA hd) u hB hadj).elim
    have hLsplit : L = (L ∩ A) ∪ (L ∩ B) := by
      ext z
      constructor
      · intro hz
        have hzAB : z ∈ A ∪ B := by
          have : z ∈ unionJ L c I := mem_union.2 (Or.inl hz)
          rw [← hunion] at this
          exact this
        rcases mem_union.1 hzAB with hA | hB
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hA⟩))
        · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hz, hB⟩))
      · intro hz
        rcases mem_union.1 hz with h | h
        · exact (mem_inter.1 h).1
        · exact (mem_inter.1 h).1
    have hnocrossL : ∀ a ∈ L ∩ A, ∀ b ∈ L ∩ B, ¬ G.Adj a b :=
      fun a ha b hb => hnocross a (mem_inter.1 ha).2 b (mem_inter.1 hb).2
    have hdisjL : Disjoint (L ∩ A) (L ∩ B) :=
      disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right hdisj)
    have hE := Cograph.eligibleSet_disjoint_union (G := G) hdisjL hnocrossL
    have huE' : u ∈ eligibleSet G ((L ∩ A) ∪ (L ∩ B)) := by
      rwa [← hLsplit]
    have huEA : u ∈ eligibleSet G (L ∩ A) := by
      have hunionE : u ∈ eligibleSet G (L ∩ A) ∪ eligibleSet G (L ∩ B) := by
        rwa [← hE]
      rcases mem_union.1 hunionE with h | h
      · exact h
      · have huB : u ∈ L ∩ B := eligibleSet_subset (G := G) (L ∩ B) h
        exact (Finset.disjoint_left.1 hdisjL (mem_inter.2 ⟨huL, huA⟩) huB).elim
    exact ⟨u, huEA, hadj⟩

/-! ### First dart and YY splits of a cover path -/

lemma GraphPath.adj_start_tail (p : GraphPath G) (h : ¬ p.walk.Nil) :
    G.Adj p.start (p.tail h).start := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q => simpa [tail, tailOfWalk] using hadj

lemma GraphPath.tail_finish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.tail h).finish = p.finish := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q => rfl

lemma pathCoverNumber_lt_of_YY_opening {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hpX : p.start ∈ X ∧ p.finish ∈ X)
    (hqX : q.start ∈ X ∧ q.finish ∈ X)
    (rD : GraphPath G) (hYs : rD.start ∈ Y) (hYf : rD.finish ∈ Y)
    {D : Finset V} (hrD : rD.support = D) (hdisj : Disjoint L D) :
    pathCoverNumber G (L ∪ D) < pathCoverNumber G L := by
  let p' := p.faceToFinish (Or.inl rfl)
  let q' := q.faceToStart (Or.inl rfl)
  have hp's : p'.support = p.support := p.faceToFinish_support (Or.inl rfl)
  have hq's : q'.support = q.support := q.faceToStart_support (Or.inl rfl)
  have hdisjmidL : Disjoint p'.support rD.support := by
    have : Disjoint p.support D := hdisj.mono_left (pc.support_subset hp)
    rw [hp's, hrD]
    exact this
  have hdisjmidR : Disjoint (p'.support ∪ rD.support) q'.support := by
    have hdisjpq : Disjoint p.support q.support :=
      pairwise_disjoint_of_mem pc.disjoint hp hq hne
    have hdisjqD : Disjoint D q.support :=
      (hdisj.mono_left (pc.support_subset hq)).symm
    rw [hp's, hq's, hrD]
    exact disjoint_union_left.2 ⟨hdisjpq, hdisjqD⟩
  have hadj1 : G.Adj p'.finish rD.start := by
    have : p'.finish ∈ X := by
      rw [p.faceToFinish_finish (Or.inl rfl)]; exact hpX.1
    exact hXY this hYs
  have hadj2 : G.Adj rD.finish q'.start := by
    have : q'.start ∈ X := by
      rw [q.faceToStart_start (Or.inl rfl)]; exact hqX.1
    exact (hXY this hYf).symm
  obtain ⟨r, hr, _, _⟩ :=
    exists_splice_three p' rD q' hadj1 hadj2 hdisjmidL hdisjmidR
  have hr' : r.support = p.support ∪ q.support ∪ D := by
    rw [hr, hp's, hq's, hrD]
    ac_rfl
  let pcN := pc.replaceTwo hdisj hp hq hne hr'
  have hNcard := pc.replaceTwo_card hdisj hp hq hne hr'
  have hle := pathCoverNumber_le (G := G) pcN
  have h2 := two_le_card_of_mem_ne pc hp hq hne
  have hle' : pathCoverNumber G (L ∪ D) ≤ pc.card - 1 := hle.trans_eq hNcard
  have hpos : 1 ≤ pc.card := le_trans (by decide : (1 : ℕ) ≤ 2) h2
  have hlt : pc.card - 1 < pathCoverNumber G L := by
    rw [← hmin]
    exact Nat.sub_lt (Nat.succ_le_iff.mp hpos) (by decide)
  exact hle'.trans_lt hlt


/-! ### Singleton-family savings (base of loc:thm:locality) -/

/-- If the selected family is a singleton `{i}`, then `J = L ∪ D_i`, so a
global saving `p(J) < p(L)` is already a single-extension saving. -/
lemma exists_single_saving_of_singleton (c : ι → GraphCycle G)
    (L : Finset V) (I : Finset ι) (_H : LocalityHyp c L I)
    (hsing : ∃ i, I = {i})
    (hsave : pathCoverNumber G (unionJ L c I) < pathCoverNumber G L) :
    ∃ i ∈ I, pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L := by
  obtain ⟨i, hI⟩ := hsing
  refine ⟨i, by simp [hI], ?_⟩
  have hunion : unionJ L c I = L ∪ (c i).support := by
    simp [unionJ, selectedSupport, hI]
  simpa [hunion] using hsave

/-- A vertex on a selected cycle belongs to its single-extension carrier.
This membership helper does not assert minimum-cover endpoint eligibility. -/
lemma eligible_on_selected_cycle (c : ι → GraphCycle G)
    {L : Finset V} {I : Finset ι} {h : V} {i : ι}
    (_hi : i ∈ I) (hh : h ∈ (c i).support) :
    h ∈ L ∪ (c i).support :=
  mem_union.2 (Or.inr hh)

/-! ### YY darts on an aligned cover shorten it -/

lemma GraphPath.adj_trimFinish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    G.Adj (p.trimFinish h).finish p.finish :=
  p.walk.adj_penultimate h

lemma GraphPath.adj_trimStart (p : GraphPath G) (h : ¬ p.walk.Nil) :
    G.Adj p.start (p.trimStart h).start := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q => simpa [trimStart] using hadj

lemma shortening_of_YY_split {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hqX : q.start ∈ X ∧ q.finish ∈ X)
    {left right : GraphPath G}
    (hst : left.start = p.start) (hfin : right.finish = p.finish)
    (hadjLR : G.Adj left.finish right.start)
    (hYl : left.finish ∈ Y) (hYr : right.start ∈ Y)
    (hdisjLR : Disjoint left.support right.support)
    (hU : left.support ∪ right.support = p.support) :
    False := by
  have hdisjpq : Disjoint p.support q.support :=
    pairwise_disjoint_of_mem pc.disjoint hp hq hne
  let q' := q.faceToStart (Or.inl rfl)
  have hq's : q'.support = q.support := q.faceToStart_support (Or.inl rfl)
  have hdisjLq : Disjoint left.support q'.support := by
    have : Disjoint left.support q.support :=
      hdisjpq.mono_left (hU ▸ subset_union_left)
    exact hq's.symm ▸ this
  have hdisjRq : Disjoint (left.support ∪ q'.support) right.support := by
    have hdisjRq0 : Disjoint q.support right.support :=
      hdisjpq.symm.mono_right (hU ▸ subset_union_right)
    refine disjoint_union_left.2 ⟨hdisjLR, ?_⟩
    exact hq's.symm ▸ hdisjRq0
  have hadj1 : G.Adj left.finish q'.start := by
    have : q'.start ∈ X := by
      rw [q.faceToStart_start (Or.inl rfl)]; exact hqX.1
    exact (hXY this hYl).symm
  have hadj2 : G.Adj q'.finish right.start := by
    have hf : q'.finish ∈ X := by
      change (q.faceToStart (Or.inl rfl)).finish ∈ X
      unfold GraphPath.faceToStart
      split_ifs
      · exact hqX.2
      · simpa [GraphPath.reverse] using hqX.1
    exact hXY hf hYr
  obtain ⟨r, hr, _, _⟩ :=
    exists_splice_three left q' right hadj1 hadj2 hdisjLq hdisjRq
  have hr' : r.support = p.support ∪ q.support ∪ (∅ : Finset V) := by
    rw [hr, hq's, ← hU]
    simp [union_comm, union_left_comm, union_assoc]
  have hdisjE : Disjoint L (∅ : Finset V) := disjoint_empty_right _
  let pc' := pc.replaceTwo hdisjE hp hq hne hr'
  have hcard : pc'.card = pc.card - 1 :=
    pc.replaceTwo_card hdisjE hp hq hne hr'
  have hUW : L ∪ (∅ : Finset V) = L := union_empty L
  have hle : pathCoverNumber G L ≤ pc'.card :=
    (pathCoverNumber_le (G := G) (pc'.cast hUW)).trans_eq
      (by simp [PathCover.cast_card, hcard])
  have h2 := two_le_card_of_mem_ne pc hp hq hne
  omega

lemma no_Y_predecessor_of_aligned {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    (hXend : ∀ r ∈ pc.paths, r.start ∈ X ∧ r.finish ∈ X)
    (h2 : 2 ≤ pc.card)
    {p : GraphPath G} (hp : p ∈ pc.paths) {y : V}
    (hy : y ∈ p.support) (hs : y ≠ p.start) (hyY : y ∈ Y) :
    ((p.takeUntil hy).trimFinish
        (fun hnil => hs ((GraphPath.takeUntil_nil_iff p hy).1 hnil))).finish ∉ Y := by
  intro hYpred
  obtain ⟨q, hqmem, hne⟩ : ∃ q, q ∈ pc.paths ∧ q ≠ p := by
    obtain ⟨a, b, ha, hb, hne⟩ := PathCover.exists_two_distinct pc h2
    by_cases h : a = p
    · exact ⟨b, hb, fun hba => hne (h.trans hba.symm)⟩
    · exact ⟨a, ha, h⟩
  have hnn : ¬ (p.takeUntil hy).walk.Nil :=
    fun hnil => hs ((GraphPath.takeUntil_nil_iff p hy).1 hnil)
  let left := (p.takeUntil hy).trimFinish hnn
  let right := p.dropUntil hy
  have hst : left.start = p.start := trimFinish_start (p.takeUntil hy) hnn
  have hfin : right.finish = p.finish := rfl
  have hstR : right.start = y := p.dropUntil_start hy
  have hadjLR : G.Adj left.finish right.start := by
    rw [hstR]
    exact GraphPath.adj_trimFinish (p.takeUntil hy) hnn
  have hYr : right.start ∈ Y := by
    rwa [hstR]
  have hdisjLR : Disjoint left.support right.support := by
    have hL : left.support = (p.takeUntil hy).support.erase y :=
      support_trimFinish (p.takeUntil hy) hnn
    refine disjoint_left.2 ?_
    intro x hxL hxR
    have hxL' : x ∈ (p.takeUntil hy).support.erase y := by rwa [hL] at hxL
    have hxT : x ∈ (p.takeUntil hy).support := (mem_erase.1 hxL').2
    have hxI := inter_support_takeUntil_dropUntil_subset p hy
      (mem_inter.2 ⟨hxT, hxR⟩)
    have hyx : x = y := mem_singleton.1 hxI
    exact (mem_erase.1 hxL').1 hyx
  have hU : left.support ∪ right.support = p.support := by
    have hL : left.support = (p.takeUntil hy).support.erase y :=
      support_trimFinish (p.takeUntil hy) hnn
    have hU0 : (p.takeUntil hy).support ∪ right.support = p.support :=
      support_takeUntil_union_dropUntil p hy
    rw [hL]
    ext x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxe | hxR
      · have hxT : x ∈ (p.takeUntil hy).support := (mem_erase.1 hxe).2
        have : x ∈ (p.takeUntil hy).support ∪ right.support :=
          mem_union.2 (Or.inl hxT)
        rwa [hU0] at this
      · have : x ∈ (p.takeUntil hy).support ∪ right.support :=
          mem_union.2 (Or.inr hxR)
        rwa [hU0] at this
    · intro hx
      have hxU : x ∈ (p.takeUntil hy).support ∪ right.support :=
        hU0.symm ▸ hx
      rcases mem_union.1 hxU with hxT | hxR
      · by_cases hxy : x = y
        · subst hxy
          refine mem_union.2 (Or.inr ?_)
          rw [← hstR]
          exact right.start_mem_support
        · exact mem_union.2 (Or.inl (mem_erase.2 ⟨hxy, hxT⟩))
      · exact mem_union.2 (Or.inr hxR)
  exact shortening_of_YY_split hXY pc hmin hp hqmem hne.symm (hXend q hqmem)
    hst hfin hadjLR hYpred hYr hdisjLR hU

lemma no_Y_successor_of_aligned {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    (hXend : ∀ r ∈ pc.paths, r.start ∈ X ∧ r.finish ∈ X)
    (h2 : 2 ≤ pc.card)
    {p : GraphPath G} (hp : p ∈ pc.paths) {y : V}
    (hy : y ∈ p.support) (hf : y ≠ p.finish) (hyY : y ∈ Y) :
    ((p.dropUntil hy).trimStart
        (fun hnil => hf ((dropUntil_nil_iff p hy).1 hnil))).start ∉ Y := by
  intro hYsucc
  obtain ⟨q, hqmem, hne⟩ : ∃ q, q ∈ pc.paths ∧ q ≠ p := by
    obtain ⟨a, b, ha, hb, hne⟩ := PathCover.exists_two_distinct pc h2
    by_cases h : a = p
    · exact ⟨b, hb, fun hba => hne (h.trans hba.symm)⟩
    · exact ⟨a, ha, h⟩
  have hnn : ¬ (p.dropUntil hy).walk.Nil :=
    fun hnil => hf ((dropUntil_nil_iff p hy).1 hnil)
  let left := p.takeUntil hy
  let right := (p.dropUntil hy).trimStart hnn
  have hst : left.start = p.start := rfl
  have hfin : right.finish = p.finish := trimStart_finish (p.dropUntil hy) hnn
  have hstL : left.finish = y := p.takeUntil_finish hy
  have hadjLR : G.Adj left.finish right.start := by
    rw [hstL]
    exact GraphPath.adj_trimStart (p.dropUntil hy) hnn
  have hYl : left.finish ∈ Y := by
    rwa [hstL]
  have hdisjLR : Disjoint left.support right.support := by
    have hR : right.support = (p.dropUntil hy).support.erase y :=
      support_trimStart (p.dropUntil hy) hnn
    refine disjoint_left.2 ?_
    intro x hxL hxR
    have hxR' : x ∈ (p.dropUntil hy).support.erase y := by rwa [hR] at hxR
    have hxD : x ∈ (p.dropUntil hy).support := (mem_erase.1 hxR').2
    have hxI := inter_support_takeUntil_dropUntil_subset p hy
      (mem_inter.2 ⟨hxL, hxD⟩)
    have hyx : x = y := mem_singleton.1 hxI
    exact (mem_erase.1 hxR').1 hyx
  have hU : left.support ∪ right.support = p.support := by
    have hR : right.support = (p.dropUntil hy).support.erase y :=
      support_trimStart (p.dropUntil hy) hnn
    have hU0 : left.support ∪ (p.dropUntil hy).support = p.support :=
      support_takeUntil_union_dropUntil p hy
    rw [hR]
    ext x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxL | hxe
      · have : x ∈ left.support ∪ (p.dropUntil hy).support :=
          mem_union.2 (Or.inl hxL)
        rwa [hU0] at this
      · have hxD : x ∈ (p.dropUntil hy).support := (mem_erase.1 hxe).2
        have : x ∈ left.support ∪ (p.dropUntil hy).support :=
          mem_union.2 (Or.inr hxD)
        rwa [hU0] at this
    · intro hx
      have hxU : x ∈ left.support ∪ (p.dropUntil hy).support := hU0.symm ▸ hx
      rcases mem_union.1 hxU with hxL | hxD
      · exact mem_union.2 (Or.inl hxL)
      · by_cases hxy : x = y
        · subst hxy
          refine mem_union.2 (Or.inl ?_)
          rw [← hstL]
          exact left.finish_mem_support
        · exact mem_union.2 (Or.inr (mem_erase.2 ⟨hxy, hxD⟩))
  exact shortening_of_YY_split hXY pc hmin hp hqmem hne.symm (hXend q hqmem)
    hst hfin hadjLR hYl hYsucc hdisjLR hU

/-! ### Disconnected restriction of a global saving -/

lemma L_split_of_cover {L A B : Finset V} {c : ι → GraphCycle G} {I : Finset ι}
    (hunion : A ∪ B = unionJ L c I) :
    L = L ∩ A ∪ L ∩ B := by
  ext x
  constructor
  · intro hx
    have : x ∈ A ∪ B := by
      rw [hunion]
      exact mem_union.2 (Or.inl hx)
    rcases mem_union.1 this with hA | hB
    · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hx, hA⟩))
    · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hx, hB⟩))
  · intro hx
    rcases mem_union.1 hx with h | h
    · exact (mem_inter.1 h).1
    · exact (mem_inter.1 h).1

lemma restrictIndex_union {c : ι → GraphCycle G} {L A B : Finset V} {I : Finset ι}
    (hunion : A ∪ B = unionJ L c I)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    I = restrictIndex c I A ∪ restrictIndex c I B := by
  have hsel : selectedSupport c I ⊆ A ∪ B := by
    rw [hunion]; exact subset_union_right
  ext i
  constructor
  · intro hi
    have hsub := GraphCycle.support_subset_of_no_cross hnocross (c i)
      ((cycle_support_subset_selected hi).trans hsel)
    rcases hsub with hA | hB
    · exact mem_union.2 (Or.inl (mem_restrictIndex.2 ⟨hi, hA⟩))
    · exact mem_union.2 (Or.inr (mem_restrictIndex.2 ⟨hi, hB⟩))
  · intro hi
    rcases mem_union.1 hi with h | h
    · exact (mem_restrictIndex.1 h).1
    · exact (mem_restrictIndex.1 h).1

lemma old_side_nonempty_of_no_cross {c : ι → GraphCycle G} {L A B : Finset V}
    {I : Finset ι} (H : LocalityHyp c L I)
    (hdisj : Disjoint A B) (hunion : A ∪ B = unionJ L c I)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hAne : A.Nonempty) :
    (L ∩ A).Nonempty := by
  obtain ⟨a, ha⟩ := hAne
  have haJ : a ∈ unionJ L c I := by
    rw [← hunion]
    exact mem_union.2 (Or.inl ha)
  rcases mem_union.1 haJ with haL | haSel
  · exact ⟨a, mem_inter.2 ⟨haL, ha⟩⟩
  · obtain ⟨i, hi, hia⟩ := mem_biUnion.1 haSel
    obtain ⟨d, hd⟩ := (c i).support_nonempty
    obtain ⟨u, huE, hadj⟩ := H.sees i hi d hd
    have huL : u ∈ L := eligibleSet_subset (G := G) L huE
    have hsub := GraphCycle.support_subset_of_no_cross hnocross (c i)
      ((cycle_support_subset_selected hi).trans (by
        rw [hunion]; exact subset_union_right))
    have hdA : d ∈ A := by
      rcases hsub with hA | hB
      · exact hA hd
      · have : a ∈ B := hB hia
        exact (Finset.disjoint_left.1 hdisj ha this).elim
    have huA : u ∈ A := by
      have huAB : u ∈ A ∪ B := by
        have : u ∈ unionJ L c I := mem_union.2 (Or.inl huL)
        rwa [← hunion] at this
      rcases mem_union.1 huAB with hA | hB
      · exact hA
      · exact (hnocross d hdA u hB hadj).elim
    exact ⟨u, mem_inter.2 ⟨huL, huA⟩⟩

/-! ### Leftover cover of `X₀` after deleting aligned `Y₀` -/

lemma GraphPath.mem_edges_of_not_nil (p : GraphPath G) (h : ¬ p.walk.Nil)
    {e : Sym2 V} (he : e ∈ p.edges) :
    e = s(p.start, p.walk.snd) ∨ e ∈ (p.trimStart h).edges := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q =>
    have he' : e ∈ (Walk.cons hadj q).edges := by
      simpa [GraphPath.edges] using he
    rw [Walk.edges_cons] at he'
    rcases List.mem_cons.1 he' with h1 | h2
    · refine Or.inl ?_
      simpa [Walk.snd_cons] using h1
    · refine Or.inr ?_
      simpa [trimStart, GraphPath.edges] using h2

lemma GraphPath.not_nil_of_mem_edges (p : GraphPath G) {e : Sym2 V}
    (he : e ∈ p.edges) : ¬ p.walk.Nil := by
  intro hnil
  have hlen : p.walk.length = 0 := (Walk.length_eq_zero_iff).2 hnil
  have hedges : p.walk.edges.length = 0 := by
    simpa [Walk.length_edges] using hlen
  have hempty : p.walk.edges = [] := List.eq_nil_of_length_eq_zero hedges
  simp [GraphPath.edges, hempty] at he

lemma GraphPath.trimStart_support_subset (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).support ⊆ p.support := by
  rw [support_trimStart]
  exact erase_subset _ _

lemma GraphPath.dropUntil_eq_self_of_start (p : GraphPath G) :
    p.dropUntil p.start_mem_support = p := by
  rcases p with ⟨u, v, walk, isPath⟩
  simp [dropUntil]

lemma GraphPath.snd_eq_trimStart_start (p : GraphPath G) (h : ¬ p.walk.Nil) :
    p.walk.snd = (p.trimStart h).start :=
  rfl

lemma GraphPath.dropUntil_walk_eq_trimStart (p : GraphPath G) (h : ¬ p.walk.Nil)
    {y : V} (hy : y ∈ (p.trimStart h).support) :
    (p.dropUntil (p.trimStart_support_subset h hy)).walk =
      ((p.trimStart h).dropUntil hy).walk := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q =>
    have hyq : y ∈ q.support.toFinset := by
      simpa [trimStart, GraphPath.support] using hy
    have hnotin : u ∉ q.support := ((Walk.cons_isPath_iff hadj q).1 isPath).2
    have hyne : y ≠ u := by
      intro hyu
      subst hyu
      exact hnotin (List.mem_toFinset.1 hyq)
    simp [GraphPath.dropUntil, GraphPath.trimStart, Walk.dropUntil,
      dite_eq_right (Ne.symm hyne)]

lemma GraphPath.exists_YY_succ_pair (p : GraphPath G) {Y : Finset V}
    {e : Sym2 V} (he : e ∈ p.edges) (hb : bothEndsIn e Y) :
    (∃ y z, y ∈ p.support ∧ z ∈ p.support ∧ y ∈ Y ∧ z ∈ Y ∧
      y ≠ p.finish ∧
        ∃ (hy : y ∈ p.support), (p.dropUntil hy).walk.snd = z) := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.walk.length = n →
        ∀ (e : Sym2 V), e ∈ p.edges → bothEndsIn e Y →
          (∃ y z, y ∈ p.support ∧ z ∈ p.support ∧ y ∈ Y ∧ z ∈ Y ∧
            y ≠ p.finish ∧
              ∃ (hy : y ∈ p.support), (p.dropUntil hy).walk.snd = z))
    p.walk.length ?_ p rfl e he hb
  intro n ih p hn e he hb
  have hnn := GraphPath.not_nil_of_mem_edges p he
  rcases GraphPath.mem_edges_of_not_nil p hnn he with hfirst | hrest
  · have hb' : bothEndsIn s(p.start, p.walk.snd) Y := by
      simpa [hfirst] using hb
    have hsY : p.start ∈ Y := (bothEndsIn_iff.1 hb').1
    have hzY : p.walk.snd ∈ Y := (bothEndsIn_iff.1 hb').2
    have hyne : p.start ≠ p.finish :=
      fun hsf => hnn ((nil_iff_start_eq_finish p).2 hsf)
    refine ⟨p.start, p.walk.snd, p.start_mem_support, ?_, hsY, hzY, hyne, ?_⟩
    · have : p.walk.snd = (p.trimStart hnn).start := rfl
      rw [this]
      exact (p.trimStart_support_subset hnn) (p.trimStart hnn).start_mem_support
    · refine ⟨p.start_mem_support, ?_⟩
      simp [GraphPath.dropUntil, Walk.dropUntil_first]
  · let q := p.trimStart hnn
    have hlt : q.walk.length < n := by
      have : q.walk.length + 1 = p.walk.length := by
        simpa [q, trimStart] using Walk.length_tail_add_one hnn
      omega
    obtain ⟨y, z, _hyq, hzq, hyY, hzY, hyne, hy, hsucc⟩ :=
      ih q.walk.length hlt q rfl e hrest hb
    have hqfin : q.finish = p.finish := trimStart_finish p hnn
    have hyneP : y ≠ p.finish := hqfin ▸ hyne
    refine ⟨y, z, p.trimStart_support_subset hnn hy,
        p.trimStart_support_subset hnn hzq, hyY, hzY, hyneP,
        ⟨p.trimStart_support_subset hnn hy, ?_⟩⟩
    have hw := GraphPath.dropUntil_walk_eq_trimStart p hnn hy
    have hsnd := congrArg Walk.snd hw
    have hqq : ((p.trimStart hnn).dropUntil hy).walk.snd =
        (q.dropUntil hy).walk.snd := by
      simp [q]
    exact hsnd.trans (hqq.trans hsucc)

/-! ### Aligned leftover profile of a complete join -/

lemma NoConsecutive_of_aligned {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    (hXend : ∀ r ∈ pc.paths, r.start ∈ X ∧ r.finish ∈ X)
    (h2 : 2 ≤ pc.card)
    {p : GraphPath G} (hp : p ∈ pc.paths) :
    NoConsecutive Y p := by
  intro e he hb
  obtain ⟨y, z, _, _, hyY, hzY, hyne, hy, hsucc⟩ :=
    GraphPath.exists_YY_succ_pair (Y := Y) p he hb
  have hnn : ¬ (p.dropUntil hy).walk.Nil :=
    fun hnil => hyne ((dropUntil_nil_iff p hy).1 hnil)
  have hz : ((p.dropUntil hy).trimStart hnn).start ∈ Y := by
    have : ((p.dropUntil hy).trimStart hnn).start = z := hsucc
    exact this ▸ hzY
  exact (no_Y_successor_of_aligned hXY pc hmin hXend h2 hp hy hyne hyY) hz

lemma leftoverCover_card_of_ends_outside {K B : Finset V}
    (pc : PathCover G K) (hBK : B ⊆ K)
    (hends : ∀ p ∈ pc.paths, p.start ∉ B ∧ p.finish ∉ B)
    (hno : ∀ p ∈ pc.paths, NoConsecutive B p) :
    (pc.leftoverCover (B := B)).card = pc.card + B.card := by
  have hlenp : ∀ p ∈ pc.paths,
      (GraphPath.leftoverPieces B p).length = (p.support ∩ B).card + 1 := by
    intro p hp
    exact leftoverPieces_length_eq_of_ends_not_mem
      (hends p hp).1 (hends p hp).2 (hno p hp)
  have hflat : (pc.leftoverCover (B := B)).card =
      (pc.paths.map fun p => (GraphPath.leftoverPieces B p).length).sum := by
    simp [PathCover.leftoverCover, PathCover.card, List.length_flatMap]
  have hmap :
      ∀ {l : List (GraphPath G)},
        (∀ p ∈ l,
            (GraphPath.leftoverPieces B p).length = (p.support ∩ B).card + 1) →
          (l.map fun p => (GraphPath.leftoverPieces B p).length).sum =
            (l.map fun p => (p.support ∩ B).card + 1).sum := by
    intro l
    induction l with
    | nil => intro; simp
    | cons p ps ih =>
      intro h
      simp [h p List.mem_cons_self,
        ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
  have hadd : ∀ l : List (GraphPath G),
      (l.map fun p => (p.support ∩ B).card + 1).sum =
        (l.map fun p => (p.support ∩ B).card).sum + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons p ps ih =>
      simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hsum :=
    sum_map_eq_sum_toFinset pc.nodup_paths fun p => (p.support ∩ B).card
  have hinter := pc.sum_support_inter_card hBK
  calc (pc.leftoverCover (B := B)).card
      = (pc.paths.map fun p => (GraphPath.leftoverPieces B p).length).sum := hflat
    _ = (pc.paths.map fun p => (p.support ∩ B).card + 1).sum := hmap hlenp
    _ = (pc.paths.map fun p => (p.support ∩ B).card).sum + pc.paths.length :=
        hadd _
    _ = B.card + pc.card := by
        rw [hsum, hinter, PathCover.card]
    _ = pc.card + B.card := Nat.add_comm _ _

lemma PathCover.card_le_card_locality {U : Finset V} (pc : PathCover G U) :
    pc.card ≤ U.card := by
  let starts := pc.paths.map (fun p => p.start)
  have hsub : starts.toFinset ⊆ U := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    exact pc.support_subset hp p.start_mem_support
  have hnodup : starts.Nodup := by
    rw [List.nodup_map_iff_inj_on (PathCover.nodup_paths pc)]
    intro p hp q hq heq
    by_contra hne
    exact (disjoint_left.1
      (PathCover.pairwise_disjoint_of_mem_refinement pc.disjoint hp hq hne)
      p.start_mem_support (heq ▸ q.start_mem_support)).elim
  have hlen : starts.toFinset.card = starts.length :=
    List.toFinset_card_of_nodup hnodup
  have hle : starts.toFinset.card ≤ U.card := Finset.card_le_card hsub
  simpa [PathCover.card, starts, List.length_map, hlen] using hle

lemma sdiff_inter_right_eq_inter_left {X Y L : Finset V}
    (hdisj : Disjoint X Y) (hL : L ⊆ X ∪ Y) :
    L \ (L ∩ Y) = L ∩ X := by
  ext z
  constructor
  · intro hz
    have hzL : z ∈ L := (mem_sdiff.1 hz).1
    have hzY : z ∉ L ∩ Y := (mem_sdiff.1 hz).2
    have hzXY : z ∈ X ∪ Y := hL hzL
    rcases mem_union.1 hzXY with hX | hY
    · exact mem_inter.2 ⟨hzL, hX⟩
    · exact (hzY (mem_inter.2 ⟨hzL, hY⟩)).elim
  · intro hz
    exact mem_sdiff.2 ⟨(mem_inter.1 hz).1, fun h =>
      (disjoint_left.1 hdisj (mem_inter.1 hz).2 (mem_inter.1 h).2).elim⟩

lemma old_complete_join_profile {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hLsub : L ⊆ X ∪ Y)
    (hX0ne : (L ∩ X).Nonempty) (hY0ne : (L ∩ Y).Nonempty)
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    (h2 : 2 ≤ pc.card)
    (hXend : ∀ p ∈ pc.paths, p.start ∈ X ∧ p.finish ∈ X) :
    pathCoverNumber G (L ∩ X) = pc.card + (L ∩ Y).card ∧
      eligibleSet G L = eligibleSet G (L ∩ X) := by
  have hdisjXY := disjoint_of_completeBetween hXY
  have hX0Y0 : G.IsCompleteBetween ↑(L ∩ X) ↑(L ∩ Y) := by
    intro v1 hv1 v2 hv2
    have hv1' : v1 ∈ L ∩ X := hv1
    have hv2' : v2 ∈ L ∩ Y := hv2
    exact hXY (mem_inter.1 hv1').2 (mem_inter.1 hv2').2
  have hLsplit : L = (L ∩ X) ∪ (L ∩ Y) := by
    ext z
    constructor
    · intro hz
      have := hLsub hz
      rcases mem_union.1 this with hX | hY
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hX⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hz, hY⟩))
    · intro hz
      rcases mem_union.1 hz with h | h
      · exact (mem_inter.1 h).1
      · exact (mem_inter.1 h).1
  have hY0L : L ∩ Y ⊆ L := inter_subset_left
  have hends : ∀ p ∈ pc.paths, p.start ∉ L ∩ Y ∧ p.finish ∉ L ∩ Y := by
    intro p hp
    have hsX := (hXend p hp).1
    have hfX := (hXend p hp).2
    exact ⟨fun h => disjoint_left.1 hdisjXY hsX (mem_inter.1 h).2,
      fun h => disjoint_left.1 hdisjXY hfX (mem_inter.1 h).2⟩
  have hno : ∀ p ∈ pc.paths, NoConsecutive (L ∩ Y) p := by
    intro p hp e he hb
    have hbY : bothEndsIn e Y := by
      intro x hx
      exact (mem_inter.1 (hb x hx)).2
    exact NoConsecutive_of_aligned hXY pc hmin hXend h2 hp e he hbY
  have hcard := leftoverCover_card_of_ends_outside pc hY0L hends hno
  have hcast : L \ (L ∩ Y) = L ∩ X := sdiff_inter_right_eq_inter_left hdisjXY hLsub
  let pcX := (pc.leftoverCover (B := L ∩ Y)).cast hcast
  have hpcX : pcX.card = pc.card + (L ∩ Y).card := by
    simpa [pcX, PathCover.cast_card] using hcard
  have hleX := pathCoverNumber_le (G := G) pcX
  have hpX_le : pathCoverNumber G (L ∩ X) ≤ pc.card + (L ∩ Y).card :=
    hleX.trans_eq hpcX
  have hgeX : pc.card + (L ∩ Y).card ≤ (L ∩ X).card := by
    have := pcX.card_le_card_locality
    omega
  have hpY : pathCoverNumber G (L ∩ Y) ≤ (L ∩ Y).card :=
    pathCoverNumber_le_card (G := G) (L ∩ Y)
  have hjoin := pathCoverNumber_complete_join hX0ne hY0ne hX0Y0
  have hLunion : (L ∩ X) ∪ (L ∩ Y) = L := hLsplit.symm
  have hYex : pathCoverNumber G (L ∩ Y) - (L ∩ X).card = 0 := by
    have : pathCoverNumber G (L ∩ Y) ≤ (L ∩ X).card := by
      have hle : (L ∩ Y).card ≤ (L ∩ X).card :=
        (Nat.le_add_left (L ∩ Y).card pc.card).trans hgeX
      exact hpY.trans hle
    exact Nat.sub_eq_zero_of_le this
  have hform :
      pathCoverNumber G L =
        max 1 (pathCoverNumber G (L ∩ X) - (L ∩ Y).card) := by
    have h1 := hjoin
    rw [hLunion, hYex] at h1
    simpa [max_eq_left (Nat.zero_le _)] using h1
  have h2pos : 2 ≤ pathCoverNumber G L := by simpa [hmin] using h2
  have hsubpos : 1 ≤ pathCoverNumber G (L ∩ X) - (L ∩ Y).card := by
    by_contra h
    have h0 : pathCoverNumber G (L ∩ X) - (L ∩ Y).card = 0 := by omega
    have : pathCoverNumber G L = 1 := by
      rw [hform, h0]
      simp
    omega
  have hsub :
      pathCoverNumber G L =
        pathCoverNumber G (L ∩ X) - (L ∩ Y).card := by
    rwa [max_eq_right hsubpos] at hform
  have hleY : (L ∩ Y).card ≤ pathCoverNumber G (L ∩ X) :=
    Nat.le_of_lt (Nat.lt_of_sub_pos (Nat.succ_le_iff.mp hsubpos))
  have hpX : pathCoverNumber G (L ∩ X) = pc.card + (L ∩ Y).card := by
    have hsum := congrArg (fun n => n + (L ∩ Y).card) hsub
    rw [Nat.sub_add_cancel hleY, ← hmin] at hsum
    exact hsum.symm
  have hdom : (L ∩ Y).card < pathCoverNumber G (L ∩ X) :=
    Nat.lt_of_sub_pos (Nat.succ_le_iff.mp hsubpos)
  have hE := eligibleSet_complete_join_dominant hX0ne hY0ne hX0Y0 hdom
  refine ⟨hpX, ?_⟩
  have hEL : eligibleSet G L = eligibleSet G ((L ∩ X) ∪ (L ∩ Y)) :=
    congrArg (eligibleSet G) hLsplit
  exact hEL.trans hE

/-! ### Opened cycle support and mixed XY Hamilton paths -/

lemma GraphCycle.openAt_support (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).support = c.support := by
  have hnn := c.rotateTo_not_nil hu
  have hcons := (c.rotateTo hu).walk.cons_tail_eq hnn
  have hsup : (c.rotateTo hu).walk.support =
      (c.rotateTo hu).start :: (c.rotateTo hu).walk.tail.support := by
    rw [← hcons]; simp [Walk.support_cons]
  have hwalk : (c.openAt hu).walk = (c.rotateTo hu).walk.tail := rfl
  ext x
  constructor
  · intro hx
    have hxL : x ∈ (c.openAt hu).walk.support :=
      (mem_walk_support (p := c.openAt hu)).1 hx
    have hxT : x ∈ (c.rotateTo hu).walk.support.tail :=
      (Walk.support_tail_of_not_nil (c.rotateTo hu).walk hnn) ▸ hxL
    have hxR : x ∈ (c.rotateTo hu).walk.support := List.mem_of_mem_tail hxT
    have : x ∈ (c.rotateTo hu).support := List.mem_toFinset.2 hxR
    simpa [c.support_rotateTo hu] using this
  · intro hx
    have hx0 : x ∈ (c.rotateTo hu).support := by
      simpa [c.support_rotateTo hu] using hx
    have hxW : x ∈ (c.rotateTo hu).walk.support := List.mem_toFinset.1 hx0
    have hxL : x ∈ (c.rotateTo hu).start :: (c.rotateTo hu).walk.tail.support := by
      simpa [hsup] using hxW
    rcases List.mem_cons.1 hxL with h | h
    · have hxu : x = u := h.trans (start_rotateTo c hu)
      simpa [hxu, c.openAt_finish hu] using (c.openAt hu).finish_mem_support
    · exact (mem_walk_support (p := c.openAt hu)).2 (hwalk ▸ h)

lemma GraphPath.exists_leaving_edge {A : Finset V} (p : GraphPath G)
    (hs : p.start ∈ A) (hf : p.finish ∉ A) :
    ∃ x y, x ∈ A ∧ y ∉ A ∧ s(x, y) ∈ p.edges := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.walk.length = n →
        p.start ∈ A → p.finish ∉ A →
          ∃ x y, x ∈ A ∧ y ∉ A ∧ s(x, y) ∈ p.edges)
    p.walk.length ?_ p rfl hs hf
  intro n ih p hn hs' hf'
  have hnn : ¬ p.walk.Nil := fun h =>
    hf' (((nil_iff_start_eq_finish p).1 h) ▸ hs')
  have hfirst : s(p.start, p.walk.snd) ∈ p.edges := first_edge_mem p hnn
  by_cases hsnd : p.walk.snd ∈ A
  · let q := p.trimStart hnn
    have hlt : q.walk.length < n := by
      have : q.walk.length + 1 = p.walk.length := by
        simpa [q, trimStart] using Walk.length_tail_add_one hnn
      omega
    have hqs : q.start ∈ A := by simpa [q, trimStart] using hsnd
    have hqf : q.finish ∉ A := by simpa [q, trimStart_finish p hnn] using hf'
    obtain ⟨x, y, hx, hy, hedge⟩ := ih q.walk.length hlt q rfl hqs hqf
    exact ⟨x, y, hx, hy, (edges_trimStart_subset p hnn) hedge⟩
  · exact ⟨p.start, p.walk.snd, hs', hsnd, hfirst⟩

lemma pathCoverNumber_lt_of_crossing {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    {u : V} (hu : u = p.start ∨ u = p.finish)
    (hqX : q.start ∈ X ∧ q.finish ∈ X)
    (rD : GraphPath G) (hXs : rD.start ∈ X) (hYf : rD.finish ∈ Y)
    (hadj_ud : G.Adj u rD.start)
    {D : Finset V} (hrD : rD.support = D) (hdisj : Disjoint L D) :
    pathCoverNumber G (L ∪ D) < pathCoverNumber G L := by
  let p' := p.faceToFinish hu
  let q' := q.faceToStart (Or.inl rfl)
  have hp's : p'.support = p.support := p.faceToFinish_support hu
  have hq's : q'.support = q.support := q.faceToStart_support (Or.inl rfl)
  have hdisjmidL : Disjoint p'.support rD.support := by
    have : Disjoint p.support D := hdisj.mono_left (pc.support_subset hp)
    rw [hp's, hrD]
    exact this
  have hdisjmidR : Disjoint (p'.support ∪ rD.support) q'.support := by
    have hdisjpq : Disjoint p.support q.support :=
      pairwise_disjoint_of_mem pc.disjoint hp hq hne
    have hdisjqD : Disjoint D q.support :=
      (hdisj.mono_left (pc.support_subset hq)).symm
    rw [hp's, hq's, hrD]
    exact disjoint_union_left.2 ⟨hdisjpq, hdisjqD⟩
  have hadj1 : G.Adj p'.finish rD.start := by
    have : p'.finish = u := p.faceToFinish_finish hu
    simpa [this] using hadj_ud
  have hadj2 : G.Adj rD.finish q'.start := by
    have : q'.start ∈ X := by
      rw [q.faceToStart_start (Or.inl rfl)]; exact hqX.1
    exact (hXY this hYf).symm
  obtain ⟨r, hr, _, _⟩ :=
    exists_splice_three p' rD q' hadj1 hadj2 hdisjmidL hdisjmidR
  have hr' : r.support = p.support ∪ q.support ∪ D := by
    rw [hr, hp's, hq's, hrD]
    ac_rfl
  let pcN := pc.replaceTwo hdisj hp hq hne hr'
  have hNcard := pc.replaceTwo_card hdisj hp hq hne hr'
  have hle := pathCoverNumber_le (G := G) pcN
  have h2 := two_le_card_of_mem_ne pc hp hq hne
  have hle' : pathCoverNumber G (L ∪ D) ≤ pc.card - 1 := hle.trans_eq hNcard
  have hpos : 1 ≤ pc.card := le_trans (by decide : (1 : ℕ) ≤ 2) h2
  have hlt : pc.card - 1 < pathCoverNumber G L := by
    rw [← hmin]
    exact Nat.sub_lt (Nat.succ_le_iff.mp hpos) (by decide)
  exact hle'.trans_lt hlt

/-- A selected cycle that meets `Y` yields a single-extension saving, once a
`q ≥ 2` old cover is aligned into `X`. Opening at a `Y`-vertex is either a
`Y`–`Y` Hamilton path of the cycle or an `X`–`Y` crossing path. -/
lemma exists_single_saving_of_Y_cycle (c : ι → GraphCycle G)
    {L X Y : Finset V} {I : Finset ι}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hLsub : L ⊆ X ∪ Y)
    (hEsub : eligibleSet G L ⊆ X)
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    (h2 : 2 ≤ pc.card)
    (hXend : ∀ r ∈ pc.paths, r.start ∈ X ∧ r.finish ∈ X)
    {i : ι} (hi : i ∈ I) (hdisj : Disjoint L (c i).support)
    (hYmeet : ∃ d ∈ (c i).support, d ∈ Y)
    (hsub : (c i).support ⊆ X ∪ Y)
    (hsees : ∀ d ∈ (c i).support, ∃ u ∈ eligibleSet G L, G.Adj d u) :
    pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L := by
  obtain ⟨d, hd, hdY⟩ := hYmeet
  let rD := (c i).openAt hd
  have hrD : rD.support = (c i).support := (c i).openAt_support hd
  have hfY : rD.finish ∈ Y := by
    change d ∈ Y
    exact hdY
  obtain ⟨p, q, hp, hq, hne⟩ := PathCover.exists_two_distinct pc h2
  have hpX := hXend p hp
  have hqX := hXend q hq
  by_cases hsY : rD.start ∈ Y
  · exact pathCoverNumber_lt_of_YY_opening hXY pc hmin hp hq hne hpX hqX
      rD hsY hfY hrD hdisj
  · have hsX : rD.start ∈ X := by
      have : rD.start ∈ X ∪ Y := hsub (by simpa [hrD] using rD.start_mem_support)
      rcases mem_union.1 this with h | h
      · exact h
      · exact (hsY h).elim
    obtain ⟨u, huE, hadj⟩ :=
      hsees rD.start (by simpa [hrD] using rD.start_mem_support)
    have huX : u ∈ X := hEsub huE
    have hEl : Eligible G L u := (mem_eligibleSet_iff (G := G)).1 huE |>.2
    obtain ⟨pcU, hminU, pU, hpU, huend⟩ := hEl
    have h2U : 2 ≤ pcU.card := by
      have : pcU.card = pc.card := hminU.trans hmin.symm
      simpa [this] using h2
    have hpt : pU.start ∈ X ∨ pU.finish ∈ X := by
      rcases huend with h | h
      · exact Or.inl (h ▸ huX)
      · exact Or.inr (h ▸ huX)
    have hXendU :=
      endpoints_aligned_of_join hXY hLsub pcU hminU h2U hpU hpt
    obtain ⟨qU, hqU, hneU⟩ : ∃ qU, qU ∈ pcU.paths ∧ qU ≠ pU := by
      obtain ⟨a, b, ha, hb, hne'⟩ := PathCover.exists_two_distinct pcU h2U
      by_cases h : a = pU
      · exact ⟨b, hb, fun hba => hne' (h.trans hba.symm)⟩
      · exact ⟨a, ha, h⟩
    exact pathCoverNumber_lt_of_crossing hXY pcU hminU hpU hqU hneU.symm huend
      (hXendU qU hqU) rD hsX hfY hadj.symm hrD hdisj

/-! ### Cardinality and transfer lemmas for the locality inductions -/

lemma two_le_unionJ_card (c : ι → GraphCycle G) {L : Finset V} {I : Finset ι}
    (H : LocalityHyp c L I) : 2 ≤ (unionJ L c I).card := by
  obtain ⟨i, hi⟩ := H.I_nonempty
  have h3 : 3 ≤ (c i).support.card := (c i).three_le_card_support
  have hdisj := H.disjL i hi
  have hsub : L ∪ (c i).support ⊆ unionJ L c I := unionJ_single_subset L c hi
  have hsum : L.card + (c i).support.card ≤ (unionJ L c I).card := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card hsub
  have hLpos : 1 ≤ L.card := card_pos.2 H.L_nonempty
  omega

lemma two_le_pathCoverNumber_of_saving {L J : Finset V} (hL : L.Nonempty)
    (hsub : L ⊆ J)
    (hsave : pathCoverNumber G J < pathCoverNumber G L) :
    2 ≤ pathCoverNumber G L := by
  have h1 := one_le_pathCoverNumber_of_nonempty (G := G) hL
  by_contra h
  have hq1 : pathCoverNumber G L = 1 := by omega
  have hJ0 : pathCoverNumber G J = 0 := by omega
  have hJempty : J = ∅ := (pathCoverNumber_eq_zero_iff (G := G) J).1 hJ0
  exact hL.ne_empty (subset_empty.1 (hJempty ▸ hsub))

lemma start_mem_eligibleSet {U : Finset V} (pc : PathCover G U)
    (hmin : pc.card = pathCoverNumber G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) : p.start ∈ eligibleSet G U :=
  (mem_eligibleSet_iff (G := G)).2
    ⟨pc.support_subset hp p.start_mem_support, ⟨pc, hmin, p, hp, Or.inl rfl⟩⟩

lemma pathCoverNumber_lt_of_disjoint_reattach {LA LB D : Finset V}
    (hdisj : Disjoint (LA ∪ D) LB)
    (hnocross : ∀ a ∈ LA ∪ D, ∀ b ∈ LB, ¬ G.Adj a b)
    (hdisjOld : Disjoint LA LB)
    (hnocrossOld : ∀ a ∈ LA, ∀ b ∈ LB, ¬ G.Adj a b)
    (hsave : pathCoverNumber G (LA ∪ D) < pathCoverNumber G LA) :
    pathCoverNumber G (LA ∪ LB ∪ D) < pathCoverNumber G (LA ∪ LB) := by
  have haddNew :=
    Cograph.pathCoverNumber_disjoint_union (A := LA ∪ D) (B := LB) hdisj hnocross
  have haddOld :=
    Cograph.pathCoverNumber_disjoint_union (A := LA) (B := LB) hdisjOld hnocrossOld
  have hU : (LA ∪ D) ∪ LB = LA ∪ LB ∪ D := by
    ext x
    simp only [mem_union]
    tauto
  rw [← hU, haddNew, haddOld]
  omega

lemma pathCoverNumber_lt_of_join_child {X0 Y D : Finset V}
    (hX0ne : X0.Nonempty) (hYne : Y.Nonempty)
    (hZY : G.IsCompleteBetween ↑(X0 ∪ D) ↑Y)
    (h2 : 2 ≤ pathCoverNumber G (X0 ∪ Y))
    (hpX : pathCoverNumber G X0 = pathCoverNumber G (X0 ∪ Y) + Y.card)
    (hsave : pathCoverNumber G (X0 ∪ D) < pathCoverNumber G X0) :
    pathCoverNumber G (X0 ∪ Y ∪ D) < pathCoverNumber G (X0 ∪ Y) := by
  have hZne : (X0 ∪ D).Nonempty := hX0ne.mono subset_union_left
  have hU : (X0 ∪ D) ∪ Y = X0 ∪ Y ∪ D := by
    ext x
    simp only [mem_union]
    tauto
  have hj := pathCoverNumber_complete_join hZne hYne hZY
  have hpZle : pathCoverNumber G (X0 ∪ D) ≤ pathCoverNumber G X0 - 1 :=
    Nat.le_pred_of_lt hsave
  have hX0card : pathCoverNumber G X0 ≤ X0.card :=
    pathCoverNumber_le_card (G := G) X0
  have hZcard : X0.card ≤ (X0 ∪ D).card := card_le_card subset_union_left
  have hYle : pathCoverNumber G Y ≤ Y.card := pathCoverNumber_le_card (G := G) Y
  have hYltX0 : Y.card < X0.card := by
    have : Y.card < pathCoverNumber G X0 := by omega
    exact this.trans_le hX0card
  have hYex : pathCoverNumber G Y - (X0 ∪ D).card = 0 :=
    Nat.sub_eq_zero_of_le (hYle.trans (hYltX0.le.trans hZcard))
  have hform :
      pathCoverNumber G ((X0 ∪ D) ∪ Y) =
        max 1 (pathCoverNumber G (X0 ∪ D) - Y.card) := by
    simpa [hYex, max_eq_left (Nat.zero_le _)] using hj
  have hle : pathCoverNumber G ((X0 ∪ D) ∪ Y) ≤
      pathCoverNumber G (X0 ∪ Y) - 1 := by
    have hbound : pathCoverNumber G (X0 ∪ D) - Y.card ≤
        pathCoverNumber G (X0 ∪ Y) - 1 := by omega
    have hmax : max 1 (pathCoverNumber G (X0 ∪ D) - Y.card) ≤
        pathCoverNumber G (X0 ∪ Y) - 1 := by
      have h1 : 1 ≤ pathCoverNumber G (X0 ∪ Y) - 1 := by omega
      exact max_le h1 hbound
    exact (le_of_eq hform).trans hmax
  have : pathCoverNumber G (X0 ∪ Y ∪ D) ≤ pathCoverNumber G (X0 ∪ Y) - 1 := by
    simpa [hU] using hle
  omega

lemma unionJ_eq_side_of_cycles_subset (c : ι → GraphCycle G)
    {L X Y : Finset V} {I : Finset ι}
    (hunion : X ∪ Y = unionJ L c I) (hdisj : Disjoint X Y)
    (hYold : Y ⊆ L) (hIin : ∀ i ∈ I, (c i).support ⊆ X) :
    unionJ (L ∩ X) c I = X := by
  have hsel : selectedSupport c I ⊆ X := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hx
    exact hIin i hi hxi
  ext x
  constructor
  · intro hx
    rcases mem_union.1 hx with hxL | hxS
    · exact (mem_inter.1 hxL).2
    · exact hsel hxS
  · intro hxX
    have hxJ : x ∈ unionJ L c I := by
      rw [← hunion]
      exact mem_union.2 (Or.inl hxX)
    rcases mem_union.1 hxJ with hxL | hxS
    · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hxL, hxX⟩))
    · exact mem_union.2 (Or.inr hxS)

lemma LocalityHyp.of_cycles_in_X (c : ι → GraphCycle G)
    {L X Y : Finset V} {I : Finset ι} (H : LocalityHyp c L I)
    (hunion : X ∪ Y = unionJ L c I) (hdisj : Disjoint X Y)
    (hYold : Y ⊆ L) (hIin : ∀ i ∈ I, (c i).support ⊆ X)
    (hE : eligibleSet G L = eligibleSet G (L ∩ X))
    (hLXne : (L ∩ X).Nonempty) :
    LocalityHyp c (L ∩ X) I where
  I_nonempty := H.I_nonempty
  L_nonempty := hLXne
  disjL := fun i hi => (H.disjL i hi).mono_left inter_subset_left
  pairwise := H.pairwise
  cog := by
    have hJ : unionJ (L ∩ X) c I = X :=
      unionJ_eq_side_of_cycles_subset c hunion hdisj hYold hIin
    have hXsub : X ⊆ unionJ L c I := by
      rw [← hunion]
      exact subset_union_left
    have hXcog : IsCograph G X := IsCograph.subset (G := G) H.cog hXsub
    simpa [hJ] using hXcog
  sees := by
    intro i hi d hd
    obtain ⟨u, huE, hadj⟩ := H.sees i hi d hd
    have huX : u ∈ eligibleSet G (L ∩ X) := by
      rw [← hE]
      exact huE
    exact ⟨u, huX, hadj⟩

lemma exists_oriented_aligned_join (c : ι → GraphCycle G)
    {L : Finset V} {I : Finset ι} (H : LocalityHyp c L I)
    (hconn : (G.induce (unionJ L c I : Set V)).Connected)
    (hq : 2 ≤ pathCoverNumber G L) :
    ∃ (X Y : Finset V) (pc : PathCover G L),
      X ⊆ unionJ L c I ∧ Y ⊆ unionJ L c I ∧
        X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧
        X ∪ Y = unionJ L c I ∧
        G.IsCompleteBetween (X : Set V) (Y : Set V) ∧
        X.card < (unionJ L c I).card ∧ Y.card < (unionJ L c I).card ∧
        pc.card = pathCoverNumber G L ∧
        (∀ p ∈ pc.paths, p.start ∈ X ∧ p.finish ∈ X) := by
  have hJ2 : 2 ≤ (unionJ L c I).card := two_le_unionJ_card c H
  have hcog : Cograph.IsCograph G (unionJ L c I) :=
    (Cograph.isCograph_iff (G := G) (U := unionJ L c I)).2 H.cog
  obtain ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hunion, hAB, hAlt, hBlt⟩ :=
    Cograph.exists_complete_join_on (U := unionJ L c I) hcog hconn hJ2
  obtain ⟨pc, hmin⟩ := exists_min_pathCover (G := G) L
  have h2 : 2 ≤ pc.card := by simpa [hmin] using hq
  obtain ⟨p0, q0, hp0, hq0, hne⟩ := PathCover.exists_two_distinct pc h2
  have hLsub : L ⊆ A ∪ B := by
    rw [hunion]
    exact subset_union_left
  by_cases hXend : ∃ p ∈ pc.paths, p.start ∈ A ∨ p.finish ∈ A
  · obtain ⟨p, hp, hpA⟩ := hXend
    refine ⟨A, B, pc, hAsub, hBsub, hAne, hBne, hdisj, hunion, hAB, hAlt, hBlt,
      hmin, ?_⟩
    exact endpoints_aligned_of_join hAB hLsub pc hmin h2 hp hpA
  · have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
      fun {_} hb {_} ha => (hAB ha hb).symm
    have hLsub' : L ⊆ B ∪ A := by
      rw [union_comm]
      exact hLsub
    have hp0B : p0.start ∈ B ∨ p0.finish ∈ B := by
      have hs : p0.start ∈ A ∪ B :=
        hLsub (pc.support_subset hp0 p0.start_mem_support)
      have hf : p0.finish ∈ A ∪ B :=
        hLsub (pc.support_subset hp0 p0.finish_mem_support)
      have hsA : p0.start ∉ A := fun h => hXend ⟨p0, hp0, Or.inl h⟩
      have hfA : p0.finish ∉ A := fun h => hXend ⟨p0, hp0, Or.inr h⟩
      rcases mem_union.1 hs with hA | hB
      · exact (hsA hA).elim
      · exact Or.inl hB
    refine ⟨B, A, pc, hBsub, hAsub, hBne, hAne, hdisj.symm, ?_, hBA, hBlt, hAlt,
      hmin, ?_⟩
    · rw [union_comm]
      exact hunion
    · exact endpoints_aligned_of_join hBA hLsub' pc hmin h2 hp0 hp0B

lemma old_profile_of_aligned {L X Y : Finset V}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hLsub : L ⊆ X ∪ Y)
    (pc : PathCover G L) (hmin : pc.card = pathCoverNumber G L)
    (h2 : 2 ≤ pc.card)
    (hXend : ∀ p ∈ pc.paths, p.start ∈ X ∧ p.finish ∈ X)
    {p0 : GraphPath G} (hp0 : p0 ∈ pc.paths) :
    pathCoverNumber G (L ∩ X) = pathCoverNumber G L + (L ∩ Y).card ∧
      eligibleSet G L = eligibleSet G (L ∩ X) := by
  have hdisj := disjoint_of_completeBetween hXY
  have hX0ne : (L ∩ X).Nonempty :=
    ⟨p0.start, mem_inter.2 ⟨pc.support_subset hp0 p0.start_mem_support,
      (hXend p0 hp0).1⟩⟩
  by_cases hY0 : (L ∩ Y).Nonempty
  · have hX0Y0 : G.IsCompleteBetween ↑(L ∩ X) ↑(L ∩ Y) := by
      intro v1 hv1 v2 hv2
      exact hXY (mem_inter.1 hv1).2 (mem_inter.1 hv2).2
    have hLsplit : (L ∩ X) ∪ (L ∩ Y) = L := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with h | h
        · exact (mem_inter.1 h).1
        · exact (mem_inter.1 h).1
      · intro hz
        have := hLsub hz
        rcases mem_union.1 this with hX | hY
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hX⟩))
        · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hz, hY⟩))
    have hxE : p0.start ∈ eligibleSet G ((L ∩ X) ∪ (L ∩ Y)) := by
      simpa [hLsplit] using start_mem_eligibleSet pc hmin hp0
    have hp2 : 2 ≤ pathCoverNumber G ((L ∩ X) ∪ (L ∩ Y)) := by
      simpa [hLsplit, hmin] using h2
    obtain ⟨hpX, hE, _⟩ :=
      Cograph.aligned_join_profile_of_eligible (X := L ∩ X) (Y := L ∩ Y)
        (x := p0.start) hX0ne hY0 hX0Y0 hp2 hxE
        (mem_inter.2 ⟨pc.support_subset hp0 p0.start_mem_support,
          (hXend p0 hp0).1⟩)
    refine ⟨?_, ?_⟩
    · simpa [hLsplit] using hpX
    · simpa [hLsplit] using hE
  · have hYempty : L ∩ Y = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hY0
    have hLX : L ∩ X = L := by
      ext z
      constructor
      · intro hz
        exact (mem_inter.1 hz).1
      · intro hz
        have hzXY := hLsub hz
        rcases mem_union.1 hzXY with hX | hY
        · exact mem_inter.2 ⟨hz, hX⟩
        · have hzY : z ∈ L ∩ Y := mem_inter.2 ⟨hz, hY⟩
          rw [hYempty] at hzY
          exact absurd hzY (notMem_empty z)
    simp [hLX, hYempty]

lemma exists_single_saving_of_card (c : ι → GraphCycle G) :
    ∀ (n : ℕ) (L : Finset V) (I : Finset ι),
      (unionJ L c I).card = n →
      LocalityHyp c L I →
      pathCoverNumber G (unionJ L c I) < pathCoverNumber G L →
      ∃ i ∈ I, pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L := by
  intro n
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (L : Finset V) (I : Finset ι),
        (unionJ L c I).card = n →
        LocalityHyp c L I →
        pathCoverNumber G (unionJ L c I) < pathCoverNumber G L →
        ∃ i ∈ I, pathCoverNumber G (L ∪ (c i).support) <
          pathCoverNumber G L) n ?_
  intro n ih L I hcard H hsave
  have hq : 2 ≤ pathCoverNumber G L :=
    two_le_pathCoverNumber_of_saving H.L_nonempty subset_union_left hsave
  by_cases hconn : (G.induce (unionJ L c I : Set V)).Connected
  · obtain ⟨X, Y, pc, hXsub, hYsub, hXne, hYne, hdisj, hunion, hXY, hXlt, hYlt,
        hmin, hXend⟩ :=
      exists_oriented_aligned_join c H hconn hq
    obtain ⟨p0, q0, hp0, hq0, _hne⟩ :=
      PathCover.exists_two_distinct pc (by simpa [hmin] using hq)
    have hLsub : L ⊆ X ∪ Y := by
      rw [hunion]
      exact subset_union_left
    obtain ⟨hpX, hE⟩ :=
      old_profile_of_aligned hXY hLsub pc hmin (by simpa [hmin] using hq)
        hXend hp0
    have hEsub : eligibleSet G L ⊆ X := by
      intro z hz
      have hzX : z ∈ eligibleSet G (L ∩ X) := by
        rw [← hE]
        exact hz
      exact (mem_inter.1 (eligibleSet_subset (G := G) (L ∩ X) hzX)).2
    by_cases hmeet : ∃ i ∈ I, ∃ d ∈ (c i).support, d ∈ Y
    · obtain ⟨i, hi, hYmeet⟩ := hmeet
      refine ⟨i, hi, ?_⟩
      have hsub : (c i).support ⊆ X ∪ Y := by
        rw [hunion]
        exact (cycle_support_subset_selected hi).trans subset_union_right
      exact exists_single_saving_of_Y_cycle c hXY hLsub hEsub pc hmin
        (by simpa [hmin] using hq) hXend hi (H.disjL i hi) hYmeet hsub
        (H.sees i hi)
    · have hIin : ∀ i ∈ I, (c i).support ⊆ X := by
        intro i hi
        have hsub : (c i).support ⊆ X ∪ Y := by
          rw [hunion]
          exact (cycle_support_subset_selected hi).trans subset_union_right
        intro d hd
        have hdXY := hsub hd
        rcases mem_union.1 hdXY with hX | hY
        · exact hX
        · exact (hmeet ⟨i, hi, d, hd, hY⟩).elim
      have hYold : Y ⊆ L := by
        intro y hy
        have hyJ : y ∈ unionJ L c I := by
          rw [← hunion]
          exact mem_union.2 (Or.inr hy)
        rcases mem_union.1 hyJ with hL | hS
        · exact hL
        · obtain ⟨i, hi, hiy⟩ := mem_biUnion.1 hS
          exact (Finset.disjoint_left.1 hdisj (hIin i hi hiy) hy).elim
      have hLXne : (L ∩ X).Nonempty :=
        ⟨p0.start, mem_inter.2 ⟨pc.support_subset hp0 p0.start_mem_support,
          (hXend p0 hp0).1⟩⟩
      have HX : LocalityHyp c (L ∩ X) I :=
        LocalityHyp.of_cycles_in_X c H hunion hdisj hYold hIin hE hLXne
      have hXeq : unionJ (L ∩ X) c I = X :=
        unionJ_eq_side_of_cycles_subset c hunion hdisj hYold hIin
      have hXcard : (unionJ (L ∩ X) c I).card = X.card := by
        rw [hXeq]
      have hYeq : L ∩ Y = Y := by
        ext z
        constructor
        · intro hz
          exact (mem_inter.1 hz).2
        · intro hz
          exact mem_inter.2 ⟨hYold hz, hz⟩
      have hpX' : pathCoverNumber G (L ∩ X) =
          pathCoverNumber G L + Y.card := by
        simpa [hYeq] using hpX
      have hYex : pathCoverNumber G Y - X.card = 0 := by
        have hYle : pathCoverNumber G Y ≤ Y.card :=
          pathCoverNumber_le_card (G := G) Y
        have hX0le : pathCoverNumber G (L ∩ X) ≤ X.card := by
          have : L ∩ X ⊆ X := inter_subset_right
          exact (pathCoverNumber_le_card (G := G) (L ∩ X)).trans
            (card_le_card this)
        have : Y.card < X.card := by omega
        exact Nat.sub_eq_zero_of_le (hYle.trans this.le)
      have hpXJ : pathCoverNumber G X ≤
          pathCoverNumber G (unionJ L c I) + Y.card := by
        have hge := pathCoverNumber_complete_join_ge_sub (A := X) (B := Y) hXY
        simpa [hunion] using hge
      have hsaveX : pathCoverNumber G (unionJ (L ∩ X) c I) <
          pathCoverNumber G (L ∩ X) := by
        rw [hXeq]
        omega
      have hlt : X.card < n := by
        rw [← hcard]
        exact hXlt
      obtain ⟨i, hi, hsavei⟩ :=
        ih X.card hlt (L ∩ X) I hXcard HX hsaveX
      refine ⟨i, hi, ?_⟩
      have hDiX : (c i).support ⊆ X := hIin i hi
      have hLsplit : L = (L ∩ X) ∪ Y := by
        ext z
        constructor
        · intro hz
          have hzXY := hLsub hz
          rcases mem_union.1 hzXY with hx | hy
          · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hx⟩))
          · exact mem_union.2 (Or.inr hy)
        · intro hz
          rcases mem_union.1 hz with hx | hy
          · exact (mem_inter.1 hx).1
          · exact hYold hy
      have hZY : G.IsCompleteBetween ↑((L ∩ X) ∪ (c i).support) ↑Y := by
        intro a ha b hb
        have haX : a ∈ X := by
          rcases mem_union.1 ha with hX0 | hD
          · exact (mem_inter.1 hX0).2
          · exact hDiX hD
        exact hXY haX hb
      have hU : (L ∩ X) ∪ Y ∪ (c i).support = L ∪ (c i).support := by
        rw [← hLsplit]
      have h2L : 2 ≤ pathCoverNumber G ((L ∩ X) ∪ Y) := by
        simpa [← hLsplit] using hq
      have hpXL : pathCoverNumber G (L ∩ X) =
          pathCoverNumber G ((L ∩ X) ∪ Y) + Y.card := by
        simpa [← hLsplit] using hpX'
      have hjoin :=
        pathCoverNumber_lt_of_join_child hLXne hYne hZY h2L hpXL hsavei
      exact lt_of_eq_of_lt (congrArg (pathCoverNumber G) hU.symm)
        (lt_of_lt_of_eq hjoin (congrArg (pathCoverNumber G) hLsplit.symm))
  · have hJne : (unionJ L c I).Nonempty := H.L_nonempty.mono subset_union_left
    obtain ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hunion, hnocross, hAlt, hBlt⟩ :=
      Cograph.exists_disjoint_union_on (U := unionJ L c I) hconn hJne
    have hLA := old_side_nonempty_of_no_cross H hdisj hunion hnocross hAne
    have hLB := old_side_nonempty_of_no_cross (A := B) (B := A) H hdisj.symm
      (by rw [union_comm]; exact hunion)
      (fun b hb a ha hab => hnocross a ha b hb hab.symm) hBne
    have hLsplit : L = L ∩ A ∪ L ∩ B := L_split_of_cover hunion
    have hdisjL : Disjoint (L ∩ A) (L ∩ B) :=
      disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right hdisj)
    have hnocrossL : ∀ a ∈ L ∩ A, ∀ b ∈ L ∩ B, ¬ G.Adj a b :=
      fun a ha b hb => hnocross a (mem_inter.1 ha).2 b (mem_inter.1 hb).2
    have hpL :=
      Cograph.pathCoverNumber_disjoint_union (A := L ∩ A) (B := L ∩ B)
        hdisjL hnocrossL
    have hAeq : unionJ (L ∩ A) c (restrictIndex c I A) = A :=
      unionJ_restrict_eq H hdisj hunion hnocross
    have hBeq : unionJ (L ∩ B) c (restrictIndex c I B) = B :=
      unionJ_restrict_eq (A := B) (B := A) H hdisj.symm
        (by rw [union_comm]; exact hunion)
        (fun b hb a ha hab => hnocross a ha b hb hab.symm)
    have hpJ :=
      Cograph.pathCoverNumber_disjoint_union (A := A) (B := B) hdisj hnocross
    have hpA_or : pathCoverNumber G A < pathCoverNumber G (L ∩ A) ∨
        pathCoverNumber G B < pathCoverNumber G (L ∩ B) := by
      have : pathCoverNumber G (A ∪ B) < pathCoverNumber G (L ∩ A ∪ L ∩ B) := by
        simpa [hunion, ← hLsplit] using hsave
      have hsumJ : pathCoverNumber G (A ∪ B) =
          pathCoverNumber G A + pathCoverNumber G B := hpJ
      have hsumL : pathCoverNumber G (L ∩ A ∪ L ∩ B) =
          pathCoverNumber G (L ∩ A) + pathCoverNumber G (L ∩ B) := hpL
      omega
    rcases hpA_or with hAsave | hBsave
    · have hIA : (restrictIndex c I A).Nonempty := by
        by_contra hempty
        have hIempty : restrictIndex c I A = ∅ :=
          Finset.not_nonempty_iff_eq_empty.1 hempty
        have hAeqL : A = L ∩ A := by
          simpa [hIempty, unionJ, selectedSupport] using hAeq.symm
        have hEq : pathCoverNumber G A = pathCoverNumber G (L ∩ A) :=
          congrArg (pathCoverNumber G) hAeqL
        exact lt_irrefl _ (hEq ▸ hAsave)
      have HA := H.restrict_side c hdisj hunion hnocross hIA hLA
      have hAcard : (unionJ (L ∩ A) c (restrictIndex c I A)).card = A.card := by
        rw [hAeq]
      have hsaveA : pathCoverNumber G (unionJ (L ∩ A) c (restrictIndex c I A)) <
          pathCoverNumber G (L ∩ A) := by
        simpa [hAeq] using hAsave
      have hlt : A.card < n := by
        rw [← hcard]
        exact hAlt
      obtain ⟨i, hi, hsavei⟩ :=
        ih A.card hlt (L ∩ A) (restrictIndex c I A) hAcard HA hsaveA
      refine ⟨i, (mem_restrictIndex.1 hi).1, ?_⟩
      have hDiA : (c i).support ⊆ A := (mem_restrictIndex.1 hi).2
      have hdisjNew : Disjoint ((L ∩ A) ∪ (c i).support) (L ∩ B) := by
        refine disjoint_left.2 ?_
        intro x hx hxB
        have hxA : x ∈ A := by
          rcases mem_union.1 hx with hLA' | hD
          · exact (mem_inter.1 hLA').2
          · exact hDiA hD
        exact Finset.disjoint_left.1 hdisj hxA (mem_inter.1 hxB).2
      have hnocrossNew :
          ∀ a ∈ (L ∩ A) ∪ (c i).support, ∀ b ∈ L ∩ B, ¬ G.Adj a b := by
        intro a ha b hb
        have haA : a ∈ A := by
          rcases mem_union.1 ha with hLA' | hD
          · exact (mem_inter.1 hLA').2
          · exact hDiA hD
        exact hnocross a haA b (mem_inter.1 hb).2
      have hreatt :=
        pathCoverNumber_lt_of_disjoint_reattach hdisjNew hnocrossNew hdisjL
          hnocrossL hsavei
      have hU : L ∩ A ∪ L ∩ B ∪ (c i).support = L ∪ (c i).support := by
        rw [← hLsplit]
      exact lt_of_eq_of_lt (congrArg (pathCoverNumber G) hU.symm)
        (lt_of_lt_of_eq hreatt (congrArg (pathCoverNumber G) hLsplit.symm))
    · have hIB : (restrictIndex c I B).Nonempty := by
        by_contra hempty
        have hIempty : restrictIndex c I B = ∅ :=
          Finset.not_nonempty_iff_eq_empty.1 hempty
        have hBeqL : B = L ∩ B := by
          simpa [hIempty, unionJ, selectedSupport] using hBeq.symm
        have hEq : pathCoverNumber G B = pathCoverNumber G (L ∩ B) :=
          congrArg (pathCoverNumber G) hBeqL
        exact lt_irrefl _ (hEq ▸ hBsave)
      have HB := H.restrict_side (A := B) (B := A) c hdisj.symm
        (by rw [union_comm]; exact hunion)
        (fun b hb a ha hab => hnocross a ha b hb hab.symm) hIB hLB
      have hBcard : (unionJ (L ∩ B) c (restrictIndex c I B)).card = B.card := by
        rw [hBeq]
      have hsaveB : pathCoverNumber G (unionJ (L ∩ B) c (restrictIndex c I B)) <
          pathCoverNumber G (L ∩ B) := by
        simpa [hBeq] using hBsave
      have hlt : B.card < n := by
        rw [← hcard]
        exact hBlt
      obtain ⟨i, hi, hsavei⟩ :=
        ih B.card hlt (L ∩ B) (restrictIndex c I B) hBcard HB hsaveB
      refine ⟨i, (mem_restrictIndex.1 hi).1, ?_⟩
      have hDiB : (c i).support ⊆ B := (mem_restrictIndex.1 hi).2
      have hdisjNew : Disjoint ((L ∩ B) ∪ (c i).support) (L ∩ A) := by
        refine disjoint_left.2 ?_
        intro x hx hxA
        have hxB : x ∈ B := by
          rcases mem_union.1 hx with hLB' | hD
          · exact (mem_inter.1 hLB').2
          · exact hDiB hD
        exact Finset.disjoint_left.1 hdisj.symm hxB (mem_inter.1 hxA).2
      have hnocrossNew :
          ∀ a ∈ (L ∩ B) ∪ (c i).support, ∀ b ∈ L ∩ A, ¬ G.Adj a b := by
        intro a ha b hb
        have haB : a ∈ B := by
          rcases mem_union.1 ha with hLB' | hD
          · exact (mem_inter.1 hLB').2
          · exact hDiB hD
        exact mt Adj.symm (hnocross b (mem_inter.1 hb).2 a haB)
      have hdisjL' : Disjoint (L ∩ B) (L ∩ A) := hdisjL.symm
      have hnocrossL' : ∀ a ∈ L ∩ B, ∀ b ∈ L ∩ A, ¬ G.Adj a b :=
        fun a ha b hb => mt Adj.symm (hnocrossL b hb a ha)
      have hreatt :=
        pathCoverNumber_lt_of_disjoint_reattach hdisjNew hnocrossNew hdisjL'
          hnocrossL' hsavei
      have hU : L ∩ B ∪ L ∩ A ∪ (c i).support = L ∪ (c i).support := by
        rw [union_comm (L ∩ B), ← hLsplit]
      exact lt_of_eq_of_lt (congrArg (pathCoverNumber G) hU.symm)
        (lt_of_lt_of_eq hreatt
          (congrArg (pathCoverNumber G)
            ((union_comm (L ∩ B) (L ∩ A)).trans hLsplit.symm)))

lemma exists_single_saving (c : ι → GraphCycle G) {L : Finset V} {I : Finset ι}
    (H : LocalityHyp c L I)
    (hsave : pathCoverNumber G (unionJ L c I) < pathCoverNumber G L) :
    ∃ i ∈ I, pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L :=
  exists_single_saving_of_card c (unionJ L c I).card L I rfl H hsave

/-! ### Cycle deletion bound and old-vertex release -/

lemma leftoverPieces_length_le_pack {B : Finset V} (p : GraphPath G) :
    (p.start ∈ B →
        (leftoverPieces B p).length ≤ (p.support ∩ B).card) ∧
      (p.finish ∈ B →
        (leftoverPieces B p).length ≤ (p.support ∩ B).card) ∧
      (p.start ∈ B → p.finish ∈ B →
        (leftoverPieces B p).length + 1 ≤ (p.support ∩ B).card) ∧
      (leftoverPieces B p).length ≤ (p.support ∩ B).card + 1 := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        (p.start ∈ B →
            (leftoverPieces B p).length ≤ (p.support ∩ B).card) ∧
          (p.finish ∈ B →
            (leftoverPieces B p).length ≤ (p.support ∩ B).card) ∧
          (p.start ∈ B → p.finish ∈ B →
            (leftoverPieces B p).length + 1 ≤ (p.support ∩ B).card) ∧
          (leftoverPieces B p).length ≤ (p.support ∩ B).card + 1)
    p.support.card ?_ p rfl
  intro n ih p hn
  have htrim_le (hnil : ¬ p.walk.Nil) :
      ((p.trimStart hnil).support ∩ B).card ≤ (p.support ∩ B).card :=
    card_le_card (inter_subset_inter (trimStart_support_subset p hnil) Subset.rfl)
  have hstart : p.start ∈ B →
      (leftoverPieces B p).length ≤ (p.support ∩ B).card := by
    intro hs
    by_cases hnil : p.walk.Nil
    · rw [leftoverPieces_of_start_mem_nil hs hnil]
      exact Nat.zero_le _
    · rw [leftoverPieces_of_start_mem_cons hs hnil]
      have hrec := ih _ (by simpa [hn] using trimStart_support_card_lt p hnil)
        (p.trimStart hnil) rfl
      have hnotStart : p.start ∉ (p.trimStart hnil).support := by
        rw [support_trimStart p hnil]
        intro hmem
        exact (mem_erase.1 hmem).1 rfl
      have hcard : ((p.trimStart hnil).support ∩ B).card + 1 =
          (p.support ∩ B).card := by
        have hunion :
            p.support ∩ B =
              insert p.start ((p.trimStart hnil).support ∩ B) := by
          ext z
          simp only [mem_inter, mem_insert, support_trimStart p hnil, mem_erase]
          constructor
          · intro hz
            rcases eq_or_ne z p.start with rfl | hne
            · exact Or.inl rfl
            · exact Or.inr ⟨⟨hne, hz.1⟩, hz.2⟩
          · intro hz
            rcases hz with rfl | hz
            · exact ⟨p.start_mem_support, hs⟩
            · exact ⟨hz.1.2, hz.2⟩
        have hnot : p.start ∉ (p.trimStart hnil).support ∩ B := fun h =>
          hnotStart (mem_inter.1 h).1
        rw [hunion, card_insert_of_notMem hnot]
      have hle := hrec.2.2.2
      omega
  have hboth : p.start ∈ B → p.finish ∈ B →
      (leftoverPieces B p).length + 1 ≤ (p.support ∩ B).card := by
    intro hs hf
    by_cases hnil : p.walk.Nil
    · rw [leftoverPieces_of_start_mem_nil hs hnil]
      have : p.start ∈ p.support ∩ B :=
        mem_inter.2 ⟨p.start_mem_support, hs⟩
      exact Nat.succ_le_of_lt (card_pos.2 ⟨_, this⟩)
    · rw [leftoverPieces_of_start_mem_cons hs hnil]
      have hrec := ih _ (by simpa [hn] using trimStart_support_card_lt p hnil)
        (p.trimStart hnil) rfl
      have hf' : (p.trimStart hnil).finish ∈ B := by
        simpa [trimStart_finish p hnil] using hf
      have hle := hrec.2.1 hf'
      have hsErase : p.start ∉ (p.trimStart hnil).support := by
        rw [support_trimStart p hnil]
        intro hmem
        exact (mem_erase.1 hmem).1 rfl
      have hcard : ((p.trimStart hnil).support ∩ B).card + 1 =
          (p.support ∩ B).card := by
        have hunion :
            p.support ∩ B =
              insert p.start ((p.trimStart hnil).support ∩ B) := by
          ext z
          simp only [mem_inter, mem_insert, support_trimStart p hnil, mem_erase]
          constructor
          · intro hz
            rcases eq_or_ne z p.start with rfl | hne
            · exact Or.inl rfl
            · exact Or.inr ⟨⟨hne, hz.1⟩, hz.2⟩
          · intro hz
            rcases hz with rfl | hz
            · exact ⟨p.start_mem_support, hs⟩
            · exact ⟨hz.1.2, hz.2⟩
        have hnot : p.start ∉ (p.trimStart hnil).support ∩ B := by
          intro h
          exact hsErase (mem_inter.1 h).1
        rw [hunion, card_insert_of_notMem hnot]
      omega
  have hfinish : p.finish ∈ B →
      (leftoverPieces B p).length ≤ (p.support ∩ B).card := by
    intro hf
    by_cases hs : p.start ∈ B
    · exact Nat.le_of_succ_le (hboth hs hf)
    · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
      | none =>
        have : p.finish ∈ p.walk.support :=
          (mem_walk_support (p := p)).1 p.finish_mem_support
        have hnot :=
          (List.find?_eq_none (p := fun x : V => decide (x ∈ B))).1 hfind
            p.finish this
        exact (hnot (decide_eq_true hf)).elim
      | some _ =>
        have hnone :
            p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
          simp [hfind]
        have hfind' := firstB_spec (B := B) (p := p) hnone
        have hx : firstB B p hnone ∈ p.support :=
          (mem_find?_B (B := B) hfind').1
        have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hs hfind'
        have hlen : (leftoverPieces B p).length =
            (leftoverPieces B (p.dropUntil hx)).length + 1 := by
          rw [leftoverPieces.eq_def]
          simp [hs, hnone]
        have hdropStart : (p.dropUntil hx).start ∈ B := by
          rw [p.dropUntil_start hx]
          exact (mem_find?_B (B := B) hfind').2
        have hdropFin : (p.dropUntil hx).finish ∈ B := hf
        have hrec := ih _ (by simpa [hn] using dropUntil_support_card_lt p hx hne)
          (p.dropUntil hx) rfl
        have hle := hrec.2.2.1 hdropStart hdropFin
        have hsub : (p.dropUntil hx).support ∩ B ⊆ p.support ∩ B :=
          inter_subset_inter (dropUntil_support_subset p hx) Subset.rfl
        rw [hlen]
        exact hle.trans (card_le_card hsub)
  have halways : (leftoverPieces B p).length ≤ (p.support ∩ B).card + 1 := by
    by_cases hs : p.start ∈ B
    · exact (hstart hs).trans (Nat.le_succ _)
    · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
      | none =>
        rw [leftoverPieces_of_not_mem_start_none hs hfind]
        simp
      | some _ =>
        have hnone :
            p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
          simp [hfind]
        have hfind' := firstB_spec (B := B) (p := p) hnone
        have hx : firstB B p hnone ∈ p.support :=
          (mem_find?_B (B := B) hfind').1
        have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hs hfind'
        have hlen : (leftoverPieces B p).length =
            (leftoverPieces B (p.dropUntil hx)).length + 1 := by
          rw [leftoverPieces.eq_def]
          simp [hs, hnone]
        have hdropStart : (p.dropUntil hx).start ∈ B := by
          rw [p.dropUntil_start hx]
          exact (mem_find?_B (B := B) hfind').2
        have hrec := ih _ (by simpa [hn] using dropUntil_support_card_lt p hx hne)
          (p.dropUntil hx) rfl
        have hle := hrec.1 hdropStart
        have hsub : (p.dropUntil hx).support ∩ B ⊆ p.support ∩ B :=
          inter_subset_inter (dropUntil_support_subset p hx) Subset.rfl
        rw [hlen]
        exact Nat.succ_le_succ (hle.trans (card_le_card hsub))
  exact ⟨hstart, hfinish, hboth, halways⟩

lemma leftoverPieces_length_le_of_finish_mem {B : Finset V} (p : GraphPath G)
    (hf : p.finish ∈ B) :
    (leftoverPieces B p).length ≤ (p.support ∩ B).card :=
  (leftoverPieces_length_le_pack (B := B) p).2.1 hf

lemma pathCoverNumber_cycle_sdiff_le (cyc : GraphCycle G) {B : Finset V}
    (hBne : B.Nonempty) (hBsub : B ⊆ cyc.support) :
    pathCoverNumber G (cyc.support \ B) ≤ B.card := by
  obtain ⟨y, hyB⟩ := hBne
  have hy : y ∈ cyc.support := hBsub hyB
  let rD := cyc.openAt hy
  have hrD : rD.support = cyc.support := cyc.openAt_support hy
  have hf : rD.finish ∈ B := by
    change y ∈ B
    exact hyB
  have hlen := leftoverPieces_length_le_of_finish_mem (B := B) rD hf
  have hcast : rD.support \ B = cyc.support \ B := by rw [hrD]
  let pc := ((PathCover.ofPath rD).leftoverCover (B := B)).cast hcast
  have hcard : pc.card = (leftoverPieces B rD).length := by
    rw [PathCover.cast_card]
    simp [PathCover.leftoverCover, PathCover.card, PathCover.ofPath]
  have hle := pathCoverNumber_le (G := G) pc
  have hinter : rD.support ∩ B = B := by
    rw [hrD]
    exact inter_eq_right.2 hBsub
  have hbound : pc.card ≤ B.card := by
    rw [hcard]
    simpa [hinter] using hlen
  exact hle.trans hbound

lemma three_le_card_of_ineligible {U : Finset V} {x : V}
    (hx : x ∈ ineligibleSet G U) (h1 : pathCoverNumber G U = 1) :
    3 ≤ U.card := by
  have hxU : x ∈ U := (mem_ineligibleSet_iff (G := G)).1 hx |>.1
  have hnot : ¬ Eligible G U x := (mem_ineligibleSet_iff (G := G)).1 hx |>.2
  by_contra h
  have hle : U.card ≤ 2 := by omega
  obtain ⟨pc, hmin⟩ := exists_min_pathCover (G := G) U
  have hpc1 : pc.card = 1 := by omega
  obtain ⟨p, hpseq⟩ := PathCover.exists_singleton_of_card_one pc hpc1
  have hp : p ∈ pc.paths := by simp [hpseq]
  have hsup : p.support = U := by
    ext y
    constructor
    · intro hy
      exact pc.support_subset hp hy
    · intro hy
      obtain ⟨q, hq, hyq⟩ := (pc.mem_iff y).1 hy
      have : q = p := by
        simp [hpseq] at hq
        exact hq
      exact this ▸ hyq
  have hnod : p.walk.support.Nodup := (Walk.isPath_def _).1 p.isPath
  have hcardp : p.support.card = p.walk.length + 1 := by
    simp [GraphPath.support, List.toFinset_card_of_nodup hnod, Walk.length_support]
  have hlen : p.walk.length ≤ 1 := by
    have : p.support.card ≤ 2 := by simpa [hsup] using hle
    omega
  have hxend : x = p.start ∨ x = p.finish := by
    have hxsup : x ∈ p.support := by simpa [hsup] using hxU
    by_cases hnil : p.walk.Nil
    · have hsing := support_eq_singleton_of_nil p hnil
      have : x = p.start := by
        have hx' : x ∈ ({p.start} : Finset V) := by simpa [hsing] using hxsup
        simpa using hx'
      exact Or.inl this
    · have hlen1 : p.walk.length = 1 := by
        have hpos : 1 ≤ p.walk.length :=
          Nat.succ_le_of_lt (Nat.pos_of_ne_zero
            (mt Walk.length_eq_zero_iff.mp hnil))
        omega
      have hf : (p.trimStart hnil).finish = p.finish := trimStart_finish p hnil
      have htnil : (p.trimStart hnil).walk.Nil := by
        have : (p.trimStart hnil).walk.length = 0 := by
          have : (p.trimStart hnil).walk.length + 1 = p.walk.length := by
            simpa [trimStart] using Walk.length_tail_add_one hnil
          omega
        exact Walk.length_eq_zero_iff.mp this
      have hsing := support_eq_singleton_of_nil (p.trimStart hnil) htnil
      have hxL : x = p.start ∨ x ∈ (p.trimStart hnil).support := by
        have : p.support = insert p.start (p.trimStart hnil).support := by
          rw [support_trimStart p hnil]
          exact (insert_erase p.start_mem_support).symm
        have hx' : x ∈ insert p.start (p.trimStart hnil).support := by
          simpa [this] using hxsup
        simpa [mem_insert] using hx'
      rcases hxL with h | h
      · exact Or.inl h
      · have hxst : x = (p.trimStart hnil).start := by
          have hx' : x ∈ ({(p.trimStart hnil).start} : Finset V) := by
            simpa [hsing] using h
          simpa using hx'
        have hsteq : (p.trimStart hnil).start = p.finish := by
          have : (p.trimStart hnil).start = (p.trimStart hnil).finish :=
            ((nil_iff_start_eq_finish (p.trimStart hnil)).1 htnil)
          exact this.trans hf
        exact Or.inr (hxst.trans hsteq)
  exact hnot ⟨pc, hmin, p, hp, hxend⟩

lemma pathCoverNumber_ge_of_no_single_saving
    (c : ι → GraphCycle G) {L : Finset V} {I : Finset ι}
    (H : LocalityHyp c L I)
    (hnosave : ∀ i ∈ I,
        ¬ pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L) :
    pathCoverNumber G L ≤ pathCoverNumber G (unionJ L c I) := by
  by_contra h
  obtain ⟨i, hi, hsave⟩ :=
    exists_single_saving c H (Nat.lt_of_not_ge h)
  exact hnosave i hi hsave

lemma pathCoverNumber_union_le_add {A B : Finset V} (hdisj : Disjoint A B) :
    pathCoverNumber G (A ∪ B) ≤ pathCoverNumber G A + pathCoverNumber G B := by
  obtain ⟨pcA, hA⟩ := exists_min_pathCover (G := G) A
  obtain ⟨pcB, hB⟩ := exists_min_pathCover (G := G) B
  have hle := pathCoverNumber_le (G := G)
    (Cograph.PathCover.unionDisjoint hdisj pcA pcB)
  have hcard := Cograph.PathCover.unionDisjoint_card hdisj pcA pcB
  omega

lemma mem_eligibleSet_of_cycle (cyc : GraphCycle G) {U : Finset V}
    (hU : cyc.support = U) {x : V} (hx : x ∈ U) :
    x ∈ eligibleSet G U := by
  have hx' : x ∈ cyc.support := by simpa [hU] using hx
  let p := cyc.openAt hx'
  have hp : p.support = U := (cyc.openAt_support hx').trans hU
  let pc := (PathCover.ofPath p).cast hp
  have hpc1 : pc.card = 1 := by
    rw [PathCover.cast_card, PathCover.ofPath_card]
  have hle := pathCoverNumber_le (G := G) pc
  have hpos := one_le_pathCoverNumber_of_nonempty (G := G) ⟨x, hx⟩
  have hmin : pc.card = pathCoverNumber G U := by omega
  have hpmem : p ∈ pc.paths := by
    simp [pc, PathCover.cast_paths, PathCover.ofPath]
  have hf : p.finish = x := cyc.openAt_finish hx'
  exact (mem_eligibleSet_iff (G := G)).2
    ⟨hx, ⟨pc, hmin, p, hpmem, Or.inr hf.symm⟩⟩

/-- Merge one path of a `D`-cover into a minimum `A`-cover across an original
edge from an `A`-eligible vertex to the start of that `D`-path. -/
lemma pathCoverNumber_union_le_pred {A D : Finset V}
    (hdisj : Disjoint A D)
    (pcD : PathCover G D) {q : GraphPath G} (hq : q ∈ pcD.paths)
    {u : V} (huE : u ∈ eligibleSet G A) (hadj : G.Adj q.start u) :
    pathCoverNumber G (A ∪ D) ≤ pathCoverNumber G A + pcD.card - 1 := by
  have hEl : Eligible G A u := (mem_eligibleSet_iff (G := G)).1 huE |>.2
  obtain ⟨pc, hmin, p, hp, huend⟩ := hEl
  let p' := p.faceToFinish huend
  have hp's : p'.support = p.support := p.faceToFinish_support huend
  have hf' : p'.finish = u := p.faceToFinish_finish huend
  let pc' := pc.replacePath_sat hp p' hp's
  have hp'mem : p' ∈ pc'.paths := replacePath_sat_self_mem pc hp p' hp's
  have hdisjpq : Disjoint p'.support q.support := by
    have : Disjoint p.support q.support :=
      disjoint_of_subset_left (pc.support_subset hp)
        (disjoint_of_subset_right (pcD.support_subset hq) hdisj)
    simpa [hp's] using this
  have hadj' : G.Adj p'.finish q.start := by
    rw [hf']
    exact hadj.symm
  let s := p'.splice q hadj' hdisjpq
  have hs : s.support = p.support ∪ q.support := by
    simp [s, GraphPath.support_splice, hp's]
  have hcastRem : A \ p'.support = A \ p.support := by rw [hp's]
  let pcRemA := (pc'.erasePath hp'mem).cast hcastRem
  let pcRemD := pcD.erasePath hq
  let pcMid : PathCover G (p.support ∪ q.support) :=
    (PathCover.ofPath s).cast hs
  have hdisjAD :
      Disjoint (A \ p.support) (D \ q.support) :=
    disjoint_of_subset_left sdiff_subset
      (disjoint_of_subset_right sdiff_subset hdisj)
  have hdisjMid :
      Disjoint ((A \ p.support) ∪ (D \ q.support)) (p.support ∪ q.support) := by
    refine disjoint_union_right.2 ⟨?_, ?_⟩
    · refine disjoint_union_left.2 ⟨?_, ?_⟩
      · exact disjoint_left.2 fun x hx hxP => (mem_sdiff.1 hx).2 hxP
      · exact disjoint_of_subset_left sdiff_subset
          (disjoint_of_subset_right (pc.support_subset hp) hdisj.symm)
    · refine disjoint_union_left.2 ⟨?_, ?_⟩
      · exact disjoint_of_subset_left sdiff_subset
          (disjoint_of_subset_right (pcD.support_subset hq) hdisj)
      · exact disjoint_left.2 fun x hx hxQ => (mem_sdiff.1 hx).2 hxQ
  let pcRem := Cograph.PathCover.unionDisjoint hdisjAD pcRemA pcRemD
  let pcU := Cograph.PathCover.unionDisjoint hdisjMid pcRem pcMid
  have hposA : 1 ≤ pc'.card :=
    Nat.succ_le_of_lt (List.length_pos_of_mem hp'mem)
  have hposD : 1 ≤ pcD.card :=
    Nat.succ_le_of_lt (List.length_pos_of_mem hq)
  have hcard : pcU.card = pc.card + pcD.card - 1 := by
    have h1 : pcU.card = pcRem.card + pcMid.card :=
      Cograph.PathCover.unionDisjoint_card hdisjMid pcRem pcMid
    have h2 : pcRem.card = pcRemA.card + pcRemD.card :=
      Cograph.PathCover.unionDisjoint_card hdisjAD pcRemA pcRemD
    have h3 : pcRemA.card = pc'.card - 1 := by
      rw [PathCover.cast_card]
      exact PathCover.erasePath_card pc' hp'mem
    have h4 : pcRemD.card = pcD.card - 1 := PathCover.erasePath_card pcD hq
    have h5 : pcMid.card = 1 := by
      rw [PathCover.cast_card]
      exact PathCover.ofPath_card s
    have h6 : pc'.card = pc.card := replacePath_sat_card pc hp p' hp's
    rw [h1, h2, h3, h4, h5, h6]
    omega
  have hUeq : ((A \ p.support) ∪ (D \ q.support)) ∪ (p.support ∪ q.support) =
      A ∪ D := by
    ext x
    constructor
    · intro hx
      rcases mem_union.1 hx with hL | hR
      · rcases mem_union.1 hL with hA | hD
        · exact mem_union.2 (Or.inl (mem_sdiff.1 hA).1)
        · exact mem_union.2 (Or.inr (mem_sdiff.1 hD).1)
      · rcases mem_union.1 hR with hxp | hxq
        · exact mem_union.2 (Or.inl ((pc.mem_iff x).2 ⟨p, hp, hxp⟩))
        · exact mem_union.2 (Or.inr ((pcD.mem_iff x).2 ⟨q, hq, hxq⟩))
    · intro hx
      rcases mem_union.1 hx with hA | hD
      · by_cases hxp : x ∈ p.support
        · exact mem_union.2 (Or.inr (mem_union.2 (Or.inl hxp)))
        · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_sdiff.2 ⟨hA, hxp⟩))))
      · by_cases hxq : x ∈ q.support
        · exact mem_union.2 (Or.inr (mem_union.2 (Or.inr hxq)))
        · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_sdiff.2 ⟨hD, hxq⟩))))
  let pcJ := pcU.cast hUeq
  have hle := pathCoverNumber_le (G := G) pcJ
  have hcardJ : pcJ.card = pc.card + pcD.card - 1 := by
    rw [PathCover.cast_card]
    exact hcard
  have hmin' : pc.card = pathCoverNumber G A := hmin
  omega

lemma cycle_sdiff_Y_eq_inter_X {X Y : Finset V} {cyc : GraphCycle G}
    (hdisj : Disjoint X Y) (hsub : cyc.support ⊆ X ∪ Y) :
    cyc.support \ (cyc.support ∩ Y) = cyc.support ∩ X := by
  ext z
  constructor
  · intro hz
    have hzC := (mem_sdiff.1 hz).1
    have hzY : z ∉ cyc.support ∩ Y := (mem_sdiff.1 hz).2
    have hzXY := hsub hzC
    rcases mem_union.1 hzXY with hX | hY
    · exact mem_inter.2 ⟨hzC, hX⟩
    · exact (hzY (mem_inter.2 ⟨hzC, hY⟩)).elim
  · intro hz
    exact mem_sdiff.2 ⟨(mem_inter.1 hz).1, fun h =>
      Finset.disjoint_left.1 hdisj (mem_inter.1 hz).2 (mem_inter.1 h).2⟩

lemma leftoverCover_ofPath_nonempty (p : GraphPath G) {B : Finset V}
    (h : (p.support \ B).Nonempty) :
    ((PathCover.ofPath p).leftoverCover (B := B)).paths ≠ [] := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨q, hq, _⟩ :=
    (((PathCover.ofPath p).leftoverCover (B := B)).mem_iff y).1 hy
  exact List.ne_nil_of_mem hq

/-- A selected cycle meeting the non-dominant join child yields a genuine
balanced original-edge Hamilton cycle of the single extension, so every old
vertex is eligible there. -/
lemma exists_release_of_Y_cycle (c : ι → GraphCycle G)
    {L X Y : Finset V} {I : Finset ι}
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hLsub : L ⊆ X ∪ Y)
    (hX0ne : (L ∩ X).Nonempty)
    (hcrit : pathCoverNumber G (L ∩ X) = (L ∩ Y).card + 1)
    (hE : eligibleSet G L = eligibleSet G (L ∩ X))
    {i : ι} (hi : i ∈ I)
    (hdisj : Disjoint L (c i).support)
    (hYmeet : ∃ d ∈ (c i).support, d ∈ Y)
    (hsub : (c i).support ⊆ X ∪ Y)
    (hsees : ∀ d ∈ (c i).support, ∃ u ∈ eligibleSet G L, G.Adj d u)
    {h : V} (hhL : h ∈ L) :
    h ∈ eligibleSet G (L ∪ (c i).support) := by
  have hXYdisj := disjoint_of_completeBetween hXY
  set X0 := L ∩ X
  set Y0 := L ∩ Y
  set DX := (c i).support ∩ X
  set DY := (c i).support ∩ Y
  obtain ⟨d0, hd0, hd0Y⟩ := hYmeet
  have hDYne : DY.Nonempty := ⟨d0, mem_inter.2 ⟨hd0, hd0Y⟩⟩
  have hLsplit : X0 ∪ Y0 = L := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzX | hzY
      · exact (mem_inter.1 hzX).1
      · exact (mem_inter.1 hzY).1
    · intro hz
      have hzXY := hLsub hz
      rcases mem_union.1 hzXY with hX | hY
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hX⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hz, hY⟩))
  have hPQunion : (X0 ∪ DX) ∪ (Y0 ∪ DY) = L ∪ (c i).support := by
    ext z
    simp only [mem_union, X0, Y0, DX, DY, mem_inter]
    constructor
    · intro hz
      rcases hz with (hX0 | hDX) | (hY0 | hDY)
      · exact Or.inl hX0.1
      · exact Or.inr hDX.1
      · exact Or.inl hY0.1
      · exact Or.inr hDY.1
    · intro hz
      rcases hz with hzL | hzD
      · have hzXY := hLsub hzL
        rcases mem_union.1 hzXY with hX | hY
        · exact Or.inl (Or.inl ⟨hzL, hX⟩)
        · exact Or.inr (Or.inl ⟨hzL, hY⟩)
      · have hzXY := hsub hzD
        rcases mem_union.1 hzXY with hX | hY
        · exact Or.inl (Or.inr ⟨hzD, hX⟩)
        · exact Or.inr (Or.inr ⟨hzD, hY⟩)
  have hPQ : G.IsCompleteBetween ↑(X0 ∪ DX) ↑(Y0 ∪ DY) := by
    intro a ha b hb
    have haX : a ∈ X := by
      rcases mem_union.1 ha with hX0 | hDX
      · exact (mem_inter.1 hX0).2
      · exact (mem_inter.1 hDX).2
    have hbY : b ∈ Y := by
      rcases mem_union.1 hb with hY0 | hDY
      · exact (mem_inter.1 hY0).2
      · exact (mem_inter.1 hDY).2
    exact hXY haX hbY
  have hPne : (X0 ∪ DX).Nonempty := hX0ne.mono subset_union_left
  have hQne : (Y0 ∪ DY).Nonempty := hDYne.mono subset_union_right
  have h3 : 3 ≤ ((X0 ∪ DX) ∪ (Y0 ∪ DY)).card := by
    have hDi3 : 3 ≤ (c i).support.card := (c i).three_le_card_support
    have hsub' : (c i).support ⊆ (X0 ∪ DX) ∪ (Y0 ∪ DY) := by
      rw [hPQunion]
      exact subset_union_right
    exact hDi3.trans (card_le_card hsub')
  have hpP : pathCoverNumber G (X0 ∪ DX) ≤ (Y0 ∪ DY).card := by
    by_cases hDXne : DX.Nonempty
    · have hd0' : d0 ∈ (c i).support := hd0
      let rD := (c i).openAt hd0'
      have hrD : rD.support = (c i).support := (c i).openAt_support hd0'
      have hfY : rD.finish ∈ DY := by
        change d0 ∈ DY
        exact mem_inter.2 ⟨hd0, hd0Y⟩
      have hcast :
          rD.support \ DY = DX := by
        rw [hrD]
        exact cycle_sdiff_Y_eq_inter_X (X := X) (Y := Y) (cyc := c i)
          hXYdisj hsub
      let pcD := ((PathCover.ofPath rD).leftoverCover (B := DY)).cast hcast
      have hDne : (rD.support \ DY).Nonempty := by
        simpa [hcast] using hDXne
      have hpaths := leftoverCover_ofPath_nonempty rD hDne
      have hqmem : ∃ q, q ∈ pcD.paths := by
        have hne : pcD.paths ≠ [] := by
          simpa [pcD, PathCover.cast_paths] using hpaths
        match hps : pcD.paths with
        | [] => exact (hne hps).elim
        | q :: _ => exact ⟨q, by simp [hps]⟩
      obtain ⟨q, hq⟩ := hqmem
      have hq0 : q ∈ ((PathCover.ofPath rD).leftoverCover (B := DY)).paths := by
        simpa [pcD, PathCover.cast_paths] using hq
      obtain ⟨p0, hp0, hqp⟩ := List.mem_flatMap.1 hq0
      have hp0' : p0 = rD := by
        simpa [PathCover.ofPath] using hp0
      have hqs : q.start ∈ (c i).support := by
        have hsubq : q.support ⊆ rD.support :=
          leftoverPieces_support_subset (B := DY) rD q
            (by simpa [hp0'] using hqp)
        have : q.start ∈ rD.support := hsubq q.start_mem_support
        simpa [hrD] using this
      obtain ⟨u, huE, hadj⟩ := hsees q.start hqs
      have huX0 : u ∈ eligibleSet G X0 := by
        rw [← hE]
        exact huE
      have hdisjXD : Disjoint X0 DX :=
        disjoint_of_subset_left inter_subset_left
          (disjoint_of_subset_right inter_subset_left hdisj)
      have hle :=
        pathCoverNumber_union_le_pred hdisjXD pcD hq huX0 hadj
      have hcard : pcD.card = (leftoverPieces DY rD).length := by
        rw [PathCover.cast_card]
        simp [PathCover.leftoverCover, PathCover.card, PathCover.ofPath]
      have hlen := leftoverPieces_length_le_of_finish_mem (B := DY) rD hfY
      have hinter : rD.support ∩ DY = DY := by
        rw [hrD]
        exact inter_eq_right.2 inter_subset_left
      have hpcDle : pcD.card ≤ DY.card := by
        rw [hcard]
        simpa [hinter] using hlen
      have hY0DY : (Y0 ∪ DY).card = Y0.card + DY.card :=
        card_union_of_disjoint
          (disjoint_of_subset_left inter_subset_left
            (disjoint_of_subset_right inter_subset_left hdisj))
      have hpos : 1 ≤ pcD.card :=
        Nat.succ_le_of_lt (List.length_pos_of_mem hq)
      have : pathCoverNumber G X0 + pcD.card - 1 ≤ Y0.card + DY.card := by
        omega
      exact hle.trans (by simpa [hY0DY] using this)
    · have hDXempty : DX = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using hDXne
      have hP : X0 ∪ DX = X0 := by simp [hDXempty]
      have hQ : Y0 ∪ DY = Y0 ∪ (c i).support := by
        have : DY = (c i).support := by
          ext z
          constructor
          · intro hz
            exact (mem_inter.1 hz).1
          · intro hz
            have hzXY := hsub hz
            rcases mem_union.1 hzXY with hX | hY
            · have : z ∈ DX := mem_inter.2 ⟨hz, hX⟩
              rw [hDXempty] at this
              exact absurd this (notMem_empty z)
            · exact mem_inter.2 ⟨hz, hY⟩
        simp [this]
      have hpQcard : (Y0 ∪ (c i).support).card = Y0.card + (c i).support.card :=
        card_union_of_disjoint (hdisj.mono_left inter_subset_left)
      have : (c i).support.card ≥ 3 := (c i).three_le_card_support
      have : pathCoverNumber G X0 ≤ Y0.card + (c i).support.card := by
        omega
      simpa [hP, hQ, hpQcard] using this
  have hpQ : pathCoverNumber G (Y0 ∪ DY) ≤ (X0 ∪ DX).card := by
    by_cases hDXne : DX.Nonempty
    · have hDYeq : DY = (c i).support \ DX := by
        have hsub' : (c i).support ⊆ Y ∪ X := by rwa [union_comm]
        have hswap :=
          cycle_sdiff_Y_eq_inter_X (X := Y) (Y := X) (cyc := c i)
            hXYdisj.symm hsub'
        simpa [DY, DX, inter_comm] using hswap.symm
      have hleDY : pathCoverNumber G DY ≤ DX.card := by
        simpa [hDYeq] using
          pathCoverNumber_cycle_sdiff_le (c i) hDXne inter_subset_left
      have hdisjY : Disjoint Y0 DY :=
        disjoint_of_subset_left inter_subset_left
          (disjoint_of_subset_right inter_subset_left hdisj)
      have hsum := pathCoverNumber_union_le_add (G := G) hdisjY
      have hpY0 : pathCoverNumber G Y0 ≤ Y0.card :=
        pathCoverNumber_le_card (G := G) Y0
      have hpX0 : pathCoverNumber G X0 ≤ X0.card :=
        pathCoverNumber_le_card (G := G) X0
      have hX0ge : Y0.card + 1 ≤ X0.card := by omega
      have hPcard : (X0 ∪ DX).card = X0.card + DX.card :=
        card_union_of_disjoint
          (disjoint_of_subset_left inter_subset_left
            (disjoint_of_subset_right inter_subset_left hdisj))
      have : pathCoverNumber G Y0 + pathCoverNumber G DY ≤
          X0.card + DX.card := by omega
      exact hsum.trans (by simpa [hPcard] using this)
    · have hDXempty : DX = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using hDXne
      have hP : X0 ∪ DX = X0 := by simp [hDXempty]
      have hQ : Y0 ∪ DY = Y0 ∪ (c i).support := by
        have : DY = (c i).support := by
          ext z
          constructor
          · intro hz
            exact (mem_inter.1 hz).1
          · intro hz
            have hzXY := hsub hz
            rcases mem_union.1 hzXY with hX | hY
            · have : z ∈ DX := mem_inter.2 ⟨hz, hX⟩
              rw [hDXempty] at this
              exact absurd this (notMem_empty z)
            · exact mem_inter.2 ⟨hz, hY⟩
        simp [this]
      have hdisjY : Disjoint Y0 (c i).support :=
        hdisj.mono_left inter_subset_left
      have hsum := pathCoverNumber_union_le_add (G := G) hdisjY
      have hpY0 : pathCoverNumber G Y0 ≤ Y0.card :=
        pathCoverNumber_le_card (G := G) Y0
      have hpDi : pathCoverNumber G (c i).support ≤ 1 := by
        have hle := pathCoverNumber_le (G := G)
          ((PathCover.ofPath ((c i).openAt hd0)).cast
            ((c i).openAt_support hd0))
        have h1 : (((PathCover.ofPath ((c i).openAt hd0)).cast
            ((c i).openAt_support hd0))).card = 1 := by
          rw [PathCover.cast_card, PathCover.ofPath_card]
        exact hle.trans_eq h1
      have hpX0 : pathCoverNumber G X0 ≤ X0.card :=
        pathCoverNumber_le_card (G := G) X0
      have hnum : pathCoverNumber G Y0 + pathCoverNumber G (c i).support ≤
          X0.card := by omega
      have hle' := hsum.trans hnum
      simpa [hP, hQ] using hle'
  obtain ⟨cyc, hsup⟩ :=
    exists_complete_join_cycle hPne hQne hPQ hpP hpQ h3
  have hhU : h ∈ (X0 ∪ DX) ∪ (Y0 ∪ DY) := by
    rw [hPQunion]
    exact mem_union.2 (Or.inl hhL)
  have helig := mem_eligibleSet_of_cycle cyc hsup hhU
  simpa [hPQunion] using helig

lemma exists_oriented_critical_join (c : ι → GraphCycle G)
    {L : Finset V} {I : Finset ι} {h : V}
    (H : LocalityHyp c L I)
    (hconn : (G.induce (unionJ L c I : Set V)).Connected)
    (h1 : pathCoverNumber G L = 1)
    (hF : h ∈ ineligibleSet G L) :
    ∃ (X Y : Finset V),
      X ⊆ unionJ L c I ∧ Y ⊆ unionJ L c I ∧
        X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧
        X ∪ Y = unionJ L c I ∧
        G.IsCompleteBetween (X : Set V) (Y : Set V) ∧
        X.card < (unionJ L c I).card ∧ Y.card < (unionJ L c I).card ∧
        (L ∩ X).Nonempty ∧
        pathCoverNumber G (L ∩ X) = (L ∩ Y).card + 1 ∧
        eligibleSet G L = eligibleSet G (L ∩ X) := by
  have hJ2 : 2 ≤ (unionJ L c I).card := two_le_unionJ_card c H
  have hcog : Cograph.IsCograph G (unionJ L c I) :=
    (Cograph.isCograph_iff (G := G) (U := unionJ L c I)).2 H.cog
  obtain ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hunion, hAB, hAlt, hBlt⟩ :=
    Cograph.exists_complete_join_on (U := unionJ L c I) hcog hconn hJ2
  have hLsub : L ⊆ A ∪ B := by
    rw [hunion]
    exact subset_union_left
  have hL3 : 3 ≤ L.card := three_le_card_of_ineligible hF h1
  have hhL : h ∈ L := (mem_ineligibleSet_iff (G := G)).1 hF |>.1
  have hnotE : ¬ Eligible G L h := (mem_ineligibleSet_iff (G := G)).1 hF |>.2
  have hLsplit : (L ∩ A) ∪ (L ∩ B) = L := (L_split_of_cover (c := c) hunion).symm
  by_cases hA0 : (L ∩ A).Nonempty
  · by_cases hB0 : (L ∩ B).Nonempty
    · have hA0B0 : G.IsCompleteBetween ↑(L ∩ A) ↑(L ∩ B) :=
        fun {_} ha {_} hb => hAB (mem_inter.1 ha).2 (mem_inter.1 hb).2
      have hjoin := pathCoverNumber_complete_join hA0 hB0 hA0B0
      have hpLform :
          pathCoverNumber G L =
            max 1 (max (pathCoverNumber G (L ∩ A) - (L ∩ B).card)
              (pathCoverNumber G (L ∩ B) - (L ∩ A).card)) := by
        simpa [hLsplit] using hjoin
      have hex :
          pathCoverNumber G (L ∩ A) - (L ∩ B).card ≤ 1 ∧
            pathCoverNumber G (L ∩ B) - (L ∩ A).card ≤ 1 := by
        have : max 1 (max (pathCoverNumber G (L ∩ A) - (L ∩ B).card)
            (pathCoverNumber G (L ∩ B) - (L ∩ A).card)) = 1 := by
          simpa [h1] using hpLform.symm
        constructor <;> omega
      by_cases hAdom : (L ∩ B).card < pathCoverNumber G (L ∩ A)
      · have hpA : pathCoverNumber G (L ∩ A) = (L ∩ B).card + 1 := by omega
        have hE :=
          eligibleSet_complete_join_dominant hA0 hB0 hA0B0 hAdom
        refine ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hunion, hAB, hAlt, hBlt,
          hA0, hpA, ?_⟩
        simpa [hLsplit] using hE
      · by_cases hBdom : (L ∩ A).card < pathCoverNumber G (L ∩ B)
        · have hpB : pathCoverNumber G (L ∩ B) = (L ∩ A).card + 1 := by omega
          have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
            fun {_} hb {_} ha => (hAB ha hb).symm
          have hB0A0 : G.IsCompleteBetween ↑(L ∩ B) ↑(L ∩ A) :=
            fun {_} hb {_} ha => (hA0B0 ha hb).symm
          have hE :=
            eligibleSet_complete_join_dominant hB0 hA0 hB0A0 hBdom
          refine ⟨B, A, hBsub, hAsub, hBne, hAne, hdisj.symm, ?_, hBA, hBlt, hAlt,
            hB0, hpB, ?_⟩
          · rw [union_comm]; exact hunion
          · rw [union_comm] at hLsplit
            simpa [hLsplit] using hE
        · have hpA : pathCoverNumber G (L ∩ A) ≤ (L ∩ B).card :=
            Nat.le_of_not_gt hAdom
          have hpB : pathCoverNumber G (L ∩ B) ≤ (L ∩ A).card :=
            Nat.le_of_not_gt hBdom
          obtain ⟨cyc, hsup⟩ :=
            exists_complete_join_cycle hA0 hB0 hA0B0 hpA hpB (by simpa [hLsplit])
          have helig := mem_eligibleSet_of_cycle cyc hsup
            (by simpa [hLsplit] using hhL)
          exact (hnotE ((mem_eligibleSet_iff (G := G)).1
            (by simpa [hLsplit] using helig)).2).elim
    · have hBempty : L ∩ B = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using hB0
      have hLA : L ∩ A = L := by
        ext z
        constructor
        · intro hz
          exact (mem_inter.1 hz).1
        · intro hz
          have hzAB := hLsub hz
          rcases mem_union.1 hzAB with hA | hB
          · exact mem_inter.2 ⟨hz, hA⟩
          · have : z ∈ L ∩ B := mem_inter.2 ⟨hz, hB⟩
            rw [hBempty] at this
            exact absurd this (notMem_empty z)
      refine ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hunion, hAB, hAlt, hBlt,
        ?_, ?_, ?_⟩
      · simpa [hLA] using H.L_nonempty
      · simp [hLA, hBempty, h1]
      · simp [hLA]
  · have hAempty : L ∩ A = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hA0
    have hLB : L ∩ B = L := by
      ext z
      constructor
      · intro hz
        exact (mem_inter.1 hz).1
      · intro hz
        have hzAB := hLsub hz
        rcases mem_union.1 hzAB with hA | hB
        · have : z ∈ L ∩ A := mem_inter.2 ⟨hz, hA⟩
          rw [hAempty] at this
          exact absurd this (notMem_empty z)
        · exact mem_inter.2 ⟨hz, hB⟩
    have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
      fun {_} hb {_} ha => (hAB ha hb).symm
    have hB0 : (L ∩ B).Nonempty := by simpa [hLB] using H.L_nonempty
    refine ⟨B, A, hBsub, hAsub, hBne, hAne, hdisj.symm, ?_, hBA, hBlt, hAlt,
      hB0, ?_, ?_⟩
    · rw [union_comm]; exact hunion
    · simp [hLB, hAempty, h1]
    · simp [hLB]

lemma cycle_support_subset_extension {A D Y : Finset V} :
    D ⊆ (A ∪ D) ∪ Y :=
  fun _ hx => mem_union.2 (Or.inl (mem_union.2 (Or.inr hx)))

lemma eligible_of_join_extension {A D Y : Finset V} {x : V}
    (hAne : (A ∪ D).Nonempty) (hYne : Y.Nonempty)
    (hAY : G.IsCompleteBetween ↑(A ∪ D) ↑Y)
    (hpA : pathCoverNumber G (A ∪ D) ≤ Y.card)
    (hpY : pathCoverNumber G Y ≤ (A ∪ D).card)
    (h3 : 3 ≤ ((A ∪ D) ∪ Y).card)
    (hx : x ∈ (A ∪ D) ∪ Y) :
    x ∈ eligibleSet G ((A ∪ D) ∪ Y) := by
  obtain ⟨cyc, hsup⟩ :=
    exists_complete_join_cycle hAne hYne hAY hpA hpY h3
  have helig := mem_eligibleSet_of_cycle cyc hsup hx
  simpa [hsup] using helig

lemma exists_single_release_of_card (c : ι → GraphCycle G) {h : V} :
    ∀ (n : ℕ) (L : Finset V) (I : Finset ι),
      (unionJ L c I).card = n →
      LocalityHyp c L I →
      h ∈ ineligibleSet G L →
      h ∈ eligibleSet G (unionJ L c I) →
      ∃ i ∈ I,
        pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L ∨
          h ∈ eligibleSet G (L ∪ (c i).support) := by
  intro n
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (L : Finset V) (I : Finset ι),
        (unionJ L c I).card = n →
        LocalityHyp c L I →
        h ∈ ineligibleSet G L →
        h ∈ eligibleSet G (unionJ L c I) →
        ∃ i ∈ I,
          pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L ∨
            h ∈ eligibleSet G (L ∪ (c i).support)) n ?_
  intro n ih L I hcard H hF hEJ
  by_cases hsave : pathCoverNumber G (unionJ L c I) < pathCoverNumber G L
  · obtain ⟨i, hi, hs⟩ := exists_single_saving c H hsave
    exact ⟨i, hi, Or.inl hs⟩
  have hpJge : pathCoverNumber G L ≤ pathCoverNumber G (unionJ L c I) :=
    Nat.le_of_not_gt hsave
  have hhL : h ∈ L := (mem_ineligibleSet_iff (G := G)).1 hF |>.1
  have hnotEL : ¬ Eligible G L h := (mem_ineligibleSet_iff (G := G)).1 hF |>.2
  have hhJ : h ∈ unionJ L c I :=
    (mem_eligibleSet_iff (G := G)).1 hEJ |>.1
  by_cases hconn : (G.induce (unionJ L c I : Set V)).Connected
  · by_cases hq : 2 ≤ pathCoverNumber G L
    · obtain ⟨X, Y, pc, hXsub, hYsub, hXne, hYne, hdisj, hunion, hXY, hXlt, hYlt,
          hmin, hXend⟩ :=
        exists_oriented_aligned_join c H hconn hq
      obtain ⟨p0, q0, hp0, hq0, _hne⟩ :=
        PathCover.exists_two_distinct pc (by simpa [hmin] using hq)
      have hLsub : L ⊆ X ∪ Y := by
        rw [hunion]
        exact subset_union_left
      obtain ⟨hpX, hEold⟩ :=
        old_profile_of_aligned hXY hLsub pc hmin (by simpa [hmin] using hq)
          hXend hp0
      have hEsub : eligibleSet G L ⊆ X := by
        intro z hz
        have hzX : z ∈ eligibleSet G (L ∩ X) := by
          rw [← hEold]
          exact hz
        exact (mem_inter.1 (eligibleSet_subset (G := G) (L ∩ X) hzX)).2
      by_cases hmeet : ∃ i ∈ I, ∃ d ∈ (c i).support, d ∈ Y
      · obtain ⟨i, hi, hYmeet⟩ := hmeet
        refine ⟨i, hi, Or.inl ?_⟩
        have hsub : (c i).support ⊆ X ∪ Y := by
          rw [hunion]
          exact (cycle_support_subset_selected hi).trans subset_union_right
        exact exists_single_saving_of_Y_cycle c hXY hLsub hEsub pc hmin
          (by simpa [hmin] using hq) hXend hi (H.disjL i hi) hYmeet hsub
          (H.sees i hi)
      · have hIin : ∀ i ∈ I, (c i).support ⊆ X := by
          intro i hi
          have hsub : (c i).support ⊆ X ∪ Y := by
            rw [hunion]
            exact (cycle_support_subset_selected hi).trans subset_union_right
          intro d hd
          have hdXY := hsub hd
          rcases mem_union.1 hdXY with hX | hY
          · exact hX
          · exact (hmeet ⟨i, hi, d, hd, hY⟩).elim
        have hYold : Y ⊆ L := by
          intro y hy
          have hyJ : y ∈ unionJ L c I := by
            rw [← hunion]
            exact mem_union.2 (Or.inr hy)
          rcases mem_union.1 hyJ with hL | hS
          · exact hL
          · obtain ⟨i, hi, hiy⟩ := mem_biUnion.1 hS
            exact (Finset.disjoint_left.1 hdisj (hIin i hi hiy) hy).elim
        have hLXne : (L ∩ X).Nonempty :=
          ⟨p0.start, mem_inter.2 ⟨pc.support_subset hp0 p0.start_mem_support,
            (hXend p0 hp0).1⟩⟩
        have HX : LocalityHyp c (L ∩ X) I :=
          LocalityHyp.of_cycles_in_X c H hunion hdisj hYold hIin hEold hLXne
        have hXeq : unionJ (L ∩ X) c I = X :=
          unionJ_eq_side_of_cycles_subset c hunion hdisj hYold hIin
        have hYeq : L ∩ Y = Y := by
          ext z
          constructor
          · intro hz
            exact (mem_inter.1 hz).2
          · intro hz
            exact mem_inter.2 ⟨hYold hz, hz⟩
        have hLsplit : L = (L ∩ X) ∪ Y := by
          ext z
          constructor
          · intro hz
            have hzXY := hLsub hz
            rcases mem_union.1 hzXY with hx | hy
            · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hx⟩))
            · exact mem_union.2 (Or.inr hy)
          · intro hz
            rcases mem_union.1 hz with hx | hy
            · exact (mem_inter.1 hx).1
            · exact hYold hy
        have hdomOld : Y.card < pathCoverNumber G (L ∩ X) := by
          have hpX' : pathCoverNumber G (L ∩ X) =
              pathCoverNumber G L + Y.card := by simpa [hYeq] using hpX
          omega
        have hFold :
            ineligibleSet G L = Y ∪ ineligibleSet G (L ∩ X) := by
          have hX0Y0 : G.IsCompleteBetween ↑(L ∩ X) ↑Y := by
            intro a ha b hb
            exact hXY (mem_inter.1 ha).2 hb
          have hFjoin :=
            ineligibleSet_complete_join_dominant hLXne hYne hX0Y0 hdomOld
          simpa [← hLsplit] using hFjoin
        have hEX : h ∈ eligibleSet G X := by
          have hJform := pathCoverNumber_complete_join hXne hYne hXY
          have hYle : pathCoverNumber G Y ≤ Y.card :=
            pathCoverNumber_le_card (G := G) Y
          have hX0leX : pathCoverNumber G (L ∩ X) ≤ X.card :=
            (pathCoverNumber_le_card (G := G) (L ∩ X)).trans
              (card_le_card inter_subset_right)
          have hYltX : Y.card < X.card :=
            hdomOld.trans_le hX0leX
          have hYex : pathCoverNumber G Y - X.card = 0 :=
            Nat.sub_eq_zero_of_le (hYle.trans hYltX.le)
          have hpJ : pathCoverNumber G (unionJ L c I) =
              max 1 (pathCoverNumber G X - Y.card) := by
            simpa [hunion, hYex, max_eq_left (Nat.zero_le _)] using hJform
          have hJ2' : 2 ≤ pathCoverNumber G (unionJ L c I) := hq.trans hpJge
          have hdomX : Y.card < pathCoverNumber G X := by omega
          have hEjoin :=
            eligibleSet_complete_join_dominant hXne hYne hXY hdomX
          have hEJ' : h ∈ eligibleSet G (X ∪ Y) := by
            simpa [hunion] using hEJ
          simpa [hEjoin] using hEJ'
        have hhX0 : h ∈ ineligibleSet G (L ∩ X) := by
          have hhF : h ∈ Y ∪ ineligibleSet G (L ∩ X) := by
            simpa [hFold] using hF
          rcases mem_union.1 hhF with hhY | hhX
          · exact (Finset.disjoint_left.1 hdisj
              ((mem_eligibleSet_iff (G := G)).1 hEX |>.1) hhY).elim
          · exact hhX
        have hXcard : (unionJ (L ∩ X) c I).card = X.card := by rw [hXeq]
        have hlt : X.card < n := by
          rw [← hcard]
          exact hXlt
        have hEX' : h ∈ eligibleSet G (unionJ (L ∩ X) c I) := by
          simpa [hXeq] using hEX
        obtain ⟨i, hi, hret⟩ :=
          ih X.card hlt (L ∩ X) I hXcard HX hhX0 hEX'
        refine ⟨i, hi, ?_⟩
        have hDiX : (c i).support ⊆ X := hIin i hi
        have hZY : G.IsCompleteBetween ↑((L ∩ X) ∪ (c i).support) ↑Y := by
          intro a ha b hb
          have haX : a ∈ X := by
            rcases mem_union.1 ha with hX0 | hD
            · exact (mem_inter.1 hX0).2
            · exact hDiX hD
          exact hXY haX hb
        have hU : (L ∩ X) ∪ Y ∪ (c i).support = L ∪ (c i).support := by
          rw [← hLsplit]
        rcases hret with hsavei | hreli
        · have h2L : 2 ≤ pathCoverNumber G ((L ∩ X) ∪ Y) := by
            simpa [← hLsplit] using hq
          have hpXL : pathCoverNumber G (L ∩ X) =
              pathCoverNumber G ((L ∩ X) ∪ Y) + Y.card := by
            simpa [← hLsplit, hYeq] using hpX
          have hjoin :=
            pathCoverNumber_lt_of_join_child hLXne hYne hZY h2L hpXL hsavei
          exact Or.inl
            (lt_of_eq_of_lt (congrArg (pathCoverNumber G) hU.symm)
              (lt_of_lt_of_eq hjoin (congrArg (pathCoverNumber G) hLsplit.symm)))
        · by_cases hsav2 :
            pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L
          · exact Or.inl hsav2
          · have hZne : ((L ∩ X) ∪ (c i).support).Nonempty :=
              hLXne.mono subset_union_left
            have hJ2' : 2 ≤ pathCoverNumber G (L ∪ (c i).support) := by
              have : pathCoverNumber G L ≤
                  pathCoverNumber G (L ∪ (c i).support) :=
                Nat.le_of_not_gt hsav2
              exact hq.trans this
            have hU' : ((L ∩ X) ∪ (c i).support) ∪ Y =
                L ∪ (c i).support := by
              rw [union_right_comm, ← hLsplit]
            have hform := pathCoverNumber_complete_join hZne hYne hZY
            have hYle : pathCoverNumber G Y ≤ Y.card :=
              pathCoverNumber_le_card (G := G) Y
            have hX0leZ : pathCoverNumber G (L ∩ X) ≤
                ((L ∩ X) ∪ (c i).support).card :=
              (pathCoverNumber_le_card (G := G) (L ∩ X)).trans
                (card_le_card subset_union_left)
            have hYltZ : Y.card < ((L ∩ X) ∪ (c i).support).card :=
              hdomOld.trans_le hX0leZ
            have hYex : pathCoverNumber G Y -
                ((L ∩ X) ∪ (c i).support).card = 0 :=
              Nat.sub_eq_zero_of_le (hYle.trans hYltZ.le)
            have hpZY : pathCoverNumber G
                (((L ∩ X) ∪ (c i).support) ∪ Y) =
                  max 1 (pathCoverNumber G ((L ∩ X) ∪ (c i).support) -
                    Y.card) := by
              simpa [hYex, max_eq_left (Nat.zero_le _)] using hform
            have hdomZ : Y.card <
                pathCoverNumber G ((L ∩ X) ∪ (c i).support) := by
              have : 2 ≤ pathCoverNumber G
                  (((L ∩ X) ∪ (c i).support) ∪ Y) := by
                simpa [hU'] using hJ2'
              omega
            have hEjoin :=
              eligibleSet_complete_join_dominant hZne hYne hZY hdomZ
            have hreli' : h ∈ eligibleSet G
                (((L ∩ X) ∪ (c i).support) ∪ Y) := by
              rwa [hEjoin]
            exact Or.inr (by simpa [hU'] using hreli')
    · have hq1 : pathCoverNumber G L = 1 := by
        have hpos := one_le_pathCoverNumber_of_nonempty (G := G) H.L_nonempty
        omega
      obtain ⟨X, Y, hXsub, hYsub, hXne, hYne, hdisj, hunion, hXY, hXlt, hYlt,
          hLXne, hcrit, hEold⟩ :=
        exists_oriented_critical_join c H hconn hq1 hF
      have hLsub : L ⊆ X ∪ Y := by
        rw [hunion]
        exact subset_union_left
      by_cases hmeet : ∃ i ∈ I, ∃ d ∈ (c i).support, d ∈ Y
      · obtain ⟨i, hi, hYmeet⟩ := hmeet
        refine ⟨i, hi, Or.inr ?_⟩
        have hsub : (c i).support ⊆ X ∪ Y := by
          rw [hunion]
          exact (cycle_support_subset_selected hi).trans subset_union_right
        exact exists_release_of_Y_cycle c hXY hLsub hLXne hcrit hEold hi
          (H.disjL i hi) hYmeet hsub (H.sees i hi) hhL
      · have hIin : ∀ i ∈ I, (c i).support ⊆ X := by
          intro i hi
          have hsub : (c i).support ⊆ X ∪ Y := by
            rw [hunion]
            exact (cycle_support_subset_selected hi).trans subset_union_right
          intro d hd
          have hdXY := hsub hd
          rcases mem_union.1 hdXY with hX | hY
          · exact hX
          · exact (hmeet ⟨i, hi, d, hd, hY⟩).elim
        have hYold : Y ⊆ L := by
          intro y hy
          have hyJ : y ∈ unionJ L c I := by
            rw [← hunion]
            exact mem_union.2 (Or.inr hy)
          rcases mem_union.1 hyJ with hL | hS
          · exact hL
          · obtain ⟨i, hi, hiy⟩ := mem_biUnion.1 hS
            exact (Finset.disjoint_left.1 hdisj (hIin i hi hiy) hy).elim
        have HX : LocalityHyp c (L ∩ X) I :=
          LocalityHyp.of_cycles_in_X c H hunion hdisj hYold hIin hEold hLXne
        have hXeq : unionJ (L ∩ X) c I = X :=
          unionJ_eq_side_of_cycles_subset c hunion hdisj hYold hIin
        have hLsplit : L = (L ∩ X) ∪ Y := by
          ext z
          constructor
          · intro hz
            have hzXY := hLsub hz
            rcases mem_union.1 hzXY with hx | hy
            · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hx⟩))
            · exact mem_union.2 (Or.inr hy)
          · intro hz
            rcases mem_union.1 hz with hx | hy
            · exact (mem_inter.1 hx).1
            · exact hYold hy
        have hYeq : L ∩ Y = Y := by
          ext z
          constructor
          · intro hz
            exact (mem_inter.1 hz).2
          · intro hz
            exact mem_inter.2 ⟨hYold hz, hz⟩
        by_cases hex : ∃ i ∈ I,
            pathCoverNumber G ((L ∩ X) ∪ (c i).support) <
              pathCoverNumber G (L ∩ X)
        · obtain ⟨i, hi, hsavei⟩ := hex
          refine ⟨i, hi, Or.inr ?_⟩
          have hDiX : (c i).support ⊆ X := hIin i hi
          have hZY : G.IsCompleteBetween
              ↑((L ∩ X) ∪ (c i).support) ↑Y := by
            intro a ha b hb
            have haX : a ∈ X := by
              rcases mem_union.1 ha with hX0 | hD
              · exact (mem_inter.1 hX0).2
              · exact hDiX hD
            exact hXY haX hb
          have hZne : ((L ∩ X) ∪ (c i).support).Nonempty :=
            hLXne.mono subset_union_left
          have hpZ : pathCoverNumber G ((L ∩ X) ∪ (c i).support) ≤ Y.card := by
            have : pathCoverNumber G (L ∩ X) = Y.card + 1 := by
              simpa [hYeq] using hcrit
            omega
          have hpY : pathCoverNumber G Y ≤
              ((L ∩ X) ∪ (c i).support).card := by
            have hYle : pathCoverNumber G Y ≤ Y.card :=
              pathCoverNumber_le_card (G := G) Y
            have hX0le : Y.card + 1 ≤ (L ∩ X).card := by
              have := pathCoverNumber_le_card (G := G) (L ∩ X)
              have : pathCoverNumber G (L ∩ X) = Y.card + 1 := by
                simpa [hYeq] using hcrit
              omega
            exact hYle.trans
              ((Nat.le_succ Y.card).trans
                (hX0le.trans (card_le_card subset_union_left)))
          have h3 : 3 ≤
              (((L ∩ X) ∪ (c i).support) ∪ Y).card := by
            have hDi3 : 3 ≤ (c i).support.card := (c i).three_le_card_support
            have hsub' : (c i).support ⊆
                ((L ∩ X) ∪ (c i).support) ∪ Y :=
              cycle_support_subset_extension
            exact hDi3.trans (card_le_card hsub')
          obtain ⟨cyc, hsup⟩ :=
            exists_complete_join_cycle hZne hYne hZY hpZ hpY h3
          have hU : ((L ∩ X) ∪ (c i).support) ∪ Y =
              L ∪ (c i).support := by
            rw [union_right_comm, ← hLsplit]
          have hhU : h ∈ ((L ∩ X) ∪ (c i).support) ∪ Y := by
            rw [hU]
            exact mem_union.2 (Or.inl hhL)
          have helig := mem_eligibleSet_of_cycle cyc hsup hhU
          simpa [hU] using helig
        · have hnosaveX : ∀ i ∈ I,
              ¬ pathCoverNumber G ((L ∩ X) ∪ (c i).support) <
                pathCoverNumber G (L ∩ X) := by
            intro i hi h
            exact hex ⟨i, hi, h⟩
          have hpXge :=
            pathCoverNumber_ge_of_no_single_saving c HX hnosaveX
          have hXeq' : unionJ (L ∩ X) c I = X := hXeq
          have hdomX : Y.card < pathCoverNumber G X := by
            have hpX0 : pathCoverNumber G (L ∩ X) = Y.card + 1 := by
              simpa [hYeq] using hcrit
            have hge : pathCoverNumber G (L ∩ X) ≤
                pathCoverNumber G (unionJ (L ∩ X) c I) := hpXge
            have : pathCoverNumber G (L ∩ X) ≤ pathCoverNumber G X := by
              simpa [hXeq'] using hge
            omega
          have hEjoin :=
            eligibleSet_complete_join_dominant hXne hYne hXY hdomX
          have hEX : h ∈ eligibleSet G X := by
            have hEJ' : h ∈ eligibleSet G (X ∪ Y) := by
              simpa [hunion] using hEJ
            simpa [hEjoin] using hEJ'
          have hdomOld : Y.card < pathCoverNumber G (L ∩ X) := by
            have hpX0 : pathCoverNumber G (L ∩ X) = Y.card + 1 := by
              simpa [hYeq] using hcrit
            omega
          have hX0Y0 : G.IsCompleteBetween ↑(L ∩ X) ↑Y := by
            intro a ha b hb
            exact hXY (mem_inter.1 ha).2 hb
          have hFold :=
            ineligibleSet_complete_join_dominant hLXne hYne hX0Y0 hdomOld
          have hhX0 : h ∈ ineligibleSet G (L ∩ X) := by
            have hFold' : ineligibleSet G L =
                Y ∪ ineligibleSet G (L ∩ X) := by
              simpa [← hLsplit] using hFold
            have hhF : h ∈ Y ∪ ineligibleSet G (L ∩ X) := by
              simpa [hFold'] using hF
            rcases mem_union.1 hhF with hhY | hhX
            · exact (Finset.disjoint_left.1 hdisj
                ((mem_eligibleSet_iff (G := G)).1 hEX |>.1) hhY).elim
            · exact hhX
          have hXcard : (unionJ (L ∩ X) c I).card = X.card := by rw [hXeq]
          have hlt : X.card < n := by
            rw [← hcard]
            exact hXlt
          have hEX' : h ∈ eligibleSet G (unionJ (L ∩ X) c I) := by
            simpa [hXeq] using hEX
          obtain ⟨i, hi, hret⟩ :=
            ih X.card hlt (L ∩ X) I hXcard HX hhX0 hEX'
          refine ⟨i, hi, ?_⟩
          have hDiX : (c i).support ⊆ X := hIin i hi
          have hZY : G.IsCompleteBetween
              ↑((L ∩ X) ∪ (c i).support) ↑Y := by
            intro a ha b hb
            have haX : a ∈ X := by
              rcases mem_union.1 ha with hX0 | hD
              · exact (mem_inter.1 hX0).2
              · exact hDiX hD
            exact hXY haX hb
          have hU : (L ∩ X) ∪ Y ∪ (c i).support = L ∪ (c i).support := by
            rw [← hLsplit]
          rcases hret with hsavei | hreli
          · have hZne : ((L ∩ X) ∪ (c i).support).Nonempty :=
              hLXne.mono subset_union_left
            have hpZ : pathCoverNumber G ((L ∩ X) ∪ (c i).support) ≤
                Y.card := by
              have : pathCoverNumber G (L ∩ X) = Y.card + 1 := by
                simpa [hYeq] using hcrit
              omega
            have hpY : pathCoverNumber G Y ≤
                ((L ∩ X) ∪ (c i).support).card := by
              have hYle : pathCoverNumber G Y ≤ Y.card :=
                pathCoverNumber_le_card (G := G) Y
              have hX0le : Y.card + 1 ≤ (L ∩ X).card := by
                have := pathCoverNumber_le_card (G := G) (L ∩ X)
                have : pathCoverNumber G (L ∩ X) = Y.card + 1 := by
                  simpa [hYeq] using hcrit
                omega
              exact hYle.trans
                ((Nat.le_succ Y.card).trans
                  (hX0le.trans (card_le_card subset_union_left)))
            have h3 : 3 ≤
                (((L ∩ X) ∪ (c i).support) ∪ Y).card := by
              have hDi3 : 3 ≤ (c i).support.card :=
                (c i).three_le_card_support
              have hsub' : (c i).support ⊆
                  ((L ∩ X) ∪ (c i).support) ∪ Y :=
                cycle_support_subset_extension
              exact hDi3.trans (card_le_card hsub')
            obtain ⟨cyc, hsup⟩ :=
              exists_complete_join_cycle hZne hYne hZY hpZ hpY h3
            have hU' : ((L ∩ X) ∪ (c i).support) ∪ Y =
                L ∪ (c i).support := by
              rw [union_right_comm, ← hLsplit]
            have hhU : h ∈ ((L ∩ X) ∪ (c i).support) ∪ Y := by
              rw [hU']
              exact mem_union.2 (Or.inl hhL)
            have helig := mem_eligibleSet_of_cycle cyc hsup hhU
            exact Or.inr (by simpa [hU'] using helig)
          · have hZne : ((L ∩ X) ∪ (c i).support).Nonempty :=
              hLXne.mono subset_union_left
            have hU' : ((L ∩ X) ∪ (c i).support) ∪ Y =
                L ∪ (c i).support := by
              rw [union_right_comm, ← hLsplit]
            have hpX0 : pathCoverNumber G (L ∩ X) = Y.card + 1 := by
              simpa [hYeq] using hcrit
            have hYle : pathCoverNumber G Y ≤ Y.card :=
              pathCoverNumber_le_card (G := G) Y
            have hX0card : pathCoverNumber G (L ∩ X) ≤ (L ∩ X).card :=
              pathCoverNumber_le_card (G := G) (L ∩ X)
            have hYltZ : Y.card < ((L ∩ X) ∪ (c i).support).card := by
              have : Y.card + 1 ≤ (L ∩ X).card := by omega
              exact Nat.lt_of_succ_le
                (this.trans (card_le_card subset_union_left))
            have hpY : pathCoverNumber G Y ≤
                ((L ∩ X) ∪ (c i).support).card := hYle.trans hYltZ.le
            have h3 : 3 ≤ (((L ∩ X) ∪ (c i).support) ∪ Y).card := by
              have hDi3 : 3 ≤ (c i).support.card :=
                (c i).three_le_card_support
              exact hDi3.trans (card_le_card cycle_support_subset_extension)
            by_cases hle : pathCoverNumber G ((L ∩ X) ∪ (c i).support) ≤
                Y.card
            · have helig :=
                eligible_of_join_extension hZne hYne hZY hle hpY h3
                  (by simpa [hU'] using mem_union.2 (Or.inl hhL))
              exact Or.inr (by simpa [hU'] using helig)
            · have hdomZ : Y.card <
                  pathCoverNumber G ((L ∩ X) ∪ (c i).support) :=
                Nat.not_le.mp hle
              have hEjoin :=
                eligibleSet_complete_join_dominant hZne hYne hZY hdomZ
              have hreli' : h ∈ eligibleSet G
                  (((L ∩ X) ∪ (c i).support) ∪ Y) := by
                rwa [hEjoin]
              exact Or.inr (by simpa [hU'] using hreli')
  · have hJne : (unionJ L c I).Nonempty := H.L_nonempty.mono subset_union_left
    obtain ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hunion, hnocross, hAlt, hBlt⟩ :=
      Cograph.exists_disjoint_union_on (U := unionJ L c I) hconn hJne
    have hLA := old_side_nonempty_of_no_cross H hdisj hunion hnocross hAne
    have hLB := old_side_nonempty_of_no_cross (A := B) (B := A) H hdisj.symm
      (by rw [union_comm]; exact hunion)
      (fun b hb a ha hab => hnocross a ha b hb hab.symm) hBne
    have hLsplit : L = L ∩ A ∪ L ∩ B := L_split_of_cover hunion
    have hdisjL : Disjoint (L ∩ A) (L ∩ B) :=
      disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right hdisj)
    have hnocrossL : ∀ a ∈ L ∩ A, ∀ b ∈ L ∩ B, ¬ G.Adj a b :=
      fun a ha b hb => hnocross a (mem_inter.1 ha).2 b (mem_inter.1 hb).2
    have hhAB : h ∈ A ∪ B := by
      rw [hunion]
      exact hhJ
    have hEsplit :=
      Cograph.eligibleSet_disjoint_union hdisj hnocross
    rcases mem_union.1 hhAB with hhA | hhB
    · have hIA : (restrictIndex c I A).Nonempty := by
        by_contra hempty
        have hAeqL : unionJ (L ∩ A) c (restrictIndex c I A) = A :=
          unionJ_restrict_eq H hdisj hunion hnocross
        have hIempty : restrictIndex c I A = ∅ :=
          Finset.not_nonempty_iff_eq_empty.1 hempty
        have : unionJ (L ∩ A) c ∅ = L ∩ A := by
          simp [unionJ, selectedSupport]
        have hAeq : A = L ∩ A := by
          simpa [hIempty, this] using hAeqL.symm
        have hEA : h ∈ eligibleSet G A := by
          have : h ∈ eligibleSet G A ∪ eligibleSet G B := by
            have hEJ' : h ∈ eligibleSet G (A ∪ B) := by
              simpa [hunion] using hEJ
            simpa [hEsplit] using hEJ'
          rcases mem_union.1 this with hA | hB
          · exact hA
          · exact (Finset.disjoint_left.1 hdisj hhA
              (eligibleSet_subset (G := G) B hB)).elim
        have hELA : Eligible G (L ∩ A) h := by
          have hEA' : Eligible G A h :=
            ((mem_eligibleSet_iff (G := G)).1 hEA).2
          exact hAeq ▸ hEA'
        have hEL : Eligible G L h := by
          have hiff := Cograph.eligible_disjoint_union_iff (x := h) hdisjL hnocrossL
          have hEunion : Eligible G ((L ∩ A) ∪ (L ∩ B)) h :=
            hiff.2 (Or.inl hELA)
          exact hLsplit ▸ hEunion
        exact hnotEL hEL
      have HA : LocalityHyp c (L ∩ A) (restrictIndex c I A) :=
        H.restrict_side c hdisj hunion hnocross hIA hLA
      have hAeq : unionJ (L ∩ A) c (restrictIndex c I A) = A :=
        unionJ_restrict_eq H hdisj hunion hnocross
      have hFA : h ∈ ineligibleSet G (L ∩ A) := by
        have hiff := Cograph.eligible_disjoint_union_iff (x := h) hdisjL hnocrossL
        have : ¬ (Eligible G (L ∩ A) h ∨ Eligible G (L ∩ B) h) := by
          intro hOr
          have hEunion : Eligible G ((L ∩ A) ∪ (L ∩ B)) h := hiff.2 hOr
          exact hnotEL (hLsplit ▸ hEunion)
        have hnotA : ¬ Eligible G (L ∩ A) h := fun hA => this (Or.inl hA)
        exact (mem_ineligibleSet_iff (G := G)).2
          ⟨mem_inter.2 ⟨hhL, hhA⟩, hnotA⟩
      have hEA : h ∈ eligibleSet G A := by
        have : h ∈ eligibleSet G A ∪ eligibleSet G B := by
          have hEJ' : h ∈ eligibleSet G (A ∪ B) := by
            simpa [hunion] using hEJ
          simpa [hEsplit] using hEJ'
        rcases mem_union.1 this with hA | hB
        · exact hA
        · exact (Finset.disjoint_left.1 hdisj hhA
            (eligibleSet_subset (G := G) B hB)).elim
      have hEA' : h ∈ eligibleSet G
          (unionJ (L ∩ A) c (restrictIndex c I A)) := by
        simpa [hAeq] using hEA
      have hAcard : (unionJ (L ∩ A) c (restrictIndex c I A)).card = A.card := by
        rw [hAeq]
      have hlt : A.card < n := by
        rw [← hcard]
        exact hAlt
      obtain ⟨i, hi, hret⟩ :=
        ih A.card hlt (L ∩ A) (restrictIndex c I A) hAcard HA hFA hEA'
      have hiI : i ∈ I := (mem_restrictIndex (c := c) (I := I) (A := A)).1 hi |>.1
      have hDiA : (c i).support ⊆ A :=
        (mem_restrictIndex (c := c) (I := I) (A := A)).1 hi |>.2
      refine ⟨i, hiI, ?_⟩
      have hdisjNew : Disjoint ((L ∩ A) ∪ (c i).support) (L ∩ B) := by
        refine disjoint_union_left.2 ⟨hdisjL, ?_⟩
        exact disjoint_of_subset_left hDiA
          (disjoint_of_subset_right inter_subset_right hdisj)
      have hnocrossNew :
          ∀ a ∈ (L ∩ A) ∪ (c i).support, ∀ b ∈ L ∩ B, ¬ G.Adj a b := by
        intro a ha b hb
        have haA : a ∈ A := by
          rcases mem_union.1 ha with hLA' | hD
          · exact (mem_inter.1 hLA').2
          · exact hDiA hD
        exact hnocross a haA b (mem_inter.1 hb).2
      rcases hret with hsavei | hreli
      · have hreatt :=
          pathCoverNumber_lt_of_disjoint_reattach hdisjNew hnocrossNew hdisjL
            hnocrossL hsavei
        have hU : L ∩ A ∪ L ∩ B ∪ (c i).support = L ∪ (c i).support := by
          rw [← hLsplit]
        exact Or.inl
          (lt_of_eq_of_lt (congrArg (pathCoverNumber G) hU.symm)
            (lt_of_lt_of_eq hreatt
              (congrArg (pathCoverNumber G) hLsplit.symm)))
      · have hEiff :=
          Cograph.eligible_disjoint_union_iff (x := h) hdisjNew hnocrossNew
        have hEU : Eligible G (((L ∩ A) ∪ (c i).support) ∪ (L ∩ B)) h :=
          hEiff.2 (Or.inl ((mem_eligibleSet_iff (G := G)).1 hreli).2)
        have hU : ((L ∩ A) ∪ (c i).support) ∪ (L ∩ B) =
            L ∪ (c i).support := by
          ext x
          simp only [mem_union]
          constructor
          · intro hx
            rcases hx with (hA | hD) | hB
            · exact Or.inl (mem_inter.1 hA).1
            · exact Or.inr hD
            · exact Or.inl (mem_inter.1 hB).1
          · intro hx
            rcases hx with hLx | hD
            · have hxL : x ∈ L ∩ A ∪ L ∩ B := by
                rw [← hLsplit]
                exact hLx
              rcases mem_union.1 hxL with hA | hB
              · exact Or.inl (Or.inl hA)
              · exact Or.inr hB
            · exact Or.inl (Or.inr hD)
        have hhmem : h ∈ ((L ∩ A) ∪ (c i).support) ∪ (L ∩ B) :=
          hU.symm ▸ mem_union.2 (Or.inl hhL)
        exact Or.inr ((mem_eligibleSet_iff (G := G)).2
          ⟨hU ▸ hhmem, hU ▸ hEU⟩)
    · have hIA : (restrictIndex c I B).Nonempty := by
        by_contra hempty
        have hBeqL : unionJ (L ∩ B) c (restrictIndex c I B) = B :=
          unionJ_restrict_eq (A := B) (B := A) H hdisj.symm
            (by rw [union_comm]; exact hunion)
            (fun b hb a ha hab => hnocross a ha b hb hab.symm)
        have hIempty : restrictIndex c I B = ∅ :=
          Finset.not_nonempty_iff_eq_empty.1 hempty
        have : unionJ (L ∩ B) c ∅ = L ∩ B := by
          simp [unionJ, selectedSupport]
        have hBeq : B = L ∩ B := by
          simpa [hIempty, this] using hBeqL.symm
        have hEB : h ∈ eligibleSet G B := by
          have : h ∈ eligibleSet G A ∪ eligibleSet G B := by
            have hEJ' : h ∈ eligibleSet G (A ∪ B) := by
              simpa [hunion] using hEJ
            simpa [hEsplit] using hEJ'
          rcases mem_union.1 this with hA | hB
          · exact (Finset.disjoint_left.1 hdisj
              (eligibleSet_subset (G := G) A hA) hhB).elim
          · exact hB
        have hELB : Eligible G (L ∩ B) h := by
          have hEB' : Eligible G B h :=
            ((mem_eligibleSet_iff (G := G)).1 hEB).2
          exact hBeq ▸ hEB'
        have hEL : Eligible G L h := by
          have hiff := Cograph.eligible_disjoint_union_iff (x := h) hdisjL hnocrossL
          have hEunion : Eligible G ((L ∩ A) ∪ (L ∩ B)) h :=
            hiff.2 (Or.inr hELB)
          exact hLsplit ▸ hEunion
        exact hnotEL hEL
      have HB : LocalityHyp c (L ∩ B) (restrictIndex c I B) :=
        H.restrict_side (A := B) (B := A) c hdisj.symm
          (by rw [union_comm]; exact hunion)
          (fun b hb a ha hab => hnocross a ha b hb hab.symm) hIA hLB
      have hBeq : unionJ (L ∩ B) c (restrictIndex c I B) = B :=
        unionJ_restrict_eq (A := B) (B := A) H hdisj.symm
          (by rw [union_comm]; exact hunion)
          (fun b hb a ha hab => hnocross a ha b hb hab.symm)
      have hFB : h ∈ ineligibleSet G (L ∩ B) := by
        have hiff := Cograph.eligible_disjoint_union_iff (x := h) hdisjL hnocrossL
        have : ¬ (Eligible G (L ∩ A) h ∨ Eligible G (L ∩ B) h) := by
          intro hOr
          have hEunion : Eligible G ((L ∩ A) ∪ (L ∩ B)) h := hiff.2 hOr
          exact hnotEL (hLsplit ▸ hEunion)
        have hnotB : ¬ Eligible G (L ∩ B) h := fun hB => this (Or.inr hB)
        exact (mem_ineligibleSet_iff (G := G)).2
          ⟨mem_inter.2 ⟨hhL, hhB⟩, hnotB⟩
      have hEB : h ∈ eligibleSet G B := by
        have : h ∈ eligibleSet G A ∪ eligibleSet G B := by
          have hEJ' : h ∈ eligibleSet G (A ∪ B) := by
            simpa [hunion] using hEJ
          simpa [hEsplit] using hEJ'
        rcases mem_union.1 this with hA | hB
        · exact (Finset.disjoint_left.1 hdisj
            (eligibleSet_subset (G := G) A hA) hhB).elim
        · exact hB
      have hEB' : h ∈ eligibleSet G
          (unionJ (L ∩ B) c (restrictIndex c I B)) := by
        simpa [hBeq] using hEB
      have hBcard : (unionJ (L ∩ B) c (restrictIndex c I B)).card = B.card := by
        rw [hBeq]
      have hlt : B.card < n := by
        rw [← hcard]
        exact hBlt
      obtain ⟨i, hi, hret⟩ :=
        ih B.card hlt (L ∩ B) (restrictIndex c I B) hBcard HB hFB hEB'
      have hiI : i ∈ I := (mem_restrictIndex (c := c) (I := I) (A := B)).1 hi |>.1
      have hDiB : (c i).support ⊆ B :=
        (mem_restrictIndex (c := c) (I := I) (A := B)).1 hi |>.2
      refine ⟨i, hiI, ?_⟩
      have hdisjNew : Disjoint ((L ∩ B) ∪ (c i).support) (L ∩ A) := by
        refine disjoint_union_left.2 ⟨hdisjL.symm, ?_⟩
        exact disjoint_of_subset_left hDiB
          (disjoint_of_subset_right inter_subset_right hdisj.symm)
      have hnocrossNew :
          ∀ a ∈ (L ∩ B) ∪ (c i).support, ∀ b ∈ L ∩ A, ¬ G.Adj a b := by
        intro a ha b hb
        have haB : a ∈ B := by
          rcases mem_union.1 ha with hLB' | hD
          · exact (mem_inter.1 hLB').2
          · exact hDiB hD
        exact mt Adj.symm (hnocross b (mem_inter.1 hb).2 a haB)
      have hdisjL' : Disjoint (L ∩ B) (L ∩ A) := hdisjL.symm
      have hnocrossL' : ∀ a ∈ L ∩ B, ∀ b ∈ L ∩ A, ¬ G.Adj a b :=
        fun a ha b hb => mt Adj.symm (hnocrossL b hb a ha)
      rcases hret with hsavei | hreli
      · have hreatt :=
          pathCoverNumber_lt_of_disjoint_reattach hdisjNew hnocrossNew hdisjL'
            hnocrossL' hsavei
        have hU : L ∩ B ∪ L ∩ A ∪ (c i).support = L ∪ (c i).support := by
          rw [union_comm (L ∩ B), ← hLsplit]
        exact Or.inl
          (lt_of_eq_of_lt (congrArg (pathCoverNumber G) hU.symm)
            (lt_of_lt_of_eq hreatt
              (congrArg (pathCoverNumber G)
                ((union_comm (L ∩ B) (L ∩ A)).trans hLsplit.symm))))
      · have hEiff :=
          Cograph.eligible_disjoint_union_iff (x := h) hdisjNew hnocrossNew
        have hEU : Eligible G (((L ∩ B) ∪ (c i).support) ∪ (L ∩ A)) h :=
          hEiff.2 (Or.inl ((mem_eligibleSet_iff (G := G)).1 hreli).2)
        have hU : ((L ∩ B) ∪ (c i).support) ∪ (L ∩ A) =
            L ∪ (c i).support := by
          ext x
          simp only [mem_union]
          constructor
          · intro hx
            rcases hx with (hB | hD) | hA
            · exact Or.inl (mem_inter.1 hB).1
            · exact Or.inr hD
            · exact Or.inl (mem_inter.1 hA).1
          · intro hx
            rcases hx with hLx | hD
            · have hxL : x ∈ L ∩ A ∪ L ∩ B := by
                rw [← hLsplit]
                exact hLx
              rcases mem_union.1 hxL with hA | hB
              · exact Or.inr hA
              · exact Or.inl (Or.inl hB)
            · exact Or.inl (Or.inr hD)
        have hhmem : h ∈ ((L ∩ B) ∪ (c i).support) ∪ (L ∩ A) :=
          hU.symm ▸ mem_union.2 (Or.inl hhL)
        exact Or.inr ((mem_eligibleSet_iff (G := G)).2
          ⟨hU ▸ hhmem, hU ▸ hEU⟩)

lemma exists_single_release (c : ι → GraphCycle G) {L : Finset V} {I : Finset ι}
    {h : V} (H : LocalityHyp c L I)
    (hF : h ∈ ineligibleSet G L)
    (hE : h ∈ eligibleSet G (unionJ L c I)) :
    ∃ i ∈ I,
      pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L ∨
        h ∈ eligibleSet G (L ∪ (c i).support) :=
  exists_single_release_of_card c (unionJ L c I).card L I rfl H hF hE

/-- Exact manuscript locality release: the non-saving witness has equal count. -/
lemma exists_single_release_eq (c : ι → GraphCycle G) {L : Finset V} {I : Finset ι}
    {h : V} (H : LocalityHyp c L I)
    (hF : h ∈ ineligibleSet G L)
    (hE : h ∈ eligibleSet G (unionJ L c I)) :
    ∃ i ∈ I,
      pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L ∨
        (pathCoverNumber G (L ∪ (c i).support) = pathCoverNumber G L ∧
          h ∈ eligibleSet G (L ∪ (c i).support)) := by
  obtain ⟨i, hi, hw⟩ := exists_single_release c H hF hE
  refine ⟨i, hi, ?_⟩
  rcases hw with hs | he
  · exact Or.inl hs
  · by_cases hs : pathCoverNumber G (L ∪ (c i).support) < pathCoverNumber G L
    · exact Or.inl hs
    · exact Or.inr ⟨le_antisymm (pathCoverNumber_union_cycle_le c H hi)
        (Nat.le_of_not_gt hs), he⟩

end Nikoghosyan
