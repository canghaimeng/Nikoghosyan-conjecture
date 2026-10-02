/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Absorption.BoundarySupport

/-!
# Exact old-side saturated cut shift for noYY absorption

Graph-general remainder after deleting the old join child `Y` from an
`X`-ended leftover cover of a no-cross saving block `U0 = X ∪ Y`. Each
leftover run contributes `|SUP ∩ Y| + 1` nonempty `X`-pieces, so
`|X| ≥ q + |Y|`. The complete-join recurrence with `p(U0) ≥ 2` then
forces `p(X) = p(U0) + |Y|` exactly. Combined with no-cross additivity
outside `U0` this yields `p(H \ (A ∪ Y)) = |A| + |Y|`.

The deletion upper bound `p(K - Y) ≤ p(K) + |Y|` is not used for this
old-side identity.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma trimStart_start (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).start = p.walk.snd :=
  rfl

lemma length_walk_trimStart (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).walk.length + 1 = p.walk.length := by
  obtain ⟨x, hadj, q, hq⟩ := Walk.not_nil_iff.1 h
  simp [trimStart, hq]

lemma snd_mem_support_of_not_nil (p : GraphPath G) (h : ¬ p.walk.Nil) :
    p.walk.snd ∈ p.support := by
  have : (p.trimStart h).start ∈ (p.trimStart h).support :=
    (p.trimStart h).start_mem_support
  have hsub : (p.trimStart h).support ⊆ p.support := by
    intro y hy
    have : y ∈ p.support.erase p.start := by
      simpa [support_trimStart p h] using hy
    exact (mem_erase.1 this).2
  simpa [trimStart_start] using hsub this

lemma card_inter_trimStart_of_mem {S : Finset V} {p : GraphPath G}
    (h : ¬ p.walk.Nil) (hs : p.start ∈ S) :
    (p.support ∩ S).card = ((p.trimStart h).support ∩ S).card + 1 := by
  rw [support_trimStart]
  have hmem : p.start ∈ p.support ∩ S :=
    mem_inter.2 ⟨p.start_mem_support, hs⟩
  have hEq : p.support.erase p.start ∩ S = (p.support ∩ S).erase p.start := by
    ext y
    simp [mem_erase, mem_inter]
  rw [hEq, card_erase_of_mem hmem]
  have : 0 < (p.support ∩ S).card := card_pos.2 ⟨p.start, hmem⟩
  omega

lemma card_inter_trimStart_of_not_mem {S : Finset V} {p : GraphPath G}
    (h : ¬ p.walk.Nil) (hs : p.start ∉ S) :
    (p.support ∩ S).card = ((p.trimStart h).support ∩ S).card := by
  rw [support_trimStart, erase_inter]
  have hne : p.start ∉ p.support ∩ S := fun hmem =>
    hs (mem_inter.1 hmem).2
  rw [erase_eq_of_notMem hne]

/-- An `X`-ended original path with no consecutive `Y`-edge has at least
one more `X`-vertex than `Y`-vertices. -/
lemma card_X_ge_succ_card_Y_of_ended_noYY {X Y : Finset V} {p : GraphPath G}
    (hdisj : Disjoint X Y) (hcover : p.support ⊆ X ∪ Y)
    (hs : p.start ∈ X) (hf : p.finish ∈ X) (hno : NoConsecutive Y p) :
    (p.support ∩ Y).card + 1 ≤ (p.support ∩ X).card := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.walk.length = n →
        p.support ⊆ X ∪ Y → p.start ∈ X → p.finish ∈ X → NoConsecutive Y p →
          (p.support ∩ Y).card + 1 ≤ (p.support ∩ X).card)
    p.walk.length ?_ p rfl hcover hs hf hno
  intro n ih p hn hcover hs hf hno
  have hsY : p.start ∉ Y := fun hY => (disjoint_left.1 hdisj hs hY)
  by_cases hnil : p.walk.Nil
  · have hsing : p.support = {p.start} := support_eq_singleton_of_nil p hnil
    have hX : p.support ∩ X = {p.start} := by
      simp [hsing, hs]
    have hYint : p.support ∩ Y = ∅ := by
      simp [hsing, hsY]
    simp [hX, hYint]
  · have hsndP : p.walk.snd ∈ p.support := snd_mem_support_of_not_nil p hnil
    have hsndXY : p.walk.snd ∈ X ∪ Y := hcover hsndP
    have hlen' : (p.trimStart hnil).walk.length < n := by
      have hEq := length_walk_trimStart p hnil
      omega
    have hcover' : (p.trimStart hnil).support ⊆ X ∪ Y :=
      (support_trimStart p hnil).symm ▸
        ((erase_subset p.start p.support).trans hcover)
    have hno' : NoConsecutive Y (p.trimStart hnil) :=
      NoConsecutive_of_edges_subset (edges_trimStart_subset p hnil) hno
    have hf' : (p.trimStart hnil).finish ∈ X := by
      simpa [trimStart_finish] using hf
    by_cases hsndY : p.walk.snd ∈ Y
    · have hnn' : ¬ (p.trimStart hnil).walk.Nil := by
        intro hn'
        have hst : (p.trimStart hnil).start = (p.trimStart hnil).finish :=
          (nil_iff_start_eq_finish _).1 hn'
        have hsnd_eq : p.walk.snd = p.finish := by
          simpa [trimStart_start, trimStart_finish] using hst
        have hfY : p.finish ∉ Y := fun hY => (disjoint_left.1 hdisj hf hY)
        exact hfY (by simpa [hsnd_eq] using hsndY)
      have hsndX : p.walk.snd ∉ X := fun hX =>
        (disjoint_left.1 hdisj hX hsndY)
      have hstart' : (p.trimStart hnil).start ∈ Y := by
        simpa [trimStart_start] using hsndY
      have hsnd2 : (p.trimStart hnil).walk.snd ∉ Y :=
        snd_not_mem_of_NoConsecutive hnn' hstart' hno'
      have hsnd2P : (p.trimStart hnil).walk.snd ∈ (p.trimStart hnil).support :=
        snd_mem_support_of_not_nil (p.trimStart hnil) hnn'
      have hsnd2XY : (p.trimStart hnil).walk.snd ∈ X ∪ Y := hcover' hsnd2P
      have hsnd2X : (p.trimStart hnil).walk.snd ∈ X := by
        rcases mem_union.1 hsnd2XY with h | h
        · exact h
        · exact (hsnd2 h).elim
      have hlen'' : ((p.trimStart hnil).trimStart hnn').walk.length < n := by
        have hEq := length_walk_trimStart (p.trimStart hnil) hnn'
        omega
      have hcover'' : ((p.trimStart hnil).trimStart hnn').support ⊆ X ∪ Y :=
        (support_trimStart (p.trimStart hnil) hnn').symm ▸
          ((erase_subset _ _).trans hcover')
      have hno'' : NoConsecutive Y ((p.trimStart hnil).trimStart hnn') :=
        NoConsecutive_of_edges_subset
          (edges_trimStart_subset (p.trimStart hnil) hnn') hno'
      have hf'' : ((p.trimStart hnil).trimStart hnn').finish ∈ X := by
        simpa [trimStart_finish] using hf'
      have hs'' : ((p.trimStart hnil).trimStart hnn').start ∈ X := by
        simpa [trimStart_start] using hsnd2X
      have ih'' :=
        ih _ hlen'' ((p.trimStart hnil).trimStart hnn') rfl hcover'' hs'' hf'' hno''
      have hXeq :
          (p.support ∩ X).card =
            (((p.trimStart hnil).trimStart hnn').support ∩ X).card + 1 := by
        have hX1 := card_inter_trimStart_of_mem (S := X) hnil hs
        have hX2 := card_inter_trimStart_of_not_mem (S := X) hnn'
          (by simpa [trimStart_start] using hsndX)
        omega
      have hYeq :
          (p.support ∩ Y).card =
            (((p.trimStart hnil).trimStart hnn').support ∩ Y).card + 1 := by
        have hY1 := card_inter_trimStart_of_not_mem (S := Y) hnil hsY
        have hY2 := card_inter_trimStart_of_mem (S := Y) hnn'
          (by simpa [trimStart_start] using hsndY)
        omega
      omega
    · have hsndX : p.walk.snd ∈ X := by
        rcases mem_union.1 hsndXY with h | h
        · exact h
        · exact (hsndY h).elim
      have hs' : (p.trimStart hnil).start ∈ X := by
        simpa [trimStart_start] using hsndX
      have ih' := ih _ hlen' (p.trimStart hnil) rfl hcover' hs' hf' hno'
      have hXeq := card_inter_trimStart_of_mem (S := X) hnil hs
      have hYeq := card_inter_trimStart_of_not_mem (S := Y) hnil hsY
      omega

lemma mem_foldr_support_union {x : V} :
    ∀ l : List (GraphPath G),
      x ∈ l.foldr (fun p acc => p.support ∪ acc) ∅ ↔ ∃ p ∈ l, x ∈ p.support
  | [] => by simp
  | p :: ps => by
    simp [mem_foldr_support_union (l := ps), mem_union]

lemma sum_inter_card_of_pairwise {S : Finset V} :
    ∀ l : List (GraphPath G),
      l.Pairwise (fun p q => Disjoint p.support q.support) →
        (l.map (fun p => (p.support ∩ S).card)).sum =
          (l.foldr (fun p acc => p.support ∪ acc) ∅ ∩ S).card
  | [] => fun _ => by simp
  | p :: ps => fun hl => by
    have hpw := List.pairwise_cons.mp hl
    have ih := sum_inter_card_of_pairwise (S := S) ps hpw.2
    have hEq : ((p :: ps).foldr (fun q acc => q.support ∪ acc) ∅ ∩ S) =
        (p.support ∩ S) ∪ (ps.foldr (fun q acc => q.support ∪ acc) ∅ ∩ S) := by
      ext y
      simp [mem_union, mem_inter]
      tauto
    have hdisj :
        Disjoint (p.support ∩ S)
          (ps.foldr (fun q acc => q.support ∪ acc) ∅ ∩ S) := by
      refine disjoint_left.2 ?_
      intro y hyP hyR
      have hyps : y ∈ ps.foldr (fun q acc => q.support ∪ acc) ∅ :=
        (mem_inter.1 hyR).1
      obtain ⟨q, hq, hyq⟩ := (mem_foldr_support_union (x := y) ps).1 hyps
      have hdisj := hpw.1 q hq
      exact disjoint_left.1 hdisj (mem_inter.1 hyP).1 hyq
    have hcard := card_union_of_disjoint hdisj
    change (p.support ∩ S).card +
        (ps.map (fun q => (q.support ∩ S).card)).sum =
      ((p.support ∪ ps.foldr (fun q acc => q.support ∪ acc) ∅) ∩ S).card
    have hfold : (p :: ps).foldr (fun q acc => q.support ∪ acc) ∅ =
        p.support ∪ ps.foldr (fun q acc => q.support ∪ acc) ∅ := rfl
    rw [ih, ← hfold, hEq, hcard]

lemma pathCover_foldr_support {U : Finset V} (pc : PathCover G U) :
    pc.paths.foldr (fun p acc => p.support ∪ acc) ∅ = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := (mem_foldr_support_union (x := x) pc.paths).1 hx
    exact (pc.mem_iff x).2 ⟨p, hp, hxp⟩
  · intro hx
    obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hx
    exact (mem_foldr_support_union (x := x) pc.paths).2 ⟨p, hp, hxp⟩

lemma sum_inter_card_pathCover {U S : Finset V} (pc : PathCover G U) :
    (pc.paths.map (fun p => (p.support ∩ S).card)).sum = (U ∩ S).card := by
  simpa [pathCover_foldr_support pc] using
    sum_inter_card_of_pairwise (S := S) pc.paths pc.disjoint

lemma map_sum_le_of_forall {α} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : f a ≤ g a := h a (List.mem_cons.2 (Or.inl rfl))
    have hl : ∀ b ∈ l, f b ≤ g b := fun b hb =>
      h b (List.mem_cons.2 (Or.inr hb))
    have := ih hl
    simpa [List.map_cons] using Nat.add_le_add ha this

lemma map_add_one_sum {α} (l : List α) (f : α → ℕ) :
    (l.map (fun a => f a + 1)).sum = (l.map f).sum + l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 : ((a :: l).map (fun x => f x + 1)).sum =
        (f a + 1) + (l.map (fun x => f x + 1)).sum := by
      simp [List.map_cons, List.sum_cons]
    have h2 : ((a :: l).map f).sum = f a + (l.map f).sum := by
      simp [List.map_cons, List.sum_cons]
    simp [h1, h2, ih]
    omega

/-- Summing the per-run `X`/`Y` counts over an `X`-ended leftover cover
gives `|X| ≥ q + |Y|`. -/
lemma card_X_ge_add_of_X_ended_cover {X Y U0 : Finset V}
    (hdisj : Disjoint X Y) (hU0 : U0 = X ∪ Y) (hXU : X ⊆ U0) (hYU : Y ⊆ U0)
    (pc : PathCover G U0)
    (hends : ∀ p ∈ pc.paths, p.start ∈ X ∧ p.finish ∈ X)
    (hno : ∀ p ∈ pc.paths, NoConsecutive Y p) :
    pc.card + Y.card ≤ X.card := by
  have hsumX := sum_inter_card_pathCover (S := X) pc
  have hsumY := sum_inter_card_pathCover (S := Y) pc
  have hXU' : U0 ∩ X = X := inter_eq_right.2 hXU
  have hYU' : U0 ∩ Y = Y := inter_eq_right.2 hYU
  have hle :=
    map_sum_le_of_forall pc.paths
      (fun p => (p.support ∩ Y).card + 1) (fun p => (p.support ∩ X).card)
      (fun p hp => by
        have hsup : p.support ⊆ X ∪ Y := by
          intro z hz
          have hzU : z ∈ U0 := pc.support_subset hp hz
          simpa [hU0] using hzU
        exact card_X_ge_succ_card_Y_of_ended_noYY hdisj hsup (hends p hp).1
          (hends p hp).2 (hno p hp))
  have hsumY1 := map_add_one_sum pc.paths (fun p => (p.support ∩ Y).card)
  have : Y.card + pc.card ≤ X.card := by
    simpa [hsumX, hsumY, hXU', hYU', PathCover.card, hsumY1] using hle
  omega

/-- Join recurrence: `p(U0) ≥ 2` and `|X| ≥ q + |Y|` force the exact
dominant-child identity `p(X) = p(U0) + |Y|`. -/
lemma pathCoverNumber_X_eq_add_card_Y {X Y U0 : Finset V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hdisj : Disjoint X Y)
    (hU0 : U0 = X ∪ Y)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hpU0 : 2 ≤ pathCoverNumber G U0)
    (hcard : pathCoverNumber G U0 + Y.card ≤ X.card) :
    pathCoverNumber G X = pathCoverNumber G U0 + Y.card := by
  have hj := pathCoverNumber_complete_join hXne hYne hjoin
  have hU0eq : pathCoverNumber G U0 =
      max 1 (max (pathCoverNumber G X - Y.card)
        (pathCoverNumber G Y - X.card)) := by
    simpa [hU0] using hj
  have hpY : pathCoverNumber G Y ≤ Y.card := pathCoverNumber_le_card (G := G) Y
  have hother : pathCoverNumber G Y - X.card = 0 := by
    have : pathCoverNumber G Y ≤ X.card :=
      hpY.trans (le_trans (Nat.le_add_left Y.card _) hcard)
    exact Nat.sub_eq_zero_of_le this
  have hU0' : pathCoverNumber G U0 = max 1 (pathCoverNumber G X - Y.card) := by
    simpa [hother] using hU0eq
  have hsub_pos : 1 ≤ pathCoverNumber G X - Y.card := by
    by_contra h
    have h0 : pathCoverNumber G X - Y.card = 0 := by omega
    have : pathCoverNumber G U0 = 1 := by simpa [hU0', h0]
    omega
  have hsub : pathCoverNumber G U0 = pathCoverNumber G X - Y.card := by
    rwa [max_eq_right hsub_pos] at hU0'
  have hle : pathCoverNumber G X ≤ pathCoverNumber G U0 + Y.card := by
    have hXeq : U0 \ Y = X := by
      rw [hU0, union_sdiff_eq_left_of_disjoint hdisj]
    have hYsub : Y ⊆ U0 := by
      rw [hU0]; exact subset_union_right
    have := pathCoverNumber_sdiff_le (G := G) U0 Y hYsub
    simpa [hXeq] using this
  omega

/-- Exact old-side remainder: no-cross additivity outside `U0` together
with the join identity on `U0 = X ∪ Y` yields
`p((W \ Y)) = p(W) + |Y|`. -/
lemma pathCoverNumber_sdiff_Y_eq_add_of_nocross_join
    {W U0 X Y : Finset V}
    (hU0 : U0 ⊆ W) (hX : X ⊆ U0) (hY : Y ⊆ U0)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hdisj : Disjoint X Y)
    (hcover : X ∪ Y = U0)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hnocross : ∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b)
    (hpU0 : 2 ≤ pathCoverNumber G U0)
    (hcard : pathCoverNumber G U0 + Y.card ≤ X.card) :
    pathCoverNumber G (W \ Y) = pathCoverNumber G W + Y.card := by
  have hXY : U0 = X ∪ Y := hcover.symm
  have hpX := pathCoverNumber_X_eq_add_card_Y (U0 := U0) hXne hYne hdisj hXY
    hjoin hpU0 hcard
  have hdisjU : Disjoint U0 (W \ U0) := disjoint_sdiff
  have hW : U0 ∪ (W \ U0) = W := union_sdiff_of_subset hU0
  have hpW :
      pathCoverNumber G W =
        pathCoverNumber G U0 + pathCoverNumber G (W \ U0) := by
    simpa [hW] using pathCoverNumber_disjoint_union (G := G) hdisjU hnocross
  have hXeq : U0 \ Y = X := by
    rw [hXY, union_sdiff_eq_left_of_disjoint hdisj]
  have hWY : W \ Y = X ∪ (W \ U0) := by
    ext z
    constructor
    · intro hz
      have hzW : z ∈ W := (mem_sdiff.1 hz).1
      have hzY : z ∉ Y := (mem_sdiff.1 hz).2
      by_cases hzU : z ∈ U0
      · refine mem_union.2 (Or.inl ?_)
        simpa [hXeq] using (mem_sdiff.2 ⟨hzU, hzY⟩ : z ∈ U0 \ Y)
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hzW, hzU⟩))
    · intro hz
      rcases mem_union.1 hz with hzX | hzR
      · have hzU : z ∈ U0 := hX hzX
        have hzY : z ∉ Y := fun h => (disjoint_left.1 hdisj hzX h)
        exact mem_sdiff.2 ⟨hU0 hzU, hzY⟩
      · have hzW : z ∈ W := (mem_sdiff.1 hzR).1
        have hzU : z ∉ U0 := (mem_sdiff.1 hzR).2
        exact mem_sdiff.2 ⟨hzW, fun hzY => hzU (hY hzY)⟩
  have hncX : ∀ a ∈ X, ∀ b ∈ W \ U0, ¬ G.Adj a b := fun a ha =>
    hnocross a (hX ha)
  have hdisjX : Disjoint X (W \ U0) :=
    disjoint_of_subset_left hX disjoint_sdiff
  have hpWY :
      pathCoverNumber G (W \ Y) =
        pathCoverNumber G X + pathCoverNumber G (W \ U0) := by
    simpa [hWY] using pathCoverNumber_disjoint_union (G := G) hdisjX hncX
  omega

lemma leftoverCountIn_eq_pathCoverNumber_of_min_nocross
    {W U0 : Finset V} (hU0 : U0 ⊆ W)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b)
    (pc : PathCover G W) (hmin : pc.card = pathCoverNumber G W) :
    leftoverCountIn pc U0 = pathCoverNumber G U0 := by
  have hunion : U0 ∪ (W \ U0) = W := union_sdiff_of_subset hU0
  let pc' : PathCover G (U0 ∪ (W \ U0)) := pc.cast hunion.symm
  have hmin' : pc'.card = pathCoverNumber G (U0 ∪ (W \ U0)) := by
    rw [PathCover.cast_card, hunion]
    exact hmin
  have hsplit :=
    splitLeft_card_eq_of_min (disjoint_sdiff : Disjoint U0 (W \ U0))
      hnocross pc' hmin'
  have hfilt : leftoverCountIn pc U0 = (PathCover.splitLeft
      (disjoint_sdiff : Disjoint U0 (W \ U0)) hnocross pc').card := by
    have hp : pc'.paths = pc.paths := PathCover.cast_paths pc hunion.symm
    simp [leftoverCountIn, PathCover.splitLeft, PathCover.card, hp]
  exact hfilt.trans hsplit

/-- Old-seam cycle boundary edges that survive on a path remain
`W`-boundary edges for `W = U0 ∪ D`. -/
lemma retained_seams_subset_W_boundary {H D U0 : Finset V}
    (c : GraphCycle G) (hc : c.support = H) (hdisj : Disjoint H D)
    (_hU0 : U0 ⊆ H) {p : GraphPath G} :
    c.boundaryEdges U0 ∩ p.edges ⊆ p.boundaryEdges (U0 ∪ D) := by
  intro e he
  obtain ⟨heS, heP⟩ := mem_inter.1 he
  obtain ⟨heC, hstr⟩ := GraphCycle.mem_boundaryEdges_iff.1 heS
  refine GraphPath.mem_boundaryEdges_iff.2 ⟨heP, ?_⟩
  obtain ⟨⟨x, hxe, hxU⟩, ⟨y, hye, hyU⟩⟩ := hstr
  have hyH : y ∈ H := by
    have : y ∈ c.support := by
      simpa [GraphCycle.support] using
        List.mem_toFinset.2
          (c.walk.mem_support_of_mem_edges (GraphCycle.mem_edges_iff.1 heC) hye)
    simpa [hc] using this
  have hyD : y ∉ D := fun hD => (disjoint_left.1 hdisj hyH hD)
  have hxW : x ∈ U0 ∪ D := mem_union.2 (Or.inl hxU)
  have hyW : y ∉ U0 ∪ D := by
    intro h
    rcases mem_union.1 h with hU | hD
    · exact hyU hU
    · exact hyD hD
  exact ⟨⟨x, hxe, hxW⟩, ⟨y, hye, hyW⟩⟩

lemma cycle_boundary_U0_eq_W {H D U0 : Finset V}
    (c : GraphCycle G) (hc : c.support = H) (hdisj : Disjoint H D)
    (_hU0 : U0 ⊆ H) :
    c.boundaryEdges (U0 ∪ D) = c.boundaryEdges U0 := by
  ext e
  simp only [GraphCycle.mem_boundaryEdges_iff]
  constructor
  · intro ⟨heC, hstr⟩
    refine ⟨heC, ?_⟩
    obtain ⟨⟨x, hxe, hxW⟩, ⟨y, hye, hyW⟩⟩ := hstr
    have hxH : x ∈ H := by
      have : x ∈ c.support := by
        simpa [GraphCycle.support] using
          List.mem_toFinset.2
            (c.walk.mem_support_of_mem_edges (GraphCycle.mem_edges_iff.1 heC) hxe)
      simpa [hc] using this
    have hxD : x ∉ D := fun hD => (disjoint_left.1 hdisj hxH hD)
    have hxU : x ∈ U0 := by
      rcases mem_union.1 hxW with h | h
      · exact h
      · exact (hxD h).elim
    have hyU : y ∉ U0 := fun h => hyW (mem_union.2 (Or.inl h))
    exact ⟨⟨x, hxe, hxU⟩, ⟨y, hye, hyU⟩⟩
  · intro ⟨heC, hstr⟩
    refine ⟨heC, ?_⟩
    obtain ⟨⟨x, hxe, hxU⟩, ⟨y, hye, hyU⟩⟩ := hstr
    have hyH : y ∈ H := by
      have : y ∈ c.support := by
        simpa [GraphCycle.support] using
          List.mem_toFinset.2
            (c.walk.mem_support_of_mem_edges (GraphCycle.mem_edges_iff.1 heC) hye)
      simpa [hc] using this
    have hyD : y ∉ D := fun hD => (disjoint_left.1 hdisj hyH hD)
    exact ⟨⟨x, hxe, mem_union.2 (Or.inl hxU)⟩,
      ⟨y, hye, fun h => (mem_union.1 h).elim hyU hyD⟩⟩

lemma eligibleSet_suppressInternal {U A' : Finset V} (hU : Disjoint U A') :
    eligibleSet (suppressInternal G A') U = eligibleSet G U := by
  ext x
  constructor
  · intro hx
    rw [mem_eligibleSet_iff] at hx
    obtain ⟨pc, hpc, p, hp, hend⟩ := hx.2
    refine (mem_eligibleSet_iff (G := G)).2 ⟨hx.1, ?_⟩
    refine ⟨PathCover.ofSuppressInternal (G := G) pc, ?_,
      GraphPath.ofSuppressInternal (G := G) p, ?_, ?_⟩
    · simpa [PathCover.ofSuppressInternal_card,
        pathCoverNumber_suppressInternal (G := G) hU] using hpc
    · exact List.mem_map.2 ⟨p, hp, rfl⟩
    · simpa [GraphPath.ofSuppressInternal_start,
        GraphPath.ofSuppressInternal_finish] using hend
  · intro hx
    rw [mem_eligibleSet_iff] at hx
    obtain ⟨pc, hpc, p, hp, hend⟩ := hx.2
    have hd : Disjoint p.support A' :=
      disjoint_of_subset_left (pc.support_subset hp) hU
    refine (mem_eligibleSet_iff (G := suppressInternal G A')).2 ⟨hx.1, ?_⟩
    refine ⟨pc.toSuppressInternal (G := G) hU, ?_,
      p.toSuppressInternal (G := G) hd, ?_, ?_⟩
    · simpa [PathCover.toSuppressInternal_card,
        pathCoverNumber_suppressInternal (G := G) hU] using hpc
    · change p.transferEdges _ ∈ (pc.transferEdges _).paths
      exact List.mem_map.2 ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩
    · simpa [GraphPath.toSuppressInternal_start,
        GraphPath.toSuppressInternal_finish] using hend

lemma completeJoin_adj_suppressInternal_W {H D A U0 X Y : Finset V}
    (hA : A ⊆ H) (hU0 : U0 ⊆ H \ A) (hX : X ⊆ U0 ∪ D)
    (hdisjXY : Disjoint X Y) (hdisjHD : Disjoint H D)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    {y x : V} (hy : y ∈ Y) (hx : x ∈ X) :
    (suppressInternal G (A ∪ Y)).Adj y x :=
  (adj_suppressInternal_iff (G := G) (A' := A ∪ Y)).2
    ⟨(hjoin hx hy).symm, fun hboth => by
      have hxAY : x ∈ A ∪ Y := hboth.2
      rcases mem_union.1 hxAY with hxA | hxY
      · have hxH : x ∈ H := hA hxA
        have hxD : x ∉ D := fun hD => disjoint_left.1 hdisjHD hxH hD
        have hxU0 : x ∈ U0 := by
          rcases mem_union.1 (hX hx) with h | h
          · exact h
          · exact (hxD h).elim
        exact (mem_sdiff.1 (hU0 hxU0)).2 hxA
      · exact disjoint_left.1 hdisjXY hx hxY⟩

lemma path_boundary_W_outside_end_mem_A {H D A U0 : Finset V}
    {G' : SimpleGraph V} (hLE : G' ≤ G)
    (hA : A ⊆ H) (hU0 : U0 ⊆ H \ A) (hdisjHD : Disjoint H D)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    (hnorestD : ∀ a ∈ D, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    {p' : GraphPath G'} (hp' : p'.support = H ∪ D)
    {e : Sym2 V} (he : e ∈ p'.boundaryEdges (U0 ∪ D)) :
    ∃ a ∈ A, a ∈ e := by
  obtain ⟨heP, hstr⟩ := GraphPath.mem_boundaryEdges_iff.1 he
  obtain ⟨x, hxe, hxW, _⟩ := existsUnique_U0_end hstr
  refine Sym2.inductionOn e (fun u v heP hstr hxe hxW => ?_) heP hstr hxe hxW
  have hadj : G.Adj u v := hLE <| by
    simpa [SimpleGraph.mem_edgeSet] using p'.edges_subset_edgeSet _ heP
  have huP : u ∈ p'.support := mem_support_of_mem_edge heP (by simp)
  have hvP : v ∈ p'.support := mem_support_of_mem_edge heP (by simp)
  have huHD : u ∈ H ∪ D := by simpa [hp'] using huP
  have hvHD : v ∈ H ∪ D := by simpa [hp'] using hvP
  have hrest {z : V} (hzHD : z ∈ H ∪ D) (hzW : z ∉ U0 ∪ D) :
      z ∈ (H \ A) \ U0 ∨ z ∈ A := by
    have hzD : z ∉ D := fun h => hzW (mem_union.2 (Or.inr h))
    have hzH : z ∈ H := by
      rcases mem_union.1 hzHD with h | h
      · exact h
      · exact (hzD h).elim
    have hzU0 : z ∉ U0 := fun h => hzW (mem_union.2 (Or.inl h))
    by_cases hzA : z ∈ A
    · exact Or.inr hzA
    · exact Or.inl (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hzH, hzA⟩, hzU0⟩)
  rcases (show u = x ∨ v = x from by
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl) with rfl | rfl
  · have hvW : v ∉ U0 ∪ D := fun hvW =>
      (endsStraddle_iff.1 hstr) (propext ⟨fun _ => hvW, fun _ => hxW⟩)
    rcases hrest hvHD hvW with hvK | hvA
    · rcases mem_union.1 hxW with hxU | hxD
      · exact (hnocross u hxU v hvK hadj).elim
      · exact (hnorestD u hxD v hvK hadj).elim
    · exact ⟨v, hvA, by simp⟩
  · have huW : u ∉ U0 ∪ D := fun huW =>
      (endsStraddle_iff.1 hstr) (propext ⟨fun _ => hxW, fun _ => huW⟩)
    rcases hrest huHD huW with huK | huA
    · rcases mem_union.1 hxW with hxU | hxD
      · exact (hnocross v hxU u huK hadj.symm).elim
      · exact (hnorestD v hxD u huK hadj.symm).elim
    · exact ⟨u, huA, by simp⟩

/-- One prefix rotation of a `G'`-path on support `H ∪ D` that starts in
`Y`, using retained old seams as the `W = U0 ∪ D` three-bound. -/
lemma exists_one_return_rotate_W {H D A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = H)
    (hA : A ⊆ H) (hU0 : U0 ⊆ H \ A) (hX : X ⊆ U0 ∪ D) (hY : Y ⊆ U0)
    (hdisjXY : Disjoint X Y) (hdisjHD : Disjoint H D)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    (hnorestD : ∀ a ∈ D, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    {pH : GraphPath G} (hpH : pH.support = H) (hsH : pH.start ∈ A)
    (hedges : pH.edges ∪ {s(pH.finish, pH.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.finish ∈ X)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    {p' : GraphPath (suppressInternal G (A ∪ Y))}
    {c' : GraphCycle (suppressInternal G (A ∪ Y))}
    (hp' : p'.support = H ∪ D) (hc' : c'.support = H)
    (hP : p'.ProtectedAt c' A) (hedges' : c'.edges = c.edges)
    (hsY : p'.start ∈ Y) :
    ∃ q : GraphPath (suppressInternal G (A ∪ Y)),
      q.support = H ∪ D ∧ q.start ∈ A ∧ q.finish = p'.finish ∧
        q.start ≠ q.finish ∧ q.ProtectedAt c' A := by
  let G' := suppressInternal G (A ∪ Y)
  have hLE : G' ≤ G := suppressInternal_le G (A ∪ Y)
  have hdisjAY : Disjoint A Y := disjoint_of_subset_right hY (disjoint_A_U0 hU0)
  have hAH : A ⊆ (p'.ofLE hLE).support := by
    intro a ha
    simpa [GraphPath.ofLE_support, hp'] using mem_union.2 (Or.inl (hA ha))
  have hPG : (p'.ofLE hLE).ProtectedAt c A :=
    ProtectedAt_ofLE_edges hLE hedges' hP
  have h2p : 2 ≤ (p'.ofLE hLE).support.card := by
    have h3 : 3 ≤ H.card := by simpa [hc] using c.three_le_card_support
    have : H ⊆ (p'.ofLE hLE).support := by
      intro z hz
      simpa [GraphPath.ofLE_support, hp'] using mem_union.2 (Or.inl hz)
    exact (le_trans (by decide : (2 : ℕ) ≤ 3) h3).trans (card_le_card this)
  have h3ret :=
    three_le_retained_cycle_seams (c := c) hc hA hU0 hY hnocross hdisjAY
      hAH hPG (by simpa [GraphPath.ofLE_start] using hsY) h4 h2p
  have hsub :=
    retained_seams_subset_W_boundary (c := c) hc hdisjHD
      (hU0.trans sdiff_subset) (p := p'.ofLE hLE)
  have h3W : 3 ≤ ((p'.ofLE hLE).boundaryEdges (U0 ∪ D)).card :=
    h3ret.trans (card_le_card hsub)
  have h2 : 2 ≤ (p'.boundaryEdges (U0 ∪ D)).card := by
    have : (p'.ofLE hLE).boundaryEdges (U0 ∪ D) = p'.boundaryEdges (U0 ∪ D) := by
      simp [GraphPath.boundaryEdges, GraphPath.ofLE_edges]
    simpa [this] using le_trans (by decide : (2 : ℕ) ≤ 3) h3W
  have hsW : p'.start ∈ U0 ∪ D := mem_union.2 (Or.inl (hY hsY))
  have hAout : Disjoint A (U0 ∪ D) := by
    refine disjoint_union_right.2 ⟨disjoint_A_U0 hU0, ?_⟩
    exact disjoint_of_subset_left hA hdisjHD
  have hYU : Y ⊆ U0 ∪ D := hY.trans subset_union_left
  have hjoin' : ∀ y ∈ Y, ∀ z ∈ X, G'.Adj y z := fun y hy z hx =>
    completeJoin_adj_suppressInternal_W hA hU0 hX hdisjXY hdisjHD hjoin hy hx
  have henterX : ∀ i, i < p'.walk.length → p'.walk.getVert i ∉ U0 ∪ D →
      p'.walk.getVert (i + 1) ∈ U0 ∪ D → p'.walk.getVert (i + 1) ∈ X := by
    intro i hi h0 h1
    have he : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈ p'.edges :=
      p'.crossingEdge_mem_edges hi
    have hbd : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈
        p'.boundaryEdges (U0 ∪ D) :=
      GraphPath.mem_boundaryEdges_iff.2 ⟨he, endsStraddle_of_outside_inside h0 h1⟩
    obtain ⟨a, haA, hae⟩ :=
      path_boundary_W_outside_end_mem_A (G := G) hLE hA hU0 hdisjHD hnocross
        hnorestD hp' hbd
    have heA : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈ p'.AIncident A :=
      mem_AIncident_iff.2 ⟨he, a, haA, hae⟩
    have heC : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈ c.edges := by
      have : _ ∈ c'.edges := hP heA
      simpa [hedges'] using this
    have haW : a ∉ U0 ∪ D := disjoint_left.1 hAout haA
    have heq := cycle_boundary_eq_ax
      (endsStraddle_of_outside_inside (U0 := U0 ∪ D) h0 h1) hae haW
      (by simp) h1
    have hxU0 : p'.walk.getVert (i + 1) ∈ U0 := by
      have hxH : p'.walk.getVert (i + 1) ∈ H := by
        have : a ∈ c.support := by
          simpa [hc] using hA haA
        -- the other end of a cycle edge is in H
        have hmem : p'.walk.getVert (i + 1) ∈ s(a, p'.walk.getVert (i + 1)) := by simp
        have : p'.walk.getVert (i + 1) ∈ c.support := by
          have heq' : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) = s(a, p'.walk.getVert (i + 1)) := heq
          have : p'.walk.getVert (i + 1) ∈ s(p'.walk.getVert i, p'.walk.getVert (i + 1)) := by simp
          have hC : p'.walk.getVert (i + 1) ∈ c.support := by
            simpa [GraphCycle.support, hc] using
              List.mem_toFinset.2
                (c.walk.mem_support_of_mem_edges
                  (GraphCycle.mem_edges_iff.1 heC) (by
                    simpa [heq] using this))
          exact hC
        simpa [hc] using this
      have hxD : p'.walk.getVert (i + 1) ∉ D := fun hD =>
        disjoint_left.1 hdisjHD hxH hD
      rcases mem_union.1 h1 with hU | hD
      · exact hU
      · exact (hxD hD).elim
    have hstrU0 : endsStraddle s(a, p'.walk.getVert (i + 1)) U0 :=
      endsStraddle_of_outside_inside
        (fun h => (disjoint_left.1 (disjoint_A_U0 hU0) haA h)) hxU0
    have heCU0 : s(a, p'.walk.getVert (i + 1)) ∈ c.boundaryEdges U0 :=
      GraphCycle.mem_boundaryEdges_iff.2 ⟨by simpa [heq] using heC, hstrU0⟩
    exact cycle_boundary_U0_end_mem_X (Y := Y) c hc hU0 hpH hsH hedges hnocross
      hstay hstartX hfinX heCU0 (by simp) hxU0
  have henterA : ∀ i, i < p'.walk.length → p'.walk.getVert i ∉ U0 ∪ D →
      p'.walk.getVert (i + 1) ∈ U0 ∪ D → p'.walk.getVert i ∈ A := by
    intro i hi h0 h1
    have he : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈ p'.edges :=
      p'.crossingEdge_mem_edges hi
    have hbd : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈
        p'.boundaryEdges (U0 ∪ D) :=
      GraphPath.mem_boundaryEdges_iff.2 ⟨he, endsStraddle_of_outside_inside h0 h1⟩
    obtain ⟨a, haA, hae⟩ :=
      path_boundary_W_outside_end_mem_A (G := G) hLE hA hU0 hdisjHD hnocross
        hnorestD hp' hbd
    have haW : a ∉ U0 ∪ D := disjoint_left.1 hAout haA
    have heq := cycle_boundary_eq_ax
      (endsStraddle_of_outside_inside (U0 := U0 ∪ D) h0 h1) hae haW
      (by simp) h1
    rcases (Sym2.eq_iff.mp heq) with ⟨rfl, _⟩ | ⟨hvu, _⟩
    · exact haA
    · exact (h0 (by simpa [hvu] using h1)).elim
  obtain ⟨i, F, hyx, hi, h0, h1, haA, hxX, hst, hsup, hProt⟩ :=
    exists_returnRotate (p := p') (U0 := U0 ∪ D) hsW h2 (A := A) (X := X)
      (Y := Y) (c := c') hjoin' hsY hP hAout hYU hX henterX henterA
  have hne : (F.rotate hyx).start ≠ (F.rotate hyx).finish :=
    F.rotate_start_ne_finish hyx
  refine ⟨F.rotate hyx, by simpa [hsup] using hp', ?_, ?_, hne, hProt⟩
  · simpa [hst] using haA
  · simpa [F.rotate_finish hyx]

lemma exists_restore_A_ends_W {H D A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = H)
    (hA : A ⊆ H) (hU0 : U0 ⊆ H \ A) (hX : X ⊆ U0 ∪ D) (hY : Y ⊆ U0)
    (hdisjXY : Disjoint X Y) (hdisjHD : Disjoint H D) (hYne : Y.Nonempty)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    (hnorestD : ∀ a ∈ D, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    {pH : GraphPath G} (hpH : pH.support = H) (hsH : pH.start ∈ A)
    (hedges : pH.edges ∪ {s(pH.finish, pH.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.finish ∈ X)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    {p' : GraphPath (suppressInternal G (A ∪ Y))}
    {c' : GraphCycle (suppressInternal G (A ∪ Y))}
    (hp' : p'.support = H ∪ D) (hc' : c'.support = H)
    (hs' : p'.start ∈ A ∪ Y) (hf' : p'.finish ∈ A ∪ Y)
    (hne' : p'.start ≠ p'.finish)
    (hP' : p'.ProtectedAt c' (A ∪ Y))
    (hedges' : c'.edges = c.edges) :
    ∃ q : GraphPath (suppressInternal G (A ∪ Y)),
      q.support = H ∪ D ∧ q.start ∈ A ∧ q.finish ∈ A ∧
        q.start ≠ q.finish ∧ q.ProtectedAt c' A := by
  have hsub : A ⊆ A ∪ Y := subset_union_left
  have hP : p'.ProtectedAt c' A := hP'.mono_set hsub
  by_cases hboth : p'.start ∈ A ∧ p'.finish ∈ A
  · exact ⟨p', hp', hboth.1, hboth.2, hne', hP⟩
  have hYend : p'.start ∈ Y ∨ p'.finish ∈ Y := by
    have hst : p'.start ∈ A ∨ p'.start ∈ Y := mem_union.1 hs'
    have hfn : p'.finish ∈ A ∨ p'.finish ∈ Y := mem_union.1 hf'
    rcases hst with hstA | hstY
    · rcases hfn with hfnA | hfnY
      · exact (hboth ⟨hstA, hfnA⟩).elim
      · exact Or.inr hfnY
    · exact Or.inl hstY
  let q0 : GraphPath (suppressInternal G (A ∪ Y)) :=
    if h : p'.start ∈ Y then p' else p'.reverse
  have hq0sup : q0.support = H ∪ D := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h] using hp'
    · simpa [q0, h, GraphPath.support_reverse] using hp'
  have hq0stY : q0.start ∈ Y := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h]
    · have hfY : p'.finish ∈ Y := hYend.resolve_left h
      simpa [q0, h, GraphPath.reverse] using hfY
  have hq0P : q0.ProtectedAt c' A := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h] using hP
    · simpa [q0, h, ProtectedAt_reverse] using hP
  have hq0fin_mem : q0.finish ∈ A ∪ Y := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h] using hf'
    · simpa [q0, h, GraphPath.reverse] using hs'
  obtain ⟨q1, hq1sup, hq1st, hq1fin, hq1ne, hq1P⟩ :=
    exists_one_return_rotate_W (Y := Y) c hc hA hU0 hX hY hdisjXY hdisjHD
      hjoin hnocross hnorestD hpH hsH hedges hstay hstartX hfinX h4 hq0sup hc'
      hq0P hedges' hq0stY
  by_cases hfA : q1.finish ∈ A
  · exact ⟨q1, hq1sup, hq1st, hfA, hq1ne, hq1P⟩
  have hfY : q1.finish ∈ Y := by
    have : q1.finish ∈ A ∪ Y := by simpa [hq1fin] using hq0fin_mem
    exact (mem_union.1 this).resolve_left hfA
  let qR := q1.reverse
  have hRsup : qR.support = H ∪ D := by
    simpa [qR, GraphPath.support_reverse] using hq1sup
  have hRstY : qR.start ∈ Y := by simpa [qR, GraphPath.reverse] using hfY
  have hRP : qR.ProtectedAt c' A := (ProtectedAt_reverse q1 c' A).2 hq1P
  obtain ⟨q2, hq2sup, hq2st, hq2fin, hq2ne, hq2P⟩ :=
    exists_one_return_rotate_W (Y := Y) c hc hA hU0 hX hY hdisjXY hdisjHD
      hjoin hnocross hnorestD hpH hsH hedges hstay hstartX hfinX h4 hRsup hc'
      hRP hedges' hRstY
  refine ⟨q2, hq2sup, hq2st, ?_, hq2ne, hq2P⟩
  simpa [hq2fin, qR, GraphPath.reverse] using hq1st

lemma exists_lift_restored_W {H D A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = H)
    (hA : A ⊆ H) (hU0 : U0 ⊆ H \ A) (hX : X ⊆ U0 ∪ D) (hY : Y ⊆ U0)
    (hdisjXY : Disjoint X Y) (hdisjHD : Disjoint H D) (hYne : Y.Nonempty)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    (hnorestD : ∀ a ∈ D, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    {pH : GraphPath G} (hpH : pH.support = H) (hsH : pH.start ∈ A)
    (hedges : pH.edges ∪ {s(pH.finish, pH.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A pH, Q.start ∈ U0 → Q.finish ∈ X)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    {p' : GraphPath (suppressInternal G (A ∪ Y))}
    {c' : GraphCycle (suppressInternal G (A ∪ Y))}
    (hp' : p'.support = H ∪ D) (hc' : c'.support = H)
    (hs' : p'.start ∈ A ∪ Y) (hf' : p'.finish ∈ A ∪ Y)
    (hne' : p'.start ≠ p'.finish)
    (hP' : p'.ProtectedAt c' (A ∪ Y))
    (hedges' : c'.edges = c.edges) :
    ∃ q : GraphPath G,
      q.support = H ∪ D ∧ q.start ∈ A ∧ q.finish ∈ A ∧
        q.start ≠ q.finish ∧ q.ProtectedAt c A := by
  obtain ⟨r, hrsup, hrst, hrfin, hrne, hrP⟩ :=
    exists_restore_A_ends_W (Y := Y) c hc hA hU0 hX hY hdisjXY hdisjHD hYne
      hjoin hnocross hnorestD hpH hsH hedges hstay hstartX hfinX h4 hp' hc'
      hs' hf' hne' hP' hedges'
  let hLE := suppressInternal_le G (A ∪ Y)
  refine ⟨r.ofLE hLE, ?_, ?_, ?_, ?_, ProtectedAt_ofLE_edges hLE hedges' hrP⟩
  · simpa [GraphPath.ofLE_support] using hrsup
  · simpa [GraphPath.ofLE_start] using hrst
  · simpa [GraphPath.ofLE_finish] using hrfin
  · simpa [GraphPath.ofLE_start, GraphPath.ofLE_finish] using hrne

end Cograph
end Nikoghosyan
