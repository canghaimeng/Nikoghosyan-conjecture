/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProtectedIncidence
import Nikoghosyan.Cograph.PathCoverUnion
import Nikoghosyan.Cograph.PathCoverJoin
import Nikoghosyan.Cograph.Decomposition

/-!
# Saving component of a leftover cover under strict slack

Manuscript `prof:thm:protected`, component step. After the A–A cycle-edge
base and the same-sign leftover switches, an opened spanning path with no
consecutive A-edge has exactly `|A|` leftover runs covering `K = U \ A`.
Grouped path counts and disjoint-union additivity of `p` produce an actual
connected component `U0 ⊆ K` with `p(U0) < q0` and `q0 ≥ 2`. This module
does not supply a saving-component certificate in a final sufficient
signature; it constructs `U0` from the leftover cover.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Filter-length of leftover runs whose start lies in `U0`. -/
noncomputable def leftoverCountIn {U : Finset V} (pc : PathCover G U)
    (U0 : Finset V) : ℕ :=
  (pc.paths.filter (fun Q => Q.start ∈ U0)).length

lemma leftoverCountIn_eq_card {U : Finset V} (pc : PathCover G U) :
    leftoverCountIn pc U = pc.card := by
  unfold leftoverCountIn
  have : pc.paths.filter (fun Q => Q.start ∈ U) = pc.paths :=
    List.filter_eq_self.2 fun Q hQ =>
      decide_eq_true (pc.support_subset hQ Q.start_mem_support)
  simpa [PathCover.card] using congrArg List.length this

/-- No original edge between `U0` and the remainder of a no-cross union
child. This is the inductive step that makes a saving subset an actual
component of the original cover carrier. -/
lemma noCross_of_union_child {U0 A B : Finset V}
    (hU0A : U0 ⊆ A)
    (hnocrossAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnocrossU0 : ∀ a ∈ U0, ∀ b ∈ A \ U0, ¬ G.Adj a b) :
    ∀ a ∈ U0, ∀ b ∈ (A ∪ B) \ U0, ¬ G.Adj a b := by
  intro a ha b hb
  have hb' : b ∈ A ∪ B ∧ b ∉ U0 := mem_sdiff.1 hb
  rcases mem_union.1 hb'.1 with hA | hB
  · exact hnocrossU0 a ha b (mem_sdiff.2 ⟨hA, hb'.2⟩)
  · exact hnocrossAB a (hU0A ha) b hB

/-- Reconstruct the leftover runs that live in `U0` as an actual path
cover of `U0`, using the no-cross cut `U0` / `W \ U0`. -/
noncomputable def actualFilteredCover {W U0 : Finset V}
    (hU0 : U0 ⊆ W)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b)
    (pc : PathCover G W) : PathCover G U0 :=
  PathCover.splitLeft (disjoint_sdiff : Disjoint U0 (W \ U0)) hnocross
    (pc.cast (union_sdiff_of_subset hU0).symm)

lemma actualFilteredCover_paths {W U0 : Finset V}
    (hU0 : U0 ⊆ W)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b)
    (pc : PathCover G W) :
    (actualFilteredCover hU0 hnocross pc).paths =
      pc.paths.filter (fun Q => Q.start ∈ U0) := by
  simp [actualFilteredCover, PathCover.splitLeft, PathCover.cast_paths]

lemma actualFilteredCover_card {W U0 : Finset V}
    (hU0 : U0 ⊆ W)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b)
    (pc : PathCover G W) :
    (actualFilteredCover hU0 hnocross pc).card = leftoverCountIn pc U0 := by
  simp [leftoverCountIn, PathCover.card, actualFilteredCover_paths hU0 hnocross pc]

/-- Distinct cover-path starts inject into the carrier, so a cover cannot
be larger than its vertex set. -/
lemma card_le_of_pathCover {U : Finset V} (pc : PathCover G U) :
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
  have hle : starts.toFinset.card ≤ U.card := card_le_card hsub
  simpa [PathCover.card, starts, List.length_map, hlen] using hle

lemma two_le_card_of_filtered {W U0 : Finset V}
    (hU0 : U0 ⊆ W)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b)
    (pc : PathCover G W)
    (h2 : 2 ≤ leftoverCountIn pc U0) :
    2 ≤ U0.card :=
  h2.trans <| by
    simpa [actualFilteredCover_card hU0 hnocross pc] using
      card_le_of_pathCover (actualFilteredCover hU0 hnocross pc)

/-- From a leftover cover of a nonempty `W` with `p(W) <` cover card,
extract a connected induced subset `U0 ⊆ W` that is anticomplete to
`W \ U0`, whose leftover-run count `q0` still strictly exceeds `p(U0)`,
and therefore `q0 ≥ 2`. -/
lemma exists_saving_of_cover {W : Finset V} (hne : W.Nonempty)
    (pc : PathCover G W) (hp : pathCoverNumber G W < pc.card) :
    ∃ U0 : Finset V,
      U0 ⊆ W ∧ U0.Nonempty ∧
        (G.induce (U0 : Set V)).Connected ∧
          (∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b) ∧
            2 ≤ leftoverCountIn pc U0 ∧
              pathCoverNumber G U0 < leftoverCountIn pc U0 ∧
                ∀ Q ∈ pc.paths, Q.start ∈ U0 → Q.support ⊆ U0 := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (W : Finset V), W.card = n → W.Nonempty →
        ∀ pc : PathCover G W, pathCoverNumber G W < pc.card →
          ∃ U0 : Finset V,
            U0 ⊆ W ∧ U0.Nonempty ∧
              (G.induce (U0 : Set V)).Connected ∧
                (∀ a ∈ U0, ∀ b ∈ W \ U0, ¬ G.Adj a b) ∧
                  2 ≤ leftoverCountIn pc U0 ∧
                    pathCoverNumber G U0 < leftoverCountIn pc U0 ∧
                      ∀ Q ∈ pc.paths, Q.start ∈ U0 → Q.support ⊆ U0)
    W.card ?_ W rfl hne pc hp
  intro n ih W hn hWne pc hp
  by_cases hconn : (G.induce (W : Set V)).Connected
  · refine ⟨W, subset_rfl, hWne, hconn, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb
      rw [sdiff_self] at hb
      exact (notMem_empty b hb).elim
    · have hpos : 1 ≤ pathCoverNumber G W :=
        one_le_pathCoverNumber_of_nonempty (G := G) hWne
      have : 2 ≤ pc.card := by omega
      simpa [leftoverCountIn_eq_card] using this
    · simpa [leftoverCountIn_eq_card] using hp
    · intro Q hQ _
      exact pc.support_subset hQ
  · obtain ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hcover, hnocross,
        hAcard, hBcard⟩ :=
      exists_disjoint_union_on (G := G) (U := W) hconn hWne
    have hEq : A ∪ B = W := hcover
    let pcW : PathCover G (A ∪ B) := pc.cast hEq.symm
    let pcA := PathCover.splitLeft (G := G) hdisj hnocross pcW
    let pcB := PathCover.splitRight (G := G) hdisj hnocross pcW
    have hadd := PathCover.card_split_add (G := G) hdisj hnocross pcW
    have hsum := pathCoverNumber_disjoint_union (G := G) hdisj hnocross
    have hpcW : pcW.card = pc.card := PathCover.cast_card pc hEq.symm
    have hpW : pathCoverNumber G (A ∪ B) < pcW.card := by
      simpa [hEq, hpcW] using hp
    have hltA : A.card < n := by simpa [hn] using hAcard
    have hltB : B.card < n := by simpa [hn] using hBcard
    have : pathCoverNumber G A < pcA.card ∨
        pathCoverNumber G B < pcB.card := by
      have hleA := pathCoverNumber_le (G := G) pcA
      have hleB := pathCoverNumber_le (G := G) pcB
      have hsum' : pathCoverNumber G A + pathCoverNumber G B =
          pathCoverNumber G (A ∪ B) := hsum.symm
      have hadd' : pcA.card + pcB.card = pcW.card := by
        change (PathCover.splitLeft (G := G) hdisj hnocross pcW).card +
            (PathCover.splitRight (G := G) hdisj hnocross pcW).card = pcW.card
        exact hadd
      omega
    have hpathsA : pcA.paths = pc.paths.filter (fun Q => Q.start ∈ A) := by
      simp [pcA, pcW, PathCover.splitLeft, PathCover.cast_paths]
    have hpathsB : pcB.paths = pc.paths.filter (fun Q => Q.start ∈ B) := by
      simp [pcB, pcW, PathCover.splitRight, PathCover.cast_paths]
    have hcountA (U0 : Finset V) (hU0 : U0 ⊆ A) :
        leftoverCountIn pc U0 = leftoverCountIn pcA U0 := by
      unfold leftoverCountIn
      rw [hpathsA, List.filter_filter]
      refine congrArg List.length (List.filter_congr ?_)
      intro Q _
      by_cases hQ : Q.start ∈ U0
      · simp [hQ, hU0 hQ]
      · simp [hQ]
    have hcountB (U0 : Finset V) (hU0 : U0 ⊆ B) :
        leftoverCountIn pc U0 = leftoverCountIn pcB U0 := by
      unfold leftoverCountIn
      rw [hpathsB, List.filter_filter]
      refine congrArg List.length (List.filter_congr ?_)
      intro Q _
      by_cases hQ : Q.start ∈ U0
      · simp [hQ, hU0 hQ]
      · simp [hQ]
    rcases this with hAstrict | hBstrict
    · obtain ⟨U0, hU0A, hU0ne, hU0conn, hU0nc, hq0, hpU0, hstay⟩ :=
        ih A.card hltA A rfl hAne pcA hAstrict
      refine ⟨U0, hU0A.trans hAsub, hU0ne, hU0conn, ?_, ?_, ?_, ?_⟩
      · intro a ha b hb
        have hb' : b ∈ (A ∪ B) \ U0 := by simpa [hEq] using hb
        exact noCross_of_union_child hU0A hnocross hU0nc a ha b hb'
      · simpa [hcountA U0 hU0A] using hq0
      · simpa [hcountA U0 hU0A] using hpU0
      · intro Q hQ hsU0
        have hsA : Q.start ∈ A := hU0A hsU0
        have hQA : Q ∈ pcA.paths := by
          simpa [hpathsA, List.mem_filter, hsA] using hQ
        exact hstay Q hQA hsU0
    · obtain ⟨U0, hU0B, hU0ne, hU0conn, hU0nc, hq0, hpU0, hstay⟩ :=
        ih B.card hltB B rfl hBne pcB hBstrict
      have hnocrossBA : ∀ b ∈ B, ∀ a ∈ A, ¬ G.Adj b a :=
        fun b hb a ha hab => hnocross a ha b hb hab.symm
      refine ⟨U0, hU0B.trans hBsub, hU0ne, hU0conn, ?_, ?_, ?_, ?_⟩
      · intro a ha b hb
        have hb' : b ∈ (B ∪ A) \ U0 := by
          simpa [hEq, union_comm] using hb
        exact noCross_of_union_child hU0B hnocrossBA hU0nc a ha b hb'
      · simpa [hcountB U0 hU0B] using hq0
      · simpa [hcountB U0 hU0B] using hpU0
      · intro Q hQ hsU0
        have hsB : Q.start ∈ B := hU0B hsU0
        have hQB : Q ∈ pcB.paths := by
          simpa [hpathsB, List.mem_filter, hsB] using hQ
        exact hstay Q hQB hsU0

/-- Opened-cycle leftover cover of `U \ A` under no consecutive `A`–`A`
edge yields an actual connected saving component `U0` of `K = U \ A`:
anticomplete to the rest of `K`, with an actual filtered leftover cover
of `U0`, `p(U0) < q0`, `q0 ≥ 2`, and therefore `|U0| ≥ 2`. -/
lemma exists_saving_component {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : IsCograph G (U \ A))
    (hstrict : pathCoverNumber G (U \ A) < A.card)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hf : p.finish ∉ A) (hno : NoConsecutive A p) :
    ∃ (U0 : Finset V) (pcU0 : PathCover G U0),
      U0 ⊆ U \ A ∧ U0.Nonempty ∧
        (G.induce (U0 : Set V)).Connected ∧
          IsCograph G U0 ∧
            (∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b) ∧
              pcU0.paths =
                List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p) ∧
                2 ≤ pcU0.card ∧
                  pathCoverNumber G U0 < pcU0.card ∧
                    2 ≤ U0.card ∧
                      ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0 := by
  obtain ⟨pc, hcard, hpaths, _hsub⟩ :=
    exists_cycle_leftover_card_eq (c := c) hc hA hAne hp hs hf hno
  have hKne : (U \ A).Nonempty := by
    refine ⟨p.finish, ?_⟩
    exact mem_sdiff.2 ⟨by simpa [hp] using p.finish_mem_support, hf⟩
  have hp' : pathCoverNumber G (U \ A) < pc.card := by
    simpa [hcard] using hstrict
  obtain ⟨U0, hU0, hU0ne, hconn, hnocross, hq0, hpU0, hstay⟩ :=
    exists_saving_of_cover hKne pc hp'
  let pcU0 := actualFilteredCover hU0 hnocross pc
  have hpcU0paths : pcU0.paths =
      pc.paths.filter (fun Q => Q.start ∈ U0) :=
    actualFilteredCover_paths hU0 hnocross pc
  have hpcU0card : pcU0.card = leftoverCountIn pc U0 :=
    actualFilteredCover_card hU0 hnocross pc
  refine ⟨U0, pcU0, hU0, hU0ne, hconn, hK.subset hU0, hnocross, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpcU0paths, hpaths]
  · simpa [hpcU0card] using hq0
  · simpa [hpcU0card] using hpU0
  · exact two_le_card_of_filtered hU0 hnocross pc hq0
  · intro Q hQ hsU0
    have hQpc : Q ∈ pc.paths := by simpa [hpaths] using hQ
    exact hstay Q hQpc hsU0

/-- A saving component of order at least two is an original complete join
of two nonempty children. This is the legitimate root-join of the
protected induction, derived from `q0 ≥ 2` and the filtered cover. -/
lemma exists_complete_join_of_saving {U0 : Finset V}
    (hU0 : IsCograph G U0)
    (hconn : (G.induce (U0 : Set V)).Connected)
    (h2 : 2 ≤ U0.card) :
    ∃ X Y : Finset V, X ⊆ U0 ∧ Y ⊆ U0 ∧ X.Nonempty ∧ Y.Nonempty ∧
      Disjoint X Y ∧ X ∪ Y = U0 ∧
        G.IsCompleteBetween (X : Set V) (Y : Set V) ∧
          X.card < U0.card ∧ Y.card < U0.card :=
  exists_complete_join_on hU0 hconn h2

/-- A complete-join child of a saving component is disjoint from original
`A`, because it lives in `U \ A`. -/
lemma disjoint_A_of_saving_child {U A U0 Y : Finset V}
    (hU0 : U0 ⊆ U \ A) (hY : Y ⊆ U0) : Disjoint A Y := by
  refine disjoint_left.2 ?_
  intro x hxA hxY
  exact (mem_sdiff.1 (hU0 (hY hxY))).2 hxA

lemma sdiff_sdiff_eq_sdiff_union (U A Y : Finset V) :
    (U \ A) \ Y = U \ (A ∪ Y) := by
  ext x
  simp [mem_sdiff, mem_union]
  tauto

/-- Global cover-deletion bound: `p(K \ Y) ≤ p(K) + |Y| < |A| + |Y| = |A ∪ Y|`.
No per-component path-count sum is used. `A` and `Y` are disjoint because
`Y` lives in the remainder `U \ A`. -/
lemma pathCoverNumber_lt_of_delete_Y {U A U0 Y : Finset V}
    (hU0 : U0 ⊆ U \ A) (hY : Y ⊆ U0)
    (hstrict : pathCoverNumber G (U \ A) < A.card) :
    pathCoverNumber G (U \ (A ∪ Y)) < (A ∪ Y).card := by
  have hdisj : Disjoint A Y := disjoint_A_of_saving_child hU0 hY
  have hcard : (A ∪ Y).card = A.card + Y.card :=
    card_union_of_disjoint hdisj
  have hYsub : Y ⊆ U \ A := hY.trans hU0
  have hle := pathCoverNumber_sdiff_le (G := G) (U \ A) Y hYsub
  have hEq : (U \ A) \ Y = U \ (A ∪ Y) := sdiff_sdiff_eq_sdiff_union U A Y
  have : pathCoverNumber G (U \ (A ∪ Y)) ≤
      pathCoverNumber G (U \ A) + Y.card := by
    simpa [hEq] using hle
  omega

/-- The remainder after deleting `A ∪ Y` inherits the cograph property
from `U \ A`. -/
lemma isCograph_sdiff_union_Y {U A Y : Finset V}
    (hK : IsCograph G (U \ A)) :
    IsCograph G (U \ (A ∪ Y)) :=
  hK.subset <| by
    rw [← sdiff_sdiff_eq_sdiff_union U A Y]
    exact sdiff_subset


end Cograph
end Nikoghosyan
