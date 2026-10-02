/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalProfileLayers
import Nikoghosyan.Prerequisites.TerminalSideChange

/-!
# One-cap original-edge construction for a balanced unique profile

The small-`p(D)` side-change already covers unique-profile `w > d` and
the unique-profile `w = d` branch whenever `|Y| ≥ 2`. The remaining
balanced case is `p(W) = |Bd|` with `|Y| = 1`: cap one outer end of a
`W`-ended cover by a `Bd` vertex, leave the other end in `W`, then
insert the unique outer connector between that open `W`-end and an
isolated original terminal.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma exists_cap_one_end {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (p : GraphPath G) (hs : p.start ∈ A)
    {b : V} (hb : b ∈ B) (h1 : b ∉ p.support) :
    ∃ r : GraphPath G,
      r.start = b ∧ r.finish = p.finish ∧
        r.support = insert b p.support := by
  have hadj : G.Adj b p.start := (hAB hs hb).symm
  refine ⟨p.consAdj hadj h1, rfl, rfl, ?_⟩
  simp [GraphPath.support_consAdj]

/-- From a nonempty `W`-ended cover of `U` and `|T| = card` unused
terminals complete to `W`, produce one path spanning `U ∪ T` with one
end in `T` and the other end in `W`. -/
lemma exists_one_cap_path_of_W_ended_cover {W T U : Finset V}
    (hWT : G.IsCompleteBetween (W : Set V) (T : Set V))
    (hdisj : Disjoint T U)
    (pc : PathCover G U)
    (hend : ∀ p ∈ pc.paths, p.start ∈ W ∧ p.finish ∈ W)
    (hpos : 1 ≤ pc.card)
    (hT : T.card = pc.card) :
    ∃ r : GraphPath G,
      r.start ∈ T ∧ r.finish ∈ W ∧ r.support = U ∪ T := by
  have aux :
      ∀ (k : ℕ) (U T : Finset V) (pc : PathCover G U),
        pc.card = k →
        1 ≤ k →
        Disjoint T U →
        (∀ p ∈ pc.paths, p.start ∈ W ∧ p.finish ∈ W) →
        T.card = k →
        G.IsCompleteBetween (W : Set V) (T : Set V) →
        ∃ r : GraphPath G,
          r.start ∈ T ∧ r.finish ∈ W ∧ r.support = U ∪ T := by
    intro k
    induction k with
    | zero =>
      intro U T pc hcard hpos hdisj hend hT hWT
      omega
    | succ k ih =>
      intro U T pc hcard hpos hdisj hend hT hWT
      by_cases hk1 : k = 0
      · have hcard1 : pc.card = 1 := by omega
        obtain ⟨p, hpseq⟩ := PathCover.exists_singleton_of_card_one pc hcard1
        have hp : p ∈ pc.paths := by simp [hpseq]
        have hs : p.start ∈ W := (hend p hp).1
        have hf : p.finish ∈ W := (hend p hp).2
        have hTpos : T.Nonempty := card_pos.mp (by omega)
        obtain ⟨b, hb⟩ := hTpos
        have hbU : b ∉ p.support := fun h =>
          (Finset.disjoint_left.1 hdisj hb) ((pc.mem_iff b).2 ⟨p, hp, h⟩)
        obtain ⟨r, hrs, hrf, hrsup⟩ :=
          exists_cap_one_end hWT p hs hb hbU
        have hU : p.support = U := by
          ext x
          constructor
          · intro hx
            exact (pc.mem_iff x).2 ⟨p, hp, hx⟩
          · intro hx
            obtain ⟨q, hq, hxq⟩ := (pc.mem_iff x).1 hx
            have : q = p := by simpa [hpseq] using hq
            subst this
            exact hxq
        have hTeq : T = ({b} : Finset V) := by
          have hsub : ({b} : Finset V) ⊆ T := singleton_subset_iff.2 hb
          have : T.card = 1 := by omega
          exact (eq_of_subset_of_card_le hsub (by simp [this])).symm
        refine ⟨r, by simpa [hrs] using hb, by simpa [hrf] using hf, ?_⟩
        rw [hrsup, hU, hTeq]
        ext x
        simp [mem_union, mem_insert, mem_singleton, or_comm]
      · have h2 : 2 ≤ pc.card := by omega
        have hTne : T.Nonempty := card_pos.mp (by omega)
        obtain ⟨t, ht⟩ := hTne
        have htU : t ∉ U := Finset.disjoint_left.1 hdisj ht
        obtain ⟨pc', hcard', hend'⟩ :=
          exists_splice_two_through hWT pc h2 hend ht htU
        let T' := T.erase t
        have hdisj' : Disjoint T' (insert t U) := by
          refine disjoint_insert_right.2 ⟨notMem_erase t T, ?_⟩
          exact disjoint_of_subset_left (erase_subset t T) hdisj
        have hWT' : G.IsCompleteBetween (W : Set V) (T' : Set V) :=
          IsCompleteBetween.mono hWT subset_rfl (erase_subset t T)
        have hck : pc'.card = k := by omega
        have hposk : 1 ≤ k := by omega
        have hTk : T'.card = k := by
          rw [card_erase_of_mem ht]
          omega
        obtain ⟨r, hrs, hrf, hrsup⟩ :=
          ih (insert t U) T' pc' hck hposk hdisj' hend' hTk hWT'
        refine ⟨r, mem_of_mem_erase hrs, hrf, ?_⟩
        rw [hrsup]
        ext x
        constructor
        · intro hx
          have hx' : x ∈ insert t U ∪ T.erase t := by simpa [T'] using hx
          rcases mem_union.1 hx' with hxL | hxR
          · rcases mem_insert.1 hxL with rfl | hxU
            · exact mem_union.2 (Or.inr ht)
            · exact mem_union.2 (Or.inl hxU)
          · exact mem_union.2 (Or.inr (mem_of_mem_erase hxR))
        · intro hx
          rcases mem_union.1 hx with hxU | hxT
          · exact mem_union.2 (Or.inl (mem_insert.2 (Or.inr hxU)))
          · by_cases hxt : x = t
            · subst hxt
              exact mem_union.2 (Or.inl (mem_insert_self _ _))
            · exact mem_union.2 (Or.inr (mem_erase.2 ⟨hxt, hxT⟩))
  exact aux pc.card U T pc rfl hpos hdisj hend hT hWT

lemma exists_Bd_W_spanning_path_of_balanced {Bd W : Finset V}
    (hBdne : Bd.Nonempty) (hWne : W.Nonempty)
    (hdisj : Disjoint Bd W)
    (hAB : G.IsCompleteBetween (Bd : Set V) (W : Set V))
    (hp : pathCoverNumber G W = Bd.card) :
    ∃ r : GraphPath G,
      r.start ∈ Bd ∧ r.finish ∈ W ∧ r.support = Bd ∪ W := by
  have hpWpos : 1 ≤ pathCoverNumber G W :=
    one_le_pathCoverNumber_of_nonempty (G := G) hWne
  obtain ⟨pcW, hWcard⟩ := exists_min_pathCover (G := G) W
  have hendW : ∀ p ∈ pcW.paths, p.start ∈ W ∧ p.finish ∈ W := by
    intro p hpW
    exact ⟨pcW.support_subset hpW p.start_mem_support,
      pcW.support_subset hpW p.finish_mem_support⟩
  have hT : Bd.card = pcW.card := by omega
  have hpos : 1 ≤ pcW.card := by omega
  have hBA : G.IsCompleteBetween (W : Set V) (Bd : Set V) :=
    IsCompleteBetween.symm hAB
  obtain ⟨r, hrs, hrf, hrsup⟩ :=
    exists_one_cap_path_of_W_ended_cover hBA hdisj pcW hendW hpos hT
  refine ⟨r, hrs, hrf, ?_⟩
  rw [hrsup, union_comm]

end Nikoghosyan
