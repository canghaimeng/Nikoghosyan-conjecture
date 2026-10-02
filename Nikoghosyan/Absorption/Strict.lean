/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Absorption.BoundarySupport
import Nikoghosyan.Absorption.SaturatedCutShift

/-!
# Strict protected absorption of an actual second cycle

Manuscript `abs:thm:strict-absorption`. A genuine original cycle `cH` on
`H`, a vertex-disjoint genuine cycle `cD` on `D`, nonempty `A ⊆ H`,
canonical cograph remainder `K₀ = H \ A` with `p(K₀) = |A|`, canonical
cograph `K = K₀ ∪ D` with every vertex of `D` adjacent to `E(K₀)`, and
strict slack `p(K) < |A|` yield a spanning original `H ∪ D` path with
distinct ends in `A` that is `ProtectedAt cH A`.

Helpers live in `BoundarySupport`. This file retains the induction body.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath
open Nikoghosyan.GraphCycle

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Canonical strict protected absorption. -/
theorem exists_strict_absorption {H D A : Finset V}
    {G : SimpleGraph V} (cH : GraphCycle G) (cD : GraphCycle G)
    (hcH : cH.support = H) (hcD : cD.support = D)
    (hdisj : Disjoint H D) (hA : A ⊆ H) (hAne : A.Nonempty)
    (hK0 : Nikoghosyan.IsCograph G (H \ A))
    (hpK0 : pathCoverNumber G (H \ A) = A.card)
    (hK : Nikoghosyan.IsCograph G ((H \ A) ∪ D))
    (hE : ∀ d ∈ D, ∃ u ∈ eligibleSet G (H \ A), G.Adj d u)
    (hpK : pathCoverNumber G ((H \ A) ∪ D) < A.card) :
    ∃ p : GraphPath G,
      p.support = H ∪ D ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧ p.ProtectedAt cH A := by
  let motive : ℕ → Prop := fun n =>
    ∀ (G : SimpleGraph V) (H D A : Finset V)
      (cH : GraphCycle G) (cD : GraphCycle G),
      ((H \ A) ∪ D).card = n →
        cH.support = H → cD.support = D → Disjoint H D →
          A ⊆ H → A.Nonempty →
            Nikoghosyan.IsCograph G (H \ A) →
              pathCoverNumber G (H \ A) = A.card →
                Nikoghosyan.IsCograph G ((H \ A) ∪ D) →
                  (∀ d ∈ D, ∃ u ∈ eligibleSet G (H \ A), G.Adj d u) →
                    pathCoverNumber G ((H \ A) ∪ D) < A.card →
                      ∃ p : GraphPath G,
                        p.support = H ∪ D ∧ p.start ∈ A ∧ p.finish ∈ A ∧
                          p.start ≠ p.finish ∧ p.ProtectedAt cH A
  refine Nat.strongRecOn (motive := motive) ((H \ A) ∪ D).card ?_ G H D A cH cD
    rfl hcH hcD hdisj hA hAne hK0 hpK0 hK hE hpK
  intro n ih Gind Hind Dind Aind cHind cDind hcard hcHind hcDind hdisjind
    hAind hAneind hK0ind hpK0ind hKind hEind hpKind
  have hK0c : IsCograph Gind (Hind \ Aind) := isCograph_iff.2 hK0ind
  have hKc : IsCograph Gind ((Hind \ Aind) ∪ Dind) := isCograph_iff.2 hKind
  have hSat : Saturated (G := Gind) Hind Aind := hpK0ind
  -- Saturation excludes a spanning A–A path of H.
  have hnoAAPath : ¬ ∃ q : GraphPath Gind,
      q.support = Hind ∧ q.start ∈ Aind ∧ q.finish ∈ Aind := by
    intro ⟨q, hq, hs, hf⟩
    have := pathCoverNumber_lt_of_spanning_AA (U := Hind) (A := Aind)
      hAind hAneind hq hs hf
    omega
  by_cases hAA : ∃ a ∈ Aind, ∃ hu : a ∈ cHind.support,
      cHind.succAt hu ∈ Aind ∨ (cHind.openAt hu).walk.penultimate ∈ Aind
  · obtain ⟨a, haA, hu, hneigh⟩ := hAA
    obtain ⟨q, hsup, hst, hfin, hne, hP⟩ :=
      exists_protectedAt_of_cycle_neighbour_A cHind hcHind haA hu hneigh
    exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
  have hnoAA : ∀ a ∈ Aind, ∀ hu : a ∈ cHind.support,
      cHind.succAt hu ∉ Aind ∧ (cHind.openAt hu).walk.penultimate ∉ Aind := by
    intro a haA hu
    constructor
    · intro h
      exact hAA ⟨a, haA, hu, Or.inl h⟩
    · intro h
      exact hAA ⟨a, haA, hu, Or.inr h⟩
  obtain ⟨pH, pc0, hpH, hsH, hcloseH, hedgesH, hmin0, hpaths0, _⟩ :=
    cycle_leftover_cover_min_of_saturated (c := cHind) hcHind hAind hAneind hSat
  have hno : NoConsecutive Aind pH :=
    NoConsecutive_of_no_AA_cycle (c := cHind) hcHind hAind hedgesH hnoAA
  -- Adjacent leftover starts/ends would give a spanning A–A path of H.
  by_cases hAdjS : ∃ Q ∈ leftoverPieces Aind pH, ∃ R ∈ leftoverPieces Aind pH,
      Q.start ≠ R.start ∧ Gind.Adj Q.start R.start
  · obtain ⟨Q, hQ, R, hR, hneQR, hadj⟩ := hAdjS
    obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
      exists_protectedAt_of_adj_leftover_starts (c := cHind) hcHind hpH hsH
        hcloseH hedgesH hQ hR hneQR hadj
    exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
  by_cases hAdjF : ∃ Q ∈ leftoverPieces Aind pH, ∃ R ∈ leftoverPieces Aind pH,
      Q.finish ≠ R.finish ∧ Gind.Adj Q.finish R.finish
  · obtain ⟨Q, hQ, R, hR, hneQR, hadj⟩ := hAdjF
    obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
      exists_protectedAt_of_adj_leftover_ends (c := cHind) hcHind hpH hsH
        hcloseH hedgesH hQ hR hneQR hadj
    exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
  have hDne : Dind.Nonempty := ⟨cDind.start, by simpa [hcDind] using
      cDind.start_mem_support⟩
  have hDconn := connected_of_cycle cDind
  have hDconn' : (Gind.induce (Dind : Set V)).Connected := hcDind ▸ hDconn
  have hDK : Dind ⊆ (Hind \ Aind) ∪ Dind := subset_union_right
  obtain ⟨U, hUK, hDU, hUne, hUconn, hUnc⟩ :=
    exists_block_containing (K := (Hind \ Aind) ∪ Dind) (D := Dind)
      hDK hDne hDconn'
  let U0 := U ∩ (Hind \ Aind)
  have hU0 : U0 ⊆ Hind \ Aind := inter_subset_right
  have hU0ne : U0.Nonempty := by
    obtain ⟨d, hdD⟩ := hDne
    obtain ⟨u, huE, hadj⟩ := hEind d hdD
    have huK0 : u ∈ Hind \ Aind :=
      (eligibleSet_subset (G := Gind) (Hind \ Aind)) huE
    have huK : u ∈ (Hind \ Aind) ∪ Dind := mem_union.2 (Or.inl huK0)
    have hdU : d ∈ U := hDU hdD
    have huU : u ∈ U := by
      by_contra hnu
      exact hUnc d hdU u (mem_sdiff.2 ⟨huK, hnu⟩) hadj
    exact ⟨u, mem_inter.2 ⟨huU, huK0⟩⟩
  have hK0cog : IsCograph Gind U0 := hK0c.subset hU0
  have hnocrossU0 : ∀ a ∈ U0, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b := by
    intro a ha b hb hadj
    have haU : a ∈ U := (mem_inter.1 ha).1
    have hbK0 : b ∈ Hind \ Aind := (mem_sdiff.1 hb).1
    have hbU : b ∉ U0 := (mem_sdiff.1 hb).2
    have hbnotU : b ∉ U := by
      intro hbinU
      exact hbU (mem_inter.2 ⟨hbinU, hbK0⟩)
    exact hUnc a haU b
      (mem_sdiff.2 ⟨mem_union.2 (Or.inl hbK0), hbnotU⟩) hadj
  have hstay : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.support ⊆ U0 := by
    intro Q hQ hsU0 x hxQ
    have hxK0 : x ∈ Hind \ Aind := by
      have hxH : x ∈ Hind := by simpa [hpH] using
        leftoverPieces_support_subset pH Q hQ hxQ
      have hxA : x ∉ Aind :=
        Finset.disjoint_left.1 (leftoverPieces_disjoint_B pH Q hQ) hxQ
      exact mem_sdiff.2 ⟨hxH, hxA⟩
    by_contra hxU0
    have hxout : x ∈ (Hind \ Aind) \ U0 := mem_sdiff.2 ⟨hxK0, hxU0⟩
    have hQs : Q.start ∈ Q.support := Q.start_mem_support
    have hsK0 : Q.start ∈ Hind \ Aind := (mem_inter.1 hsU0).2
    have hQconn : (Gind.induce (Q.support : Set V)).Connected :=
      connected_of_spanning_path Q rfl
    have hcross := subset_left_or_right_of_connected
      (A := U0) (B := (Hind \ Aind) \ U0) (D := Q.support)
      Finset.disjoint_sdiff (fun y hy => by
        have hyH : y ∈ Hind := by simpa [hpH] using
          leftoverPieces_support_subset pH Q hQ hy
        have hyA : y ∉ Aind :=
          Finset.disjoint_left.1 (leftoverPieces_disjoint_B pH Q hQ) hy
        have hyK0 : y ∈ Hind \ Aind := mem_sdiff.2 ⟨hyH, hyA⟩
        by_cases hyU : y ∈ U0
        · exact mem_union.2 (Or.inl hyU)
        · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hyK0, hyU⟩)))
      hnocrossU0 hQconn
    rcases hcross with hQ0 | hQout
    · exact hxU0 (hQ0 hxQ)
    · exact (mem_sdiff.1 (hQout hQs)).2 hsU0
  have h2 : 2 ≤
      (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces Aind pH)).length := by
    have hq0 : pc0.card = Aind.card := by simpa [hpK0ind] using hmin0
    have hpaths : pc0.paths = leftoverPieces Aind pH := hpaths0
    -- At least two leftover runs meet U0: otherwise p(U) < p(U0) ≤ 1
    -- contradicts a connected cograph of order ≥ 2 containing D.
    have hUcard : 2 ≤ U.card := by
      have h3 : 3 ≤ Dind.card := by simpa [hcDind] using cDind.three_le_card_support
      exact le_trans (by decide : (2 : ℕ) ≤ 3)
        (h3.trans (card_le_card hDU))
    have hfilter :
        leftoverCountIn pc0 U0 =
          (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces Aind pH)).length := by
      simp [leftoverCountIn, hpaths]
    have hpU0 : pathCoverNumber Gind U0 ≤ leftoverCountIn pc0 U0 := by
      let pcU0 := actualFilteredCover hU0 hnocrossU0 pc0
      have hcard := actualFilteredCover_card hU0 hnocrossU0 pc0
      exact (pathCoverNumber_le (G := Gind) pcU0).trans (le_of_eq hcard)
    have hKsdiffU : ((Hind \ Aind) ∪ Dind) \ U = (Hind \ Aind) \ U0 := by
      ext x
      simp only [mem_sdiff, mem_union, U0, mem_inter]
      constructor
      · intro ⟨hx, hnu⟩
        rcases hx with hx0 | hxD
        · exact ⟨hx0, fun h => hnu h.1⟩
        · exact (hnu (hDU hxD)).elim
      · intro ⟨hx0, hxU0⟩
        refine ⟨Or.inl hx0, ?_⟩
        intro hxU
        exact hxU0 ⟨hxU, hx0⟩
    have hncUK : ∀ a ∈ U, ∀ b ∈ ((Hind \ Aind) ∪ Dind) \ U, ¬ Gind.Adj a b :=
      hUnc
    have hdisjUK : Disjoint U (((Hind \ Aind) ∪ Dind) \ U) := disjoint_sdiff
    have hUunion : U ∪ (((Hind \ Aind) ∪ Dind) \ U) = (Hind \ Aind) ∪ Dind :=
      union_sdiff_of_subset hUK
    have hpKadd :
        pathCoverNumber Gind ((Hind \ Aind) ∪ Dind) =
          pathCoverNumber Gind U +
            pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ U) := by
      simpa [hUunion] using
        pathCoverNumber_disjoint_union (G := Gind) hdisjUK hncUK
    have hdisjU0 : Disjoint U0 ((Hind \ Aind) \ U0) := disjoint_sdiff
    have hU0union : U0 ∪ ((Hind \ Aind) \ U0) = Hind \ Aind :=
      union_sdiff_of_subset hU0
    have hpK0add :
        pathCoverNumber Gind (Hind \ Aind) =
          pathCoverNumber Gind U0 +
            pathCoverNumber Gind ((Hind \ Aind) \ U0) := by
      simpa [hU0union] using
        pathCoverNumber_disjoint_union (G := Gind) hdisjU0 hnocrossU0
    have hEqRest :
        pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ U) =
          pathCoverNumber Gind ((Hind \ Aind) \ U0) := by
      simpa [hKsdiffU]
    have hpUlt : pathCoverNumber Gind U < pathCoverNumber Gind U0 := by
      have hsum :
          pathCoverNumber Gind U +
              pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ U) <
            pathCoverNumber Gind U0 +
              pathCoverNumber Gind ((Hind \ Aind) \ U0) := by
        have := hpKind
        simpa [hpKadd.symm, hpK0add.symm, hpK0ind] using this
      have hsum' :
          pathCoverNumber Gind U +
              pathCoverNumber Gind ((Hind \ Aind) \ U0) <
            pathCoverNumber Gind U0 +
              pathCoverNumber Gind ((Hind \ Aind) \ U0) := by
        simpa [hEqRest] using hsum
      exact Nat.lt_of_add_lt_add_right hsum'
    have hq : 2 ≤ leftoverCountIn pc0 U0 := by
      have hpUpos : 1 ≤ pathCoverNumber Gind U :=
        one_le_pathCoverNumber_of_nonempty (G := Gind) hUne
      have hpU0pos : 2 ≤ pathCoverNumber Gind U0 := by
        have hge : 1 ≤ pathCoverNumber Gind U0 :=
          one_le_pathCoverNumber_of_nonempty (G := Gind) hU0ne
        have hlt := hpUlt
        have hposU := hpUpos
        omega
      exact hpU0pos.trans hpU0
    simpa [hfilter] using hq
  obtain ⟨Q0, _, hQ0, _, hs0, _, _⟩ := exists_two_leftover_in h2
  have hU0card : 2 ≤ U0.card := by
    have hcnt : leftoverCountIn pc0 U0 =
        (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces Aind pH)).length := by
      simp [leftoverCountIn, hpaths0]
    have h2c : 2 ≤ leftoverCountIn pc0 U0 := by simpa [hcnt] using h2
    exact two_le_card_of_filtered hU0 hnocrossU0 pc0 h2c
  have hUcard : 2 ≤ U.card :=
    hU0card.trans (card_le_card (inter_subset_left (s₁ := U)))
  have hUcog : IsCograph Gind U := hKc.subset hUK
  obtain ⟨X, Y, hX, hY, hXne, hYne, hdisjXY, hcover, hjoin, _, _⟩ :=
    exists_complete_join_of_saving hUcog hUconn hUcard
  have hIndS : ∀ Q ∈ leftoverPieces Aind pH, ∀ R ∈ leftoverPieces Aind pH,
      Q.start ∈ U0 → R.start ∈ U0 → Q.start ≠ R.start →
        ¬ Gind.Adj Q.start R.start :=
    fun Q hQ R hR _ _ hne hadj => hAdjS ⟨Q, hQ, R, hR, hne, hadj⟩
  have hIndF : ∀ Q ∈ leftoverPieces Aind pH, ∀ R ∈ leftoverPieces Aind pH,
      Q.finish ∈ U0 → R.finish ∈ U0 → Q.finish ≠ R.finish →
        ¬ Gind.Adj Q.finish R.finish :=
    fun Q hQ R hR _ _ hne hadj => hAdjF ⟨Q, hQ, R, hR, hne, hadj⟩
  have hstartMemU : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ U :=
    fun Q hQ hs => (mem_inter.1 hs).1
  have hstartMemK : ∀ Q ∈ leftoverPieces Aind pH,
      Q.start ∈ Hind \ Aind :=
    fun Q hQ =>
      mem_sdiff.2 ⟨by simpa [hpH] using leftoverPieces_start_mem hQ,
        leftover_start_not_mem hQ⟩
  have hfinMemK : ∀ Q ∈ leftoverPieces Aind pH,
      Q.finish ∈ Hind \ Aind :=
    fun Q hQ =>
      mem_sdiff.2 ⟨by simpa [hpH] using leftoverPieces_finish_mem hQ,
        leftover_finish_not_mem hQ⟩
  have hs0U : Q0.start ∈ U := (mem_inter.1 hs0).1
  have hIndSU : ∀ Q ∈ leftoverPieces Aind pH, ∀ R ∈ leftoverPieces Aind pH,
      Q.start ∈ U → R.start ∈ U → Q.start ≠ R.start →
        ¬ Gind.Adj Q.start R.start :=
    fun Q hQ R hR hsU hsU' hne hadj =>
      hIndS Q hQ R hR (mem_inter.2 ⟨hsU, hstartMemK Q hQ⟩)
        (mem_inter.2 ⟨hsU', hstartMemK R hR⟩) hne hadj
  have hIndFU : ∀ Q ∈ leftoverPieces Aind pH, ∀ R ∈ leftoverPieces Aind pH,
      Q.finish ∈ U → R.finish ∈ U → Q.finish ≠ R.finish →
        ¬ Gind.Adj Q.finish R.finish :=
    fun Q hQ R hR hfU hfU' hne hadj =>
      hIndF Q hQ R hR
        (mem_inter.2 ⟨hfU, hfinMemK Q hQ⟩)
        (mem_inter.2 ⟨hfU', hfinMemK R hR⟩) hne hadj
  have hstartSide := leftover_starts_in_one_join_side (A := Aind) (U0 := U)
    (X := X) (Y := Y) hjoin hcover hIndSU hQ0 hs0U
  have hf0U' : Q0.finish ∈ U := by
    have hx : Q0.finish ∈ U0 := hstay Q0 hQ0 hs0 Q0.finish_mem_support
    exact (mem_inter.1 hx).1
  have hfinSide := leftover_finishes_in_one_join_side (A := Aind) (U0 := U)
    (X := X) (Y := Y) hjoin hcover hIndFU hQ0 hf0U'
  have hU0subU : U0 ⊆ U := inter_subset_left
  let X0 := X ∩ U0
  let Y0 := Y ∩ U0
  have hcover0 : X0 ∪ Y0 = U0 := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with h | h
      · exact (mem_inter.1 h).2
      · exact (mem_inter.1 h).2
    · intro hz
      have hzU : z ∈ U := (mem_inter.1 hz).1
      have hzXY : z ∈ X ∨ z ∈ Y := by
        have : z ∈ X ∪ Y := by simpa [hcover] using hzU
        simpa [mem_union] using this
      rcases hzXY with hx | hy
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hx, hz⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hy, hz⟩))
  have hjoin0 : Gind.IsCompleteBetween (X0 : Set V) (Y0 : Set V) :=
    fun {x} hx {y} hy => hjoin (mem_inter.1 hx).1 (mem_inter.1 hy).1
  have hjoinYX : Gind.IsCompleteBetween (Y : Set V) (X : Set V) :=
    fun {y} hy {x} hx => (hjoin hx hy).symm
  have hmemXY : ∀ z, z ∈ U → z ∈ X ∨ z ∈ Y := fun z hz => by
    have : z ∈ X ∪ Y := by simpa [hcover] using hz
    simpa [mem_union] using this
  have hDsubXY : Dind ⊆ X ∪ Y := fun z hz => by
    simpa [hcover] using hDU hz
  rcases hstartSide with hstartX | hstartY
  · rcases hfinSide with hfinX0 | hfinY0
    · have hstartX0 : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ X0 :=
        fun Q hQ hs => mem_inter.2 ⟨hstartX Q hQ (hU0subU hs), hs⟩
      have hfinX0' : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.finish ∈ X0 :=
        fun Q hQ hs =>
          mem_inter.2 ⟨hfinX0 Q hQ (hU0subU (hstay Q hQ hs Q.finish_mem_support)),
            hstay Q hQ hs Q.finish_mem_support⟩
      by_cases hYY : ∃ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 ∧
          ∃ u ∈ Y0, ∃ v ∈ Y0, s(u, v) ∈ Q.edges
      · obtain ⟨Q, hQ, hQs, u, huY, v, hvY, huvQ⟩ := hYY
        have hadjuv : Gind.Adj u v := by
          simpa [SimpleGraph.mem_edgeSet] using Q.edges_subset_edgeSet _ huvQ
        obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
          exists_protectedAt_of_join_insert_YY_of_saving (c := cHind) hcHind
            hU0 hjoin0 hcover0 hpH hsH hcloseH hedgesH hstay h2
            hfinX0' hstartX0 hQ hQs huY hvY hadjuv huvQ
        exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
      · by_cases hYYd : ∃ d ∈ Dind ∩ Y, ∃ hdC : d ∈ cDind.support,
            cDind.succAt hdC ∈ Y
        · obtain ⟨d, hdDY, hdC, heY⟩ := hYYd
          have hdD : d ∈ Dind := (mem_inter.1 hdDY).1
          have hdY : d ∈ Y := (mem_inter.1 hdDY).2
          let r := cDind.openAt hdC
          have hr : r.support = Dind := by
            simpa [r, hcDind] using openAt_support cDind hdC
          have hrd : r.finish = d := openAt_finish cDind hdC
          have hreY : r.start ∈ Y := by
            simpa [r, openAt_start cDind hdC] using heY
          obtain ⟨Q, R, hQ, hR, hQs, hRs, hneQR⟩ := exists_two_leftover_in h2
          have hQsX : Q.start ∈ X := hstartX Q hQ (hU0subU hQs)
          have hRsX : R.start ∈ X := hstartX R hR (hU0subU hRs)
          have hneSt : Q.start ≠ R.start := by
            intro heq
            have hdisjQR : Disjoint Q.support R.support :=
              PathCover.pairwise_disjoint_of_mem
                (leftoverPieces_pairwise (B := Aind) pH) hQ hR hneQR
            exact Finset.disjoint_left.1 hdisjQR Q.start_mem_support
              (heq ▸ R.start_mem_support)
          have hadjQe : Gind.Adj Q.start r.start := hjoin hQsX hreY
          have hadjdR : Gind.Adj r.finish R.start := by
            simpa [hrd] using (hjoin hRsX hdY).symm
          obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
            exists_switchThrough_leftover_starts (cH := cHind) hcHind hAind
              hpH hsH hcloseH hedgesH hr hdisjind hQ hR hneSt hadjQe hadjdR
          exact ⟨q, hsup, hst, hfin, hne, hProt⟩
        · by_cases hDY : (Dind ∩ Y).Nonempty
          · obtain ⟨d, hdDY⟩ := hDY
            have hdD : d ∈ Dind := (mem_inter.1 hdDY).1
            have hdY : d ∈ Y := (mem_inter.1 hdDY).2
            have hdC : d ∈ cDind.support := by simpa [hcDind] using hdD
            have heD : cDind.succAt hdC ∈ Dind := by
              simpa [hcDind] using succAt_mem_support cDind hdC
            rcases hmemXY _ (hDU heD) with heX | heY
            · -- `e = succ(d) ∈ X`, `d ∈ Y`. Open `D` at `d` so the NEW
              -- path starts at the `X`-port and finishes in `Y`.
              let evert := cDind.succAt hdC
              have heX' : evert ∈ X := heX
              obtain ⟨u, huE, hadjue⟩ := hEind evert heD
              have huK0 : u ∈ Hind \ Aind :=
                eligibleSet_subset (G := Gind) (Hind \ Aind) huE
              have heU : evert ∈ U := hDU heD
              have huU : u ∈ U := by
                by_contra hnu
                exact hUnc evert heU u
                  (mem_sdiff.2 ⟨mem_union.2 (Or.inl huK0), hnu⟩) hadjue
              have huU0 : u ∈ U0 := mem_inter.2 ⟨huU, huK0⟩
              obtain ⟨Qi, hQi, huQi, hQiU0, _hQisup⟩ :=
                leftover_U0_run_of_mem (U := Hind) (A := Aind) (U0 := U0)
                  hpH hU0 hnocrossU0 hstay huU0
              obtain ⟨Q1, Q2, hQ1, hQ2, hs1, hs2, hne12⟩ := exists_two_leftover_in h2
              have hRchoice : ∃ R, R ∈ leftoverPieces Aind pH ∧
                  R.start ∈ U0 ∧ R ≠ Qi := by
                by_cases h1 : Q1 = Qi
                · exact ⟨Q2, hQ2, hs2, fun h => hne12 (h1.trans h.symm)⟩
                · exact ⟨Q1, hQ1, hs1, h1⟩
              obtain ⟨R, hR, hRU0, hneQiR⟩ := hRchoice
              have hneSt : Qi.start ≠ R.start := by
                intro heq
                have hdisjQR : Disjoint Qi.support R.support :=
                  PathCover.pairwise_disjoint_of_mem
                    (leftoverPieces_pairwise (B := Aind) pH) hQi hR hneQiR.symm
                exact Finset.disjoint_left.1 hdisjQR Qi.start_mem_support
                  (heq ▸ R.start_mem_support)
              let r := cDind.openAt hdC
              have hr : r.support = Dind := by
                simpa [r, hcDind] using openAt_support cDind hdC
              have hrd : r.finish = d := openAt_finish cDind hdC
              have hre : r.start = evert := openAt_start cDind hdC
              have hRsX : R.start ∈ X := hstartX R hR (hU0subU hRU0)
              have hQsX : Qi.start ∈ X := hstartX Qi hQi (hU0subU hQiU0)
              have hRfX : R.finish ∈ X :=
                hfinX0 R hR (hU0subU (hstay R hR hRU0 R.finish_mem_support))
              have hQfX : Qi.finish ∈ X :=
                hfinX0 Qi hQi (hU0subU (hstay Qi hQi hQiU0 Qi.finish_mem_support))
              by_cases hst : u = Qi.start
              · have hadjQe : Gind.Adj Qi.start r.start := by
                  simpa [hst, hre] using hadjue.symm
                have hadjdR : Gind.Adj r.finish R.start := by
                  simpa [hrd] using (hjoin hRsX hdY).symm
                obtain ⟨q, hsup, hProt, hstA, hfin, hne⟩ :=
                  exists_switchThrough_leftover_starts (cH := cHind) hcHind hAind
                    hpH hsH hcloseH hedgesH hr hdisjind hQi hR hneSt hadjQe hadjdR
                exact ⟨q, hsup, hstA, hfin, hne, hProt⟩
              · by_cases hfn : u = Qi.finish
                · have hneFin : Qi.finish ≠ R.finish := by
                    intro heq
                    have hdisjQR : Disjoint Qi.support R.support :=
                      PathCover.pairwise_disjoint_of_mem
                        (leftoverPieces_pairwise (B := Aind) pH) hQi hR hneQiR.symm
                    exact Finset.disjoint_left.1 hdisjQR Qi.finish_mem_support
                      (heq ▸ R.finish_mem_support)
                  have hadjQe : Gind.Adj Qi.finish r.start := by
                    simpa [hfn, hre] using hadjue.symm
                  have hadjdR : Gind.Adj r.finish R.finish := by
                    simpa [hrd] using (hjoin hRfX hdY).symm
                  obtain ⟨q, hsup, hProt, hstA, hfin, hne⟩ :=
                    exists_switchThrough_leftover_finishes (cH := cHind) hcHind
                      hAind hpH hsH hcloseH hedgesH hr hdisjind hQi hR hneFin
                      hadjQe hadjdR
                  exact ⟨q, hsup, hstA, hfin, hne, hProt⟩
                · have hneSF : Qi.start ≠ Qi.finish := by
                    intro h
                    have hn : Qi.walk.Nil := (nil_iff_start_eq_finish Qi).2 h
                    have hsing : Qi.support = {Qi.start} :=
                      support_eq_singleton_of_nil Qi hn
                    have : u = Qi.start := by
                      have : u ∈ ({Qi.start} : Finset V) := by
                        simpa [hsing] using huQi
                      exact mem_singleton.1 this
                    exact hst this
                  have h2Q : 2 ≤ Qi.support.card :=
                    two_le_card_of_start_ne_finish Qi hneSF
                  have hQsubK : Qi.support ⊆ Hind \ Aind :=
                    leftover_support_subset_K hpH hQi
                  have hcogQ : IsCograph Gind Qi.support := hK0c.subset hQsubK
                  have huEl : Eligible Gind Qi.support u :=
                    eligible_on_leftover_of_eligible_K0 (H := Hind) (A := Aind)
                      hK0ind hpH hmin0 hpaths0 hQi huE huQi
                  obtain ⟨p0, hp0, hst0, hf0, hP0⟩ :=
                    exists_spanning_H_from_eligible_leftover (cH := cHind)
                      hcHind hpH hsH hcloseH hedgesH hQi huQi h2Q hcogQ huEl
                  have huA : p0.start ∉ Aind := by
                    have : u ∈ Hind \ Aind := hQsubK huQi
                    simpa [hst0] using (mem_sdiff.1 this).2
                  have hadjUe : Gind.Adj p0.start r.start := by
                    simpa [hst0, hre] using hadjue.symm
                  have h4p0 : 4 ≤ (cHind.boundaryEdges U0).card :=
                    four_le_card_cycle_boundary_U0 (c := cHind) hcHind hU0 hpH hsH
                      hedgesH hstay h2
                  have hYu : ({u} : Finset V) ⊆ U0 := singleton_subset_iff.2 huU0
                  have huNotA : u ∉ Aind := (mem_sdiff.1 (hQsubK huQi)).2
                  have hdisjAu : Disjoint Aind ({u} : Finset V) :=
                    disjoint_singleton_right.2 huNotA
                  have hAH : Aind ⊆ p0.support := by simpa [hp0] using hAind
                  have h2p0 : 2 ≤ p0.support.card := by
                    have h3 : 3 ≤ Hind.card := by
                      simpa [hcHind] using cHind.three_le_card_support
                    simpa [hp0] using
                      (le_trans (by decide : (2 : ℕ) ≤ 3) h3)
                  have h3bd : 3 ≤ (p0.boundaryEdges U0).card :=
                    three_le_path_boundary_weak (c := cHind) hcHind hAind hU0 hYu
                      hnocrossU0 hdisjAu hAH hP0 (by simp [hst0]) h4p0 h2p0
                  have hsU0 : p0.start ∈ U0 := by simpa [hst0] using huU0
                  obtain ⟨i, F, hi, haU0, hxU0, _haneS, _haneF⟩ :=
                    p0.exists_enteringFactor U0 hsU0
                      (le_trans (by decide : (2 : ℕ) ≤ 3) h3bd)
                  set a := p0.walk.getVert i
                  set x := p0.walk.getVert (i + 1)
                  have haP : a ∈ p0.support :=
                    List.mem_toFinset.2 (Walk.getVert_mem_support p0.walk i)
                  have hxP : x ∈ p0.support :=
                    List.mem_toFinset.2 (Walk.getVert_mem_support p0.walk (i + 1))
                  have haH : a ∈ Hind := by simpa [hp0] using haP
                  have haA : a ∈ Aind := by
                    by_contra hna
                    have haK : a ∈ (Hind \ Aind) \ U0 :=
                      mem_sdiff.2 ⟨mem_sdiff.2 ⟨haH, hna⟩, haU0⟩
                    exact hnocrossU0 x hxU0 a haK F.oldAdj.symm
                  have hxA : x ∉ Aind := (mem_sdiff.1 (hU0 hxU0)).2
                  have hxX : x ∈ X := by
                    obtain ⟨Qx, hQx, hxQx, hQsU0, _⟩ :=
                      leftover_U0_run_of_mem (U := Hind) (A := Aind) (U0 := U0)
                        hpH hU0 hnocrossU0 hstay hxU0
                    have haQx : a ∉ Qx.support :=
                      disjoint_right.1 (leftoverPieces_disjoint_B pH Qx hQx) haA
                    have heC : s(a, x) ∈ cHind.walk.edges.toFinset :=
                      hP0 (mem_AIncident_iff.2 ⟨F.old_mem_edges, ⟨a, haA, by simp⟩⟩)
                    have heUnion :
                        s(a, x) ∈
                          pH.walk.edges.toFinset ∪ {s(pH.finish, pH.start)} := by
                      rwa [← hedgesH] at heC
                    rcases Finset.mem_union.1 heUnion with heP | hcl
                    · have hends :=
                        leftover_endpoint_of_leaving_edge (A := Aind) hQx
                          heP hxQx haQx
                      rcases hends with hst | hfn
                      · have hst' : x = Qx.start := hst
                        simpa [hst'] using
                          hstartX Qx hQx (hU0subU (by simpa [hst'] using hxU0))
                      · have hfn' : x = Qx.finish := hfn
                        simpa [hfn'] using
                          hfinX0 Qx hQx (hU0subU (by simpa [hfn'] using hxU0))
                    · have heq : s(a, x) = s(pH.finish, pH.start) :=
                        mem_singleton.1 hcl
                      have hxfin : x = pH.finish := by
                        have : x ∈ s(pH.finish, pH.start) := by
                          simpa [heq] using (by simp : x ∈ s(a, x))
                        rcases Sym2.mem_iff.1 this with h | h
                        · exact h
                        · exact (hxA (h ▸ hsH)).elim
                      have hQfin : Qx.finish = pH.finish :=
                        leftover_finish_eq_of_mem hQx
                          (by simpa [hxfin] using hxQx)
                      simpa [hxfin, hQfin] using
                        hfinX0 Qx hQx
                          (hU0subU (by simpa [hxfin, hQfin] using hxU0))
                  have hadjdX : Gind.Adj r.finish x := by
                    simpa [hrd] using (hjoin hxX hdY).symm
                  obtain ⟨q, hsup, hProt, hstA, hfin, hne⟩ :=
                    exists_insert_D_across_factor (cH := cHind) hcHind hAind
                      hp0 huA hf0 hP0 hr hdisjind hadjUe hadjdX F haA hxA
                  exact ⟨q, hsup, hstA, hfin, hne, hProt⟩
            · exact (hYYd ⟨d, hdDY, hdC, heY⟩).elim
          · have hDsubX : Dind ⊆ X := by
              intro z hz
              rcases hmemXY z (hDU hz) with hXz | hYz
              · exact hXz
              · exact (hDY ⟨z, mem_inter.2 ⟨hz, hYz⟩⟩).elim
            have hYold : Y ⊆ U0 := by
              intro y hy
              have hyU : y ∈ U := hY hy
              have hyD : y ∉ Dind := fun hD =>
                disjoint_left.1 hdisjXY (hDsubX hD) hy
              have hyK0 : y ∈ Hind \ Aind := by
                rcases mem_union.1 (hUK hyU) with h | hD
                · exact h
                · exact (hyD hD).elim
              exact mem_inter.2 ⟨hyU, hyK0⟩
            have h4 : 4 ≤ (cHind.boundaryEdges U0).card :=
              four_le_card_cycle_boundary_U0 (c := cHind) hcHind hU0 hpH hsH
                hedgesH hstay h2
            have hnoYY : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 →
                ∀ u ∈ Y, ∀ v ∈ Y, s(u, v) ∉ Q.edges := by
              intro Q hQ hsU u hu v hv he
              exact hYY ⟨Q, hQ, hsU, u, mem_inter.2 ⟨hu, hYold hu⟩,
                v, mem_inter.2 ⟨hv, hYold hv⟩, he⟩
            have hfinX := finish_mem_of_start_U0 (S := X) hstay
              (fun Q hQ hf => hfinX0 Q hQ (hU0subU hf))
            have hstartXU0 : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ X :=
              fun Q hQ hs => hstartX Q hQ (hU0subU hs)
            have hsurv :=
              cycle_edges_mem_suppressInternal_noYY (c := cHind) hcHind hU0
                hYold hdisjXY hpH hsH hedgesH hnoAA hnocrossU0 hstay
                hstartXU0 hfinX hnoYY
            have hdisjDA' : Disjoint Dind (Aind ∪ Y) := by
              refine disjoint_union_right.2 ⟨hdisjind.symm.mono_right hAind, ?_⟩
              exact disjoint_of_subset_right (hYold.trans (hU0.trans sdiff_subset))
                hdisjind.symm
            have hsurvD :
                ∀ e ∈ cDind.edges, e ∈ (suppressInternal Gind (Aind ∪ Y)).edgeSet :=
              cycle_edges_subset_suppressInternal_of_disjoint (G := Gind)
                cDind (by simpa [hcDind] using hdisjDA')
            let G' := suppressInternal Gind (Aind ∪ Y)
            let cH' := cHind.transferEdges hsurv
            let cD' := cDind.transferEdges hsurvD
            have hcH' : cH'.support = Hind :=
              (GraphCycle.transferEdges_support cHind hsurv).trans hcHind
            have hcD' : cD'.support = Dind :=
              (GraphCycle.transferEdges_support cDind hsurvD).trans hcDind
            have hedges' : cH'.edges = cHind.edges :=
              GraphCycle.transferEdges_edges cHind hsurv
            have hA'sub : Aind ∪ Y ⊆ Hind := by
              intro x hx
              rcases mem_union.1 hx with h | h
              · exact hAind h
              · exact (mem_sdiff.1 (hU0 (hYold h))).1
            have hAne' : (Aind ∪ Y).Nonempty := hAneind.mono subset_union_left
            have hdisjAY : Disjoint Aind Y :=
              disjoint_of_subset_right (hYold.trans hU0) disjoint_sdiff
            have hpc0min : pc0.card = pathCoverNumber Gind (Hind \ Aind) := by
              simpa [hpK0ind] using hmin0
            have hpU0eq :
                leftoverCountIn pc0 U0 = pathCoverNumber Gind U0 :=
              leftoverCountIn_eq_pathCoverNumber_of_min_nocross hU0
                hnocrossU0 pc0 hpc0min
            have hpU0 : 2 ≤ pathCoverNumber Gind U0 := by
              have hcnt : leftoverCountIn pc0 U0 =
                  (List.filter (fun Q => Q.start ∈ U0)
                    (leftoverPieces Aind pH)).length := by
                simp [leftoverCountIn, hpaths0]
              have : 2 ≤ leftoverCountIn pc0 U0 := by simpa [hcnt] using h2
              simpa [hpU0eq] using this
            let pcU0 := actualFilteredCover hU0 hnocrossU0 pc0
            have hcardU0 : pcU0.card = leftoverCountIn pc0 U0 :=
              actualFilteredCover_card hU0 hnocrossU0 pc0
            have hY0eq : Y0 = Y := by
              ext z
              constructor
              · intro hz; exact (mem_inter.1 hz).1
              · intro hz; exact mem_inter.2 ⟨hz, hYold hz⟩
            have hX0Y : X0 ∪ Y = U0 := by simpa [hY0eq] using hcover0
            have hjoinX0Y : Gind.IsCompleteBetween (X0 : Set V) (Y : Set V) := by
              intro x hx y hy
              exact hjoin0 hx (by simpa [hY0eq] using hy)
            have hdisjX0Y : Disjoint X0 Y :=
              disjoint_of_subset_left inter_subset_left hdisjXY
            have hendsU0 : ∀ Q ∈ pcU0.paths, Q.start ∈ X0 ∧ Q.finish ∈ X0 := by
              intro Q hQ
              have hmem : Q ∈ pc0.paths.filter (fun Q => Q.start ∈ U0) := by
                rwa [← actualFilteredCover_paths hU0 hnocrossU0 pc0]
              have hQf := List.mem_filter.1 hmem
              have hQl : Q ∈ leftoverPieces Aind pH := by
                simpa [hpaths0] using hQf.1
              exact ⟨hstartX0 Q hQl (of_decide_eq_true hQf.2),
                hfinX0' Q hQl (of_decide_eq_true hQf.2)⟩
            have hnoU0 : ∀ Q ∈ pcU0.paths, NoConsecutive Y Q := by
              intro Q hQ
              have hmem : Q ∈ pc0.paths.filter (fun Q => Q.start ∈ U0) := by
                rwa [← actualFilteredCover_paths hU0 hnocrossU0 pc0]
              have hQf := List.mem_filter.1 hmem
              have hQl : Q ∈ leftoverPieces Aind pH := by
                simpa [hpaths0] using hQf.1
              have hsU0 : Q.start ∈ U0 := of_decide_eq_true hQf.2
              intro e
              refine Sym2.inductionOn e (fun u v => ?_)
              intro he hb
              have ⟨huY, hvY⟩ := bothEndsIn_iff.1 hb
              exact hnoYY Q hQl hsU0 u huY v hvY he
            have hX0sub : X0 ⊆ U0 := inter_subset_right
            have hcardXY :
                pathCoverNumber Gind U0 + Y.card ≤ X0.card := by
              have := card_X_ge_add_of_X_ended_cover (X := X0) (Y := Y)
                (U0 := U0) hdisjX0Y hX0Y.symm hX0sub hYold pcU0 hendsU0 hnoU0
              simpa [hcardU0, hpU0eq] using this
            have hX0ne : X0.Nonempty := by
              have : 0 < X0.card := by
                have hpos : 1 ≤ pathCoverNumber Gind U0 + Y.card :=
                  (one_le_pathCoverNumber_of_nonempty (G := Gind) hU0ne).trans
                    (Nat.le_add_right _ _)
                omega
              exact card_pos.1 this
            have hpK0Y :
                pathCoverNumber Gind ((Hind \ Aind) \ Y) =
                  pathCoverNumber Gind (Hind \ Aind) + Y.card :=
              pathCoverNumber_sdiff_Y_eq_add_of_nocross_join
                (W := Hind \ Aind) (U0 := U0) (X := X0) (Y := Y)
                hU0 hX0sub hYold hX0ne hYne hdisjX0Y hX0Y hjoinX0Y
                hnocrossU0 hpU0 hcardXY
            have hEqAY : Hind \ (Aind ∪ Y) = (Hind \ Aind) \ Y :=
              (sdiff_sdiff_eq_sdiff_union Hind Aind Y).symm
            have hK0ind' : Nikoghosyan.IsCograph G' (Hind \ (Aind ∪ Y)) :=
              isCograph_iff.1
                (isCograph_suppressInternal (Finset.disjoint_sdiff).symm
                  (isCograph_sdiff_union_Y (U := Hind) (A := Aind) (Y := Y) hK0c))
            have hKind' : Nikoghosyan.IsCograph G'
                ((Hind \ (Aind ∪ Y)) ∪ Dind) := by
              have hdisj : Disjoint ((Hind \ (Aind ∪ Y)) ∪ Dind) (Aind ∪ Y) :=
                disjoint_union_left.2 ⟨Finset.disjoint_sdiff.symm, hdisjDA'⟩
              have hsub : (Hind \ (Aind ∪ Y)) ∪ Dind ⊆
                  (Hind \ Aind) ∪ Dind := by
                intro z hz
                rcases mem_union.1 hz with h | h
                · have hz' : z ∈ (Hind \ Aind) \ Y := by simpa [hEqAY] using h
                  exact mem_union.2 (Or.inl (mem_sdiff.1 hz').1)
                · exact mem_union.2 (Or.inr h)
              exact isCograph_iff.1 (isCograph_suppressInternal hdisj (hKc.subset hsub))
            have hpK0' :
                pathCoverNumber G' (Hind \ (Aind ∪ Y)) = (Aind ∪ Y).card := by
              have hdisj : Disjoint (Hind \ (Aind ∪ Y)) (Aind ∪ Y) :=
                Finset.disjoint_sdiff.symm
              have hp := pathCoverNumber_suppressInternal (G := Gind) hdisj
              have hAY : (Aind ∪ Y).card = Aind.card + Y.card :=
                card_union_of_disjoint hdisjAY
              have hpG : pathCoverNumber Gind (Hind \ (Aind ∪ Y)) =
                  (Aind ∪ Y).card := by
                simpa [hEqAY, hpK0ind, hAY] using hpK0Y
              exact hp.trans hpG
            have hpK' :
                pathCoverNumber G' ((Hind \ (Aind ∪ Y)) ∪ Dind) <
                  (Aind ∪ Y).card := by
              have hdisj : Disjoint ((Hind \ (Aind ∪ Y)) ∪ Dind) (Aind ∪ Y) :=
                disjoint_union_left.2 ⟨Finset.disjoint_sdiff.symm, hdisjDA'⟩
              have hpEq := pathCoverNumber_suppressInternal (G := Gind) hdisj
              have hKsY : ((Hind \ Aind) ∪ Dind) \ Y =
                  (Hind \ (Aind ∪ Y)) ∪ Dind := by
                ext z
                constructor
                · intro hz
                  have hzKY : z ∈ (Hind \ Aind) ∪ Dind := (mem_sdiff.1 hz).1
                  have hzY : z ∉ Y := (mem_sdiff.1 hz).2
                  rcases mem_union.1 hzKY with hz0 | hzD
                  · refine mem_union.2 (Or.inl ?_)
                    simpa [hEqAY] using (mem_sdiff.2 ⟨hz0, hzY⟩ : z ∈ (Hind \ Aind) \ Y)
                  · exact mem_union.2 (Or.inr hzD)
                · intro hz
                  rcases mem_union.1 hz with hz0 | hzD
                  · have hz' : z ∈ (Hind \ Aind) \ Y := by simpa [hEqAY] using hz0
                    exact mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hz').1),
                      (mem_sdiff.1 hz').2⟩
                  · exact mem_sdiff.2 ⟨mem_union.2 (Or.inr hzD), fun hy =>
                      disjoint_left.1 hdisjind
                        ((mem_sdiff.1 (hU0 (hYold hy))).1) hzD⟩
              have hle := pathCoverNumber_sdiff_le (G := Gind)
                ((Hind \ Aind) ∪ Dind) Y
                (hYold.trans (hU0.trans subset_union_left))
              have hAY : (Aind ∪ Y).card = Aind.card + Y.card :=
                card_union_of_disjoint hdisjAY
              have hltG : pathCoverNumber Gind ((Hind \ (Aind ∪ Y)) ∪ Dind) <
                  Aind.card + Y.card := by
                have : pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ Y) ≤
                    pathCoverNumber Gind ((Hind \ Aind) ∪ Dind) + Y.card := hle
                have : pathCoverNumber Gind ((Hind \ (Aind ∪ Y)) ∪ Dind) ≤
                    pathCoverNumber Gind ((Hind \ Aind) ∪ Dind) + Y.card := by
                  simpa [hKsY] using this
                omega
              have hltG' :
                  pathCoverNumber G' ((Hind \ (Aind ∪ Y)) ∪ Dind) <
                    Aind.card + Y.card :=
                hpEq.symm ▸ hltG
              simpa [hAY] using hltG'
            have hE' : ∀ d ∈ Dind, ∃ u ∈ eligibleSet G' (Hind \ (Aind ∪ Y)),
                G'.Adj d u := by
              have hdom : Y.card < pathCoverNumber Gind X0 := by
                have hpX := pathCoverNumber_X_eq_add_card_Y (U0 := U0)
                  hX0ne hYne hdisjX0Y hX0Y.symm hjoinX0Y hpU0 hcardXY
                omega
              have hEU0 :
                  eligibleSet Gind U0 = eligibleSet Gind X0 := by
                simpa [hX0Y] using
                  eligibleSet_complete_join_dominant hX0ne hYne hjoinX0Y hdom
              have hdisjRest : Disjoint U0 ((Hind \ Aind) \ U0) := disjoint_sdiff
              have hEKA :
                  eligibleSet Gind (Hind \ Aind) =
                    eligibleSet Gind U0 ∪
                      eligibleSet Gind ((Hind \ Aind) \ U0) := by
                simpa [union_sdiff_of_subset hU0] using
                  eligibleSet_disjoint_union (G := Gind) hdisjRest hnocrossU0
              have hdisjXrest : Disjoint X0 ((Hind \ Aind) \ U0) :=
                disjoint_of_subset_left hX0sub disjoint_sdiff
              have hncXrest : ∀ a ∈ X0, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b :=
                fun a ha => hnocrossU0 a (hX0sub ha)
              have hEKY :
                  eligibleSet Gind (Hind \ (Aind ∪ Y)) =
                    eligibleSet Gind X0 ∪
                      eligibleSet Gind ((Hind \ Aind) \ U0) := by
                have hW : X0 ∪ ((Hind \ Aind) \ U0) = Hind \ (Aind ∪ Y) := by
                  rw [hEqAY]
                  ext z
                  constructor
                  · intro hz
                    rcases mem_union.1 hz with hzX | hzR
                    · exact mem_sdiff.2 ⟨hU0 (mem_inter.1 hzX).2, fun hy =>
                        disjoint_left.1 hdisjX0Y hzX hy⟩
                    · exact mem_sdiff.2 ⟨(mem_sdiff.1 hzR).1, fun hy =>
                        (mem_sdiff.1 hzR).2 (hYold hy)⟩
                  · intro hz
                    have hz0 : z ∈ Hind \ Aind := (mem_sdiff.1 hz).1
                    have hzY : z ∉ Y := (mem_sdiff.1 hz).2
                    by_cases hzU : z ∈ U0
                    · have hzXY : z ∈ X0 ∪ Y := by simpa [hX0Y] using hzU
                      rcases mem_union.1 hzXY with h | h
                      · exact mem_union.2 (Or.inl h)
                      · exact (hzY h).elim
                    · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hz0, hzU⟩))
                simpa [hW] using
                  eligibleSet_disjoint_union (G := Gind) hdisjXrest hncXrest
              have hEeq : eligibleSet Gind (Hind \ Aind) =
                  eligibleSet Gind (Hind \ (Aind ∪ Y)) := by
                rw [hEKA, hEKY, hEU0]
              have hEsup : eligibleSet G' (Hind \ (Aind ∪ Y)) =
                  eligibleSet Gind (Hind \ (Aind ∪ Y)) :=
                eligibleSet_suppressInternal (G := Gind)
                  (Finset.disjoint_sdiff).symm
              intro d hd
              obtain ⟨u, huE, hadj⟩ := hEind d hd
              have hu' : u ∈ eligibleSet G' (Hind \ (Aind ∪ Y)) := by
                have : u ∈ eligibleSet Gind (Hind \ (Aind ∪ Y)) := by
                  simpa [hEeq] using huE
                simpa [hEsup] using this
              have huA' : u ∉ Aind ∪ Y :=
                disjoint_left.1 (Finset.disjoint_sdiff.symm)
                  ((eligibleSet_subset (G := G') (Hind \ (Aind ∪ Y))) hu')
              have hdA' : d ∉ Aind ∪ Y := disjoint_left.1 hdisjDA' hd
              exact ⟨u, hu', (adj_eq_on_carrier (G := Gind) hdA' huA').2 hadj⟩
            have hlt : ((Hind \ (Aind ∪ Y)) ∪ Dind).card < n := by
              have hsubY : Y ⊆ Hind \ Aind := hYold.trans hU0
              have hpos : 0 < Y.card := card_pos.2 hYne
              have hdisjD : Disjoint (Hind \ Aind) Dind :=
                disjoint_of_subset_left sdiff_subset hdisjind
              have hdisjD' : Disjoint ((Hind \ Aind) \ Y) Dind :=
                disjoint_of_subset_left sdiff_subset hdisjD
              have hn : n = (Hind \ Aind).card + Dind.card := by
                rw [← hcard, card_union_of_disjoint hdisjD]
              have hnew : ((Hind \ (Aind ∪ Y)) ∪ Dind).card =
                  ((Hind \ Aind) \ Y).card + Dind.card := by
                rw [hEqAY, card_union_of_disjoint hdisjD']
              have hYle : Y.card ≤ (Hind \ Aind).card := card_le_card hsubY
              rw [hnew, card_sdiff_of_subset hsubY, hn]
              omega
            have hXW : X ⊆ U0 ∪ Dind := by
              intro z hz
              have hzU : z ∈ U := by
                have hzXY : z ∈ X ∪ Y := mem_union.2 (Or.inl hz)
                simpa [hcover] using hzXY
              have : U ⊆ U0 ∪ Dind := by
                intro w hw
                by_cases hwD : w ∈ Dind
                · exact mem_union.2 (Or.inr hwD)
                · have hwK : w ∈ Hind \ Aind := by
                    rcases mem_union.1 (hUK hw) with h | h
                    · exact h
                    · exact (hwD h).elim
                  exact mem_union.2 (Or.inl (mem_inter.2 ⟨hw, hwK⟩))
              exact this hzU
            have hnorestD : ∀ a ∈ Dind, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b := by
              intro a ha b hb hadj
              have haU : a ∈ U := hDU ha
              exact hUnc a haU b (mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hb).1),
                fun hU => (mem_sdiff.1 hb).2 (mem_inter.2 ⟨hU, (mem_sdiff.1 hb).1⟩)⟩) hadj
            obtain ⟨q', hq'sup, hq'st, hq'fin, hq'ne, hq'P⟩ :=
              ih ((Hind \ (Aind ∪ Y)) ∪ Dind).card hlt G' Hind Dind (Aind ∪ Y)
                cH' cD' rfl hcH' hcD' hdisjind hA'sub hAne' hK0ind' hpK0'
                hKind' hE' hpK'
            obtain ⟨q, hsup, hst, hfin, hne, hP⟩ :=
              exists_lift_restored_W (c := cHind) hcHind hAind hU0 hXW hYold
                hdisjXY hdisjind hYne hjoin hnocrossU0 hnorestD hpH hsH hedgesH
                hstay hstartXU0 hfinX h4 hq'sup hcH' hq'st hq'fin hq'ne hq'P
                hedges'
            exact ⟨q, hsup, hst, hfin, hne, hP⟩
    · have hstartX0 : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ X0 :=
        fun Q hQ hs => mem_inter.2 ⟨hstartX Q hQ (hU0subU hs), hs⟩
      have hfinY0' : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.finish ∈ Y0 :=
        fun Q hQ hs =>
          mem_inter.2 ⟨hfinY0 Q hQ (hU0subU (hstay Q hQ hs Q.finish_mem_support)),
            hstay Q hQ hs Q.finish_mem_support⟩
      obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
        exists_protectedAt_of_join_insert_XZ_of_saving (c := cHind) hcHind
          hU0 hjoin0 hcover0 hpH hsH hcloseH hedgesH hstay h2 hstartX0 hfinY0'
      exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
  · rcases hfinSide with hfinX0 | hfinY0
    · have hstartY0 : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ Y0 :=
        fun Q hQ hs => mem_inter.2 ⟨hstartY Q hQ (hU0subU hs), hs⟩
      have hfinX0' : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.finish ∈ X0 :=
        fun Q hQ hs =>
          mem_inter.2 ⟨hfinX0 Q hQ (hU0subU (hstay Q hQ hs Q.finish_mem_support)),
            hstay Q hQ hs Q.finish_mem_support⟩
      have hjoin0YX : Gind.IsCompleteBetween (Y0 : Set V) (X0 : Set V) :=
        fun {y} hy {x} hx => (hjoin0 hx hy).symm
      have hcover0YX : Y0 ∪ X0 = U0 := by rw [union_comm, hcover0]
      obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
        exists_protectedAt_of_join_insert_XZ_of_saving (c := cHind) hcHind
          hU0 hjoin0YX hcover0YX hpH hsH hcloseH hedgesH hstay h2
          hstartY0 hfinX0'
      exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
    · have hstartY0 : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ Y0 :=
        fun Q hQ hs => mem_inter.2 ⟨hstartY Q hQ (hU0subU hs), hs⟩
      have hfinY0' : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.finish ∈ Y0 :=
        fun Q hQ hs =>
          mem_inter.2 ⟨hfinY0 Q hQ (hU0subU (hstay Q hQ hs Q.finish_mem_support)),
            hstay Q hQ hs Q.finish_mem_support⟩
      by_cases hXX : ∃ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 ∧
          ∃ u ∈ X0, ∃ v ∈ X0, s(u, v) ∈ Q.edges
      · obtain ⟨Q, hQ, hQs, u, huX, v, hvX, huvQ⟩ := hXX
        have hadjuv : Gind.Adj u v := by
          simpa [SimpleGraph.mem_edgeSet] using Q.edges_subset_edgeSet _ huvQ
        have hjoin0YX : Gind.IsCompleteBetween (Y0 : Set V) (X0 : Set V) :=
          fun {y} hy {x} hx => (hjoin0 hx hy).symm
        have hcover0YX : Y0 ∪ X0 = U0 := by rw [union_comm, hcover0]
        obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
          exists_protectedAt_of_join_insert_YY_of_saving (c := cHind) hcHind
            hU0 hjoin0YX hcover0YX hpH hsH hcloseH hedgesH hstay h2
            hfinY0' hstartY0 hQ hQs huX hvX hadjuv huvQ
        exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
      · by_cases hXXd : ∃ d ∈ Dind ∩ X, ∃ hdC : d ∈ cDind.support,
            cDind.succAt hdC ∈ X
        · obtain ⟨d, hdDX, hdC, heX⟩ := hXXd
          have hdX : d ∈ X := (mem_inter.1 hdDX).2
          let r := cDind.openAt hdC
          have hr : r.support = Dind := by
            simpa [r, hcDind] using openAt_support cDind hdC
          have hrd : r.finish = d := openAt_finish cDind hdC
          have hreX : r.start ∈ X := by
            simpa [r, openAt_start cDind hdC] using heX
          obtain ⟨Q, R, hQ, hR, hQs, hRs, hneQR⟩ := exists_two_leftover_in h2
          have hQsY : Q.start ∈ Y := hstartY Q hQ (hU0subU hQs)
          have hRsY : R.start ∈ Y := hstartY R hR (hU0subU hRs)
          have hneSt : Q.start ≠ R.start := by
            intro heq
            have hdisjQR : Disjoint Q.support R.support :=
              PathCover.pairwise_disjoint_of_mem
                (leftoverPieces_pairwise (B := Aind) pH) hQ hR hneQR
            exact Finset.disjoint_left.1 hdisjQR Q.start_mem_support
              (heq ▸ R.start_mem_support)
          have hadjQe : Gind.Adj Q.start r.start := hjoinYX hQsY hreX
          have hadjdR : Gind.Adj r.finish R.start := by
            simpa [hrd] using (hjoinYX hRsY hdX).symm
          obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
            exists_switchThrough_leftover_starts (cH := cHind) hcHind hAind
              hpH hsH hcloseH hedgesH hr hdisjind hQ hR hneSt hadjQe hadjdR
          exact ⟨q, hsup, hst, hfin, hne, hProt⟩
        · -- Dual: leftover ends in `Y`. Mixed `D ∩ X` or pure `D ⊆ Y`.
          by_cases hDX : (Dind ∩ X).Nonempty
          · obtain ⟨d, hdDX⟩ := hDX
            have hdD : d ∈ Dind := (mem_inter.1 hdDX).1
            have hdX : d ∈ X := (mem_inter.1 hdDX).2
            have hdC : d ∈ cDind.support := by simpa [hcDind] using hdD
            have heD : cDind.succAt hdC ∈ Dind := by
              simpa [hcDind] using succAt_mem_support cDind hdC
            rcases hmemXY _ (hDU heD) with heX | heY
            · exact (hXXd ⟨d, hdDX, hdC, heX⟩).elim
            · let evert := cDind.succAt hdC
              have heY' : evert ∈ Y := heY
              obtain ⟨u, huE, hadjue⟩ := hEind evert heD
              have huK0 : u ∈ Hind \ Aind :=
                eligibleSet_subset (G := Gind) (Hind \ Aind) huE
              have heU : evert ∈ U := hDU heD
              have huU : u ∈ U := by
                by_contra hnu
                exact hUnc evert heU u
                  (mem_sdiff.2 ⟨mem_union.2 (Or.inl huK0), hnu⟩) hadjue
              have huU0 : u ∈ U0 := mem_inter.2 ⟨huU, huK0⟩
              obtain ⟨Qi, hQi, huQi, hQiU0, _hQisup⟩ :=
                leftover_U0_run_of_mem (U := Hind) (A := Aind) (U0 := U0)
                  hpH hU0 hnocrossU0 hstay huU0
              obtain ⟨Q1, Q2, hQ1, hQ2, hs1, hs2, hne12⟩ := exists_two_leftover_in h2
              have hRchoice : ∃ R, R ∈ leftoverPieces Aind pH ∧
                  R.start ∈ U0 ∧ R ≠ Qi := by
                by_cases h1 : Q1 = Qi
                · exact ⟨Q2, hQ2, hs2, fun h => hne12 (h1.trans h.symm)⟩
                · exact ⟨Q1, hQ1, hs1, h1⟩
              obtain ⟨R, hR, hRU0, hneQiR⟩ := hRchoice
              have hneSt : Qi.start ≠ R.start := by
                intro heq
                have hdisjQR : Disjoint Qi.support R.support :=
                  PathCover.pairwise_disjoint_of_mem
                    (leftoverPieces_pairwise (B := Aind) pH) hQi hR hneQiR.symm
                exact Finset.disjoint_left.1 hdisjQR Qi.start_mem_support
                  (heq ▸ R.start_mem_support)
              let r := cDind.openAt hdC
              have hr : r.support = Dind := by
                simpa [r, hcDind] using openAt_support cDind hdC
              have hrd : r.finish = d := openAt_finish cDind hdC
              have hre : r.start = evert := openAt_start cDind hdC
              have hRsY : R.start ∈ Y := hstartY R hR (hU0subU hRU0)
              have hQsY : Qi.start ∈ Y := hstartY Qi hQi (hU0subU hQiU0)
              have hRfY : R.finish ∈ Y :=
                hfinY0 R hR (hU0subU (hstay R hR hRU0 R.finish_mem_support))
              have hQfY : Qi.finish ∈ Y :=
                hfinY0 Qi hQi (hU0subU (hstay Qi hQi hQiU0 Qi.finish_mem_support))
              by_cases hst : u = Qi.start
              · have hadjQe : Gind.Adj Qi.start r.start := by
                  simpa [hst, hre] using hadjue.symm
                have hadjdR : Gind.Adj r.finish R.start := by
                  simpa [hrd] using hjoin hdX hRsY
                obtain ⟨q, hsup, hProt, hstA, hfin, hne⟩ :=
                  exists_switchThrough_leftover_starts (cH := cHind) hcHind hAind
                    hpH hsH hcloseH hedgesH hr hdisjind hQi hR hneSt hadjQe hadjdR
                exact ⟨q, hsup, hstA, hfin, hne, hProt⟩
              · by_cases hfn : u = Qi.finish
                · have hneFin : Qi.finish ≠ R.finish := by
                    intro heq
                    have hdisjQR : Disjoint Qi.support R.support :=
                      PathCover.pairwise_disjoint_of_mem
                        (leftoverPieces_pairwise (B := Aind) pH) hQi hR hneQiR.symm
                    exact Finset.disjoint_left.1 hdisjQR Qi.finish_mem_support
                      (heq ▸ R.finish_mem_support)
                  have hadjQe : Gind.Adj Qi.finish r.start := by
                    simpa [hfn, hre] using hadjue.symm
                  have hadjdR : Gind.Adj r.finish R.finish := by
                    simpa [hrd] using hjoin hdX hRfY
                  obtain ⟨q, hsup, hProt, hstA, hfin, hne⟩ :=
                    exists_switchThrough_leftover_finishes (cH := cHind) hcHind
                      hAind hpH hsH hcloseH hedgesH hr hdisjind hQi hR hneFin
                      hadjQe hadjdR
                  exact ⟨q, hsup, hstA, hfin, hne, hProt⟩
                · have hneSF : Qi.start ≠ Qi.finish := by
                    intro h
                    have hn : Qi.walk.Nil := (nil_iff_start_eq_finish Qi).2 h
                    have hsing : Qi.support = {Qi.start} :=
                      support_eq_singleton_of_nil Qi hn
                    have : u = Qi.start := by
                      have : u ∈ ({Qi.start} : Finset V) := by
                        simpa [hsing] using huQi
                      exact mem_singleton.1 this
                    exact hst this
                  have h2Q : 2 ≤ Qi.support.card :=
                    two_le_card_of_start_ne_finish Qi hneSF
                  have hQsubK : Qi.support ⊆ Hind \ Aind :=
                    leftover_support_subset_K hpH hQi
                  have hcogQ : IsCograph Gind Qi.support := hK0c.subset hQsubK
                  have huEl : Eligible Gind Qi.support u :=
                    eligible_on_leftover_of_eligible_K0 (H := Hind) (A := Aind)
                      hK0ind hpH hmin0 hpaths0 hQi huE huQi
                  obtain ⟨p0, hp0, hst0, hf0, hP0⟩ :=
                    exists_spanning_H_from_eligible_leftover (cH := cHind)
                      hcHind hpH hsH hcloseH hedgesH hQi huQi h2Q hcogQ huEl
                  have huA : p0.start ∉ Aind := by
                    have : u ∈ Hind \ Aind := hQsubK huQi
                    simpa [hst0] using (mem_sdiff.1 this).2
                  have hadjUe : Gind.Adj p0.start r.start := by
                    simpa [hst0, hre] using hadjue.symm
                  have h4p0 : 4 ≤ (cHind.boundaryEdges U0).card :=
                    four_le_card_cycle_boundary_U0 (c := cHind) hcHind hU0 hpH hsH
                      hedgesH hstay h2
                  have hYu : ({u} : Finset V) ⊆ U0 := singleton_subset_iff.2 huU0
                  have huNotA : u ∉ Aind := (mem_sdiff.1 (hQsubK huQi)).2
                  have hdisjAu : Disjoint Aind ({u} : Finset V) :=
                    disjoint_singleton_right.2 huNotA
                  have hAH : Aind ⊆ p0.support := by simpa [hp0] using hAind
                  have h2p0 : 2 ≤ p0.support.card := by
                    have h3 : 3 ≤ Hind.card := by
                      simpa [hcHind] using cHind.three_le_card_support
                    simpa [hp0] using
                      (le_trans (by decide : (2 : ℕ) ≤ 3) h3)
                  have h3bd : 3 ≤ (p0.boundaryEdges U0).card :=
                    three_le_path_boundary_weak (c := cHind) hcHind hAind hU0 hYu
                      hnocrossU0 hdisjAu hAH hP0 (by simp [hst0]) h4p0 h2p0
                  have hsU0 : p0.start ∈ U0 := by simpa [hst0] using huU0
                  obtain ⟨i, F, hi, haU0, hxU0, _haneS, _haneF⟩ :=
                    p0.exists_enteringFactor U0 hsU0
                      (le_trans (by decide : (2 : ℕ) ≤ 3) h3bd)
                  set a := p0.walk.getVert i
                  set x := p0.walk.getVert (i + 1)
                  have haP : a ∈ p0.support :=
                    List.mem_toFinset.2 (Walk.getVert_mem_support p0.walk i)
                  have hxP : x ∈ p0.support :=
                    List.mem_toFinset.2 (Walk.getVert_mem_support p0.walk (i + 1))
                  have haH : a ∈ Hind := by simpa [hp0] using haP
                  have haA : a ∈ Aind := by
                    by_contra hna
                    have haK : a ∈ (Hind \ Aind) \ U0 :=
                      mem_sdiff.2 ⟨mem_sdiff.2 ⟨haH, hna⟩, haU0⟩
                    exact hnocrossU0 x hxU0 a haK F.oldAdj.symm
                  have hxA : x ∉ Aind := (mem_sdiff.1 (hU0 hxU0)).2
                  have hxY : x ∈ Y := by
                    obtain ⟨Qx, hQx, hxQx, hQsU0, _⟩ :=
                      leftover_U0_run_of_mem (U := Hind) (A := Aind) (U0 := U0)
                        hpH hU0 hnocrossU0 hstay hxU0
                    have haQx : a ∉ Qx.support :=
                      disjoint_right.1 (leftoverPieces_disjoint_B pH Qx hQx) haA
                    have heC : s(a, x) ∈ cHind.walk.edges.toFinset :=
                      hP0 (mem_AIncident_iff.2 ⟨F.old_mem_edges, ⟨a, haA, by simp⟩⟩)
                    have heUnion :
                        s(a, x) ∈
                          pH.walk.edges.toFinset ∪ {s(pH.finish, pH.start)} := by
                      rwa [← hedgesH] at heC
                    rcases Finset.mem_union.1 heUnion with heP | hcl
                    · have hends :=
                        leftover_endpoint_of_leaving_edge (A := Aind) hQx
                          heP hxQx haQx
                      rcases hends with hst | hfn
                      · have hst' : x = Qx.start := hst
                        simpa [hst'] using
                          hstartY Qx hQx (hU0subU (by simpa [hst'] using hxU0))
                      · have hfn' : x = Qx.finish := hfn
                        simpa [hfn'] using
                          hfinY0 Qx hQx (hU0subU (by simpa [hfn'] using hxU0))
                    · have heq : s(a, x) = s(pH.finish, pH.start) :=
                        mem_singleton.1 hcl
                      have hxfin : x = pH.finish := by
                        have : x ∈ s(pH.finish, pH.start) := by
                          simpa [heq] using (by simp : x ∈ s(a, x))
                        rcases Sym2.mem_iff.1 this with h | h
                        · exact h
                        · exact (hxA (h ▸ hsH)).elim
                      have hQfin : Qx.finish = pH.finish :=
                        leftover_finish_eq_of_mem hQx
                          (by simpa [hxfin] using hxQx)
                      simpa [hxfin, hQfin] using
                        hfinY0 Qx hQx
                          (hU0subU (by simpa [hxfin, hQfin] using hxU0))
                  have hadjdY : Gind.Adj r.finish x := by
                    simpa [hrd] using hjoin hdX hxY
                  obtain ⟨q, hsup, hProt, hstA, hfin, hne⟩ :=
                    exists_insert_D_across_factor (cH := cHind) hcHind hAind
                      hp0 huA hf0 hP0 hr hdisjind hadjUe hadjdY F haA hxA
                  exact ⟨q, hsup, hstA, hfin, hne, hProt⟩
          · have hDsubY : Dind ⊆ Y := by
              intro z hz
              rcases hmemXY z (hDU hz) with hXz | hYz
              · exact (hDX ⟨z, mem_inter.2 ⟨hz, hXz⟩⟩).elim
              · exact hYz
            have hXold : X ⊆ U0 := by
              intro x hx
              have hxU : x ∈ U := hX hx
              have hxD : x ∉ Dind := fun hD =>
                disjoint_left.1 hdisjXY hx (hDsubY hD)
              have hxK0 : x ∈ Hind \ Aind := by
                rcases mem_union.1 (hUK hxU) with h | hD
                · exact h
                · exact (hxD hD).elim
              exact mem_inter.2 ⟨hxU, hxK0⟩
            have h4 : 4 ≤ (cHind.boundaryEdges U0).card :=
              four_le_card_cycle_boundary_U0 (c := cHind) hcHind hU0 hpH hsH
                hedgesH hstay h2
            have hnoXX : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 →
                ∀ u ∈ X, ∀ v ∈ X, s(u, v) ∉ Q.edges := by
              intro Q hQ hsU u hu v hv he
              exact hXX ⟨Q, hQ, hsU, u, mem_inter.2 ⟨hu, hXold hu⟩,
                v, mem_inter.2 ⟨hv, hXold hv⟩, he⟩
            have hfinY := finish_mem_of_start_U0 (S := Y) hstay
              (fun Q hQ hf => hfinY0 Q hQ (hU0subU hf))
            have hstartYU0 : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ Y :=
              fun Q hQ hs => hstartY Q hQ (hU0subU hs)
            have hdisjYX : Disjoint Y X := hdisjXY.symm
            have hsurv :=
              cycle_edges_mem_suppressInternal_noYY (X := Y) (Y := X)
                (c := cHind) hcHind hU0 hXold hdisjYX hpH hsH hedgesH hnoAA
                hnocrossU0 hstay hstartYU0 hfinY hnoXX
            have hdisjDA' : Disjoint Dind (Aind ∪ X) := by
              refine disjoint_union_right.2 ⟨hdisjind.symm.mono_right hAind, ?_⟩
              exact disjoint_of_subset_left hDsubY hdisjYX
            have hsurvD :
                ∀ e ∈ cDind.edges, e ∈ (suppressInternal Gind (Aind ∪ X)).edgeSet :=
              cycle_edges_subset_suppressInternal_of_disjoint (G := Gind)
                cDind (by simpa [hcDind] using hdisjDA')
            let G' := suppressInternal Gind (Aind ∪ X)
            let cH' := cHind.transferEdges hsurv
            let cD' := cDind.transferEdges hsurvD
            have hcH' : cH'.support = Hind :=
              (GraphCycle.transferEdges_support cHind hsurv).trans hcHind
            have hcD' : cD'.support = Dind :=
              (GraphCycle.transferEdges_support cDind hsurvD).trans hcDind
            have hedges' : cH'.edges = cHind.edges :=
              GraphCycle.transferEdges_edges cHind hsurv
            have hA'sub : Aind ∪ X ⊆ Hind := by
              intro z hz
              rcases mem_union.1 hz with h | h
              · exact hAind h
              · exact (mem_sdiff.1 (hU0 (hXold h))).1
            have hAne' : (Aind ∪ X).Nonempty := hAneind.mono subset_union_left
            have hdisjAX : Disjoint Aind X :=
              disjoint_of_subset_right (hXold.trans hU0) disjoint_sdiff
            have hpc0min : pc0.card = pathCoverNumber Gind (Hind \ Aind) := by
              simpa [hpK0ind] using hmin0
            have hpU0eq :
                leftoverCountIn pc0 U0 = pathCoverNumber Gind U0 :=
              leftoverCountIn_eq_pathCoverNumber_of_min_nocross hU0
                hnocrossU0 pc0 hpc0min
            have hpU0 : 2 ≤ pathCoverNumber Gind U0 := by
              have hcnt : leftoverCountIn pc0 U0 =
                  (List.filter (fun Q => Q.start ∈ U0)
                    (leftoverPieces Aind pH)).length := by
                simp [leftoverCountIn, hpaths0]
              have : 2 ≤ leftoverCountIn pc0 U0 := by simpa [hcnt] using h2
              simpa [hpU0eq] using this
            let pcU0 := actualFilteredCover hU0 hnocrossU0 pc0
            have hcardU0 : pcU0.card = leftoverCountIn pc0 U0 :=
              actualFilteredCover_card hU0 hnocrossU0 pc0
            have hX0eq : X0 = X := by
              ext z
              constructor
              · intro hz; exact (mem_inter.1 hz).1
              · intro hz; exact mem_inter.2 ⟨hz, hXold hz⟩
            have hY0X : Y0 ∪ X = U0 := by
              simpa [hX0eq, union_comm] using hcover0
            have hjoinY0X : Gind.IsCompleteBetween (Y0 : Set V) (X : Set V) := by
              intro y hy x hx
              exact (hjoin0 (by simpa [hX0eq] using hx) hy).symm
            have hdisjY0X : Disjoint Y0 X :=
              disjoint_of_subset_left inter_subset_left hdisjYX
            have hendsU0 : ∀ Q ∈ pcU0.paths, Q.start ∈ Y0 ∧ Q.finish ∈ Y0 := by
              intro Q hQ
              have hmem : Q ∈ pc0.paths.filter (fun Q => Q.start ∈ U0) := by
                rwa [← actualFilteredCover_paths hU0 hnocrossU0 pc0]
              have hQf := List.mem_filter.1 hmem
              have hQl : Q ∈ leftoverPieces Aind pH := by
                simpa [hpaths0] using hQf.1
              exact ⟨hstartY0 Q hQl (of_decide_eq_true hQf.2),
                hfinY0' Q hQl (of_decide_eq_true hQf.2)⟩
            have hnoU0 : ∀ Q ∈ pcU0.paths, NoConsecutive X Q := by
              intro Q hQ
              have hmem : Q ∈ pc0.paths.filter (fun Q => Q.start ∈ U0) := by
                rwa [← actualFilteredCover_paths hU0 hnocrossU0 pc0]
              have hQf := List.mem_filter.1 hmem
              have hQl : Q ∈ leftoverPieces Aind pH := by
                simpa [hpaths0] using hQf.1
              have hsU0 : Q.start ∈ U0 := of_decide_eq_true hQf.2
              intro e
              refine Sym2.inductionOn e (fun u v => ?_)
              intro he hb
              have ⟨huX, hvX⟩ := bothEndsIn_iff.1 hb
              exact hnoXX Q hQl hsU0 u huX v hvX he
            have hY0sub : Y0 ⊆ U0 := inter_subset_right
            have hcardYX :
                pathCoverNumber Gind U0 + X.card ≤ Y0.card := by
              have := card_X_ge_add_of_X_ended_cover (X := Y0) (Y := X)
                (U0 := U0) hdisjY0X hY0X.symm hY0sub hXold pcU0 hendsU0 hnoU0
              simpa [hcardU0, hpU0eq] using this
            have hY0ne : Y0.Nonempty := by
              have : 0 < Y0.card := by
                have hpos : 1 ≤ pathCoverNumber Gind U0 + X.card :=
                  (one_le_pathCoverNumber_of_nonempty (G := Gind) hU0ne).trans
                    (Nat.le_add_right _ _)
                omega
              exact card_pos.1 this
            have hpK0X :
                pathCoverNumber Gind ((Hind \ Aind) \ X) =
                  pathCoverNumber Gind (Hind \ Aind) + X.card :=
              pathCoverNumber_sdiff_Y_eq_add_of_nocross_join
                (W := Hind \ Aind) (U0 := U0) (X := Y0) (Y := X)
                hU0 hY0sub hXold hY0ne hXne hdisjY0X hY0X hjoinY0X
                hnocrossU0 hpU0 hcardYX
            have hEqAX : Hind \ (Aind ∪ X) = (Hind \ Aind) \ X :=
              (sdiff_sdiff_eq_sdiff_union Hind Aind X).symm
            have hK0ind' : Nikoghosyan.IsCograph G' (Hind \ (Aind ∪ X)) :=
              isCograph_iff.1
                (isCograph_suppressInternal (Finset.disjoint_sdiff).symm
                  (isCograph_sdiff_union_Y (U := Hind) (A := Aind) (Y := X) hK0c))
            have hKind' : Nikoghosyan.IsCograph G'
                ((Hind \ (Aind ∪ X)) ∪ Dind) := by
              have hdisj : Disjoint ((Hind \ (Aind ∪ X)) ∪ Dind) (Aind ∪ X) :=
                disjoint_union_left.2 ⟨Finset.disjoint_sdiff.symm, hdisjDA'⟩
              have hsub : (Hind \ (Aind ∪ X)) ∪ Dind ⊆
                  (Hind \ Aind) ∪ Dind := by
                intro z hz
                rcases mem_union.1 hz with h | h
                · have hz' : z ∈ (Hind \ Aind) \ X := by simpa [hEqAX] using h
                  exact mem_union.2 (Or.inl (mem_sdiff.1 hz').1)
                · exact mem_union.2 (Or.inr h)
              exact isCograph_iff.1 (isCograph_suppressInternal hdisj (hKc.subset hsub))
            have hpK0' :
                pathCoverNumber G' (Hind \ (Aind ∪ X)) = (Aind ∪ X).card := by
              have hdisj : Disjoint (Hind \ (Aind ∪ X)) (Aind ∪ X) :=
                Finset.disjoint_sdiff.symm
              have hp := pathCoverNumber_suppressInternal (G := Gind) hdisj
              have hAX : (Aind ∪ X).card = Aind.card + X.card :=
                card_union_of_disjoint hdisjAX
              have hpG : pathCoverNumber Gind (Hind \ (Aind ∪ X)) =
                  (Aind ∪ X).card := by
                simpa [hEqAX, hpK0ind, hAX] using hpK0X
              exact hp.trans hpG
            have hpK' :
                pathCoverNumber G' ((Hind \ (Aind ∪ X)) ∪ Dind) <
                  (Aind ∪ X).card := by
              have hdisj : Disjoint ((Hind \ (Aind ∪ X)) ∪ Dind) (Aind ∪ X) :=
                disjoint_union_left.2 ⟨Finset.disjoint_sdiff.symm, hdisjDA'⟩
              have hpEq := pathCoverNumber_suppressInternal (G := Gind) hdisj
              have hKsX : ((Hind \ Aind) ∪ Dind) \ X =
                  (Hind \ (Aind ∪ X)) ∪ Dind := by
                ext z
                constructor
                · intro hz
                  have hzKY : z ∈ (Hind \ Aind) ∪ Dind := (mem_sdiff.1 hz).1
                  have hzX : z ∉ X := (mem_sdiff.1 hz).2
                  rcases mem_union.1 hzKY with hz0 | hzD
                  · refine mem_union.2 (Or.inl ?_)
                    simpa [hEqAX] using (mem_sdiff.2 ⟨hz0, hzX⟩ : z ∈ (Hind \ Aind) \ X)
                  · exact mem_union.2 (Or.inr hzD)
                · intro hz
                  rcases mem_union.1 hz with hz0 | hzD
                  · have hz' : z ∈ (Hind \ Aind) \ X := by simpa [hEqAX] using hz0
                    exact mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hz').1),
                      (mem_sdiff.1 hz').2⟩
                  · exact mem_sdiff.2 ⟨mem_union.2 (Or.inr hzD), fun hx =>
                      disjoint_left.1 hdisjind
                        ((mem_sdiff.1 (hU0 (hXold hx))).1) hzD⟩
              have hle := pathCoverNumber_sdiff_le (G := Gind)
                ((Hind \ Aind) ∪ Dind) X
                (hXold.trans (hU0.trans subset_union_left))
              have hAX : (Aind ∪ X).card = Aind.card + X.card :=
                card_union_of_disjoint hdisjAX
              have hltG : pathCoverNumber Gind ((Hind \ (Aind ∪ X)) ∪ Dind) <
                  Aind.card + X.card := by
                have : pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ X) ≤
                    pathCoverNumber Gind ((Hind \ Aind) ∪ Dind) + X.card := hle
                have : pathCoverNumber Gind ((Hind \ (Aind ∪ X)) ∪ Dind) ≤
                    pathCoverNumber Gind ((Hind \ Aind) ∪ Dind) + X.card := by
                  simpa [hKsX] using this
                omega
              have hltG' :
                  pathCoverNumber G' ((Hind \ (Aind ∪ X)) ∪ Dind) <
                    Aind.card + X.card :=
                hpEq.symm ▸ hltG
              simpa [hAX] using hltG'
            have hE' : ∀ d ∈ Dind, ∃ u ∈ eligibleSet G' (Hind \ (Aind ∪ X)),
                G'.Adj d u := by
              have hdom : X.card < pathCoverNumber Gind Y0 := by
                have hpY := pathCoverNumber_X_eq_add_card_Y (U0 := U0)
                  hY0ne hXne hdisjY0X hY0X.symm hjoinY0X hpU0 hcardYX
                omega
              have hEU0 :
                  eligibleSet Gind U0 = eligibleSet Gind Y0 := by
                simpa [hY0X] using
                  eligibleSet_complete_join_dominant hY0ne hXne hjoinY0X hdom
              have hdisjRest : Disjoint U0 ((Hind \ Aind) \ U0) := disjoint_sdiff
              have hEKA :
                  eligibleSet Gind (Hind \ Aind) =
                    eligibleSet Gind U0 ∪
                      eligibleSet Gind ((Hind \ Aind) \ U0) := by
                simpa [union_sdiff_of_subset hU0] using
                  eligibleSet_disjoint_union (G := Gind) hdisjRest hnocrossU0
              have hdisjYrest : Disjoint Y0 ((Hind \ Aind) \ U0) :=
                disjoint_of_subset_left hY0sub disjoint_sdiff
              have hncYrest : ∀ a ∈ Y0, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b :=
                fun a ha => hnocrossU0 a (hY0sub ha)
              have hEKX :
                  eligibleSet Gind (Hind \ (Aind ∪ X)) =
                    eligibleSet Gind Y0 ∪
                      eligibleSet Gind ((Hind \ Aind) \ U0) := by
                have hW : Y0 ∪ ((Hind \ Aind) \ U0) = Hind \ (Aind ∪ X) := by
                  rw [hEqAX]
                  ext z
                  constructor
                  · intro hz
                    rcases mem_union.1 hz with hzY | hzR
                    · exact mem_sdiff.2 ⟨hU0 (mem_inter.1 hzY).2, fun hx =>
                        disjoint_left.1 hdisjY0X hzY hx⟩
                    · exact mem_sdiff.2 ⟨(mem_sdiff.1 hzR).1, fun hx =>
                        (mem_sdiff.1 hzR).2 (hXold hx)⟩
                  · intro hz
                    have hz0 : z ∈ Hind \ Aind := (mem_sdiff.1 hz).1
                    have hzX : z ∉ X := (mem_sdiff.1 hz).2
                    by_cases hzU : z ∈ U0
                    · have hzYX : z ∈ Y0 ∪ X := by simpa [hY0X] using hzU
                      rcases mem_union.1 hzYX with h | h
                      · exact mem_union.2 (Or.inl h)
                      · exact (hzX h).elim
                    · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hz0, hzU⟩))
                simpa [hW] using
                  eligibleSet_disjoint_union (G := Gind) hdisjYrest hncYrest
              have hEeq : eligibleSet Gind (Hind \ Aind) =
                  eligibleSet Gind (Hind \ (Aind ∪ X)) := by
                rw [hEKA, hEKX, hEU0]
              have hEsup : eligibleSet G' (Hind \ (Aind ∪ X)) =
                  eligibleSet Gind (Hind \ (Aind ∪ X)) :=
                eligibleSet_suppressInternal (G := Gind)
                  (Finset.disjoint_sdiff).symm
              intro d hd
              obtain ⟨u, huE, hadj⟩ := hEind d hd
              have hu' : u ∈ eligibleSet G' (Hind \ (Aind ∪ X)) := by
                have : u ∈ eligibleSet Gind (Hind \ (Aind ∪ X)) := by
                  simpa [hEeq] using huE
                simpa [hEsup] using this
              have huA' : u ∉ Aind ∪ X :=
                disjoint_left.1 (Finset.disjoint_sdiff.symm)
                  ((eligibleSet_subset (G := G') (Hind \ (Aind ∪ X))) hu')
              have hdA' : d ∉ Aind ∪ X := disjoint_left.1 hdisjDA' hd
              exact ⟨u, hu', (adj_eq_on_carrier (G := Gind) hdA' huA').2 hadj⟩
            have hlt : ((Hind \ (Aind ∪ X)) ∪ Dind).card < n := by
              have hsubX : X ⊆ Hind \ Aind := hXold.trans hU0
              have hpos : 0 < X.card := card_pos.2 hXne
              have hdisjD : Disjoint (Hind \ Aind) Dind :=
                disjoint_of_subset_left sdiff_subset hdisjind
              have hdisjD' : Disjoint ((Hind \ Aind) \ X) Dind :=
                disjoint_of_subset_left sdiff_subset hdisjD
              have hn : n = (Hind \ Aind).card + Dind.card := by
                rw [← hcard, card_union_of_disjoint hdisjD]
              have hnew : ((Hind \ (Aind ∪ X)) ∪ Dind).card =
                  ((Hind \ Aind) \ X).card + Dind.card := by
                rw [hEqAX, card_union_of_disjoint hdisjD']
              have hXle : X.card ≤ (Hind \ Aind).card := card_le_card hsubX
              rw [hnew, card_sdiff_of_subset hsubX, hn]
              omega
            have hYW : Y ⊆ U0 ∪ Dind := by
              intro z hz
              have hzU : z ∈ U := by
                have hzXY : z ∈ X ∪ Y := mem_union.2 (Or.inr hz)
                simpa [hcover] using hzXY
              have : U ⊆ U0 ∪ Dind := by
                intro w hw
                by_cases hwD : w ∈ Dind
                · exact mem_union.2 (Or.inr hwD)
                · have hwK : w ∈ Hind \ Aind := by
                    rcases mem_union.1 (hUK hw) with h | h
                    · exact h
                    · exact (hwD h).elim
                  exact mem_union.2 (Or.inl (mem_inter.2 ⟨hw, hwK⟩))
              exact this hzU
            have hnorestD : ∀ a ∈ Dind, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b := by
              intro a ha b hb hadj
              have haU : a ∈ U := hDU ha
              exact hUnc a haU b (mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hb).1),
                fun hU => (mem_sdiff.1 hb).2 (mem_inter.2 ⟨hU, (mem_sdiff.1 hb).1⟩)⟩) hadj
            obtain ⟨q', hq'sup, hq'st, hq'fin, hq'ne, hq'P⟩ :=
              ih ((Hind \ (Aind ∪ X)) ∪ Dind).card hlt G' Hind Dind (Aind ∪ X)
                cH' cD' rfl hcH' hcD' hdisjind hA'sub hAne' hK0ind' hpK0'
                hKind' hE' hpK'
            obtain ⟨q, hsup, hst, hfin, hne, hP⟩ :=
              exists_lift_restored_W (X := Y) (Y := X) (c := cHind) hcHind hAind
                hU0 hYW hXold hdisjYX hdisjind hXne hjoinYX hnocrossU0 hnorestD
                hpH hsH hedgesH hstay hstartYU0 hfinY h4 hq'sup hcH' hq'st hq'fin
                hq'ne hq'P hedges'
            exact ⟨q, hsup, hst, hfin, hne, hP⟩

end Cograph
end Nikoghosyan
