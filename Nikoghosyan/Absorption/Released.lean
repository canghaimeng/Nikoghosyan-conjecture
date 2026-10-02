/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ReleasedTraceable
import Nikoghosyan.Absorption.BoundarySupport
import Nikoghosyan.Absorption.SaturatedCutShift

/-!
# Protected released-endpoint absorption

Manuscript `abs:thm:released-absorption` and `abs:cor:three-cycle`.

A genuine original cycle `cH` on `H`, nonempty `A ⊆ H`, canonical cograph
remainder `K₀ = H \ A` with `p(K₀) = |A|`, a vertex-disjoint genuine cycle
`cD` on `D`, and canonical cograph `J = K₀ ∪ D` with `p(J) = p(K₀)` yield,
for `h ∈ F(K₀) ∩ E(J)`, a spanning original `H ∪ D` path from a vertex of
`A` to the exact released vertex `h` that is `ProtectedAt cH A`.

The `q = 1` block consumes `traceable_release` and retains one old `A`-seam
together with the omit-run complement. The `q ≥ 2` block follows the
critical join, `suppressInternal (A ∪ Y)`, graph-general induction on
`|J|`, and a single `PrefixEdgeFactor` rotation at an original `A`–`X`
entering dart against the `Y`–`X` join chord. Restoration uses `W = U0 ∪ D`
boundary, not equal-support old helpers.

No eligible-old-neighbour, toughness, cofree, desired-path, count
certificate, or induction callback appears in the final signature.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma ProtectedAt_of_disjoint_A (p : GraphPath G) (c : GraphCycle G)
    {A : Finset V} (hd : Disjoint p.support A) : p.ProtectedAt c A := by
  intro e he
  have : e ∈ (∅ : Finset (Sym2 V)) := by
    simpa [AIncident_eq_empty_of_disjoint_support p hd] using he
  exact (notMem_empty e this).elim

lemma ProtectedAt_of_edges_subset (p : GraphPath G) (c : GraphCycle G)
    {A : Finset V} (hsub : p.edges ⊆ c.walk.edges.toFinset) :
    p.ProtectedAt c A := by
  intro e he
  exact hsub (mem_AIncident_iff.1 he).1

/-- Splice may add one `A`-incident seam; every other `A`-incidence comes
from a factor. -/
lemma AIncident_splice_subset (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) (A : Finset V) :
    (p.splice q h hd).AIncident A ⊆
      p.AIncident A ∪ q.AIncident A ∪ {s(p.finish, q.start)} := by
  intro e he
  have ⟨heE, hb⟩ := mem_AIncident_iff.1 he
  have hE : e ∈ p.edges ∪ q.edges ∪ {s(p.finish, q.start)} := by
    simpa [edges_splice p q h hd] using heE
  rcases mem_union.1 hE with h' | hsing
  · rcases mem_union.1 h' with hp | hq
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_AIncident_iff.2 ⟨hp, hb⟩))))
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_AIncident_iff.2 ⟨hq, hb⟩))))
  · exact mem_union.2 (Or.inr hsing)

lemma ProtectedAt_splice_seam (p q : GraphPath G) (c : GraphCycle G)
    {A : Finset V} (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support)
    (hp : p.ProtectedAt c A) (hq : q.ProtectedAt c A)
    (hseam : s(p.finish, q.start) ∈ c.walk.edges.toFinset) :
    (p.splice q h hd).ProtectedAt c A := by
  intro e he
  have hsub := AIncident_splice_subset p q h hd A he
  rcases mem_union.1 hsub with h' | hsing
  · rcases mem_union.1 h' with hpE | hqE
    · exact hp hpE
    · exact hq hqE
  · simpa [mem_singleton.1 hsing] using hseam

end GraphPath

namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath
open Nikoghosyan.GraphCycle

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Retain one old `A`-seam of a unique leftover run and splice the
traceable released `U`-path to the omit-run complement. -/
lemma exists_released_absorption_q1 {H D A L : Finset V} {h : V}
    (cH : GraphCycle G) (cD : GraphCycle G)
    (pH Q r : GraphPath G)
    (hcH : cH.support = H) (hcD : cD.support = D)
    (hHD : Disjoint H D) (hA : A ⊆ H) (hAne : A.Nonempty)
    (hLcog : Nikoghosyan.IsCograph G L)
    (hUcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hpL : pathCoverNumber G L = 1)
    (hpU : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hpH : pH.support = H) (hsH : pH.start ∈ A)
    (hcloseH : G.Adj pH.finish pH.start)
    (hedgesH : pH.walk.edges.toFinset ∪ {s(pH.finish, pH.start)} =
      cH.walk.edges.toFinset)
    (hQ : Q ∈ leftoverPieces A pH) (hQsup : Q.support = L)
    (hr : r.support = H \ Q.support)
    (hrs : r.start ∈ A) (hrf : r.finish ∈ A)
    (hpred : G.Adj r.finish Q.start) (hsucc : G.Adj Q.finish r.start)
    (hrE : r.edges ⊆ pH.edges ∪ {s(pH.finish, pH.start)})
    (hseamS : s(r.finish, Q.start) ∈ pH.edges ∪ {s(pH.finish, pH.start)})
    (hseamF : s(Q.finish, r.start) ∈ pH.edges ∪ {s(pH.finish, pH.start)})
    (hLD : Disjoint L D) :
    ∃ p : GraphPath G,
      p.support = H ∪ D ∧ p.start ∈ A ∧ p.finish = h ∧
        p.start ≠ p.finish ∧ p.ProtectedAt cH A := by
  have ⟨hrel, _⟩ :=
    traceable_release (G := G) (L := L) (D := D) (h := h)
      (u := Q.start) (v := Q.finish) cD Q hLD hcD hUcog hLcog hpU hpL
      hhF hhE hQsup rfl rfl
  have hLsubH : L ⊆ H := by
    intro z hz
    simpa [hpH] using leftoverPieces_support_subset pH Q hQ (by simpa [hQsup] using hz)
  have hLA : Disjoint L A := by
    rw [Finset.disjoint_left]
    intro z hzL
    exact Finset.disjoint_left.1 (leftoverPieces_disjoint_B pH Q hQ)
      (by simpa [hQsup] using hzL)
  have hRAdisj : Disjoint (L ∪ D) A :=
    disjoint_union_left.2 ⟨hLA, disjoint_of_subset_right hA hHD.symm⟩
  have hcycle :
      pH.edges ∪ {s(pH.finish, pH.start)} = cH.walk.edges.toFinset := hedgesH
  have hrC : r.ProtectedAt cH A :=
    ProtectedAt_of_edges_subset r cH (by
      intro e he
      have : e ∈ pH.edges ∪ {s(pH.finish, pH.start)} := hrE he
      rwa [hcycle] at this)
  have hrevC : r.reverse.ProtectedAt cH A := (ProtectedAt_reverse r cH A).2 hrC
  have hdRL : Disjoint (L ∪ D) r.support := by
    rw [hr, hQsup]
    exact disjoint_union_left.2 ⟨disjoint_sdiff,
      disjoint_of_subset_right sdiff_subset hHD.symm⟩
  have hsup_eq : (L ∪ D) ∪ (H \ L) = H ∪ D := by
    ext z
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro ((hL | hD) | ⟨hH, _⟩)
      · exact Or.inl (hLsubH hL)
      · exact Or.inr hD
      · exact Or.inl hH
    · rintro (hH | hD)
      · by_cases hzL : z ∈ L
        · exact Or.inl (Or.inl hzL)
        · exact Or.inr ⟨hH, hzL⟩
      · exact Or.inl (Or.inr hD)
  rcases hrel with ⟨R, hRsup, hRst, hRfin⟩ | ⟨R, hRsup, hRst, hRfin⟩
  · have hRA : R.ProtectedAt cH A :=
      ProtectedAt_of_disjoint_A R cH (by simpa [hRsup] using hRAdisj)
    have hadj : G.Adj R.finish r.reverse.start := by
      simpa [hRfin, GraphPath.reverse] using hpred.symm
    have hd : Disjoint R.support r.reverse.support := by
      simpa [hRsup, GraphPath.support_reverse] using hdRL
    let S := R.splice r.reverse hadj hd
    have hseam : s(R.finish, r.reverse.start) ∈ cH.walk.edges.toFinset := by
      have hmem : s(r.finish, Q.start) ∈
          pH.edges ∪ {s(pH.finish, pH.start)} := hseamS
      have : s(R.finish, r.reverse.start) = s(r.finish, Q.start) := by
        rw [hRfin]
        simp [GraphPath.reverse, Sym2.eq_swap]
      rw [this]
      exact hcycle ▸ hmem
    have hProtS : S.ProtectedAt cH A :=
      ProtectedAt_splice_seam R r.reverse cH hadj hd hRA hrevC hseam
    have hsupS : S.support = H ∪ D := by
      rw [support_splice, hRsup, GraphPath.support_reverse, hr, hQsup, hsup_eq]
    refine ⟨S.reverse, by rw [GraphPath.support_reverse, hsupS], ?_, ?_, ?_,
      (ProtectedAt_reverse S cH A).2 hProtS⟩
    · simpa [GraphPath.reverse, S, splice] using hrs
    · simpa [GraphPath.reverse, S, splice, hRst]
    · intro heq
      have hstA : S.reverse.start ∈ A := by simpa [GraphPath.reverse, S, splice] using hrs
      have hfin : S.reverse.finish = h := by simpa [GraphPath.reverse, S, splice, hRst]
      have hhA : h ∈ A := by rw [← hfin, ← heq]; exact hstA
      have hin : h ∈ L ∪ D := by
        have : R.start ∈ R.support := R.start_mem_support
        simpa [hRsup, hRst] using this
      exact (Finset.disjoint_left.1 hRAdisj hin hhA).elim
  · have hRA : R.ProtectedAt cH A :=
      ProtectedAt_of_disjoint_A R cH (by simpa [hRsup] using hRAdisj)
    have hadj : G.Adj R.finish r.start := by simpa [hRfin] using hsucc
    have hd : Disjoint R.support r.support := by simpa [hRsup] using hdRL
    let S := R.splice r hadj hd
    have hseam : s(R.finish, r.start) ∈ cH.walk.edges.toFinset := by
      have heqE : s(R.finish, r.start) = s(Q.finish, r.start) := by rw [hRfin]
      rw [heqE, ← hcycle]
      exact hseamF
    have hProtS : S.ProtectedAt cH A :=
      ProtectedAt_splice_seam R r cH hadj hd hRA hrC hseam
    have hsupS : S.support = H ∪ D := by
      rw [support_splice, hRsup, hr, hQsup, hsup_eq]
    refine ⟨S.reverse, by rw [GraphPath.support_reverse, hsupS], ?_, ?_, ?_,
      (ProtectedAt_reverse S cH A).2 hProtS⟩
    · simpa [GraphPath.reverse, S, splice] using hrf
    · simpa [GraphPath.reverse, S, splice, hRst]
    · intro heq
      have hstA : S.reverse.start ∈ A := by simpa [GraphPath.reverse, S, splice] using hrf
      have hfin : S.reverse.finish = h := by simpa [GraphPath.reverse, S, splice, hRst]
      have hhA : h ∈ A := by rw [← hfin, ← heq]; exact hstA
      have hin : h ∈ L ∪ D := by
        have : R.start ∈ R.support := R.start_mem_support
        simpa [hRsup, hRst] using this
      exact (Finset.disjoint_left.1 hRAdisj hin hhA).elim

lemma ineligibleSet_suppressInternal {U A' : Finset V} (hU : Disjoint U A') :
    ineligibleSet (suppressInternal G A') U = ineligibleSet G U := by
  ext x
  constructor
  · intro hx
    have hx' := (mem_ineligibleSet_iff (G := suppressInternal G A')).1 hx
    refine (mem_ineligibleSet_iff (G := G)).2 ⟨hx'.1, ?_⟩
    intro hE
    have hxE : x ∈ eligibleSet G U := (mem_eligibleSet_iff (G := G)).2 ⟨hx'.1, hE⟩
    have hxE' : x ∈ eligibleSet (suppressInternal G A') U := by
      simpa [eligibleSet_suppressInternal (G := G) hU] using hxE
    exact hx'.2 ((mem_eligibleSet_iff (G := suppressInternal G A')).1 hxE').2
  · intro hx
    have hx' := (mem_ineligibleSet_iff (G := G)).1 hx
    refine (mem_ineligibleSet_iff (G := suppressInternal G A')).2 ⟨hx'.1, ?_⟩
    intro hE
    have hxE' : x ∈ eligibleSet (suppressInternal G A') U :=
      (mem_eligibleSet_iff (G := suppressInternal G A')).2 ⟨hx'.1, hE⟩
    have hxE : x ∈ eligibleSet G U := by
      simpa [eligibleSet_suppressInternal (G := G) hU] using hxE'
    exact hx'.2 ((mem_eligibleSet_iff (G := G)).1 hxE).2

lemma one_side_dominant_of_join {X Y : Finset V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hq : 2 ≤ pathCoverNumber G (X ∪ Y)) :
    Y.card < pathCoverNumber G X ∨ X.card < pathCoverNumber G Y := by
  have hpjoin := pathCoverNumber_complete_join hXne hYne hjoin
  by_cases hXd : Y.card < pathCoverNumber G X
  · exact Or.inl hXd
  · have hXle : pathCoverNumber G X ≤ Y.card := Nat.le_of_not_gt hXd
    refine Or.inr ?_
    by_cases hYle : pathCoverNumber G Y ≤ X.card
    · have : pathCoverNumber G (X ∪ Y) = 1 := by
        rw [hpjoin]
        simp [Nat.sub_eq_zero_of_le hXle, Nat.sub_eq_zero_of_le hYle]
      omega
    · exact Nat.lt_of_not_ge hYle

/-- Canonical protected released-endpoint absorption. -/
theorem exists_released_absorption {H D A : Finset V} {h : V}
    {G : SimpleGraph V} (cH : GraphCycle G) (cD : GraphCycle G)
    (hcH : cH.support = H) (hcD : cD.support = D)
    (hdisj : Disjoint H D) (hA : A ⊆ H) (hAne : A.Nonempty)
    (hK0 : Nikoghosyan.IsCograph G (H \ A))
    (hpK0 : pathCoverNumber G (H \ A) = A.card)
    (hK : Nikoghosyan.IsCograph G ((H \ A) ∪ D))
    (hpK : pathCoverNumber G ((H \ A) ∪ D) = A.card)
    (hhF : h ∈ ineligibleSet G (H \ A))
    (hhE : h ∈ eligibleSet G ((H \ A) ∪ D)) :
    ∃ p : GraphPath G,
      p.support = H ∪ D ∧ p.start ∈ A ∧ p.finish = h ∧
        p.start ≠ p.finish ∧ p.ProtectedAt cH A := by
  let motive : ℕ → Prop := fun n =>
    ∀ (G : SimpleGraph V) (H D A : Finset V) (h : V)
      (cH : GraphCycle G) (cD : GraphCycle G),
      ((H \ A) ∪ D).card = n →
        cH.support = H → cD.support = D → Disjoint H D →
          A ⊆ H → A.Nonempty →
            Nikoghosyan.IsCograph G (H \ A) →
              pathCoverNumber G (H \ A) = A.card →
                Nikoghosyan.IsCograph G ((H \ A) ∪ D) →
                  pathCoverNumber G ((H \ A) ∪ D) = A.card →
                    h ∈ ineligibleSet G (H \ A) →
                      h ∈ eligibleSet G ((H \ A) ∪ D) →
                        ∃ p : GraphPath G,
                          p.support = H ∪ D ∧ p.start ∈ A ∧ p.finish = h ∧
                            p.start ≠ p.finish ∧ p.ProtectedAt cH A
  refine Nat.strongRecOn (motive := motive) ((H \ A) ∪ D).card ?_ G H D A h cH cD
    rfl hcH hcD hdisj hA hAne hK0 hpK0 hK hpK hhF hhE
  intro n ih Gind Hind Dind Aind hind cHind cDind hcard hcHind hcDind hdisjind
    hAind hAneind hK0ind hpK0ind hKind hpKind hhFind hhEind
  have hK0c : IsCograph Gind (Hind \ Aind) := isCograph_iff.2 hK0ind
  have hKc : IsCograph Gind ((Hind \ Aind) ∪ Dind) := isCograph_iff.2 hKind
  have hSat : Saturated (G := Gind) Hind Aind := hpK0ind
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
  have hJ := (Hind \ Aind) ∪ Dind
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
  have hpUeq : pathCoverNumber Gind U = pathCoverNumber Gind U0 := by
    have hsum :
        pathCoverNumber Gind U +
            pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ U) =
          pathCoverNumber Gind U0 +
            pathCoverNumber Gind ((Hind \ Aind) \ U0) := by
      rw [← hpKadd, hpKind, ← hpK0ind, hpK0add]
    have hsum' :
        pathCoverNumber Gind U +
            pathCoverNumber Gind ((Hind \ Aind) \ U0) =
          pathCoverNumber Gind U0 +
            pathCoverNumber Gind ((Hind \ Aind) \ U0) := by
      simpa [hEqRest] using hsum
    exact Nat.add_right_cancel hsum'
  have hhK0 : hind ∈ Hind \ Aind := ineligibleSet_subset (G := Gind) _ hhFind
  have hhJ : hind ∈ (Hind \ Aind) ∪ Dind := mem_union.2 (Or.inl hhK0)
  have hhU : hind ∈ U := by
    by_contra hnu
    have hout : hind ∈ ((Hind \ Aind) ∪ Dind) \ U := mem_sdiff.2 ⟨hhJ, hnu⟩
    have hEsplit :=
      eligibleSet_disjoint_union (G := Gind) hdisjUK hncUK
    have hhE' : hind ∈ eligibleSet Gind U ∪
        eligibleSet Gind (((Hind \ Aind) ∪ Dind) \ U) := by
      have : eligibleSet Gind ((Hind \ Aind) ∪ Dind) =
          eligibleSet Gind U ∪
            eligibleSet Gind (((Hind \ Aind) ∪ Dind) \ U) := by
        simpa [hUunion] using hEsplit
      simpa [this] using hhEind
    rcases mem_union.1 hhE' with hEU | hEout
    · exact hnu (eligibleSet_subset (G := Gind) U hEU)
    · have hFsplit :=
        ineligibleSet_disjoint_union (G := Gind) hdisjU0 hnocrossU0
      have hhF' : hind ∈ ineligibleSet Gind U0 ∪
          ineligibleSet Gind ((Hind \ Aind) \ U0) := by
        have : ineligibleSet Gind (Hind \ Aind) =
            ineligibleSet Gind U0 ∪
              ineligibleSet Gind ((Hind \ Aind) \ U0) := by
          simpa [hU0union] using hFsplit
        simpa [this] using hhFind
      have houtK : hind ∈ (Hind \ Aind) \ U0 := by
        simpa [hKsdiffU] using hout
      have hhFout : hind ∈ ineligibleSet Gind ((Hind \ Aind) \ U0) := by
        rcases mem_union.1 hhF' with hhU0 | hhout
        · exact ((mem_sdiff.1 houtK).2 (ineligibleSet_subset (G := Gind) U0 hhU0)).elim
        · exact hhout
      have hEout' : hind ∈
          eligibleSet Gind ((Hind \ Aind) \ U0) := by
        have : eligibleSet Gind (((Hind \ Aind) ∪ Dind) \ U) =
            eligibleSet Gind ((Hind \ Aind) \ U0) := by
          simpa [hKsdiffU]
        simpa [this] using hEout
      exact ((mem_ineligibleSet_iff (G := Gind)).1 hhFout).2
        ((mem_eligibleSet_iff (G := Gind)).1 hEout').2
  have hhU0 : hind ∈ U0 := mem_inter.2 ⟨hhU, hhK0⟩
  have hU0ne : U0.Nonempty := ⟨hind, hhU0⟩
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
  have hpU0le : pathCoverNumber Gind U0 ≤ leftoverCountIn pc0 U0 := by
    let pcU0 := actualFilteredCover hU0 hnocrossU0 pc0
    have hcardU := actualFilteredCover_card hU0 hnocrossU0 pc0
    exact (pathCoverNumber_le (G := Gind) pcU0).trans (le_of_eq hcardU)
  have hminU0 : leftoverCountIn pc0 U0 = pathCoverNumber Gind U0 :=
    leftoverCountIn_eq_pathCoverNumber_of_min_nocross hU0 hnocrossU0 pc0 hmin0
  have hq : leftoverCountIn pc0 U0 = pathCoverNumber Gind U := by
    simpa [hminU0, hpUeq]
  have hUeq : U0 ∪ Dind = U := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hz0 | hzD
      · exact (mem_inter.1 hz0).1
      · exact hDU hzD
    · intro hzU
      have hzJ : z ∈ (Hind \ Aind) ∪ Dind := hUK hzU
      rcases mem_union.1 hzJ with hz0 | hzD
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzU, hz0⟩))
      · exact mem_union.2 (Or.inr hzD)
  have hdisjU0D : Disjoint U0 Dind :=
    disjoint_of_subset_left (inter_subset_right (s₁ := U))
      (disjoint_of_subset_left sdiff_subset hdisjind)
  have hU0cogCan : Nikoghosyan.IsCograph Gind U0 :=
    isCograph_canonical_subset hK0ind hU0
  have hUcogCan : Nikoghosyan.IsCograph Gind U :=
    isCograph_canonical_subset hKind hUK
  have hUcog' : Nikoghosyan.IsCograph Gind (U0 ∪ Dind) := by
    simpa [hUeq] using hUcogCan
  have hhFU0 : hind ∈ ineligibleSet Gind U0 := by
    have hFsplit :=
      ineligibleSet_disjoint_union (G := Gind) hdisjU0 hnocrossU0
    have hhF' : hind ∈ ineligibleSet Gind U0 ∪
        ineligibleSet Gind ((Hind \ Aind) \ U0) := by
      have : ineligibleSet Gind (Hind \ Aind) =
          ineligibleSet Gind U0 ∪
            ineligibleSet Gind ((Hind \ Aind) \ U0) := by
        simpa [hU0union] using hFsplit
      simpa [this] using hhFind
    rcases mem_union.1 hhF' with h | hout
    · exact h
    · have : hind ∉ U0 :=
        (mem_sdiff.1 (ineligibleSet_subset (G := Gind) _ hout)).2
      exact (this hhU0).elim
  have hhEU : hind ∈ eligibleSet Gind U := by
    have hEsplit :=
      eligibleSet_disjoint_union (G := Gind) hdisjUK hncUK
    have hhE' : hind ∈ eligibleSet Gind U ∪
        eligibleSet Gind (((Hind \ Aind) ∪ Dind) \ U) := by
      have : eligibleSet Gind ((Hind \ Aind) ∪ Dind) =
          eligibleSet Gind U ∪
            eligibleSet Gind (((Hind \ Aind) ∪ Dind) \ U) := by
        simpa [hUunion] using hEsplit
      simpa [this] using hhEind
    rcases mem_union.1 hhE' with h | hout
    · exact h
    · exact ((mem_sdiff.1 (eligibleSet_subset (G := Gind) _ hout)).2 hhU).elim
  have hhEU' : hind ∈ eligibleSet Gind (U0 ∪ Dind) := by
    simpa [hUeq] using hhEU
  by_cases hq1 : leftoverCountIn pc0 U0 = 1
  · have hpL1 : pathCoverNumber Gind U0 = 1 := by simpa [hminU0] using hq1
    have hpU1 : pathCoverNumber Gind U0 = pathCoverNumber Gind (U0 ∪ Dind) := by
      simpa [hUeq, hpUeq]
    let pcU0 := actualFilteredCover hU0 hnocrossU0 pc0
    have hcard1 : pcU0.card = 1 := by
      rw [actualFilteredCover_card hU0 hnocrossU0 pc0]
      exact hq1
    have hpathsU : pcU0.paths =
        pc0.paths.filter (fun Q => Q.start ∈ U0) :=
      actualFilteredCover_paths hU0 hnocrossU0 pc0
    match hpl : pcU0.paths with
    | [] =>
      have : pcU0.card = 0 := by simp [PathCover.card, hpl]
      omega
    | Q :: rest =>
      have hrest : rest = [] := by
        have hlen : (Q :: rest).length = 1 := by
          simpa [PathCover.card, hpl] using hcard1
        have h0 : rest.length = 0 := by
          simpa [List.length_cons] using hlen
        exact List.eq_nil_of_length_eq_zero h0
      have hQeq : pcU0.paths = [Q] := by simpa [hpl, hrest]
      have hQin : Q ∈ pc0.paths := by
        have : Q ∈ pcU0.paths := by simp [hQeq]
        have hmem : Q ∈ pc0.paths.filter (fun R => R.start ∈ U0) := by
          simpa [hpathsU] using this
        exact (List.mem_filter.1 hmem).1
      have hQleft : Q ∈ leftoverPieces Aind pH := by simpa [hpaths0] using hQin
      have hsU0 : Q.start ∈ U0 := by
        have : Q ∈ pcU0.paths := by simp [hQeq]
        have hmem : Q ∈ pc0.paths.filter (fun R => R.start ∈ U0) := by
          simpa [hpathsU] using this
        exact of_decide_eq_true (List.mem_filter.1 hmem).2
      have hQsupU0 : Q.support ⊆ U0 := hstay Q hQleft hsU0
      have hQsup : Q.support = U0 := by
        ext z
        constructor
        · intro hz
          exact hQsupU0 hz
        · intro hz
          obtain ⟨R, hR, hzR⟩ := (pcU0.mem_iff z).1 hz
          have hReq : R = Q := List.mem_singleton.1 (hQeq ▸ hR)
          simpa [hReq] using hzR
      obtain ⟨r, hr, hrs, hrf, hpred, hsucc, hrE, hseamS, hseamF⟩ :=
        exists_complement_of_leftover_edges hsH hQleft hcloseH
      have hr' : r.support = Hind \ Q.support := by simpa [hpH] using hr
      exact exists_released_absorption_q1 (G := Gind)
        cHind cDind pH Q r hcHind hcDind hdisjind hAind hAneind
        hU0cogCan hUcog' hpL1 hpU1 hhFU0 hhEU' hpH hsH hcloseH hedgesH
        hQleft hQsup hr' hrs hrf hpred hsucc hrE hseamS hseamF hdisjU0D
  · have hq2 : 2 ≤ leftoverCountIn pc0 U0 := by
      have hpos : 1 ≤ pathCoverNumber Gind U0 :=
        one_le_pathCoverNumber_of_nonempty (G := Gind) hU0ne
      have heq := hminU0
      have hne := hq1
      omega
    have h2len : 2 ≤
        (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces Aind pH)).length := by
      simpa [leftoverCountIn, hpaths0] using hq2
    have hU0card : 2 ≤ U0.card :=
      two_le_card_of_filtered hU0 hnocrossU0 pc0 hq2
    have hUcard : 2 ≤ U.card :=
      hU0card.trans (card_le_card (inter_subset_left (s₁ := U)))
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
    have hUcog : IsCograph Gind U := hKc.subset hUK
    obtain ⟨X0, Y0, hX0, hY0, hX0ne, hY0ne, hdisj0, hcover0U, hjoin0, _, _⟩ :=
      exists_complete_join_on hUcog hUconn hUcard
    have hpU2 : 2 ≤ pathCoverNumber Gind U := by simpa [hq] using hq2
    have hpU02 : 2 ≤ pathCoverNumber Gind U0 := by simpa [hpUeq] using hpU2
    have hpU2join : 2 ≤ pathCoverNumber Gind (X0 ∪ Y0) := by
      simpa [hcover0U] using hpU2
    have hnorm :
        ∃ X Y : Finset V, X ⊆ U ∧ Y ⊆ U ∧ X.Nonempty ∧ Y.Nonempty ∧
          Disjoint X Y ∧ X ∪ Y = U ∧
          Gind.IsCompleteBetween (X : Set V) (Y : Set V) ∧
          Y.card < pathCoverNumber Gind X := by
      rcases one_side_dominant_of_join hX0ne hY0ne hjoin0 hpU2join with hdomX | hdomY
      · exact ⟨X0, Y0, hX0, hY0, hX0ne, hY0ne, hdisj0, hcover0U, hjoin0, hdomX⟩
      · refine ⟨Y0, X0, hY0, hX0, hY0ne, hX0ne, hdisj0.symm, ?_, ?_, hdomY⟩
        · rw [union_comm, hcover0U]
        · intro y hy x hx
          exact (hjoin0 hx hy).symm
    obtain ⟨X, Y, hXsub, hYsub, hXne, hYne, hdisjXY, hcover, hjoin, hdom⟩ := hnorm
    have hcoverLD : X ∪ Y = U0 ∪ Dind := by
      rw [hcover, hUeq]
    have hpLD : pathCoverNumber Gind U0 =
        pathCoverNumber Gind (U0 ∪ Dind) := by
      simpa [hUeq] using hpUeq.symm
    have hqLD : 2 ≤ pathCoverNumber Gind (U0 ∪ Dind) := by
      simpa [hUeq, hq] using hq2
    have hXcog : Nikoghosyan.IsCograph Gind X :=
      isCograph_canonical_subset hKind (hXsub.trans hUK)
    have hDYfalse : ¬ (Dind ∩ Y).Nonempty := by
      intro hneDY
      exact false_of_cycle_meets_nondominant (c := cDind) hdisjU0D hcDind
        hcoverLD hXne hYne hjoin hdom hXcog hU0cogCan hpLD hqLD hhFU0 hhEU' hneDY
    have hDsubX : Dind ⊆ X := by
      intro z hz
      have hzU : z ∈ U := hDU hz
      have hzXY : z ∈ X ∪ Y := by simpa [hcover] using hzU
      rcases mem_union.1 hzXY with hzX | hzY
      · exact hzX
      · exact (hDYfalse ⟨z, mem_inter.2 ⟨hz, hzY⟩⟩).elim
    obtain ⟨hXeq, hYold, hdisjLXY⟩ :=
      union_inter_eq_of_cycle_subset_left hcoverLD hdisjU0D hdisjXY hDsubX
    let LX := U0 ∩ X
    have hXeq' : LX ∪ Dind = X := by simpa [LX] using hXeq
    have hdisjLXD : Disjoint LX Dind :=
      disjoint_of_subset_left (inter_subset_left (s₁ := U0)) hdisjU0D
    have hpX : pathCoverNumber Gind X =
        pathCoverNumber Gind U + Y.card := by
      have := pathCoverNumber_add_card_of_dominant hXne hYne hjoin hdom
      simpa [hcover] using this
    have hpD1 : pathCoverNumber Gind Dind = 1 :=
      pathCoverNumber_eq_one_of_cycle cDind hcDind
    have hpXle : pathCoverNumber Gind X ≤ pathCoverNumber Gind LX + 1 := by
      have hle := pathCoverNumber_union_le_of_disjoint (G := Gind) hdisjLXD
      have hle' : pathCoverNumber Gind (LX ∪ Dind) ≤
          pathCoverNumber Gind LX + pathCoverNumber Gind Dind := hle
      have hleX : pathCoverNumber Gind X ≤
          pathCoverNumber Gind LX + pathCoverNumber Gind Dind := by
        simpa [hXeq'] using hle'
      omega
    have hLXne : LX.Nonempty := by
      by_contra hempty
      have hLXempty : LX = ∅ := not_nonempty_iff_eq_empty.1 hempty
      have hpX1 : pathCoverNumber Gind X ≤ 1 := by
        have : pathCoverNumber Gind LX = 0 := by
          simpa [hLXempty, pathCoverNumber_empty]
        omega
      have : 3 ≤ pathCoverNumber Gind X := by
        have hYpos : 1 ≤ Y.card := Nat.succ_le_of_lt (card_pos.2 hYne)
        omega
      omega
    have hLsplit : LX ∪ Y = U0 := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with hzL | hzY
        · exact (mem_inter.1 hzL).1
        · exact hYold hzY
      · intro hzU0
        have hzU : z ∈ U := (mem_inter.1 hzU0).1
        have hzXY : z ∈ X ∪ Y := by simpa [hcover] using hzU
        rcases mem_union.1 hzXY with hzX | hzY
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzU0, hzX⟩))
        · exact mem_union.2 (Or.inr hzY)
    have hLXY : Gind.IsCompleteBetween (LX : Set V) (Y : Set V) :=
      isCompleteBetween_mono (A := X) (A' := LX) (B := Y) (B' := Y)
        hjoin (inter_subset_right (s₁ := U0)) subset_rfl
    have hdomLX : Y.card < pathCoverNumber Gind LX := by
      have : pathCoverNumber Gind U + Y.card ≤ pathCoverNumber Gind LX + 1 := by
        simpa [hpX] using hpXle
      omega
    have hpLX : pathCoverNumber Gind LX =
        pathCoverNumber Gind U0 + Y.card := by
      have := pathCoverNumber_add_card_of_dominant hLXne hYne hLXY hdomLX
      simpa [hLsplit] using this
    let pcU0 := actualFilteredCover hU0 hnocrossU0 pc0
    have hminpcU0 : pcU0.card = pathCoverNumber Gind U0 := by
      rw [actualFilteredCover_card hU0 hnocrossU0 pc0, hminU0]
    have hQin : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q ∈ pcU0.paths := by
      intro Q hQ hs
      have hpc : Q ∈ pc0.paths := by simpa [hpaths0] using hQ
      have hpathsU : pcU0.paths =
          pc0.paths.filter (fun R => R.start ∈ U0) :=
        actualFilteredCover_paths hU0 hnocrossU0 pc0
      rw [hpathsU]
      exact List.mem_filter.2 ⟨hpc, decide_eq_true hs⟩
    have hEU0 : eligibleSet Gind U0 = eligibleSet Gind LX := by
      simpa [hLsplit] using
        eligibleSet_complete_join_dominant hLXne hYne hLXY hdomLX
    have hstartX : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ X := by
      intro Q hQ hs
      have hEl := Eligible.of_min_cover_endpoint pcU0 hminpcU0 (hQin Q hQ hs)
      have hEset : Q.start ∈ eligibleSet Gind U0 :=
        (mem_eligibleSet_iff (G := Gind)).2
          ⟨pcU0.support_subset (hQin Q hQ hs) Q.start_mem_support, hEl.1⟩
      have hELX : Q.start ∈ eligibleSet Gind LX := by simpa [hEU0] using hEset
      exact (inter_subset_right (s₁ := U0) : LX ⊆ X)
        ((eligibleSet_subset (G := Gind) LX) hELX)
    have hfinX : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.finish ∈ X := by
      intro Q hQ hs
      have hEl := Eligible.of_min_cover_endpoint pcU0 hminpcU0 (hQin Q hQ hs)
      have hEset : Q.finish ∈ eligibleSet Gind U0 :=
        (mem_eligibleSet_iff (G := Gind)).2
          ⟨pcU0.support_subset (hQin Q hQ hs) Q.finish_mem_support, hEl.2⟩
      have hELX : Q.finish ∈ eligibleSet Gind LX := by simpa [hEU0] using hEset
      exact (inter_subset_right (s₁ := U0) : LX ⊆ X)
        ((eligibleSet_subset (G := Gind) LX) hELX)
    have hstartLX : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.start ∈ LX := by
      intro Q hQ hs
      exact mem_inter.2 ⟨hs, hstartX Q hQ hs⟩
    have hfinLX : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 → Q.finish ∈ LX := by
      intro Q hQ hs
      exact mem_inter.2 ⟨hstay Q hQ hs Q.finish_mem_support, hfinX Q hQ hs⟩
    by_cases hYY : ∃ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 ∧
        ∃ u ∈ Y, ∃ v ∈ Y, s(u, v) ∈ Q.edges
    · obtain ⟨Q, hQ, hsQ, u, huY, v, hvY, huvQ⟩ := hYY
      have hadjuv : Gind.Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using Q.edges_subset_edgeSet _ huvQ
      obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
        exists_protectedAt_of_join_insert_YY_of_saving (c := cHind) hcHind
          hU0 hLXY hLsplit hpH hsH hcloseH hedgesH hstay h2len hfinLX hstartLX
          hQ hsQ huY hvY hadjuv huvQ
      exact (hnoAAPath ⟨q, hsup, hst, hfin⟩).elim
    have hnoYY : ∀ Q ∈ leftoverPieces Aind pH, Q.start ∈ U0 →
        ∀ u ∈ Y, ∀ v ∈ Y, s(u, v) ∉ Q.edges := by
      intro Q hQ hs u hu v hv he
      exact hYY ⟨Q, hQ, hs, u, hu, v, hv, he⟩
    have h4 : 4 ≤ (cHind.boundaryEdges U0).card :=
      four_le_card_cycle_boundary_U0 (c := cHind) hcHind hU0 hpH hsH
        hedgesH hstay h2len
    have hsurv :=
      cycle_edges_mem_suppressInternal_noYY (c := cHind) hcHind hU0
        hYold hdisjXY hpH hsH hedgesH hnoAA hnocrossU0 hstay
        hstartX hfinX hnoYY
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
    have hEqAY : Hind \ (Aind ∪ Y) = (Hind \ Aind) \ Y :=
      (sdiff_sdiff_eq_sdiff_union Hind Aind Y).symm
    have hcardLX : pathCoverNumber Gind U0 + Y.card ≤ LX.card := by
      have hle := pathCoverNumber_le_card (G := Gind) LX
      omega
    have hpK0Y :
        pathCoverNumber Gind ((Hind \ Aind) \ Y) =
          pathCoverNumber Gind (Hind \ Aind) + Y.card :=
      pathCoverNumber_sdiff_Y_eq_add_of_nocross_join
        (W := Hind \ Aind) (U0 := U0) (X := LX) (Y := Y)
        hU0 (inter_subset_left (s₁ := U0)) hYold hLXne hYne
        (disjoint_of_subset_left (inter_subset_right (s₁ := U0)) hdisjXY)
        hLsplit hLXY hnocrossU0 hpU02 hcardLX
    have hcardX : pathCoverNumber Gind U + Y.card ≤ X.card := by
      have hle := pathCoverNumber_le_card (G := Gind) X
      omega
    have hpJY :
        pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ Y) =
          pathCoverNumber Gind ((Hind \ Aind) ∪ Dind) + Y.card :=
      pathCoverNumber_sdiff_Y_eq_add_of_nocross_join
        (W := (Hind \ Aind) ∪ Dind) (U0 := U) (X := X) (Y := Y)
        hUK hXsub hYsub hXne hYne hdisjXY hcover hjoin hUnc hpU2 hcardX
    have hKsY :
        ((Hind \ Aind) ∪ Dind) \ Y = (Hind \ (Aind ∪ Y)) ∪ Dind := by
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
    have hK0ind' : Nikoghosyan.IsCograph G' (Hind \ (Aind ∪ Y)) :=
      isCograph_iff.1
        (isCograph_suppressInternal (Finset.disjoint_sdiff).symm
          (isCograph_sdiff_union_Y (U := Hind) (A := Aind) (Y := Y) hK0c))
    have hKind' : Nikoghosyan.IsCograph G'
        ((Hind \ (Aind ∪ Y)) ∪ Dind) := by
      have hdisjCar : Disjoint ((Hind \ (Aind ∪ Y)) ∪ Dind) (Aind ∪ Y) :=
        disjoint_union_left.2 ⟨Finset.disjoint_sdiff.symm, hdisjDA'⟩
      have hsub : (Hind \ (Aind ∪ Y)) ∪ Dind ⊆
          (Hind \ Aind) ∪ Dind := by
        intro z hz
        rcases mem_union.1 hz with h | h
        · have hz' : z ∈ (Hind \ Aind) \ Y := by simpa [hEqAY] using h
          exact mem_union.2 (Or.inl (mem_sdiff.1 hz').1)
        · exact mem_union.2 (Or.inr h)
      exact isCograph_iff.1 (isCograph_suppressInternal hdisjCar (hKc.subset hsub))
    have hpK0' :
        pathCoverNumber G' (Hind \ (Aind ∪ Y)) = (Aind ∪ Y).card := by
      have hdisjCar : Disjoint (Hind \ (Aind ∪ Y)) (Aind ∪ Y) :=
        Finset.disjoint_sdiff.symm
      have hp := pathCoverNumber_suppressInternal (G := Gind) hdisjCar
      have hAY : (Aind ∪ Y).card = Aind.card + Y.card :=
        card_union_of_disjoint hdisjAY
      have hpG : pathCoverNumber Gind (Hind \ (Aind ∪ Y)) =
          (Aind ∪ Y).card := by
        simpa [hEqAY, hpK0ind, hAY] using hpK0Y
      exact hp.trans hpG
    have hpK' :
        pathCoverNumber G' ((Hind \ (Aind ∪ Y)) ∪ Dind) = (Aind ∪ Y).card := by
      have hdisjCar : Disjoint ((Hind \ (Aind ∪ Y)) ∪ Dind) (Aind ∪ Y) :=
        disjoint_union_left.2 ⟨Finset.disjoint_sdiff.symm, hdisjDA'⟩
      have hpEq := pathCoverNumber_suppressInternal (G := Gind) hdisjCar
      have hAY : (Aind ∪ Y).card = Aind.card + Y.card :=
        card_union_of_disjoint hdisjAY
      have hpG : pathCoverNumber Gind ((Hind \ (Aind ∪ Y)) ∪ Dind) =
          (Aind ∪ Y).card := by
        have : pathCoverNumber Gind (((Hind \ Aind) ∪ Dind) \ Y) =
            Aind.card + Y.card := by
          simpa [hpKind] using hpJY
        simpa [hKsY, hAY] using this
      exact hpEq.trans hpG
    have hWold : LX ∪ ((Hind \ Aind) \ U0) = (Hind \ Aind) \ Y := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with hzL | hzR
        · have hzU0 : z ∈ U0 := (mem_inter.1 hzL).1
          have hzX : z ∈ X := (mem_inter.1 hzL).2
          have hzY : z ∉ Y := fun hy => disjoint_left.1 hdisjXY hzX hy
          exact mem_sdiff.2 ⟨hU0 hzU0, hzY⟩
        · have hz0 : z ∈ Hind \ Aind := (mem_sdiff.1 hzR).1
          have hzU0 : z ∉ U0 := (mem_sdiff.1 hzR).2
          have hzY : z ∉ Y := fun hy => hzU0 (hYold hy)
          exact mem_sdiff.2 ⟨hz0, hzY⟩
      · intro hz
        have hz0 : z ∈ Hind \ Aind := (mem_sdiff.1 hz).1
        have hzY : z ∉ Y := (mem_sdiff.1 hz).2
        by_cases hzU : z ∈ U0
        · have hzXY : z ∈ LX ∪ Y := by simpa [hLsplit] using hzU
          rcases mem_union.1 hzXY with hLX | hY
          · exact mem_union.2 (Or.inl hLX)
          · exact (hzY hY).elim
        · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hz0, hzU⟩))
    have hncLX : ∀ a ∈ LX, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b :=
      fun a ha => hnocrossU0 a (inter_subset_left ha)
    have hdisjLXRest : Disjoint LX ((Hind \ Aind) \ U0) :=
      disjoint_of_subset_left (inter_subset_left (s₁ := U0)) disjoint_sdiff
    have hFU0 : ineligibleSet Gind U0 = Y ∪ ineligibleSet Gind LX := by
      simpa [hLsplit] using
        ineligibleSet_complete_join_dominant hLXne hYne hLXY hdomLX
    have hEU : eligibleSet Gind U = eligibleSet Gind X := by
      simpa [hcover] using
        eligibleSet_complete_join_dominant hXne hYne hjoin hdom
    have hhEX : hind ∈ eligibleSet Gind X := by simpa [hEU] using hhEU
    have hhFLX : hind ∈ ineligibleSet Gind LX := by
      have hmem : hind ∈ Y ∪ ineligibleSet Gind LX := by
        simpa [hFU0] using hhFU0
      rcases mem_union.1 hmem with hYh | hF
      · exact (Finset.disjoint_left.1 hdisjXY
          (eligibleSet_subset (G := Gind) X hhEX) hYh).elim
      · exact hF
    have hFold : ineligibleSet Gind ((Hind \ Aind) \ Y) =
        ineligibleSet Gind LX ∪ ineligibleSet Gind ((Hind \ Aind) \ U0) := by
      simpa [hWold] using
        ineligibleSet_disjoint_union (G := Gind) hdisjLXRest hncLX
    have hhFold : hind ∈ ineligibleSet Gind (Hind \ (Aind ∪ Y)) := by
      have hmem : hind ∈
          ineligibleSet Gind LX ∪ ineligibleSet Gind ((Hind \ Aind) \ U0) :=
        mem_union.2 (Or.inl hhFLX)
      have hmem' : hind ∈ ineligibleSet Gind ((Hind \ Aind) \ Y) := by
        simpa [hFold] using hmem
      simpa [hEqAY] using hmem'
    have hhF' : hind ∈ ineligibleSet G' (Hind \ (Aind ∪ Y)) := by
      have hdisjCar : Disjoint (Hind \ (Aind ∪ Y)) (Aind ∪ Y) :=
        Finset.disjoint_sdiff.symm
      have : ineligibleSet G' (Hind \ (Aind ∪ Y)) =
          ineligibleSet Gind (Hind \ (Aind ∪ Y)) :=
        ineligibleSet_suppressInternal (G := Gind) hdisjCar
      simpa [this] using hhFold
    have hncXrest : ∀ a ∈ X, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b := by
      intro a ha b hb hadj
      have haU : a ∈ U := hXsub ha
      have hb0 : b ∈ Hind \ Aind := (mem_sdiff.1 hb).1
      have hbU0 : b ∉ U0 := (mem_sdiff.1 hb).2
      have hbU : b ∉ U := fun hU => hbU0 (mem_inter.2 ⟨hU, hb0⟩)
      exact hUnc a haU b
        (mem_sdiff.2 ⟨mem_union.2 (Or.inl hb0), hbU⟩) hadj
    have hdisjXrest : Disjoint X ((Hind \ Aind) \ U0) := by
      rw [Finset.disjoint_left]
      intro z hzX hzR
      have hzU : z ∈ U := hXsub hzX
      have hz0 : z ∈ Hind \ Aind := (mem_sdiff.1 hzR).1
      have hzU0 : z ∉ U0 := (mem_sdiff.1 hzR).2
      exact hzU0 (mem_inter.2 ⟨hzU, hz0⟩)
    have hWnew : X ∪ ((Hind \ Aind) \ U0) = (Hind \ (Aind ∪ Y)) ∪ Dind := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with hzX | hzR
        · have hzLD : z ∈ LX ∪ Dind := by simpa [hXeq'] using hzX
          rcases mem_union.1 hzLD with hzL | hzD
          · refine mem_union.2 (Or.inl ?_)
            have hzKY : z ∈ (Hind \ Aind) \ Y := by
              have : z ∈ LX ∪ ((Hind \ Aind) \ U0) := mem_union.2 (Or.inl hzL)
              simpa [hWold] using this
            simpa [hEqAY] using hzKY
          · exact mem_union.2 (Or.inr hzD)
        · refine mem_union.2 (Or.inl ?_)
          have hzKY : z ∈ (Hind \ Aind) \ Y := by
            have : z ∈ LX ∪ ((Hind \ Aind) \ U0) := mem_union.2 (Or.inr hzR)
            simpa [hWold] using this
          simpa [hEqAY] using hzKY
      · intro hz
        rcases mem_union.1 hz with hz0 | hzD
        · have hzKY : z ∈ (Hind \ Aind) \ Y := by simpa [hEqAY] using hz0
          have hzsplit : z ∈ LX ∪ ((Hind \ Aind) \ U0) := by
            simpa [hWold] using hzKY
          rcases mem_union.1 hzsplit with hzL | hzR
          · exact mem_union.2 (Or.inl ((inter_subset_right (s₁ := U0)) hzL))
          · exact mem_union.2 (Or.inr hzR)
        · exact mem_union.2 (Or.inl (hDsubX hzD))
    have hEnew : eligibleSet Gind ((Hind \ (Aind ∪ Y)) ∪ Dind) =
        eligibleSet Gind X ∪ eligibleSet Gind ((Hind \ Aind) \ U0) := by
      simpa [hWnew] using
        eligibleSet_disjoint_union (G := Gind) hdisjXrest hncXrest
    have hhEnew : hind ∈ eligibleSet Gind ((Hind \ (Aind ∪ Y)) ∪ Dind) := by
      have : hind ∈
          eligibleSet Gind X ∪ eligibleSet Gind ((Hind \ Aind) \ U0) :=
        mem_union.2 (Or.inl hhEX)
      simpa [hEnew] using this
    have hhE' : hind ∈ eligibleSet G' ((Hind \ (Aind ∪ Y)) ∪ Dind) := by
      have hdisjCar : Disjoint ((Hind \ (Aind ∪ Y)) ∪ Dind) (Aind ∪ Y) :=
        disjoint_union_left.2 ⟨Finset.disjoint_sdiff.symm, hdisjDA'⟩
      have : eligibleSet G' ((Hind \ (Aind ∪ Y)) ∪ Dind) =
          eligibleSet Gind ((Hind \ (Aind ∪ Y)) ∪ Dind) :=
        eligibleSet_suppressInternal (G := Gind) hdisjCar
      simpa [this] using hhEnew
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
      have : z ∈ LX ∪ Dind := by simpa [hXeq'] using hz
      rcases mem_union.1 this with hzL | hzD
      · exact mem_union.2 (Or.inl ((inter_subset_left (s₁ := U0)) hzL))
      · exact mem_union.2 (Or.inr hzD)
    have hnorestD : ∀ a ∈ Dind, ∀ b ∈ (Hind \ Aind) \ U0, ¬ Gind.Adj a b := by
      intro a ha b hb hadj
      have haU : a ∈ U := hDU ha
      have hb0 : b ∈ Hind \ Aind := (mem_sdiff.1 hb).1
      have hbU0 : b ∉ U0 := (mem_sdiff.1 hb).2
      have hbU : b ∉ U := fun hU => hbU0 (mem_inter.2 ⟨hU, hb0⟩)
      exact hUnc a haU b
        (mem_sdiff.2 ⟨mem_union.2 (Or.inl hb0), hbU⟩) hadj
    obtain ⟨q', hq'sup, hq'st, hq'fin, hq'ne, hq'P⟩ :=
      ih ((Hind \ (Aind ∪ Y)) ∪ Dind).card hlt G' Hind Dind (Aind ∪ Y) hind
        cH' cD' rfl hcH' hcD' hdisjind hA'sub hAne' hK0ind' hpK0'
        hKind' hpK' hhF' hhE'
    have hLE := suppressInternal_le Gind (Aind ∪ Y)
    by_cases hstA : q'.start ∈ Aind
    · refine ⟨q'.ofLE hLE, ?_, ?_, ?_, ?_,
        ProtectedAt_ofLE_edges hLE hedges'
          (hq'P.mono_set subset_union_left)⟩
      · simpa [GraphPath.ofLE_support] using hq'sup
      · simpa [GraphPath.ofLE_start] using hstA
      · simpa [GraphPath.ofLE_finish] using hq'fin
      · simpa [GraphPath.ofLE_start, GraphPath.ofLE_finish] using hq'ne
    · have hsY : q'.start ∈ Y := (mem_union.1 hq'st).resolve_left hstA
      have hPAind : q'.ProtectedAt cH' Aind :=
        hq'P.mono_set subset_union_left
      obtain ⟨qW, hsupW, hstW, hfinW, hneW, hPW⟩ :=
        exists_one_return_rotate_W (c := cHind) (Y := Y) hcHind
          hAind hU0 hXW hYold hdisjXY hdisjind hjoin hnocrossU0 hnorestD
          hpH hsH hedgesH hstay hstartX hfinX h4 hq'sup hcH' hPAind
          hedges' hsY
      refine ⟨qW.ofLE hLE, ?_, ?_, ?_, ?_,
        ProtectedAt_ofLE_edges hLE hedges' hPW⟩
      · simpa [GraphPath.ofLE_support] using hsupW
      · simpa [GraphPath.ofLE_start] using hstW
      · simpa [GraphPath.ofLE_finish, hfinW] using hq'fin
      · simpa [GraphPath.ofLE_start, GraphPath.ofLE_finish] using hneW

/-- Three-cycle merger from one released `A`-to-`h` path. -/
theorem exists_released_three_cycle {H D Qset A : Finset V} {x z h : V}
    {G : SimpleGraph V} (cH : GraphCycle G) (cD : GraphCycle G)
    (cQ : GraphCycle G)
    (hcH : cH.support = H) (hcD : cD.support = D) (hcQ : cQ.support = Qset)
    (hHD : Disjoint H D) (hHQ : Disjoint H Qset) (hDQ : Disjoint D Qset)
    (hA : A ⊆ H) (hAne : A.Nonempty)
    (hxQ : x ∈ Qset) (hzQ : z ∈ Qset)
    (hAx : ∀ a ∈ A, G.Adj a x)
    (hK0 : Nikoghosyan.IsCograph G (H \ A))
    (hpK0 : pathCoverNumber G (H \ A) = A.card)
    (hJ : Nikoghosyan.IsCograph G ((H \ A) ∪ D))
    (hpJ : pathCoverNumber G ((H \ A) ∪ D) = A.card)
    (hhF : h ∈ ineligibleSet G (H \ A))
    (hhE : h ∈ eligibleSet G ((H \ A) ∪ D))
    (hzh : G.Adj z h)
    (hxC : x ∈ cQ.support) (hzC : z ∈ cQ.support)
    (hxz : cQ.succAt hxC = z ∨ cQ.succAt hzC = x) :
    ∃ c : GraphCycle G, c.support = H ∪ D ∪ Qset := by
  obtain ⟨P, hPsup, hPst, hPfin, hPne, _⟩ :=
    exists_released_absorption (G := G) (H := H) (D := D) (A := A) (h := h)
      cH cD hcH hcD hHD hA hAne hK0 hpK0 hJ hpJ hhF hhE
  have hPnn : ¬ P.walk.Nil := fun hn =>
    hPne ((nil_iff_start_eq_finish P).1 hn)
  let Qxz : GraphPath G :=
    if hs : cQ.succAt hxC = z then
      (cQ.openAt hxC).reverse
    else
      cQ.openAt hzC
  have hQst : Qxz.start = x := by
    by_cases hs : cQ.succAt hxC = z
    · simp [Qxz, hs, GraphPath.reverse, openAt_finish]
    · have hsucc : cQ.succAt hzC = x := hxz.resolve_left hs
      simpa [Qxz, hs, openAt_start] using hsucc
  have hQfn : Qxz.finish = z := by
    by_cases hs : cQ.succAt hxC = z
    · simp [Qxz, hs, GraphPath.reverse, openAt_start]
    · simp [Qxz, hs, openAt_finish]
  have hQsup : Qxz.support = Qset := by
    by_cases hs : cQ.succAt hxC = z
    · simpa [Qxz, hs, GraphPath.support_reverse, openAt_support, hcQ]
    · simpa [Qxz, hs, openAt_support, hcQ]
  have hhQ : h ∉ Qset := by
    have hhK : h ∈ H \ A := ineligibleSet_subset (G := G) _ hhF
    exact fun hzQ => Finset.disjoint_left.1 hHQ (mem_sdiff.1 hhK).1 hzQ
  have hhQxz : h ∉ Qxz.support := by simpa [hQsup] using hhQ
  have hadjzh : G.Adj Qxz.finish h := by simpa [hQfn] using hzh
  let T := Qxz.concatAdj hadjzh hhQxz
  have hTst : T.start = x := by simp [T, concatAdj, hQst]
  have hTfn : T.finish = h := by simp [T, concatAdj]
  have hTsup : T.support = insert h Qset := by
    simpa [T, support_concatAdj, hQsup]
  have hPnnR : ¬ P.reverse.walk.Nil := by simpa [GraphPath.reverse] using hPnn
  let Utail := P.reverse.trimStart hPnnR
  have hUst : Utail.start = P.reverse.walk.snd := by simp [Utail, trimStart]
  have hUfn : Utail.finish = P.start := by simp [Utail, trimStart, GraphPath.reverse]
  have hrevst : P.reverse.start = h := by simp [GraphPath.reverse, hPfin]
  have hUsup : Utail.support = P.support.erase h := by
    simpa [Utail, GraphPath.support_reverse, hrevst] using
      support_trimStart P.reverse hPnnR
  have hadjTU : G.Adj T.finish Utail.start := by
    have hf : T.finish = P.reverse.start := by
      simp [T, concatAdj, hrevst]
    have hs : Utail.start = P.reverse.walk.snd := hUst
    simpa [hf, hs] using P.reverse.walk.adj_snd hPnnR
  have hdTU : Disjoint T.support Utail.support := by
    rw [hTsup, hUsup]
    refine disjoint_left.2 ?_
    intro w hwT hwU
    have hwP : w ∈ P.support := (mem_erase.1 hwU).2
    have hwHD : w ∈ H ∪ D := by simpa [hPsup] using hwP
    have hneh : w ≠ h := (mem_erase.1 hwU).1
    rcases mem_insert.1 hwT with rfl | hwQ
    · exact hneh rfl
    · rcases mem_union.1 hwHD with hwH | hwD
      · exact Finset.disjoint_left.1 hHQ hwH hwQ
      · exact Finset.disjoint_left.1 hDQ hwD hwQ
  let R := T.splice Utail hadjTU hdTU
  have hRst : R.start = x := by simp [R, splice, hTst]
  have hRfn : R.finish = P.start := by simp [R, splice, hUfn]
  have hRsup : R.support = H ∪ D ∪ Qset := by
    rw [support_splice, hTsup, hUsup, hPsup]
    ext z
    simp only [mem_union, mem_insert, mem_erase]
    constructor
    · intro hz
      rcases hz with (rfl | hzQ) | ⟨_, hzHD⟩
      · exact Or.inl (Or.inl (mem_sdiff.1 (ineligibleSet_subset (G := G) _ hhF)).1)
      · exact Or.inr hzQ
      · exact Or.inl hzHD
    · intro hz
      rcases hz with (hzH | hzD) | hzQ
      · by_cases heq : z = h
        · exact Or.inl (Or.inl heq)
        · exact Or.inr ⟨heq, Or.inl hzH⟩
      · by_cases heq : z = h
        · exact Or.inl (Or.inl heq)
        · exact Or.inr ⟨heq, Or.inr hzD⟩
      · exact Or.inl (Or.inr hzQ)
  have h3 : 3 ≤ R.support.card := by
    have hQ3 : 3 ≤ Qset.card := by simpa [hcQ] using cQ.three_le_card_support
    have hsub : Qset ⊆ R.support := by
      intro w hw
      have : w ∈ (H ∪ D) ∪ Qset := mem_union.2 (Or.inr hw)
      simpa [hRsup] using this
    exact hQ3.trans (card_le_card hsub)
  have hclose : G.Adj R.finish R.start := by
    simpa [hRfn, hRst] using hAx P.start hPst
  refine ⟨R.toCycle hclose h3, ?_⟩
  simpa [support_toCycle] using hRsup

end Cograph
end Nikoghosyan
