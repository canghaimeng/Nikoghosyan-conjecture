/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.HamiltonBalanced
import Nikoghosyan.Cograph.ProfileMaximum
import Nikoghosyan.Cograph.Restriction

/-!
# Canonical saturated profile containers and exact endpoint neighbourhoods

Manuscript `prof:prop:container`, `prof:prop:endpoints`,
`prof:prop:incompatible`, `prof:cor:containers`.

Work is on an actual original-edge cycle support `U` of order at least
three, a nonempty `A ⊆ U`, and the cograph remainder `K = U \ A`. Tightness
is `c(U \ T) = |T|` on original finite supports. Integer `δ_A` is never
replaced by truncated natural subtraction.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `T` is tight in the Hamiltonian support `U` when `c(U \ T) = |T|`. -/
def Tight (U T : Finset V) : Prop :=
  T ⊆ U ∧ componentCount G (U \ T) = T.card

/-- `A` is saturated when the cograph remainder meets `p(K) = |A|`. -/
def Saturated (U A : Finset V) : Prop :=
  pathCoverNumber G (U \ A) = A.card

/-- Canonical container `S_A = A ∪ F(K)`. -/
noncomputable def canonicalContainer (U A : Finset V) : Finset V :=
  profileContainer (G := G) U A

/-- Vertices of `U` that are `R(U)`-adjacent to at least one vertex of `A`. -/
noncomputable def spanningPathNeighbors (U A : Finset V) : Finset V :=
  U.filter fun b => ∃ a ∈ A, SpanningPathCompatible (G := G) U a b

lemma mem_spanningPathNeighbors_iff {U A : Finset V} {b : V} :
    b ∈ spanningPathNeighbors (G := G) U A ↔
      b ∈ U ∧ ∃ a ∈ A, SpanningPathCompatible (G := G) U a b := by
  simp [spanningPathNeighbors]

lemma canonicalContainer_eq {U A : Finset V} :
    canonicalContainer (G := G) U A = A ∪ ineligibleSet G (U \ A) :=
  rfl

lemma Tight.subset {U T : Finset V} (h : Tight (G := G) U T) : T ⊆ U := h.1

lemma Tight.eq_card {U T : Finset V} (h : Tight (G := G) U T) :
    componentCount G (U \ T) = T.card := h.2

lemma canonicalContainer_subset {U A : Finset V} (hA : A ⊆ U) :
    canonicalContainer (G := G) U A ⊆ U :=
  profileContainer_subset (G := G) hA

lemma mem_canonicalContainer_of_mem_A {U A : Finset V} {x : V}
    (hx : x ∈ A) : x ∈ canonicalContainer (G := G) U A :=
  mem_union.2 (Or.inl hx)

/-! ### Cycle rotation and opening at a prescribed vertex -/

lemma mem_walk_support_of_mem_cycle {c : GraphCycle G} {x : V}
    (hx : x ∈ c.support) : x ∈ c.walk.support :=
  List.mem_toFinset.mp (by simpa [GraphCycle.support] using hx)

noncomputable def rotateTo (c : GraphCycle G) {u : V}
    (hu : u ∈ c.support) : GraphCycle G where
  start := u
  walk := c.walk.rotate u (mem_walk_support_of_mem_cycle hu)
  isCycle :=
    (Walk.isCycle_rotate (mem_walk_support_of_mem_cycle hu)).2 c.isCycle

lemma support_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (rotateTo c hu).support = c.support := by
  ext x
  simp only [rotateTo, GraphCycle.support, List.mem_toFinset]
  exact Walk.mem_support_rotate_iff (w := x) c.walk u
    (mem_walk_support_of_mem_cycle hu)

lemma start_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (rotateTo c hu).start = u :=
  rfl

lemma cycle_length_pos (c : GraphCycle G) : 0 < c.walk.length :=
  lt_of_lt_of_le (by decide : (0 : ℕ) < 3) c.three_le_length

noncomputable def cycleSucc (c : GraphCycle G) : V :=
  c.walk.getVert 1

lemma adj_start_cycleSucc (c : GraphCycle G) : G.Adj c.start (cycleSucc c) := by
  simpa [cycleSucc, Walk.getVert_zero] using
    c.walk.adj_getVert_succ (cycle_length_pos c)

lemma cycleSucc_mem_support (c : GraphCycle G) : cycleSucc c ∈ c.support :=
  List.mem_toFinset.2 (Walk.getVert_mem_support c.walk 1)

lemma cycleSucc_ne_start (c : GraphCycle G) : cycleSucc c ≠ c.start :=
  (adj_start_cycleSucc c).ne.symm

/-- Open the cycle so the resulting spanning path starts at `x`. -/
lemma exists_spanning_path_from (c : GraphCycle G) {x : V}
    (hx : x ∈ c.support) :
    ∃ p : GraphPath G, p.support = c.support ∧ p.start = x ∧
      G.Adj p.finish x := by
  let c' := rotateTo c hx
  have hnil : ¬ c'.walk.Nil := c'.isCycle.not_nil
  obtain ⟨w, hadj, q, hwalk⟩ := (Walk.not_nil_iff.1 hnil)
  have hq : q.IsPath :=
    ((Walk.cons_isCycle_iff q hadj).1 (by simpa [hwalk] using c'.isCycle)).1
  let p0 : GraphPath G := ⟨w, c'.start, q, hq⟩
  have hp0 : p0.support = c'.support := by
    have hstart : c'.start ∈ q.support := Walk.end_mem_support q
    simp [p0, GraphPath.support, GraphCycle.support, hwalk, Walk.support_cons,
      insert_eq_of_mem (List.mem_toFinset.2 hstart)]
  have hx' : c'.start = x := start_rotateTo c hx
  refine ⟨p0.reverse, ?_, ?_, ?_⟩
  · rw [GraphPath.support_reverse, hp0, support_rotateTo]
  · simp [p0, GraphPath.reverse, hx']
  · simpa [p0, GraphPath.reverse, hx'] using hadj.symm

/-- Open the cycle so the resulting spanning path ends at `x`. -/
lemma exists_spanning_path_to (c : GraphCycle G) {x : V}
    (hx : x ∈ c.support) :
    ∃ p : GraphPath G, p.support = c.support ∧ p.finish = x ∧
      G.Adj x p.start := by
  let c' := rotateTo c hx
  have hnil : ¬ c'.walk.Nil := c'.isCycle.not_nil
  obtain ⟨w, hadj, q, hwalk⟩ := (Walk.not_nil_iff.1 hnil)
  have hq : q.IsPath :=
    ((Walk.cons_isCycle_iff q hadj).1 (by simpa [hwalk] using c'.isCycle)).1
  let p0 : GraphPath G := ⟨w, c'.start, q, hq⟩
  have hp0 : p0.support = c'.support := by
    have hstart : c'.start ∈ q.support := Walk.end_mem_support q
    simp [p0, GraphPath.support, GraphCycle.support, hwalk, Walk.support_cons,
      insert_eq_of_mem (List.mem_toFinset.2 hstart)]
  have hx' : c'.start = x := start_rotateTo c hx
  refine ⟨p0, ?_, ?_, ?_⟩
  · rw [hp0, support_rotateTo]
  · simp [p0, hx']
  · simpa [p0, hx'] using hadj

/-! ### Numerical container from cycle opening and ProfileMaximum -/

lemma pathCoverNumber_eq_one_of_cycle {U : Finset V}
    (c : GraphCycle G) (hc : c.support = U) :
    pathCoverNumber G U = 1 := by
  obtain ⟨p, hp, _⟩ := GraphCycle.exists_spanning_path c
  exact pathCoverNumber_eq_one_of_support p (hp.trans hc)

lemma pathCoverNumber_sdiff_le_card_of_cycle {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U) (hA : A ⊆ U) (hAne : A.Nonempty) :
    pathCoverNumber G (U \ A) ≤ A.card := by
  obtain ⟨a, haA⟩ := hAne
  have hE : Eligible G U a := eligible_of_cycle c hc (hA haA)
  have hle := pathCoverNumber_sdiff_le_of_eligible (G := G) hA haA hE
  have hpU : pathCoverNumber G U = 1 := pathCoverNumber_eq_one_of_cycle c hc
  have hpos : 1 ≤ A.card := Nat.succ_le_of_lt (card_pos.2 ⟨a, haA⟩)
  omega

lemma Saturated_of_tight_container {U A T : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty) (hAT : A ⊆ T)
    (hT : Tight (G := G) U T) :
    Saturated (G := G) U A := by
  have hle : (componentCount G (U \ T) : ℤ) - (T.card : ℤ) ≤
      profileDelta (G := G) U A :=
    profileDelta_le_of_nested hAT hT.1
  have hpK : pathCoverNumber G (U \ A) ≤ A.card :=
    pathCoverNumber_sdiff_le_card_of_cycle c hc hA hAne
  simp only [profileDelta, hT.2] at hle
  exact le_antisymm hpK (by omega)

lemma tight_container_subset_canonical {U A T : Finset V}
    (hAT : A ⊆ T) (hT : Tight (G := G) U T)
    (hK : IsCograph G (U \ A)) (hSat : Saturated (G := G) U A) :
    T ⊆ canonicalContainer (G := G) U A := by
  have hSat' : pathCoverNumber G (U \ A) = A.card := hSat
  have hatt :
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
        profileDelta (G := G) U A := by
    simp [profileDelta, hSat', hT.2]
  exact profile_maximizer_subset_container hAT hT.1 hK hatt

lemma canonicalContainer_tight_of_saturated {U A : Finset V}
    (hA : A ⊆ U) (hK : IsCograph G (U \ A))
    (hKne : (U \ A).Nonempty) (hSat : Saturated (G := G) U A) :
    Tight (G := G) U (canonicalContainer (G := G) U A) := by
  refine ⟨canonicalContainer_subset (G := G) hA, ?_⟩
  have hatt := profileContainer_attains (G := G) hA hK hKne
  have hSat' : pathCoverNumber G (U \ A) = A.card := hSat
  simp only [canonicalContainer, profileDelta, hSat'] at hatt ⊢
  omega

lemma canonicalContainer_proper_of_saturated {U A : Finset V}
    (hA : A ⊆ U) (hK : IsCograph G (U \ A))
    (hKne : (U \ A).Nonempty) (hSat : Saturated (G := G) U A) :
    canonicalContainer (G := G) U A ⊂ U := by
  refine (ssubset_iff_subset_ne).2 ⟨canonicalContainer_subset (G := G) hA, ?_⟩
  intro hEq
  have hrem := sdiff_profileContainer (G := G) hA
  have hF := componentCount_sdiff_ineligibleSet_eq (cotreeOn_of_isCograph hK)
  have hp : 1 ≤ pathCoverNumber G (U \ A) :=
    one_le_pathCoverNumber_of_nonempty (G := G) hKne
  have : U \ canonicalContainer (G := G) U A = ∅ := by
    rw [hEq]; simp
  have hempty : (U \ A) \ ineligibleSet G (U \ A) = ∅ := by
    simpa [canonicalContainer] using hrem.symm.trans this
  have : componentCount G ((U \ A) \ ineligibleSet G (U \ A)) = 0 := by
    simpa [hempty] using componentCount_empty (G := G)
  omega

lemma eq_univ_of_sdiff_not_nonempty {U A : Finset V}
    (hA : A ⊆ U) (h : ¬ (U \ A).Nonempty) : A = U :=
  hA.antisymm (sdiff_eq_empty_iff_subset.1 (not_nonempty_iff_eq_empty.1 h))

/-- Manuscript `prof:prop:container`: a tight container of `A` exists if and
only if `A` is saturated. -/
lemma canonical_saturated_container {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty) (hK : IsCograph G (U \ A)) :
    (∃ T, Tight (G := G) U T ∧ A ⊆ T) ↔ Saturated (G := G) U A := by
  constructor
  · intro ⟨T, hT, hAT⟩
    exact Saturated_of_tight_container c hc hA hAne hAT hT
  · intro hSat
    by_cases hKne : (U \ A).Nonempty
    · exact ⟨canonicalContainer (G := G) U A,
        canonicalContainer_tight_of_saturated hA hK hKne hSat, subset_union_left⟩
    · have hAU := eq_univ_of_sdiff_not_nonempty hA hKne
      have : A.card = 0 := by
        have hp0 : pathCoverNumber G (U \ A) = 0 := by
          simpa [hAU] using pathCoverNumber_empty (G := G)
        simpa [Saturated, hp0] using hSat.symm
      exact (Nat.ne_of_gt (card_pos.2 hAne) this).elim

/-- When `A` is saturated and `K` is nonempty, `S_A` is the unique largest
proper tight container of `A`. -/
lemma canonical_saturated_container_spec {U A : Finset V}
    (hA : A ⊆ U) (hAne : A.Nonempty) (hK : IsCograph G (U \ A))
    (hSat : Saturated (G := G) U A) :
    Tight (G := G) U (canonicalContainer (G := G) U A) ∧
      canonicalContainer (G := G) U A ⊂ U ∧
        ∀ T, Tight (G := G) U T → A ⊆ T →
          T ⊆ canonicalContainer (G := G) U A := by
  have hKne : (U \ A).Nonempty := by
    by_contra h
    have hAU := eq_univ_of_sdiff_not_nonempty hA h
    have : A.card = 0 := by
      have hp0 : pathCoverNumber G (U \ A) = 0 := by
        simpa [hAU] using pathCoverNumber_empty (G := G)
      simpa [Saturated, hp0] using hSat.symm
    exact Nat.ne_of_gt (card_pos.2 hAne) this
  exact ⟨canonicalContainer_tight_of_saturated hA hK hKne hSat,
    canonicalContainer_proper_of_saturated hA hK hKne hSat,
    fun T hT hAT => tight_container_subset_canonical hAT hT hK hSat⟩

lemma canonical_saturated_container_of_canonical {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : Nikoghosyan.IsCograph G (U \ A)) :
    (∃ T, Tight (G := G) U T ∧ A ⊆ T) ↔ Saturated (G := G) U A :=
  canonical_saturated_container c hc hA hAne (isCograph_iff.2 hK)

lemma canonical_saturated_container_spec_of_canonical {U A : Finset V}
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : Nikoghosyan.IsCograph G (U \ A))
    (hSat : Saturated (G := G) U A) :
    Tight (G := G) U (canonicalContainer (G := G) U A) ∧
      canonicalContainer (G := G) U A ⊂ U ∧
        ∀ T, Tight (G := G) U T → A ⊆ T →
          T ⊆ canonicalContainer (G := G) U A :=
  canonical_saturated_container_spec hA hAne (isCograph_iff.2 hK) hSat

/-! ### Actual cover obtained by deleting `A` from a fixed cycle -/

lemma exists_cycle_delete_cover {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty) :
    ∃ (p : GraphPath G) (pc : PathCover G (U \ A)),
      p.support = U ∧ p.start ∈ A ∧ G.Adj p.finish p.start ∧
        pc.card ≤ A.card ∧
          ∀ q ∈ pc.paths, q.support ⊆ p.support := by
  obtain ⟨a, haA⟩ := hAne
  have hx : a ∈ c.support := by simpa [hc] using hA haA
  obtain ⟨p, hp, hs, hadj⟩ := exists_spanning_path_from c hx
  have hpU : p.support = U := hp.trans hc
  have hstartA : p.start ∈ A := by simpa [hs] using haA
  let pc0 : PathCover G U := (PathCover.ofPath p).cast hpU
  have hend : pc0.IsEndpoint p.start := by
    refine ⟨p, ?_, Or.inl rfl⟩
    rw [PathCover.cast_paths, PathCover.ofPath]
    exact List.mem_singleton.2 rfl
  have hArest : A.erase p.start ⊆ U.erase p.start := by
    intro x hx
    exact mem_erase.2 ⟨(mem_erase.1 hx).1, hA (mem_of_mem_erase hx)⟩
  obtain ⟨pc1, hcard1, hsup1⟩ :=
    exists_pathCover_sdiff (pc0.deleteVertex p.start) hArest
  have hEq : U.erase p.start \ A.erase p.start = U \ A := by
    ext x
    simp only [mem_sdiff, mem_erase]
    constructor
    · intro ⟨⟨hxne, hxU⟩, hxA⟩
      exact ⟨hxU, fun hA' => hxA ⟨hxne, hA'⟩⟩
    · intro ⟨hxU, hxA⟩
      exact ⟨⟨fun h => hxA (by simpa [h] using hstartA), hxU⟩,
        fun h => hxA h.2⟩
  refine ⟨p, pc1.cast hEq, hpU, hstartA, by simpa [hs] using hadj, ?_, ?_⟩
  · have hdv := pc0.card_deleteVertex_le_of_endpoint hend
    have hcard0 : pc0.card = 1 := by
      rw [PathCover.cast_card, PathCover.ofPath_card]
    have herase : (A.erase p.start).card = A.card - 1 :=
      card_erase_of_mem hstartA
    have hpos : 1 ≤ A.card := Nat.succ_le_of_lt (card_pos.2 ⟨p.start, hstartA⟩)
    rw [PathCover.cast_card]
    omega
  · intro q hq
    rw [PathCover.cast_paths] at hq
    obtain ⟨r, hr, hqr⟩ := hsup1 q hq
    obtain ⟨t, ht, hrt⟩ := List.mem_flatMap.1
      (show r ∈ pc0.paths.flatMap fun s => GraphPath.deleteVertex s p.start from
        by simpa [PathCover.deleteVertex] using hr)
    have htP : t = p := by
      rw [PathCover.cast_paths, PathCover.ofPath] at ht
      simpa using ht
    exact hqr.trans (by
      simpa [htP] using GraphPath.support_subset_of_mem_deleteVertex hrt)

lemma cycle_delete_cover_min_of_saturated {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty) (hSat : Saturated (G := G) U A) :
    ∃ (p : GraphPath G) (pc : PathCover G (U \ A)),
      p.support = U ∧ p.start ∈ A ∧ G.Adj p.finish p.start ∧
        pc.card = pathCoverNumber G (U \ A) ∧
          ∀ q ∈ pc.paths, q.support ⊆ p.support := by
  obtain ⟨p, pc, hp, hs, hadj, hcard, hsub⟩ :=
    exists_cycle_delete_cover c hc hA hAne
  have hmin : pc.card = pathCoverNumber G (U \ A) := by
    have hle := pathCoverNumber_le (G := G) pc
    have hSat' : pathCoverNumber G (U \ A) = A.card := hSat
    exact le_antisymm (hcard.trans (le_of_eq hSat'.symm)) hle
  exact ⟨p, pc, hp, hs, hadj, hmin, hsub⟩

/-! ### Compatibility of an eligible vertex with an old end of `Q` -/

lemma spanningPathCompatible_of_path (p : GraphPath G)
    (hne : p.start ≠ p.finish) :
    SpanningPathCompatible (G := G) p.support p.start p.finish :=
  ⟨hne, p, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma exists_compatible_old_end {Q : GraphPath G} {b : V}
    (h2 : 2 ≤ Q.support.card) (hcog : IsCograph G Q.support)
    (hbE : Eligible G Q.support b) (hb : b ∈ Q.support) :
    SpanningPathCompatible (G := G) Q.support b Q.start ∨
      SpanningPathCompatible (G := G) Q.support b Q.finish := by
  have hneSF : Q.start ≠ Q.finish := by
    intro h
    have hnil : Q.walk.Nil := (GraphPath.nil_iff_start_eq_finish Q).2 h
    have : Q.support.card = 1 := by
      simpa using
        (congrArg Finset.card (GraphPath.support_eq_singleton_of_nil Q hnil))
    omega
  have hpQ : pathCoverNumber G Q.support = 1 :=
    pathCoverNumber_eq_one_of_support Q rfl
  have hconn := connected_of_spanning_path Q rfl
  have hdata :=
    hamilton_endpoints_of_traceable_cograph (G := G) h2 hcog hconn hpQ
  have hRuv := spanningPathCompatible_of_path Q hneSF
  by_cases hbs : b = Q.start
  · exact Or.inr (by simpa [hbs] using hRuv)
  by_cases hbf : b = Q.finish
  · exact Or.inl (by simpa [hbf] using spanningPathCompatible_symm hRuv)
  rcases hdata with hcrit | hbal
  · obtain ⟨A, B, _, _, hunion, _, _, hA, hEeq, _, hRiff, _⟩ := hcrit
    have hbEA : b ∈ eligibleSet G A := by
      have : b ∈ eligibleSet G Q.support :=
        (mem_eligibleSet_iff (G := G)).2 ⟨hb, hbE⟩
      simpa [hunion] using (hEeq ▸ this)
    have huE := (Eligible_of_support_ends Q rfl).1
    have hvE := (Eligible_of_support_ends Q rfl).2
    have huEA : Q.start ∈ eligibleSet G A := by
      have : Q.start ∈ eligibleSet G Q.support :=
        (mem_eligibleSet_iff (G := G)).2 ⟨Q.start_mem_support, huE⟩
      simpa [hunion] using (hEeq ▸ this)
    have hvEA : Q.finish ∈ eligibleSet G A := by
      have : Q.finish ∈ eligibleSet G Q.support :=
        (mem_eligibleSet_iff (G := G)).2 ⟨Q.finish_mem_support, hvE⟩
      simpa [hunion] using (hEeq ▸ this)
    have hDuv : DistinctPathCompatible (G := G) A Q.start Q.finish :=
      (hRiff Q.start Q.finish).1 (by simpa [hunion] using hRuv)
    by_cases hDu : DistinctPathCompatible (G := G) A b Q.start
    · exact Or.inl ((hRiff b Q.start).2 hDu)
    · by_cases hDv : DistinctPathCompatible (G := G) A b Q.finish
      · exact Or.inr ((hRiff b Q.finish).2 hDv)
      · have hyb : Q.start ∈ dNonadjClass (G := G) A b :=
          mem_dNonadjClass_iff.2 ⟨huEA, hDu⟩
        have hzb : Q.finish ∈ dNonadjClass (G := G) A b :=
          mem_dNonadjClass_iff.2 ⟨hvEA, hDv⟩
        have hb_in_u := dNonadjClass_symm hbEA hyb
        have hcontra :=
          dNonadjClass_trans (cotreeOn_of_isCograph hA)
            huEA hbEA hvEA hb_in_u hzb
        exact ((mem_dNonadjClass_iff.1 hcontra).2 hDuv).elim
  · have hQu : rNonadjClass (G := G) Q.support Q.start ≠
        rNonadjClass (G := G) Q.support Q.finish := by
      intro heq
      have hvQ : Q.finish ∈ rNonadjClass (G := G) Q.support Q.start := by
        simpa [heq] using mem_rNonadjClass_self Q.finish_mem_support
      exact (mem_rNonadjClass_iff.1 hvQ).2 hRuv
    by_cases hbu :
        rNonadjClass (G := G) Q.support b =
          rNonadjClass (G := G) Q.support Q.start
    · exact Or.inr (spanningPath_of_distinct_classes hbal hb
        Q.finish_mem_support (by intro h; exact hQu (hbu.symm.trans h)))
    · exact Or.inl (spanningPath_of_distinct_classes hbal hb
        Q.start_mem_support hbu)

/-! ### Reverse neighbourhood inclusion from the both-endpoints cut -/

lemma spanningPathNeighbors_subset_sdiff_container {U A : Finset V}
    (hA : A ⊆ U) (hK : IsCograph G (U \ A))
    (hAne : A.Nonempty) (hSat : Saturated (G := G) U A) :
    spanningPathNeighbors (G := G) U A ⊆
      U \ canonicalContainer (G := G) U A := by
  intro b hb
  obtain ⟨hbU, a, haA, hR⟩ := mem_spanningPathNeighbors_iff.1 hb
  have hspec := canonical_saturated_container_spec hA hAne hK hSat
  have hT := hspec.1
  have haS : a ∈ canonicalContainer (G := G) U A :=
    mem_canonicalContainer_of_mem_A haA
  refine mem_sdiff.2 ⟨hbU, ?_⟩
  intro hbS
  have hle :=
    componentCount_sdiff_le_of_both_endpoints (G := G)
      (U := U) (S := canonicalContainer (G := G) U A)
      (x := a) (y := b) hT.1 haS hbS hR.1 hR
  have heq := hT.2
  have hpos : 1 ≤ (canonicalContainer (G := G) U A).card :=
    Nat.succ_le_of_lt (card_pos.2 ⟨a, haS⟩)
  omega

/-- Opening `c` at its start produces a spanning path from `succ` to `start`. -/
lemma exists_spanning_path_succ (c : GraphCycle G) :
    ∃ p : GraphPath G, p.support = c.support ∧ p.start = cycleSucc c ∧
      p.finish = c.start ∧ G.Adj c.start (cycleSucc c) := by
  have hnil : ¬ c.walk.Nil := c.isCycle.not_nil
  obtain ⟨w, hadj, q, hwalk⟩ := (Walk.not_nil_iff.1 hnil)
  have hq : q.IsPath :=
    ((Walk.cons_isCycle_iff q hadj).1 (by simpa [hwalk] using c.isCycle)).1
  let p : GraphPath G := ⟨w, c.start, q, hq⟩
  have hw : w = cycleSucc c := by
    simp [cycleSucc, hwalk]
  refine ⟨p, ?_, hw, rfl, by simpa [hw] using hadj⟩
  have hstart : c.start ∈ q.support := Walk.end_mem_support q
  simp [p, GraphPath.support, GraphCycle.support, hwalk, Walk.support_cons,
    insert_eq_of_mem (List.mem_toFinset.2 hstart)]

lemma exists_path_of_mem_cover {U : Finset V} (pc : PathCover G U) {x : V}
    (hx : x ∈ U) : ∃ p ∈ pc.paths, x ∈ p.support :=
  (pc.mem_iff x).1 hx

lemma exists_spanning_from_cycle_succ {U : Finset V} {b : V}
    (c : GraphCycle G) (hc : c.support = U) (hbU : b ∈ U) :
    SpanningPathCompatible (G := G) U b
      (cycleSucc (rotateTo c (by simpa [hc] using hbU))) := by
  set c' := rotateTo c (by simpa [hc] using hbU)
  obtain ⟨p, hp, hs, hf, _hadj⟩ := exists_spanning_path_succ c'
  have hstart : c'.start = b := start_rotateTo c (by simpa [hc] using hbU)
  have hne : b ≠ cycleSucc c' := by
    intro h
    exact cycleSucc_ne_start c' (h.symm.trans hstart.symm)
  refine ⟨hne, p, ?_, Or.inr ⟨hs, ?_⟩⟩
  · rw [hp, support_rotateTo, hc]
  · rw [hf, hstart]

lemma exists_spanning_from_cycle_pred {U : Finset V} {b : V}
    (c : GraphCycle G) (hc : c.support = U) (hbU : b ∈ U) :
    SpanningPathCompatible (G := G) U b
      (cycleSucc (rotateTo c.reverse
        (by simpa [hc, GraphCycle.support_reverse] using hbU))) := by
  have hb' : b ∈ c.reverse.support := by
    simpa [GraphCycle.support_reverse, hc] using hbU
  simpa [GraphCycle.support_reverse, hc] using
    (exists_spanning_from_cycle_succ c.reverse
      (by simpa [GraphCycle.support_reverse] using hc) hb')

lemma eligible_of_mem_sdiff_container {U A : Finset V} {b : V}
    (hb : b ∈ U \ canonicalContainer (G := G) U A) :
    b ∈ U \ A ∧ Eligible G (U \ A) b := by
  have hbU : b ∈ U := (mem_sdiff.1 hb).1
  have hbS : b ∉ canonicalContainer (G := G) U A := (mem_sdiff.1 hb).2
  have hbA : b ∉ A := fun h => hbS (mem_canonicalContainer_of_mem_A h)
  have hbF : b ∉ ineligibleSet G (U \ A) := fun h =>
    hbS (mem_union.2 (Or.inr h))
  have hbK : b ∈ U \ A := mem_sdiff.2 ⟨hbU, hbA⟩
  have hE : Eligible G (U \ A) b := by
    have h := (mem_ineligibleSet_iff (G := G) (U := U \ A) (x := b)).not
    simp only [not_and, Classical.not_not] at h
    exact h.mp hbF hbK
  exact ⟨hbK, hE⟩

lemma restriction_eligible_on_selected_path {U : Finset V}
    (hU : IsCograph G U) (pc : PathCover G U)
    (hpc : pc.card = pathCoverNumber G U) {Q : GraphPath G}
    (hQ : Q ∈ pc.paths) {b : V}
    (hbE : Eligible G U b) (hbQ : b ∈ Q.support) :
    Eligible G Q.support b := by
  have hrest :=
    restriction_eq_of_min_cover_of_isCograph (G := G) hU pc hpc
      (fun r => decide (b ∈ r.support))
  have hbL : b ∈ supportUnion (pc.paths.filter fun r =>
      decide (b ∈ r.support)) :=
    mem_supportUnion_iff.2 ⟨Q, List.mem_filter.2 ⟨hQ, by simp [hbQ]⟩, hbQ⟩
  have hEQ : eligibleSet G (supportUnion (pc.paths.filter fun r =>
      decide (b ∈ r.support))) =
    eligibleSet G U ∩ supportUnion (pc.paths.filter fun r =>
      decide (b ∈ r.support)) := hrest.2.1
  have hbEU : b ∈ eligibleSet G U :=
    (mem_eligibleSet_iff (G := G)).2 ⟨Eligible.mem (G := G) hbE, hbE⟩
  have : b ∈ eligibleSet G (supportUnion (pc.paths.filter fun r =>
      decide (b ∈ r.support))) := by
    rw [hEQ]
    exact mem_inter.2 ⟨hbEU, hbL⟩
  have hQE : Eligible G (supportUnion (pc.paths.filter fun r =>
      decide (b ∈ r.support))) b :=
    (mem_eligibleSet_iff (G := G)).1 this |>.2
  have hQeq : supportUnion (pc.paths.filter fun r =>
      decide (b ∈ r.support)) = Q.support := by
    ext z
    constructor
    · intro hz
      obtain ⟨r, hr, hzr⟩ := mem_supportUnion_iff.1 hz
      have hr' := List.mem_filter.1 hr
      have hbR : b ∈ r.support := of_decide_eq_true hr'.2
      have : r = Q := by
        by_contra hne
        exact Finset.disjoint_left.1
          (PathCover.pairwise_disjoint_of_mem pc.disjoint hr'.1 hQ hne)
          hbR hbQ
      simpa [this] using hzr
    · intro hz
      exact mem_supportUnion_iff.2
        ⟨Q, List.mem_filter.2 ⟨hQ, by simp [hbQ]⟩, hz⟩
  simpa [hQeq] using hQE

/-- If a cycle neighbour of `b` lies in `A`, opening that original edge
realises a spanning `U`-path from `b` into `A`. -/
lemma exists_spanning_of_cycle_neighbor_in_A {U A : Finset V} {b : V}
    (c : GraphCycle G) (hc : c.support = U)
    (hbU : b ∈ U)
    (hA : cycleSucc (rotateTo c (by simpa [hc] using hbU)) ∈ A ∨
      cycleSucc (rotateTo c.reverse
        (by simpa [hc, GraphCycle.support_reverse] using hbU)) ∈ A) :
    ∃ a ∈ A, SpanningPathCompatible (G := G) U b a := by
  rcases hA with h | h
  · exact ⟨_, h, exists_spanning_from_cycle_succ c hc hbU⟩
  · exact ⟨_, h, exists_spanning_from_cycle_pred c hc hbU⟩

/-- Reorient a spanning path of `L` so that it starts at `b` and ends at the
chosen old end `w`. -/
lemma exists_oriented_path_from {L : Finset V} {b w : V}
    (hR : SpanningPathCompatible (G := G) L b w) :
    ∃ q : GraphPath G, q.support = L ∧ q.start = b ∧ q.finish = w := by
  obtain ⟨hne, p, hp, hends⟩ := hR
  rcases hends with h | h
  · exact ⟨p, hp, h.1, h.2⟩
  · exact ⟨p.reverse, by simpa [GraphPath.support_reverse, hp],
      by simp [GraphPath.reverse, h.2], by simp [GraphPath.reverse, h.1]⟩

/-- Attach an original A-seam at the surviving old end of a remainder path. -/
lemma SpanningPathCompatible_attach_A {L : Finset V} {b w a : V}
    (hR : SpanningPathCompatible (G := G) L b w)
    (hadj : G.Adj w a) (haL : a ∉ L) :
    SpanningPathCompatible (G := G) (insert a L) b a := by
  obtain ⟨q, hq, hs, hf⟩ := exists_oriented_path_from hR
  have hbL : b ∈ L := by
    have : q.start ∈ L := by simpa [hq] using q.start_mem_support
    simpa [hs] using this
  have hne : b ≠ a := fun hba => haL (by simpa [hba] using hbL)
  have haq : a ∉ q.support := by simpa [hq] using haL
  have hadj' : G.Adj q.finish a := by simpa [hf] using hadj
  let r := q.concatAdj hadj' haq
  refine ⟨hne, r, ?_, Or.inl ⟨by simp [r, GraphPath.concatAdj, hs],
    by simp [r, GraphPath.concatAdj]⟩⟩
  simpa [r, GraphPath.support_concatAdj, hq]

lemma insert_sdiff_eq_of_mem {U L : Finset V} {a : V}
    (haU : a ∈ U) (haL : a ∉ L) (hLU : L ⊆ U) :
    insert a L = U ↔ L = U.erase a := by
  constructor
  · intro h
    ext x
    simp only [mem_erase]
    constructor
    · intro hxL
      exact ⟨fun hxa => haL (by simpa [hxa] using hxL), hLU hxL⟩
    · intro ⟨hxne, hxU⟩
      have : x ∈ insert a L := by simpa [h] using hxU
      exact (mem_insert.1 this).resolve_left hxne
  · intro h
    ext x
    simp only [mem_insert]
    constructor
    · intro hx
      rcases hx with rfl | hxL
      · exact haU
      · exact hLU hxL
    · intro hxU
      by_cases hxa : x = a
      · exact Or.inl hxa
      · have : x ∈ U.erase a := mem_erase.2 ⟨hxa, hxU⟩
        exact Or.inr (by simpa [h] using this)

/-- Every remaining path after deleting `A` from a cover whose every start
is already `A`-adjacent keeps an original `A`-seam at its start. -/
lemma deleteVertex_start_adj {U A : Finset V} (pc : PathCover G U) {f : V}
    (hfA : f ∈ A)
    (h : ∀ q ∈ pc.paths, ∃ a ∈ A, G.Adj a q.start) :
    ∀ q ∈ (pc.deleteVertex f).paths, ∃ a ∈ A, G.Adj a q.start := by
  intro q hq
  obtain ⟨p, hp, hq'⟩ := List.mem_flatMap.1
    (show q ∈ pc.paths.flatMap fun r => GraphPath.deleteVertex r f from by
      simpa [PathCover.deleteVertex] using hq)
  obtain ⟨a, haA, hadj⟩ := h p hp
  unfold GraphPath.deleteVertex at hq'
  split_ifs at hq' with hx hnil hs hf
  · cases hq'
  · simp only [List.mem_singleton] at hq'
    subst hq'
    refine ⟨f, hfA, ?_⟩
    obtain ⟨w, hadj', rest, hwalk⟩ := (Walk.not_nil_iff.1 hnil)
    simpa [GraphPath.trimStart, hs, hwalk] using hadj'
  · simp only [List.mem_singleton] at hq'
    subst hq'
    exact ⟨a, haA, by simpa [GraphPath.trimFinish] using hadj⟩
  · rcases List.mem_cons.mp hq' with h | h
    · subst h
      exact ⟨a, haA, hadj⟩
    · have : q = (p.dropUntil hx).trimStart (fun hnil' =>
          hf ((GraphPath.dropUntil_nil_iff (p := p) (x := f) hx).1
            (by simpa [GraphPath.dropUntil] using hnil'))) :=
        List.mem_singleton.mp h
      subst this
      refine ⟨f, hfA, ?_⟩
      have hnilD : ¬ (p.dropUntil hx).walk.Nil := by
        intro hnil'
        exact hf ((GraphPath.dropUntil_nil_iff (p := p) (x := f) hx).1
          (by simpa [GraphPath.dropUntil] using hnil'))
      obtain ⟨w, hadj', rest, hwalk⟩ :=
        (Walk.not_nil_iff.1 (by simpa [GraphPath.dropUntil] using hnilD))
      have hst : (p.dropUntil hx).start = f := by simp [GraphPath.dropUntil]
      simpa [GraphPath.trimStart, GraphPath.dropUntil, hst, hwalk] using hadj'
  · simp only [List.mem_singleton] at hq'
    subst hq'
    exact ⟨a, haA, hadj⟩

lemma exists_delete_sdiff_start_adj {U S A : Finset V}
    (pc : PathCover G U) (hS : S ⊆ U)
    (h : ∀ q ∈ pc.paths, ∃ a ∈ A, G.Adj a q.start)
    (hSA : S ⊆ A) :
    ∃ pc' : PathCover G (U \ S),
      pc'.card ≤ pc.card + S.card ∧
        ∀ q ∈ pc'.paths, ∃ a ∈ A, G.Adj a q.start := by
  induction S using Finset.induction generalizing U pc with
  | empty =>
    refine ⟨pc.cast (by simp), ?_, ?_⟩
    · simp [PathCover.cast_card]
    · intro q hq
      rw [PathCover.cast_paths] at hq
      exact h q hq
  | insert f S hf ih =>
    have hfU : f ∈ U := hS (mem_insert_self f S)
    have hfA : f ∈ A := hSA (mem_insert_self f S)
    have hSsub : S ⊆ U.erase f := by
      intro y hy
      exact mem_erase.2 ⟨fun hfy => hf (hfy ▸ hy), hS (mem_insert_of_mem hy)⟩
    have hSA' : S ⊆ A := fun y hy => hSA (mem_insert_of_mem hy)
    have hdel := deleteVertex_start_adj (A := A) pc hfA h
    obtain ⟨pc1, hcard1, hinv1⟩ :=
      ih (U := U.erase f) (pc.deleteVertex f) hSsub hdel hSA'
    have hEq : U.erase f \ S = U \ insert f S := by
      rw [sdiff_insert, erase_sdiff_distrib, erase_eq_of_notMem hf]
    refine ⟨pc1.cast hEq, ?_, ?_⟩
    · have hdv := pc.card_deleteVertex_le f
      have hins : (insert f S).card = S.card + 1 := card_insert_of_notMem hf
      rw [PathCover.cast_card]
      omega
    · intro q hq
      rw [PathCover.cast_paths] at hq
      exact hinv1 q hq

lemma cycle_delete_cover_start_adj {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty) :
    ∃ (p : GraphPath G) (pc : PathCover G (U \ A)),
      p.support = U ∧ p.start ∈ A ∧ G.Adj p.finish p.start ∧
        pc.card ≤ A.card ∧
          ∀ q ∈ pc.paths, ∃ a ∈ A, G.Adj a q.start := by
  obtain ⟨x0, hx0A⟩ := hAne
  have hx : x0 ∈ c.support := by simpa [hc] using hA hx0A
  obtain ⟨p, hp, hs, hadj⟩ := exists_spanning_path_from c hx
  have hpU : p.support = U := hp.trans hc
  have hstartA : p.start ∈ A := by simpa [hs] using hx0A
  let pc0 : PathCover G U := (PathCover.ofPath p).cast hpU
  have hend : pc0.IsEndpoint p.start := by
    refine ⟨p, ?_, Or.inl rfl⟩
    rw [PathCover.cast_paths, PathCover.ofPath]
    exact List.mem_singleton.2 rfl
  have hinv0 : ∀ q ∈ (pc0.deleteVertex p.start).paths,
      ∃ a ∈ A, G.Adj a q.start := by
    intro q hq
    have hq' : q ∈ (GraphPath.deleteVertex p p.start) := by
      have : (pc0.deleteVertex p.start).paths =
          pc0.paths.flatMap fun r => GraphPath.deleteVertex r p.start := rfl
      have hmem : p ∈ pc0.paths := by
        rw [PathCover.cast_paths, PathCover.ofPath]
        exact List.mem_singleton.2 rfl
      obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.1 (by simpa [this] using hq)
      have : r = p := by
        rw [PathCover.cast_paths, PathCover.ofPath] at hr
        simpa using hr
      simpa [this] using hqr
    have hnil : ¬ p.walk.Nil := by
      intro hnil
      have : p.start = p.finish := (GraphPath.nil_iff_start_eq_finish p).1 hnil
      have hcard : p.support.card = 1 := by
        simpa using congrArg Finset.card
          (GraphPath.support_eq_singleton_of_nil p hnil)
      have h3 : 3 ≤ U.card := by simpa [hc] using c.three_le_card_support
      have : U.card = 1 := by simpa [hpU] using hcard
      omega
    have hsdel : p.start ∈ p.support := p.start_mem_support
    have hdv : GraphPath.deleteVertex p p.start = [p.trimStart hnil] := by
      unfold GraphPath.deleteVertex
      simp [hsdel, hnil]
    have : q = p.trimStart hnil := by
      simpa [hdv] using hq'
    subst this
    refine ⟨p.start, hstartA, ?_⟩
    obtain ⟨w, hadj', rest, hwalk⟩ := (Walk.not_nil_iff.1 hnil)
    simpa [GraphPath.trimStart, hwalk] using hadj'
  have hArest : A.erase p.start ⊆ U.erase p.start := by
    intro y hy
    exact mem_erase.2 ⟨(mem_erase.1 hy).1, hA (mem_of_mem_erase hy)⟩
  obtain ⟨pc1, hcard1, hinv1⟩ :=
    exists_delete_sdiff_start_adj (A := A) (pc0.deleteVertex p.start)
      hArest hinv0 (erase_subset _ _)
  have hEq : U.erase p.start \ A.erase p.start = U \ A := by
    ext y
    simp only [mem_sdiff, mem_erase]
    constructor
    · intro ⟨⟨hyne, hyU⟩, hyA⟩
      exact ⟨hyU, fun hA' => hyA ⟨hyne, hA'⟩⟩
    · intro ⟨hyU, hyA⟩
      exact ⟨⟨fun h => hyA (by simpa [h] using hstartA), hyU⟩,
        fun h => hyA h.2⟩
  have hcard0 : pc0.card = 1 := by
    rw [PathCover.cast_card, PathCover.ofPath_card]
  have hdv := pc0.card_deleteVertex_le_of_endpoint hend
  have herase : (A.erase p.start).card = A.card - 1 :=
    card_erase_of_mem hstartA
  have hpos : 1 ≤ A.card := Nat.succ_le_of_lt (card_pos.2 ⟨p.start, hstartA⟩)
  refine ⟨p, pc1.cast hEq, hpU, hstartA, by simpa [hs] using hadj, ?_, ?_⟩
  · rw [PathCover.cast_card]
    omega
  · intro q hq
    rw [PathCover.cast_paths] at hq
    exact hinv1 q hq

/-- Forward neighbourhood when an original cycle neighbour of `b` lies in
`A`. This is the singleton-gap opening of `prof:prop:endpoints`. -/
lemma sdiff_container_subset_spanningPathNeighbors_of_cycle_neighbor
    {U A : Finset V} {b : V}
    (c : GraphCycle G) (hc : c.support = U) (hbU : b ∈ U)
    (hn : cycleSucc (rotateTo c (by simpa [hc] using hbU)) ∈ A ∨
      cycleSucc (rotateTo c.reverse
        (by simpa [hc, GraphCycle.support_reverse] using hbU)) ∈ A) :
    b ∈ spanningPathNeighbors (G := G) U A := by
  obtain ⟨a, haA, hR⟩ :=
    exists_spanning_of_cycle_neighbor_in_A c hc hbU hn
  exact mem_spanningPathNeighbors_iff.2
    ⟨hbU, a, haA, spanningPathCompatible_symm hR⟩

/-- Manuscript `prof:cor:containers`: coincidence of canonical containers.
Both profiles are saturated, so each `S` is the unique largest tight
container of its input; containment `B ⊆ S_A` makes `S_A` a tight
container of `B`. -/
lemma coincidence_canonical_containers {U A B : Finset V}
    (hA : A ⊆ U) (hAne : A.Nonempty) (hKA : IsCograph G (U \ A))
    (hB : B ⊆ U) (hBne : B.Nonempty) (hKB : IsCograph G (U \ B))
    (hSatA : Saturated (G := G) U A) (hSatB : Saturated (G := G) U B)
    (hBA : B ⊆ canonicalContainer (G := G) U A) :
    canonicalContainer (G := G) U A = canonicalContainer (G := G) U B := by
  have hTA := canonical_saturated_container_spec hA hAne hKA hSatA
  have hTB := canonical_saturated_container_spec hB hBne hKB hSatB
  have hAin : A ⊆ canonicalContainer (G := G) U A := subset_union_left
  have hSAsubSB : canonicalContainer (G := G) U A ⊆
      canonicalContainer (G := G) U B :=
    hTB.2.2 _ hTA.1 hBA
  have hSBsubSA : canonicalContainer (G := G) U B ⊆
      canonicalContainer (G := G) U A :=
    hTA.2.2 _ hTB.1 (hAin.trans hSAsubSB)
  exact subset_antisymm hSAsubSB hSBsubSA

lemma coincidence_canonical_containers_of_canonical {U A B : Finset V}
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hKA : Nikoghosyan.IsCograph G (U \ A))
    (hB : B ⊆ U) (hBne : B.Nonempty)
    (hKB : Nikoghosyan.IsCograph G (U \ B))
    (hSatA : Saturated (G := G) U A) (hSatB : Saturated (G := G) U B)
    (hBA : B ⊆ canonicalContainer (G := G) U A) :
    canonicalContainer (G := G) U A = canonicalContainer (G := G) U B :=
  coincidence_canonical_containers hA hAne (isCograph_iff.2 hKA)
    hB hBne (isCograph_iff.2 hKB) hSatA hSatB hBA

end Cograph
end Nikoghosyan

