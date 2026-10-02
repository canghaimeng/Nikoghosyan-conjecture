/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProtectedJoin
import Nikoghosyan.Cograph.Compatibility
import Nikoghosyan.PathGraphRestriction
import Nikoghosyan.PathBoundaryReturn

/-!
# noYY `A' = A ∪ Y` deletion and original-`A` endpoint restoration

Manuscript `prof:thm:protected`, remaining same-child branch.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma exists_straddle_edge {S : Finset V} (p : GraphPath G)
    (hmeet : (p.support ∩ S).Nonempty) (hmiss : (p.support \ S).Nonempty) :
    ∃ e ∈ p.edges, endsStraddle e S := by
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨y, hy⟩ := hmiss
  have hxS : x ∈ p.support ∧ x ∈ S := mem_inter.1 hx
  have hyS : y ∈ p.support ∧ y ∉ S := mem_sdiff.1 hy
  by_cases hs : p.start ∈ S
  · let B : Finset V := univ.filter fun z => z ∉ S
    have hyB : y ∈ B := by simp [B, hyS.2]
    obtain ⟨_, hb⟩ := find?_B_of_mem (B := B) hyS.1 hyB
    have hnone : p.walk.support.find? (inB B) ≠ none := by simp [hb]
    have hsB : p.start ∉ B := by simp [B, hs]
    have hfind := firstB_spec (B := B) (p := p) hnone
    have hb0 : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind).1
    have hbB : firstB B p hnone ∈ B := (mem_find?_B (B := B) hfind).2
    have hv : firstB B p hnone ∉ S := by simpa [B] using hbB
    have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind
    have hnn : ¬ (p.takeUntil hb0).walk.Nil := fun hn =>
      hne ((takeUntil_nil_iff p hb0).1 hn)
    let pre := (p.takeUntil hb0).trimFinish hnn
    have hu : pre.finish ∈ S := by
      have hpen : pre.finish ∈ (p.takeUntil hb0).support := by
        have : pre.support ⊆ (p.takeUntil hb0).support := by
          rw [support_trimFinish]; exact erase_subset _ _
        exact this pre.finish_mem_support
      have hneP : pre.finish ≠ firstB B p hnone := by
        have hmem : pre.finish ∈
            (p.takeUntil hb0).support.erase (p.takeUntil hb0).finish := by
          rw [← support_trimFinish (p.takeUntil hb0) hnn]
          exact pre.finish_mem_support
        have : (p.takeUntil hb0).finish = firstB B p hnone := by simp [takeUntil]
        exact this ▸ (mem_erase.1 hmem).1
      have hnotB : pre.finish ∉ B :=
        takeUntil_ne_first_not_mem_B (B := B) hfind hb0 hpen hneP
      simpa [B] using hnotB
    have hePre : s(pre.finish, (p.takeUntil hb0).finish) ∈
        (p.takeUntil hb0).edges :=
      last_edge_mem (p.takeUntil hb0) hnn
    refine ⟨s(pre.finish, firstB B p hnone),
      edges_takeUntil_subset p hb0 (by simpa [takeUntil] using hePre),
      endsStraddle_iff.2 (fun heq => hv ((iff_of_eq heq).mp hu))⟩
  · obtain ⟨_, hb⟩ := find?_B_of_mem (B := S) hxS.1 hxS.2
    have hnone : p.walk.support.find? (inB S) ≠ none := by simp [hb]
    have hfind := firstB_spec (B := S) (p := p) hnone
    have hb0 : firstB S p hnone ∈ p.support := (mem_find?_B (B := S) hfind).1
    have hbS : firstB S p hnone ∈ S := (mem_find?_B (B := S) hfind).2
    have hne : firstB S p hnone ≠ p.start := find?_B_ne_start hs hfind
    have hnn : ¬ (p.takeUntil hb0).walk.Nil := fun hn =>
      hne ((takeUntil_nil_iff p hb0).1 hn)
    let pre := (p.takeUntil hb0).trimFinish hnn
    have hu : pre.finish ∉ S := by
      have hpen : pre.finish ∈ (p.takeUntil hb0).support := by
        have : pre.support ⊆ (p.takeUntil hb0).support := by
          rw [support_trimFinish]; exact erase_subset _ _
        exact this pre.finish_mem_support
      have hneP : pre.finish ≠ firstB S p hnone := by
        have hmem : pre.finish ∈
            (p.takeUntil hb0).support.erase (p.takeUntil hb0).finish := by
          rw [← support_trimFinish (p.takeUntil hb0) hnn]
          exact pre.finish_mem_support
        have : (p.takeUntil hb0).finish = firstB S p hnone := by simp [takeUntil]
        exact this ▸ (mem_erase.1 hmem).1
      exact takeUntil_ne_first_not_mem_B (B := S) hfind hb0 hpen hneP
    have hePre : s(pre.finish, (p.takeUntil hb0).finish) ∈
        (p.takeUntil hb0).edges :=
      last_edge_mem (p.takeUntil hb0) hnn
    refine ⟨s(pre.finish, firstB S p hnone),
      edges_takeUntil_subset p hb0 (by simpa [takeUntil] using hePre),
      endsStraddle_iff.2 (fun heq => hu ((iff_of_eq heq).mpr hbS))⟩

lemma ProtectedAt.mono_set {p : GraphPath G} {c : GraphCycle G}
    {A A' : Finset V} (h : p.ProtectedAt c A') (hsub : A ⊆ A') :
    p.ProtectedAt c A := by
  intro e he
  obtain ⟨heE, b, hbA, hb⟩ := mem_AIncident_iff.1 he
  exact h (mem_AIncident_iff.2 ⟨heE, b, hsub hbA, hb⟩)

lemma ProtectedAt.of_cycle_edges_eq {p : GraphPath G}
    {c c' : GraphCycle G} {A : Finset V}
    (h : c.walk.edges.toFinset = c'.walk.edges.toFinset)
    (hP : p.ProtectedAt c A) : p.ProtectedAt c' A := by
  intro e he
  simpa [h] using hP he

lemma exists_leftover_containing {p : GraphPath G} {A : Finset V} {x : V}
    (hx : x ∈ p.support \ A) :
    ∃ Q ∈ leftoverPieces A p, x ∈ Q.support := by
  obtain ⟨Q, hQ, hxQ⟩ := (leftoverCoverOfPath p A |>.mem_iff x).1 hx
  exact ⟨Q, by simpa [leftoverCoverOfPath_paths] using hQ, hxQ⟩

lemma mem_support_tail_of_ne_start {p : GraphPath G} {x : V}
    (hx : x ∈ p.support) (hne : x ≠ p.start) : x ∈ p.walk.support.tail := by
  have hxL : x ∈ p.walk.support := (mem_walk_support (p := p)).1 hx
  have hnn : ¬ p.walk.Nil := by
    intro h
    have : p.support = {p.start} := support_eq_singleton_of_nil p h
    exact hne (by simpa [this] using hx)
  obtain ⟨w, hadj, q, hwalk⟩ := Walk.not_nil_iff.1 hnn
  have hcons : p.walk.support = p.start :: q.support := by simp [hwalk]
  have := List.mem_cons.1 (by simpa [hcons] using hxL)
  rcases this with h | h
  · exact (hne h).elim
  · simpa [hcons] using h

lemma leftover_factor_edges_mem {A : Finset V} {p Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) {u v : V}
    (he : s(u, v) ∈ p.edges) (hu : u ∈ Q.support) (hv : v ∈ Q.support) :
    s(u, v) ∈ Q.edges := by
  obtain ⟨ru, rv, heq, _, _⟩ := leftoverPieces_factor (B := A) p Q hQ
  have heW : s(u, v) ∈ ((ru.append Q.walk).append rv).edges := by
    simpa [heq] using mem_edges_iff.1 he
  rw [Walk.edges_append, List.mem_append] at heW
  rcases heW with hmid | hrv
  · rw [Walk.edges_append, List.mem_append] at hmid
    rcases hmid with hru | hQe
    · have huR : u ∈ ru.support := Walk.mem_support_of_mem_edges hru (by simp)
      have hvR : v ∈ ru.support := Walk.mem_support_of_mem_edges hru (by simp)
      have hpathAQ : (ru.append Q.walk).IsPath :=
        Walk.IsPath.of_append_left (by simpa [heq] using p.isPath)
      have hnodAQ := hpathAQ.support_nodup
      rw [Walk.support_append] at hnodAQ
      have hdis := (List.nodup_append.1 hnodAQ).2.2
      have hu_eq : u = Q.start := by
        by_contra hne
        exact hdis u huR u (mem_support_tail_of_ne_start hu hne) rfl
      have hv_eq : v = Q.start := by
        by_contra hne
        exact hdis v hvR v (mem_support_tail_of_ne_start hv hne) rfl
      have hadj : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using p.edges_subset_edgeSet _ he
      exact (hadj.ne (hu_eq.trans hv_eq.symm)).elim
    · exact mem_edges_iff.2 hQe
  · have heq' : p.walk = ru.append (Q.walk.append rv) := by
      simpa [Walk.append_assoc] using heq
    have hpathQR : (Q.walk.append rv).IsPath :=
      Walk.IsPath.of_append_right (by simpa [heq'] using p.isPath)
    have hnod := hpathQR.support_nodup
    rw [Walk.support_append] at hnod
    have hdis := (List.nodup_append.1 hnod).2.2
    have hvW : v ∈ Q.walk.support := (mem_walk_support (p := Q)).1 hv
    have hvR : v ∈ rv.support := Walk.mem_support_of_mem_edges hrv (by simp)
    have hv_ne : v ≠ Q.finish := by
      intro hvQ
      have hadj : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using p.edges_subset_edgeSet _ he
      have huR : u ∈ rv.support := Walk.mem_support_of_mem_edges hrv (by simp)
      have huW : u ∈ Q.walk.support := (mem_walk_support (p := Q)).1 hu
      by_cases hu_eq : u = Q.finish
      · exact hadj.ne (hu_eq.trans hvQ.symm)
      · exact hdis u huW u
          (mem_support_tail_of_ne_start (p := ofWalk rv
            (Walk.IsPath.of_append_right hpathQR))
            (List.mem_toFinset.2 huR) hu_eq) rfl
    exact (hdis v hvW v
      (mem_support_tail_of_ne_start (p := ofWalk rv
        (Walk.IsPath.of_append_right hpathQR))
        (List.mem_toFinset.2 hvR) hv_ne) rfl).elim

lemma leftover_finish_eq_of_mem {A : Finset V} {p Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hf : p.finish ∈ Q.support) :
    Q.finish = p.finish := by
  obtain ⟨ru, rv, heq, _, _⟩ := leftoverPieces_factor (B := A) p Q hQ
  by_cases hnil : rv.Nil
  · exact Walk.Nil.eq hnil
  · have heq' : p.walk = ru.append (Q.walk.append rv) := by
      simpa [Walk.append_assoc] using heq
    have hpathQR : (Q.walk.append rv).IsPath :=
      Walk.IsPath.of_append_right (by simpa [heq'] using p.isPath)
    have hpathR : rv.IsPath := Walk.IsPath.of_append_right hpathQR
    have hnod := hpathQR.support_nodup
    rw [Walk.support_append] at hnod
    have hdis := (List.nodup_append.1 hnod).2.2
    have hfQ : p.finish ∈ Q.walk.support := (mem_walk_support (p := Q)).1 hf
    have hne : (ofWalk rv hpathR).start ≠ (ofWalk rv hpathR).finish :=
      (nil_iff_start_eq_finish (ofWalk rv hpathR)).not.mp
        (by simpa [ofWalk] using hnil)
    have hfR : p.finish ∈ (ofWalk rv hpathR).walk.support.tail :=
      mem_support_tail_of_ne_start (p := ofWalk rv hpathR)
        (by simpa [ofWalk] using ofWalk rv hpathR |>.finish_mem_support)
        (by simpa [ofWalk] using hne.symm)
    exact (hdis p.finish hfQ p.finish hfR rfl).elim

lemma leftover_endpoint_of_leaving_edge {A : Finset V} {p Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) {a y : V}
    (he : s(a, y) ∈ p.edges) (hy : y ∈ Q.support) (ha : a ∉ Q.support) :
    y = Q.start ∨ y = Q.finish := by
  obtain ⟨ru, rv, heq, _, _⟩ := leftoverPieces_factor (B := A) p Q hQ
  have heW : s(a, y) ∈ ((ru.append Q.walk).append rv).edges := by
    simpa [heq] using mem_edges_iff.1 he
  rw [Walk.edges_append, List.mem_append] at heW
  rcases heW with hmid | hrv
  · rw [Walk.edges_append, List.mem_append] at hmid
    rcases hmid with hru | hQe
    · have hyR : y ∈ ru.support := Walk.mem_support_of_mem_edges hru (by simp)
      have hpath : (ru.append Q.walk).IsPath :=
        Walk.IsPath.of_append_left (by simpa [heq] using p.isPath)
      have hnod := hpath.support_nodup
      rw [Walk.support_append] at hnod
      have hdis := (List.nodup_append.1 hnod).2.2
      refine Or.inl ?_
      by_contra hne
      exact hdis y hyR y (mem_support_tail_of_ne_start hy hne) rfl
    · have haQ : a ∈ Q.support :=
        mem_support_of_mem_edge (mem_edges_iff.2 hQe) (by simp)
      exact (ha haQ).elim
  · have heq' : p.walk = ru.append (Q.walk.append rv) := by
      simpa [Walk.append_assoc] using heq
    have hpath : (Q.walk.append rv).IsPath :=
      Walk.IsPath.of_append_right (by simpa [heq'] using p.isPath)
    have hnod := hpath.support_nodup
    rw [Walk.support_append] at hnod
    have hdis := (List.nodup_append.1 hnod).2.2
    have hyQ : y ∈ Q.walk.support := (mem_walk_support (p := Q)).1 hy
    refine Or.inr ?_
    by_cases hst : y = Q.finish
    · exact hst
    · have hyR : y ∈ rv.support := Walk.mem_support_of_mem_edges hrv (by simp)
      exact (hdis y hyQ y
        (mem_support_tail_of_ne_start (p := ofWalk rv
          (Walk.IsPath.of_append_right hpath))
          (List.mem_toFinset.2 hyR) hst) rfl).elim

end GraphPath

namespace GraphCycle

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma mem_incident_imp_succ_or_pred (c : GraphCycle G) {u v : V}
    (hu : u ∈ c.support) (he : s(u, v) ∈ c.edges) (hne : u ≠ v) :
    v = c.succAt hu ∨ v = (c.openAt hu).walk.penultimate := by
  have hmem : s(u, v) ∈ c.incidentEdges u :=
    mem_incidentEdges_iff.2 ⟨he, by simp⟩
  have : s(u, v) ∈
      ({s(u, c.succAt hu), s((c.openAt hu).walk.penultimate, u)} :
        Finset (Sym2 V)) := by
    simpa [c.incidentEdges_eq hu] using hmem
  rcases mem_insert.1 this with h | h
  · rcases (Sym2.eq_iff.mp h) with ⟨_, hv⟩ | ⟨_, hv'⟩
    · exact Or.inl hv
    · exact (hne hv'.symm).elim
  · rcases (Sym2.eq_iff.mp (mem_singleton.1 h)) with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact (hne h2.symm).elim
    · exact Or.inr h2

noncomputable def boundaryEdges (c : GraphCycle G) (U0 : Finset V) :
    Finset (Sym2 V) :=
  c.edges.filter fun e => endsStraddle e U0

lemma mem_boundaryEdges_iff {c : GraphCycle G} {U0 : Finset V} {e : Sym2 V} :
    e ∈ c.boundaryEdges U0 ↔ e ∈ c.edges ∧ endsStraddle e U0 := by
  simp [boundaryEdges]

end GraphCycle

namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath
open Nikoghosyan.GraphCycle

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma leftover_support_subset_K {U A : Finset V} {p Q : GraphPath G}
    (hp : p.support = U) (hQ : Q ∈ leftoverPieces A p) :
    Q.support ⊆ U \ A := by
  intro x hx
  exact mem_sdiff.2 ⟨by simpa [hp] using leftoverPieces_support_subset p Q hQ hx,
    disjoint_left.1 (leftoverPieces_disjoint_B p Q hQ) hx⟩

lemma leftover_in_U0_or_disjoint {U A U0 : Finset V} {p Q : GraphPath G}
    (hp : p.support = U) (hQ : Q ∈ leftoverPieces A p)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b) :
    Q.support ⊆ U0 ∨ Disjoint Q.support U0 := by
  by_cases hmeet : (Q.support ∩ U0).Nonempty
  · refine Or.inl ?_
    by_contra hnot
    have hmiss : (Q.support \ U0).Nonempty := by
      by_contra hmiss
      have hsub : Q.support ⊆ U0 := by
        intro x hx
        by_contra hxU
        exact hmiss ⟨x, mem_sdiff.2 ⟨hx, hxU⟩⟩
      exact hnot hsub
    obtain ⟨e, he, hstr⟩ := exists_straddle_edge (S := U0) Q hmeet hmiss
    refine Sym2.inductionOn e (fun a b he hstr => ?_) he hstr
    have haQ : a ∈ Q.support := mem_support_of_mem_edge he (by simp)
    have hbQ : b ∈ Q.support := mem_support_of_mem_edge he (by simp)
    have hK : Q.support ⊆ U \ A := leftover_support_subset_K hp hQ
    have hadj : G.Adj a b := by
      simpa [SimpleGraph.mem_edgeSet] using Q.edges_subset_edgeSet _ he
    have hxor := endsStraddle_iff.1 hstr
    by_cases haU : a ∈ U0
    · have hbU : b ∉ U0 := fun hbU =>
        hxor (propext ⟨fun _ => hbU, fun _ => haU⟩)
      exact hnocross a haU b (mem_sdiff.2 ⟨hK hbQ, hbU⟩) hadj
    · have hbU : b ∈ U0 := by
        by_contra hbU
        exact hxor (propext ⟨fun h => (haU h).elim, fun h => (hbU h).elim⟩)
      exact hnocross b hbU a (mem_sdiff.2 ⟨hK haQ, haU⟩) hadj.symm
  · refine Or.inr (disjoint_left.2 ?_)
    intro x hxQ hxU
    exact hmeet ⟨x, mem_inter.2 ⟨hxQ, hxU⟩⟩

lemma leftover_start_of_meet_U0 {U A U0 : Finset V} {p Q : GraphPath G}
    (hp : p.support = U) (hQ : Q ∈ leftoverPieces A p)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hmeet : (Q.support ∩ U0).Nonempty) : Q.start ∈ U0 := by
  rcases leftover_in_U0_or_disjoint (U := U) (A := A) (U0 := U0) hp hQ hnocross
    with hsub | hdisj
  · exact hsub Q.start_mem_support
  · obtain ⟨x, hx⟩ := hmeet
    exact (disjoint_left.1 hdisj (mem_inter.1 hx).1 (mem_inter.1 hx).2).elim

lemma exists_leftover_start_seam {A : Finset V} {p Q : GraphPath G}
    (hs : p.start ∈ A) (hQ : Q ∈ leftoverPieces A p) :
    ∃ a, a ∈ A ∧ G.Adj a Q.start ∧ s(a, Q.start) ∈ p.edges := by
  obtain ⟨ru, rv, heq, hru, _⟩ := leftoverPieces_factor (B := A) p Q hQ
  have hnn : ¬ ru.Nil := leftoverPieces_factor_ru_not_nil hs hQ heq
  have ha : ru.penultimate ∈ A := hru.resolve_left hnn
  have heRu : s(ru.penultimate, Q.start) ∈ ru.edges :=
    Walk.mk_penultimate_end_mem_edges hnn
  have heP : s(ru.penultimate, Q.start) ∈ p.walk.edges := by
    have : s(ru.penultimate, Q.start) ∈ (ru.append Q.walk).edges :=
      mem_edges_append_left heRu
    simpa [heq] using mem_edges_append_left (q := rv) this
  have hadj : G.Adj ru.penultimate Q.start := by
    have : s(ru.penultimate, Q.start) ∈ G.edgeSet :=
      ru.edges_subset_edgeSet heRu
    simpa [SimpleGraph.mem_edgeSet] using this
  exact ⟨ru.penultimate, ha, hadj, mem_edges_iff.2 heP⟩

lemma exists_leftover_finish_seam {A : Finset V} {p Q : GraphPath G}
    (hs : p.start ∈ A) (hQ : Q ∈ leftoverPieces A p)
    (hclose : G.Adj p.finish p.start) :
    ∃ a, a ∈ A ∧ G.Adj Q.finish a ∧
      (s(Q.finish, a) ∈ p.edges ∨ s(Q.finish, a) = s(p.finish, p.start)) := by
  obtain ⟨ru, rv, heq, _, hrv⟩ := leftoverPieces_factor (B := A) p Q hQ
  by_cases hnil : rv.Nil
  · have hfin : Q.finish = p.finish := Walk.Nil.eq hnil
    refine ⟨p.start, hs, by simpa [hfin] using hclose, Or.inr ?_⟩
    simp [hfin]
  · have hsnd : rv.snd ∈ A := hrv.resolve_left hnil
    obtain ⟨w, hadj, rest, hwalk⟩ := Walk.not_nil_iff.1 hnil
    have hw : w = rv.snd := by simp [hwalk]
    have heRv : s(Q.finish, w) ∈ rv.edges := by simp [hwalk, Walk.edges_cons]
    have heP : s(Q.finish, w) ∈ p.walk.edges := by
      have : s(Q.finish, w) ∈ ((ru.append Q.walk).append rv).edges :=
        mem_edges_append_right heRv
      simpa [heq] using this
    refine ⟨w, by simpa [hw] using hsnd, by simpa [hw] using hadj, Or.inl ?_⟩
    exact mem_edges_iff.2 heP

lemma NoConsecutive_of_no_AA_cycle {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U) (hA : A ⊆ U)
    {p : GraphPath G}
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hno : ∀ a ∈ A, ∀ hu : a ∈ c.support,
      c.succAt hu ∉ A ∧ (c.openAt hu).walk.penultimate ∉ A) :
    NoConsecutive A p := by
  intro e he hboth
  refine Sym2.inductionOn e (fun u v he hboth => ?_) he hboth
  obtain ⟨huA, hvA⟩ := bothEndsIn_iff.1 hboth
  have heC : s(u, v) ∈ c.edges := by
    have : s(u, v) ∈ p.edges ∪ {s(p.finish, p.start)} :=
      mem_union.2 (Or.inl he)
    simpa [hedges, GraphCycle.edges] using this
  have hu : u ∈ c.support := by simpa [hc] using hA huA
  have hne : u ≠ v := by
    have hadj : G.Adj u v := by
      simpa [SimpleGraph.mem_edgeSet] using
        c.walk.edges_subset_edgeSet (GraphCycle.mem_edges_iff.1 heC)
    exact hadj.ne
  rcases mem_incident_imp_succ_or_pred c hu heC hne with h | h
  · exact (hno u huA hu).1 (by simpa [h] using hvA)
  · exact (hno u huA hu).2 (by simpa [h] using hvA)

lemma mem_edgeSet_suppressInternal_of_not_both {A' : Finset V} {u v : V}
    (hadj : G.Adj u v) (hnot : ¬ (u ∈ A' ∧ v ∈ A')) :
    s(u, v) ∈ (suppressInternal G A').edgeSet := by
  have hAdj : (suppressInternal G A').Adj u v :=
    (adj_suppressInternal_iff (G := G) (A' := A')).2 ⟨hadj, hnot⟩
  simpa [SimpleGraph.mem_edgeSet] using hAdj

lemma opened_edges_subset_cycle {p : GraphPath G}
    (c : GraphCycle G)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset) :
    p.edges ⊆ c.edges := by
  intro e he
  have : e ∈ p.edges ∪ {s(p.finish, p.start)} := mem_union.2 (Or.inl he)
  simpa [hedges, GraphCycle.edges] using this

lemma cycle_mem_support_of_mem_edge (c : GraphCycle G) {e : Sym2 V} {v : V}
    (he : e ∈ c.edges) (hv : v ∈ e) : v ∈ c.support := by
  simpa [GraphCycle.support] using
    List.mem_toFinset.2 (c.walk.mem_support_of_mem_edges (mem_edges_iff.1 he) hv)

lemma existsUnique_U0_end {e : Sym2 V} {U0 : Finset V}
    (h : endsStraddle e U0) :
    ∃ x, x ∈ e ∧ x ∈ U0 ∧ ∀ y, y ∈ e → y ∈ U0 → y = x := by
  refine Sym2.inductionOn e (fun a b h => ?_) h
  have hxor := endsStraddle_iff.1 h
  by_cases ha : a ∈ U0
  · have hb : b ∉ U0 := fun hb =>
      hxor (propext ⟨fun _ => hb, fun _ => ha⟩)
    refine ⟨a, by simp, ha, ?_⟩
    intro y hy hyU
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · rfl
    · exact (hb hyU).elim
  · have hb : b ∈ U0 := by
      by_contra hb
      exact hxor (propext ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩)
    refine ⟨b, by simp, hb, ?_⟩
    intro y hy hyU
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · exact (ha hyU).elim
    · rfl

lemma not_mem_AunionY_of_mem_X {U A U0 X Y : Finset V} {x : V}
    (hU0 : U0 ⊆ U \ A) (hX : X ⊆ U0) (hdisj : Disjoint X Y) (hx : x ∈ X) :
    x ∉ A ∪ Y := by
  intro hx'
  rcases mem_union.1 hx' with hA | hY
  · exact (mem_sdiff.1 (hU0 (hX hx))).2 hA
  · exact (disjoint_left.1 hdisj hx hY)

lemma leftover_U0_run_of_mem {U A U0 : Finset V} {p : GraphPath G} {y : V}
    (hp : p.support = U) (hU0 : U0 ⊆ U \ A)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hyU0 : y ∈ U0) :
    ∃ Q ∈ leftoverPieces A p, y ∈ Q.support ∧ Q.start ∈ U0 ∧ Q.support ⊆ U0 := by
  have hyK : y ∈ p.support \ A := by
    have hyU : y ∈ U := (mem_sdiff.1 (hU0 hyU0)).1
    exact mem_sdiff.2 ⟨by simpa [hp] using hyU, (mem_sdiff.1 (hU0 hyU0)).2⟩
  obtain ⟨Q, hQ, hyQ⟩ := exists_leftover_containing (p := p) (A := A) hyK
  have hmeet : (Q.support ∩ U0).Nonempty := ⟨y, mem_inter.2 ⟨hyQ, hyU0⟩⟩
  have hsU0 : Q.start ∈ U0 :=
    leftover_start_of_meet_U0 (U := U) (A := A) (U0 := U0) hp hQ hnocross hmeet
  exact ⟨Q, hQ, hyQ, hsU0, hstay Q hQ hsU0⟩

/-- A `Y`-vertex of an `X`-ended leftover run is strictly internal on the
opened spanning path. -/
lemma mem_Y_is_internal_U0_run {U A U0 X Y : Finset V} {p : GraphPath G}
    (hU0 : U0 ⊆ U \ A)
    (hdisj : Disjoint X Y)
    (hp : p.support = U) (hs : p.start ∈ A)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    {y : V} (hyY : y ∈ Y) (hyU0 : y ∈ U0) :
    ∃ Q ∈ leftoverPieces A p,
      y ∈ Q.support ∧ Q.start ∈ U0 ∧ Q.start ∈ X ∧ Q.finish ∈ X ∧
        y ≠ Q.start ∧ y ≠ Q.finish ∧ y ≠ p.start ∧ y ≠ p.finish := by
  obtain ⟨Q, hQ, hyQ, hsU0, _hQsup⟩ :=
    leftover_U0_run_of_mem (U := U) (A := A) (U0 := U0) hp hU0 hnocross hstay hyU0
  have hsX : Q.start ∈ X := hstartX Q hQ hsU0
  have hfX : Q.finish ∈ X := hfinX Q hQ hsU0
  have hyA : y ∉ A := (mem_sdiff.1 (hU0 hyU0)).2
  refine ⟨Q, hQ, hyQ, hsU0, hsX, hfX, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact (disjoint_left.1 hdisj (heq ▸ hsX) hyY)
  · intro heq
    exact (disjoint_left.1 hdisj (heq ▸ hfX) hyY)
  · intro heq
    exact hyA (heq ▸ hs)
  · intro hyf
    have hfinQ : Q.finish = p.finish :=
      leftover_finish_eq_of_mem (A := A) hQ (by simpa [hyf] using hyQ)
    exact (disjoint_left.1 hdisj (hfinQ ▸ hfX) (hyf ▸ hyY))

lemma cycle_neighbor_of_internal_on_leftover {A : Finset V}
    {p Q : GraphPath G} {y v : V}
    (hQ : Q ∈ leftoverPieces A p)
    (hyQ : y ∈ Q.support) (hns : y ≠ Q.start) (hnf : y ≠ Q.finish)
    (he : s(y, v) ∈ p.edges) :
    v ∈ Q.support := by
  by_contra hvQ
  have hends := leftover_endpoint_of_leaving_edge (A := A) hQ
    (by simpa [Sym2.eq_swap] using he) hyQ hvQ
  exact hends.elim hns hnf

/-- Internal vertices of an opened spanning path inherit the two cycle
incidences; the dropped closing edge is incident only to the path ends. -/
lemma incidentEdges_eq_cycle_of_internal_opened
    {p : GraphPath G} (c : GraphCycle G)
    (hsup : p.support = c.support) (hedges : p.edges ⊆ c.edges)
    {v : V} (hv : v ∈ p.support) (hs : v ≠ p.start) (hf : v ≠ p.finish) :
    p.incidentEdges v = c.incidentEdges v := by
  have hP : p.ProtectedAt c {v} := by
    intro e he
    exact hedges (mem_AIncident_iff.1 he).1
  exact incidentEdges_eq_cycle_of_internal_protected p c hsup
    (singleton_subset_iff.2 hv) hP (mem_singleton_self v) hs hf

lemma not_AA_of_no_cycle_neighbor {A : Finset V}
    (c : GraphCycle G) {u v : V}
    (hnoAA : ∀ a ∈ A, ∀ hu : a ∈ c.support,
      c.succAt hu ∉ A ∧ (c.openAt hu).walk.penultimate ∉ A)
    (huC : u ∈ c.support) (he : s(u, v) ∈ c.edges) (hne : u ≠ v)
    (huA : u ∈ A) (hvA : v ∈ A) : False := by
  rcases mem_incident_imp_succ_or_pred c huC he hne with h | h
  · exact (hnoAA u huA huC).1 (by simpa [h] using hvA)
  · exact (hnoAA u huA huC).2 (by simpa [h] using hvA)

/-- A cycle neighbour of a `Y`-vertex lies on the same leftover `U0`-run. -/
lemma cycle_neighbor_of_Y_on_leftover {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A) (hdisj : Disjoint X Y)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    {y v : V} (hyY : y ∈ Y) (hyU0 : y ∈ U0)
    (he : s(y, v) ∈ c.edges) (heP : s(y, v) ∈ p.edges) :
    ∃ Q ∈ leftoverPieces A p,
      y ∈ Q.support ∧ Q.start ∈ U0 ∧ v ∈ Q.support ∧ s(y, v) ∈ Q.edges := by
  obtain ⟨Q, hQ, hyQ, hsU0, _, _, hns, hnf, hnps, hnpf⟩ :=
    mem_Y_is_internal_U0_run (U := U) (A := A) (U0 := U0) (X := X) (Y := Y)
      hU0 hdisj hp hs hnocross hstay hstartX hfinX hyY hyU0
  have hyP : y ∈ p.support := leftoverPieces_support_subset p Q hQ hyQ
  have hsubP : p.edges ⊆ c.edges := opened_edges_subset_cycle c hedges
  have hinc :=
    incidentEdges_eq_cycle_of_internal_opened (p := p) c (hp.trans hc.symm)
      hsubP hyP hnps hnpf
  have hePy : s(y, v) ∈ p.incidentEdges y :=
    mem_incidentEdges_iff.2 ⟨heP, by simp⟩
  have hvQ : v ∈ Q.support :=
    cycle_neighbor_of_internal_on_leftover (A := A) hQ hyQ hns hnf heP
  exact ⟨Q, hQ, hyQ, hsU0, hvQ,
    leftover_factor_edges_mem (A := A) hQ heP hyQ hvQ⟩

/-- Every prescribed cycle edge survives `suppressInternal G (A ∪ Y)`
when leftover `U0`-runs end in `X`, there is no leftover `Y`–`Y` edge,
and `A` has no original cycle neighbour in `A`. -/
lemma cycle_edge_survives_suppressInternal_noYY {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A) (hY : Y ⊆ U0)
    (hdisj : Disjoint X Y)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hnoAA : ∀ a ∈ A, ∀ hu : a ∈ c.support,
      c.succAt hu ∉ A ∧ (c.openAt hu).walk.penultimate ∉ A)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    (hnoYY : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 →
      ∀ u ∈ Y, ∀ v ∈ Y, s(u, v) ∉ Q.edges)
    {e : Sym2 V} (he : e ∈ c.edges) :
    e ∈ (suppressInternal G (A ∪ Y)).edgeSet := by
  refine Sym2.inductionOn e (fun u v he => ?_) he
  have hadj : G.Adj u v := by
    simpa [SimpleGraph.mem_edgeSet] using
      c.walk.edges_subset_edgeSet (mem_edges_iff.1 he)
  have hnot : ¬ (u ∈ A ∪ Y ∧ v ∈ A ∪ Y) := by
    intro ⟨huAY, hvAY⟩
    have huC : u ∈ c.support := cycle_mem_support_of_mem_edge c he (by simp)
    have hvC : v ∈ c.support := cycle_mem_support_of_mem_edge c he (by simp)
    have hne : u ≠ v := hadj.ne
    have hclosing : s(u, v) ≠ s(p.finish, p.start) := by
      intro heq
      have hfinAY : p.finish ∈ A ∪ Y := by
        rcases (Sym2.eq_iff.mp heq) with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
        · simpa [hu'] using huAY
        · simpa [hv'] using hvAY
      rcases mem_union.1 hfinAY with hfinA | hfinY
      · have hstC : p.start ∈ c.support :=
          by simpa [hc, hp] using p.start_mem_support
        have heClose : s(p.start, p.finish) ∈ c.edges := by
          simpa [heq, Sym2.eq_swap] using he
        have hneSF : p.start ≠ p.finish := by
          have : G.Adj p.start p.finish := by
            simpa [SimpleGraph.mem_edgeSet] using
              c.walk.edges_subset_edgeSet (mem_edges_iff.1 heClose)
          exact this.ne
        exact not_AA_of_no_cycle_neighbor (c := c) hnoAA hstC heClose hneSF hs hfinA
      · obtain ⟨_, _, _, _, _, _, _, _, _, hnpf⟩ :=
          mem_Y_is_internal_U0_run (U := U) (A := A) (U0 := U0) (X := X)
            (Y := Y) hU0 hdisj hp hs hnocross hstay hstartX hfinX hfinY (hY hfinY)
        exact hnpf rfl
    have heP : s(u, v) ∈ p.edges := by
      have : s(u, v) ∈ p.edges ∪ {s(p.finish, p.start)} := by
        simpa [hedges, GraphCycle.edges] using he
      exact (mem_union.1 this).resolve_right fun h =>
        hclosing (mem_singleton.1 h)
    rcases mem_union.1 huAY with huA | huY
    · rcases mem_union.1 hvAY with hvA | hvY
      · exact not_AA_of_no_cycle_neighbor (c := c) hnoAA huC he hne huA hvA
      · have he' : s(v, u) ∈ c.edges := by simpa [Sym2.eq_swap] using he
        have heP' : s(v, u) ∈ p.edges := by simpa [Sym2.eq_swap] using heP
        obtain ⟨Q, hQ, _, _, huQ, _⟩ :=
          cycle_neighbor_of_Y_on_leftover (c := c) hc hU0 hdisj hp hs hedges
            hnocross hstay hstartX hfinX hvY (hY hvY) he' heP'
        exact (disjoint_left.1 (leftoverPieces_disjoint_B (B := A) p Q hQ) huQ huA)
    · rcases mem_union.1 hvAY with hvA | hvY
      · obtain ⟨Q, hQ, _, _, hvQ, _⟩ :=
          cycle_neighbor_of_Y_on_leftover (c := c) hc hU0 hdisj hp hs hedges
            hnocross hstay hstartX hfinX huY (hY huY) he heP
        exact (disjoint_left.1 (leftoverPieces_disjoint_B (B := A) p Q hQ) hvQ hvA)
      · obtain ⟨Q, hQ, _, hsU0, _, heQ⟩ :=
          cycle_neighbor_of_Y_on_leftover (c := c) hc hU0 hdisj hp hs hedges
            hnocross hstay hstartX hfinX huY (hY huY) he heP
        exact hnoYY Q hQ hsU0 u huY v hvY heQ
  exact mem_edgeSet_suppressInternal_of_not_both hadj hnot

lemma cycle_edges_mem_suppressInternal_noYY {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A) (hY : Y ⊆ U0) (hdisj : Disjoint X Y)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hnoAA : ∀ a ∈ A, ∀ hu : a ∈ c.support,
      c.succAt hu ∉ A ∧ (c.openAt hu).walk.penultimate ∉ A)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    (hnoYY : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 →
      ∀ u ∈ Y, ∀ v ∈ Y, s(u, v) ∉ Q.edges) :
    ∀ e ∈ c.edges, e ∈ (suppressInternal G (A ∪ Y)).edgeSet :=
  fun e he =>
    cycle_edge_survives_suppressInternal_noYY (c := c) hc hU0 hY hdisj hp hs
      hedges hnoAA hnocross hstay hstartX hfinX hnoYY he

lemma disjoint_A_U0 {U A U0 : Finset V} (hU0 : U0 ⊆ U \ A) : Disjoint A U0 :=
  disjoint_A_of_saving_child (U := U) (A := A) (U0 := U0) (Y := U0) hU0 subset_rfl

lemma card_path_edges (p : GraphPath G) : p.edges.card = p.walk.length := by
  have hnod := p.isPath.isTrail.edges_nodup
  simpa [GraphPath.edges, List.toFinset_card_of_nodup hnod, Walk.length_edges]

lemma card_cycle_edges (c : GraphCycle G) : c.edges.card = c.walk.length := by
  have hnod := c.isCycle.edges_nodup
  simpa [GraphCycle.edges, List.toFinset_card_of_nodup hnod, Walk.length_edges]

/-- The dropped closing edge of a spanning opening is not a path edge. -/
lemma closing_not_mem_opened_edges {p : GraphPath G} (c : GraphCycle G)
    (hp : p.support = c.support)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset) :
    s(p.finish, p.start) ∉ p.edges := by
  intro hmem
  have hEq : p.edges = c.edges := by
    have : p.edges ∪ {s(p.finish, p.start)} = p.edges :=
      union_eq_left.2 (singleton_subset_iff.2 hmem)
    simpa [this, GraphCycle.edges] using hedges
  have hlen : p.walk.length + 1 = c.walk.length := by
    have hpc := GraphPath.card_support p
    have hcc := c.card_support
    rw [← hp] at hcc
    exact hpc.symm.trans hcc
  have hlen' : p.walk.length = c.walk.length := by
    have := congrArg Finset.card hEq
    simpa [card_path_edges p, card_cycle_edges c] using this
  omega

lemma snd_mem_tail_of_not_nil {u v : V} {w : G.Walk u v} (h : ¬ w.Nil) :
    w.snd ∈ w.support.tail := by
  obtain ⟨x, hadj, rest, hwalk⟩ := Walk.not_nil_iff.1 h
  simp [hwalk]

/-- Two original `A`–seam edges of one leftover `U0`-run. -/
lemma exists_two_seams_of_U0_leftover {U A U0 : Finset V} {p Q : GraphPath G}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A) (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hQ : Q ∈ leftoverPieces A p) (hQsup : Q.support ⊆ U0) :
    ∃ e1 e2, e1 ≠ e2 ∧
      e1 ∈ c.boundaryEdges U0 ∧ e2 ∈ c.boundaryEdges U0 ∧
        (∃ x ∈ Q.support, x ∈ e1 ∧ x ∈ U0) ∧
          (∃ x ∈ Q.support, x ∈ e2 ∧ x ∈ U0) := by
  obtain ⟨ru, rv, hfact, hru, hrv⟩ := leftoverPieces_factor (B := A) p Q hQ
  have hnnRu : ¬ ru.Nil := leftoverPieces_factor_ru_not_nil hs hQ hfact
  have haA : ru.penultimate ∈ A := hru.resolve_left hnnRu
  let e1 : Sym2 V := s(ru.penultimate, Q.start)
  have he1Ru : e1 ∈ ru.edges := Walk.mk_penultimate_end_mem_edges hnnRu
  have he1P : e1 ∈ p.edges := by
    have : e1 ∈ (ru.append Q.walk).edges := mem_edges_append_left he1Ru
    exact mem_edges_iff.2 (by simpa [hfact] using mem_edges_append_left (q := rv) this)
  have hsU0 : Q.start ∈ U0 := hQsup Q.start_mem_support
  have hfU0 : Q.finish ∈ U0 := hQsup Q.finish_mem_support
  have haU0 : ru.penultimate ∉ U0 := disjoint_left.1 (disjoint_A_U0 hU0) haA
  have he1C : e1 ∈ c.edges := opened_edges_subset_cycle c hedges he1P
  have hstr1 : endsStraddle e1 U0 := endsStraddle_of_outside_inside haU0 hsU0
  have hbd1 : e1 ∈ c.boundaryEdges U0 := mem_boundaryEdges_iff.2 ⟨he1C, hstr1⟩
  by_cases hnilRv : rv.Nil
  · have hfin : Q.finish = p.finish := Walk.Nil.eq hnilRv
    let e2 : Sym2 V := s(p.finish, p.start)
    have he2C : e2 ∈ c.edges := by
      have : e2 ∈ p.edges ∪ {s(p.finish, p.start)} :=
        mem_union.2 (Or.inr (mem_singleton.2 rfl))
      simpa [hedges, GraphCycle.edges] using this
    have hbU0 : p.start ∉ U0 := disjoint_left.1 (disjoint_A_U0 hU0) hs
    have hstr2 : endsStraddle e2 U0 := by
      simpa [e2, hfin, Sym2.eq_swap] using
        (endsStraddle_of_outside_inside hbU0 hfU0)
    have hbd2 : e2 ∈ c.boundaryEdges U0 := mem_boundaryEdges_iff.2 ⟨he2C, hstr2⟩
    have hne12 : e1 ≠ e2 := by
      intro heq
      have : s(p.finish, p.start) ∈ p.edges := by simpa [← heq, e2] using he1P
      exact closing_not_mem_opened_edges c (hp.trans hc.symm) hedges this
    refine ⟨e1, e2, hne12, hbd1, hbd2,
      ⟨Q.start, Q.start_mem_support, by simp [e1], hsU0⟩,
      ⟨Q.finish, Q.finish_mem_support, by simp [e2, hfin], hfU0⟩⟩
  · have hsndA : rv.snd ∈ A := hrv.resolve_left hnilRv
    let e2 : Sym2 V := s(Q.finish, rv.snd)
    have he2Rv : e2 ∈ rv.edges := by
      obtain ⟨w, hadj, rest, hwalk⟩ := Walk.not_nil_iff.1 hnilRv
      simp [e2, hwalk, Walk.edges_cons]
    have he2P : e2 ∈ p.edges := by
      have : e2 ∈ ((ru.append Q.walk).append rv).edges :=
        mem_edges_append_right he2Rv
      exact mem_edges_iff.2 (by simpa [hfact] using this)
    have hbU0 : rv.snd ∉ U0 := disjoint_left.1 (disjoint_A_U0 hU0) hsndA
    have he2C : e2 ∈ c.edges := opened_edges_subset_cycle c hedges he2P
    have hstr2 : endsStraddle e2 U0 := by
      simpa [e2, Sym2.eq_swap] using endsStraddle_of_outside_inside hbU0 hfU0
    have hbd2 : e2 ∈ c.boundaryEdges U0 := mem_boundaryEdges_iff.2 ⟨he2C, hstr2⟩
    have hne12 : e1 ≠ e2 := by
      intro heq
      have hnod := p.isPath.isTrail.edges_nodup
      have hedgesW : p.walk.edges = (ru.append Q.walk).edges ++ rv.edges := by
        simp [hfact, Walk.edges_append]
      have hleft : e1 ∈ (ru.append Q.walk).edges := mem_edges_append_left he1Ru
      have hnod' : ((ru.append Q.walk).edges ++ rv.edges).Nodup := by
        simpa [hedgesW] using hnod
      exact hnod'.disjoint hleft (by simpa [heq] using he2Rv)
    refine ⟨e1, e2, hne12, hbd1, hbd2,
      ⟨Q.start, Q.start_mem_support, by simp [e1], hsU0⟩,
      ⟨Q.finish, Q.finish_mem_support, by simp [e2], hfU0⟩⟩

lemma ne_seams_of_disjoint_runs {U0 : Finset V} {Q R : GraphPath G}
    (c : GraphCycle G) {e e' : Sym2 V}
    (he : e ∈ c.boundaryEdges U0) (he' : e' ∈ c.boundaryEdges U0)
    {x y : V} (hx : x ∈ e ∧ x ∈ U0 ∧ x ∈ Q.support)
    (hy : y ∈ e' ∧ y ∈ U0 ∧ y ∈ R.support)
    (hdisj : Disjoint Q.support R.support) : e ≠ e' := by
  intro heq
  obtain ⟨z, hze, hzU, huniq⟩ := existsUnique_U0_end (mem_boundaryEdges_iff.1 he).2
  have hx' : x = z := huniq x hx.1 hx.2.1
  have hy' : y = z := by
    have hye : y ∈ e := by simpa [heq] using hy.1
    exact huniq y hye hy.2.1
  have hxy : x = y := hx'.trans hy'.symm
  exact Finset.disjoint_left.1 hdisj (hxy ▸ hx.2.2) hy.2.2

/-- Two leftover `U0`-runs contribute four distinct original `A`–`U0` cycle
seams, so the cycle boundary at `U0` has cardinality at least four. -/
lemma four_le_card_cycle_boundary_U0 {U A U0 : Finset V} {p : GraphPath G}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A) (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (h2 : 2 ≤ (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p)).length) :
    4 ≤ (c.boundaryEdges U0).card := by
  obtain ⟨Q, R, hQ, hR, hsQ, hsR, hneQR⟩ := exists_two_leftover_in h2
  have hQsup := hstay Q hQ hsQ
  have hRsup := hstay R hR hsR
  obtain ⟨e1, e2, h12, hb1, hb2, ⟨x1, hx1Q, hx1e, hx1U⟩, ⟨x2, hx2Q, hx2e, hx2U⟩⟩ :=
    exists_two_seams_of_U0_leftover (c := c) hc hU0 hp hs hedges hQ hQsup
  obtain ⟨e3, e4, h34, hb3, hb4, ⟨x3, hx3R, hx3e, hx3U⟩, ⟨x4, hx4R, hx4e, hx4U⟩⟩ :=
    exists_two_seams_of_U0_leftover (c := c) hc hU0 hp hs hedges hR hRsup
  have hdisjQR : Disjoint Q.support R.support :=
    PathCover.pairwise_disjoint_of_mem (leftoverPieces_pairwise (B := A) p)
      hQ hR hneQR
  have h13 : e1 ≠ e3 :=
    ne_seams_of_disjoint_runs c hb1 hb3 ⟨hx1e, hx1U, hx1Q⟩ ⟨hx3e, hx3U, hx3R⟩ hdisjQR
  have h14 : e1 ≠ e4 :=
    ne_seams_of_disjoint_runs c hb1 hb4 ⟨hx1e, hx1U, hx1Q⟩ ⟨hx4e, hx4U, hx4R⟩ hdisjQR
  have h23 : e2 ≠ e3 :=
    ne_seams_of_disjoint_runs c hb2 hb3 ⟨hx2e, hx2U, hx2Q⟩ ⟨hx3e, hx3U, hx3R⟩ hdisjQR
  have h24 : e2 ≠ e4 :=
    ne_seams_of_disjoint_runs c hb2 hb4 ⟨hx2e, hx2U, hx2Q⟩ ⟨hx4e, hx4U, hx4R⟩ hdisjQR
  have hsub : ({e1, e2, e3, e4} : Finset (Sym2 V)) ⊆ c.boundaryEdges U0 := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hb1
    · exact hb2
    · exact hb3
    · exact hb4
  have hcard : ({e1, e2, e3, e4} : Finset (Sym2 V)).card = 4 := by
    repeat' rw [card_insert_of_notMem]
    · simp
    · simp [h34]
    · simp [h23, h24, h34]
    · simp [h12, h13, h14, h23, h24]
  have := card_le_card hsub
  omega

lemma completeJoin_adj_suppressInternal {U A U0 X Y : Finset V}
    (hU0 : U0 ⊆ U \ A) (hX : X ⊆ U0) (hdisj : Disjoint X Y)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    {y x : V} (hy : y ∈ Y) (hx : x ∈ X) :
    (suppressInternal G (A ∪ Y)).Adj y x :=
  (adj_suppressInternal_iff (G := G) (A' := A ∪ Y)).2
    ⟨(hjoin hx hy).symm, fun hboth => (not_mem_AunionY_of_mem_X hU0 hX hdisj hx) hboth.2⟩

lemma boundary_outside_end_mem_A {U A U0 : Finset V}
    (c : GraphCycle G) (hc : c.support = U) (hU0 : U0 ⊆ U \ A)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    {e : Sym2 V} (he : e ∈ c.boundaryEdges U0) :
    ∃ a ∈ A, a ∈ e := by
  obtain ⟨heC, hstr⟩ := mem_boundaryEdges_iff.1 he
  obtain ⟨x, hxe, hxU, huniq⟩ := existsUnique_U0_end hstr
  refine Sym2.inductionOn e (fun u v heC hstr hxe hxU huniq => ?_) heC hstr hxe hxU huniq
  have hadj : G.Adj u v := by
    simpa [SimpleGraph.mem_edgeSet] using
      c.walk.edges_subset_edgeSet (mem_edges_iff.1 heC)
  have huC : u ∈ c.support := cycle_mem_support_of_mem_edge c heC (by simp)
  have hvC : v ∈ c.support := cycle_mem_support_of_mem_edge c heC (by simp)
  rcases (show u = x ∨ v = x from by
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl) with rfl | rfl
  · have hvU : v ∉ U0 := fun hvU => (endsStraddle_iff.1 hstr)
      (propext ⟨fun _ => hvU, fun _ => hxU⟩)
    have hvUset : v ∈ U := by simpa [hc] using hvC
    by_cases hvA : v ∈ A
    · exact ⟨v, hvA, by simp⟩
    · have hvK : v ∈ (U \ A) \ U0 := mem_sdiff.2 ⟨mem_sdiff.2 ⟨hvUset, hvA⟩, hvU⟩
      exact (hnocross u hxU v hvK hadj).elim
  · have huU : u ∉ U0 := fun huU => (endsStraddle_iff.1 hstr)
      (propext ⟨fun _ => hxU, fun _ => huU⟩)
    have huUset : u ∈ U := by simpa [hc] using huC
    by_cases huA : u ∈ A
    · exact ⟨u, huA, by simp⟩
    · have huK : u ∈ (U \ A) \ U0 := mem_sdiff.2 ⟨mem_sdiff.2 ⟨huUset, huA⟩, huU⟩
      exact (hnocross v hxU u huK hadj.symm).elim

set_option maxHeartbeats 4000000

/-- A `G'`-path protected at original `A`, starting in `Y`, retains at
least three of the four original `U0` cycle seams as path boundary edges. -/
lemma three_le_path_boundary_of_start_Y {U A U0 Y : Finset V}
    {G' : SimpleGraph V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hU0 : U0 ⊆ U \ A) (hY : Y ⊆ U0)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hdisjAY : Disjoint A Y)
    {p' : GraphPath G'} {c' : GraphCycle G'}
    (hp' : p'.support = U) (hc' : c'.support = U)
    (hP : p'.ProtectedAt c' A) (hedges' : c'.edges = c.edges)
    (hsY : p'.start ∈ Y)
    (h4 : 4 ≤ (c.boundaryEdges U0).card) :
    3 ≤ (p'.boundaryEdges U0).card := by
  let S := c.boundaryEdges U0
  change 4 ≤ S.card at h4
  have hSsub : S ∩ p'.edges ⊆ p'.boundaryEdges U0 := by
    intro e he
    have ⟨heS, heP⟩ := mem_inter.1 he
    exact GraphPath.mem_boundaryEdges_iff.2
      ⟨heP, ((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).2⟩
  have hmiss : (S \ p'.edges).card ≤ 1 := by
    by_cases hfA : p'.finish ∈ A
    · have hfP : p'.finish ∈ p'.support := p'.finish_mem_support
      have hfC : p'.finish ∈ c'.support := by simpa [hc', hp'] using hfP
      have h2c : (c'.incidentEdges p'.finish).card = 2 := c'.incidentEdges_card hfC
      have h3 : 3 ≤ p'.support.card := by simpa [hp', hc] using c.three_le_card_support
      have h2 : 2 ≤ p'.support.card := le_trans (by decide : (2 : ℕ) ≤ 3) h3
      have h1p : (p'.incidentEdges p'.finish).card = 1 :=
        p'.incidentEdges_card_finish h2
      have hsubI : p'.incidentEdges p'.finish ⊆ c'.incidentEdges p'.finish :=
        hP.incidentEdges_subset_cycle hfA
      have hmissF :
          (c'.incidentEdges p'.finish \ p'.incidentEdges p'.finish).card ≤ 1 := by
        have : (p'.incidentEdges p'.finish ∪
            (c'.incidentEdges p'.finish \ p'.incidentEdges p'.finish)).card =
            (c'.incidentEdges p'.finish).card := by
          rw [union_sdiff_of_subset hsubI]
        have hdisj :
            Disjoint (p'.incidentEdges p'.finish)
              (c'.incidentEdges p'.finish \ p'.incidentEdges p'.finish) :=
          disjoint_sdiff
        have := card_union_of_disjoint hdisj
        omega
      have hsubMiss : S \ p'.edges ⊆
          c'.incidentEdges p'.finish \ p'.incidentEdges p'.finish := by
        intro e he
        have ⟨heS, hneP⟩ := mem_sdiff.1 he
        obtain ⟨a, haA, hae⟩ :=
          boundary_outside_end_mem_A (c := c) hc hU0 hnocross heS
        have haP : a ∈ p'.support := by simpa [hp'] using hA haA
        have hsA : a ≠ p'.start := fun h =>
          (disjoint_left.1 hdisjAY (h ▸ haA) hsY)
        have haFin : a = p'.finish := by
          by_contra hne
          have heqI :=
            incidentEdges_eq_cycle_of_internal_protected p' c' (hp'.trans hc'.symm)
              (fun x hx => by simpa [hp'] using hA hx) hP haA hsA hne
          have heC' : e ∈ c'.incidentEdges a := by
            have heC : e ∈ c.edges := ((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).1
            exact (GraphCycle.mem_incidentEdges_iff (c := c') (v := a)).2 ⟨by simpa [hedges'] using heC, hae⟩
          have : e ∈ p'.incidentEdges a := by simpa [heqI] using heC'
          exact hneP (GraphPath.mem_incidentEdges_iff.1 this).1
        have heC' : e ∈ c'.incidentEdges p'.finish := by
          have heC : e ∈ c.edges := ((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).1
          exact (GraphCycle.mem_incidentEdges_iff (c := c') (v := p'.finish)).2
            ⟨by rw [hedges']; exact heC, by simpa [haFin] using hae⟩
        have hnotP : e ∉ p'.incidentEdges p'.finish := fun hin =>
          hneP (GraphPath.mem_incidentEdges_iff.1 hin).1
        exact mem_sdiff.2 ⟨heC', hnotP⟩
      exact (card_le_card hsubMiss).trans hmissF
    · have hnone : S \ p'.edges = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        obtain ⟨heS, hneP⟩ := Finset.mem_sdiff.1 he
        obtain ⟨a, haA, hae⟩ :=
          boundary_outside_end_mem_A (c := c) hc hU0 hnocross heS
        have hsA : a ≠ p'.start := fun h =>
          (disjoint_left.1 hdisjAY (h ▸ haA) hsY)
        have hfA' : a ≠ p'.finish := fun h => hfA (by simpa [h] using haA)
        have heqI :=
          incidentEdges_eq_cycle_of_internal_protected p' c' (hp'.trans hc'.symm)
            (fun x hx => by simpa [hp'] using hA hx) hP haA hsA hfA'
        have heC' : e ∈ c'.incidentEdges a :=
          (GraphCycle.mem_incidentEdges_iff (c := c') (v := a)).2
            ⟨by simpa [hedges'] using ((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).1, hae⟩
        have : e ∈ p'.incidentEdges a := by simpa [heqI] using heC'
        exact hneP (GraphPath.mem_incidentEdges_iff.1 this).1
      simp [hnone]
  have hinter : 3 ≤ (S ∩ p'.edges).card := by
    have hd : Disjoint (S ∩ p'.edges) (S \ p'.edges) := by
      apply Finset.disjoint_left.2
      intro e heI heD
      exact (Finset.mem_sdiff.1 heD).2 (Finset.mem_inter.1 heI).2
    have hdecomp : S = (S ∩ p'.edges) ∪ (S \ p'.edges) := by
      ext e
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hcard := congrArg Finset.card hdecomp
    rw [Finset.card_union_of_disjoint hd] at hcard
    omega
  exact le_trans hinter (card_le_card hSsub)

end Cograph
end Nikoghosyan
