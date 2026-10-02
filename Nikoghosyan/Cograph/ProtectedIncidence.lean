/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.PathRotation
import Nikoghosyan.CycleSwitches
import Nikoghosyan.Cograph.CycleProfileSegments

/-!
# Extensional A-incidence protection and complement-edge bookkeeping

Manuscript `prof:thm:protected`, incidence layer.

Protection is `GraphPath.ProtectedAt`: every path edge that meets `A` is an
edge of the prescribed original cycle. Exact retained 2/1 counts then follow
from path degrees and the two cycle darts at a cycle vertex.

This module exports the complementary leftover arc with `r.edges ⊆ c.edges`
and original seam membership, and the exact leftover-run count when the
opened path has no consecutive `A`–`A` edge.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Both ends of an undirected edge lie in `B`. -/
def bothEndsIn (e : Sym2 V) (B : Finset V) : Prop :=
  ∀ x ∈ e, x ∈ B

lemma bothEndsIn_iff {u v : V} {B : Finset V} :
    bothEndsIn s(u, v) B ↔ u ∈ B ∧ v ∈ B := by
  constructor
  · intro h
    exact ⟨h u (by simp), h v (by simp)⟩
  · intro ⟨hu, hv⟩ x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hu
    · exact hv

/-- No original path edge has both ends in `B`. -/
def NoConsecutive (B : Finset V) (p : GraphPath G) : Prop :=
  ∀ e ∈ p.edges, ¬ bothEndsIn e B

lemma edges_trimStart_subset (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).edges ⊆ p.edges := by
  intro e he
  exact mem_edges_iff.2
    ((isSubwalk_trimStart p h).edges_subset (mem_edges_iff.1 he))

lemma edges_trimFinish_subset (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimFinish h).edges ⊆ p.edges := by
  intro e he
  exact mem_edges_iff.2
    ((isSubwalk_trimFinish p h).edges_subset (mem_edges_iff.1 he))

lemma edges_dropUntil_subset (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.dropUntil hx).edges ⊆ p.edges := by
  intro e he
  exact mem_edges_iff.2
    ((Walk.isSubwalk_dropUntil p.walk (mem_walk_support.1 hx)).edges_subset
      (mem_edges_iff.1 he))

lemma NoConsecutive_of_edges_subset {B : Finset V} {p q : GraphPath G}
    (hsub : q.edges ⊆ p.edges) (hno : NoConsecutive B p) :
    NoConsecutive B q :=
  fun e he => hno e (hsub he)

lemma first_edge_mem (p : GraphPath G) (h : ¬ p.walk.Nil) :
    s(p.start, p.walk.snd) ∈ p.edges := by
  obtain ⟨w, hadj, q, hwalk⟩ := Walk.not_nil_iff.1 h
  rw [mem_edges_iff, hwalk, Walk.edges_cons, Walk.snd_cons]
  exact List.mem_cons_self

lemma snd_not_mem_of_NoConsecutive {B : Finset V} {p : GraphPath G}
    (h : ¬ p.walk.Nil) (hs : p.start ∈ B) (hno : NoConsecutive B p) :
    p.walk.snd ∉ B := by
  intro hsnd
  exact hno _ (first_edge_mem p h) (bothEndsIn_iff.2 ⟨hs, hsnd⟩)

lemma edges_concatAdj {x : V} (p : GraphPath G) (h : G.Adj p.finish x)
    (hx : x ∉ p.support) :
    (p.concatAdj h hx).edges = p.edges ∪ {s(p.finish, x)} := by
  ext e
  simp [edges, concatAdj, Walk.edges_concat, List.concat_eq_append]

lemma edges_consAdj {x : V} (p : GraphPath G) (h : G.Adj x p.start)
    (hx : x ∉ p.support) :
    (p.consAdj h hx).edges = p.edges ∪ {s(x, p.start)} := by
  ext e
  simp [edges, consAdj, Walk.edges_cons]

lemma edges_splice (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) :
    (p.splice q h hd).edges = p.edges ∪ q.edges ∪ {s(p.finish, q.start)} := by
  ext e
  simp [edges, splice, Walk.edges_append, Walk.edges_cons]

lemma leftover_edges_subset {B : Finset V} (p : GraphPath G) {Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces B p) : Q.edges ⊆ p.edges := by
  intro e he
  exact mem_edges_iff.2
    ((leftoverPieces_isSubwalk p Q hQ).edges_subset (mem_edges_iff.1 he))

lemma last_edge_mem_ofWalk {u v : V} (w : G.Walk u v) (hw : w.IsPath)
    (h : ¬ w.Nil) :
    s((ofWalk w hw).trimFinish h |>.finish, v) ∈ (ofWalk w hw).edges := by
  have : s(w.penultimate, v) ∈ w.edges :=
    Walk.mk_penultimate_end_mem_edges h
  simpa [edges, ofWalk, trimFinish] using List.mem_toFinset.2 this

lemma mem_edges_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    {e : Sym2 V} (he : e ∈ p.edges) : e ∈ (p.append q).edges := by
  rw [Walk.edges_append, List.mem_append]
  exact Or.inl he

lemma mem_edges_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    {e : Sym2 V} (he : e ∈ q.edges) : e ∈ (p.append q).edges := by
  rw [Walk.edges_append, List.mem_append]
  exact Or.inr he

/-- Complement of a leftover run, with exported original-edge subset of the
opened path plus its closing edge, and both seams among those edges. -/
lemma exists_complement_of_leftover_edges {A : Finset V} {p Q : GraphPath G}
    (hs : p.start ∈ A) (hQ : Q ∈ leftoverPieces A p)
    (hclose : G.Adj p.finish p.start) :
    ∃ r : GraphPath G,
      r.support = p.support \ Q.support ∧
        r.start ∈ A ∧ r.finish ∈ A ∧
          G.Adj r.finish Q.start ∧ G.Adj Q.finish r.start ∧
            r.edges ⊆ p.edges ∪ {s(p.finish, p.start)} ∧
              s(r.finish, Q.start) ∈ p.edges ∪ {s(p.finish, p.start)} ∧
                s(Q.finish, r.start) ∈ p.edges ∪ {s(p.finish, p.start)} := by
  obtain ⟨ru, rv, heq, hruB, hrvB⟩ := leftoverPieces_factor (B := A) p Q hQ
  have hru : ¬ ru.Nil := leftoverPieces_factor_ru_not_nil hs hQ heq
  have hpreA : ru.penultimate ∈ A := hruB.resolve_left hru
  let prefixR := (ofWalk ru (isPath_of_factor_left heq)).trimFinish hru
  have hpreStart : prefixR.start = p.start := rfl
  have hpreFin : prefixR.finish = ru.penultimate := rfl
  have hadjPre : G.Adj prefixR.finish Q.start := ru.adj_penultimate hru
  have hruE : ru.edges.toFinset ⊆ p.edges := by
    intro e he
    apply mem_edges_iff.2
    rw [heq]
    exact mem_edges_append_left (mem_edges_append_left (List.mem_toFinset.1 he))
  have hpreE : prefixR.edges ⊆ p.edges :=
    (edges_trimFinish_subset (ofWalk ru (isPath_of_factor_left heq)) hru).trans
      (by change ru.edges.toFinset ⊆ p.edges; exact hruE)
  have hlast : s(prefixR.finish, Q.start) ∈ p.edges :=
    hruE (last_edge_mem_ofWalk ru (isPath_of_factor_left heq) hru)
  have hsd := sdiff_eq_prefix_suffix heq
  by_cases hrv : rv.Nil
  · refine ⟨prefixR, ?_, ?_, ?_, hadjPre, ?_, ?_, ?_, ?_⟩
    · have hf : Q.finish = p.finish := Walk.Nil.eq hrv
      have hR : rv.support.toFinset.erase Q.finish = ∅ := by
        simpa [hf] using erase_eq_empty_of_nil hrv
      have hsd' : p.support \ Q.support = ru.support.toFinset.erase Q.start := by
        rw [hsd, hR, union_empty]
      rw [support_trimFinish_ofWalk heq hru]
      exact hsd'.symm
    · exact hpreStart ▸ hs
    · exact hpreFin ▸ hpreA
    · have hf : Q.finish = p.finish := Walk.Nil.eq hrv
      rw [hpreStart, hf]
      exact hclose
    · exact hpreE.trans subset_union_left
    · exact mem_union.2 (Or.inl hlast)
    · have hf : Q.finish = p.finish := Walk.Nil.eq hrv
      rw [hpreStart, hf]
      exact mem_union.2 (Or.inr (mem_singleton.2 rfl))
  · have hsucA : rv.snd ∈ A := hrvB.resolve_left hrv
    let suffixR := (ofWalk rv (isPath_of_factor_right heq)).trimStart hrv
    have hsufStart : suffixR.start = rv.snd := rfl
    have hsufFin : suffixR.finish = p.finish := rfl
    have hdisj : Disjoint suffixR.support prefixR.support := by
      dsimp [suffixR, prefixR]
      exact (disjoint_trim_prefix_suffix heq hru hrv).symm
    have hclose' : G.Adj suffixR.finish prefixR.start := by
      rw [hsufFin, hpreStart]
      exact hclose
    have hrvE : rv.edges.toFinset ⊆ p.edges := by
      intro e he
      apply mem_edges_iff.2
      rw [heq]
      exact mem_edges_append_right (List.mem_toFinset.1 he)
    have hsufE : suffixR.edges ⊆ p.edges :=
      (edges_trimStart_subset (ofWalk rv (isPath_of_factor_right heq)) hrv).trans
        (by change rv.edges.toFinset ⊆ p.edges; exact hrvE)
    have hfirst : s(Q.finish, suffixR.start) ∈ p.edges := by
      have hf0 := first_edge_mem (ofWalk rv (isPath_of_factor_right heq)) hrv
      have : s(Q.finish, rv.snd) ∈ rv.edges.toFinset := by
        simpa [edges, ofWalk] using hf0
      exact hrvE (by simpa [hsufStart] using this)
    let r := suffixR.splice prefixR hclose' hdisj
    have hrStart : r.start = suffixR.start := rfl
    have hrFin : r.finish = prefixR.finish := rfl
    refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hsup : r.support = suffixR.support ∪ prefixR.support :=
        support_splice suffixR prefixR hclose' hdisj
      rw [hsup, support_trimStart_ofWalk heq hrv,
        support_trimFinish_ofWalk heq hru, union_comm]
      exact hsd.symm
    · exact hrStart ▸ (hsufStart ▸ hsucA)
    · exact hrFin ▸ (hpreFin ▸ hpreA)
    · rw [hrFin]
      exact hadjPre
    · rw [hrStart, hsufStart]
      exact rv.adj_snd hrv
    · intro e he
      have he' : e ∈ suffixR.edges ∪ prefixR.edges ∪ {s(suffixR.finish, prefixR.start)} := by
        simpa [r, edges_splice] using he
      rcases mem_union.1 he' with h | hs0
      · rcases mem_union.1 h with h | h
        · exact mem_union.2 (Or.inl (hsufE h))
        · exact mem_union.2 (Or.inl (hpreE h))
      · have : e = s(suffixR.finish, prefixR.start) := mem_singleton.1 hs0
        rw [this, hsufFin, hpreStart]
        exact mem_union.2 (Or.inr (mem_singleton.2 rfl))
    · rw [hrFin]
      exact mem_union.2 (Or.inl hlast)
    · rw [hrStart]
      exact mem_union.2 (Or.inl hfirst)

/-- Exact leftover-run count when the path starts in `B`, finishes outside
`B`, and has no consecutive `B`–`B` edge. No independence of `B` in `G`. -/
lemma leftoverPieces_length_eq_of_start_mem_finish_not {B : Finset V}
    {p : GraphPath G} (hs : p.start ∈ B) (hf : p.finish ∉ B)
    (hno : NoConsecutive B p) :
    (leftoverPieces B p).length = (p.support ∩ B).card := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        p.start ∈ B → p.finish ∉ B → NoConsecutive B p →
          (leftoverPieces B p).length = (p.support ∩ B).card)
    p.support.card ?_ p rfl hs hf hno
  intro n ih p hn hs' hf' hno'
  have hnil : ¬ p.walk.Nil := by
    intro h
    have : p.finish = p.start := ((nil_iff_start_eq_finish p).1 h).symm
    exact hf' (this ▸ hs')
  rw [leftoverPieces_of_start_mem_cons hs' hnil]
  have hsT : (p.trimStart hnil).start ∉ B := by
    simpa [trimStart] using snd_not_mem_of_NoConsecutive hnil hs' hno'
  have hnoT : NoConsecutive B (p.trimStart hnil) :=
    NoConsecutive_of_edges_subset (edges_trimStart_subset p hnil) hno'
  have hps : p.support = insert p.start (p.trimStart hnil).support := by
    rw [support_trimStart, insert_erase p.start_mem_support]
  have hstart_not : p.start ∉ (p.trimStart hnil).support := by
    rw [support_trimStart]; exact notMem_erase _ _
  have hcard : (p.support ∩ B).card =
      ((p.trimStart hnil).support ∩ B).card + 1 := by
    rw [hps, insert_inter_of_mem hs', card_insert_of_notMem]
    exact fun hz => hstart_not (mem_inter.1 hz).1
  cases hfind :
    (p.trimStart hnil).walk.support.find? (fun x => decide (x ∈ B)) with
  | none =>
    have hlist : leftoverPieces B (p.trimStart hnil) = [p.trimStart hnil] :=
      leftoverPieces_of_not_mem_start_none hsT hfind
    have hemp : (p.trimStart hnil).support ∩ B = ∅ := by
      ext y
      constructor
      · intro hy
        have hyW : y ∈ (p.trimStart hnil).walk.support :=
          (mem_walk_support (p := p.trimStart hnil)).1 (mem_inter.1 hy).1
        have hnot : ¬ decide (y ∈ B) :=
          (List.find?_eq_none
            (p := fun x : V => decide (x ∈ B))).1 hfind y hyW
        exact (hnot (decide_eq_true (mem_inter.1 hy).2)).elim
      · intro hy
        exact (notMem_empty y hy).elim
    simp [hlist, hcard, hemp]
  | some _ =>
    have hnone :
        (p.trimStart hnil).walk.support.find?
          (fun x => decide (x ∈ B)) ≠ none := by
      simp [hfind]
    rw [leftoverPieces.eq_def]
    simp only [hsT, hnone, dite_false]
    have hfind' := firstB_spec (B := B) (p := p.trimStart hnil) hnone
    have hx : firstB B (p.trimStart hnil) hnone ∈ (p.trimStart hnil).support :=
      (mem_find?_B (B := B) hfind').1
    have hbB : firstB B (p.trimStart hnil) hnone ∈ B :=
      (mem_find?_B (B := B) hfind').2
    have hne : firstB B (p.trimStart hnil) hnone ≠ (p.trimStart hnil).start :=
      find?_B_ne_start hsT hfind'
    have hlt :
        (p.trimStart hnil).support.card < n := by
      simpa [hn, support_trimStart] using
        card_erase_lt_of_mem p.start_mem_support
    have hltD :
        ((p.trimStart hnil).dropUntil hx).support.card <
          (p.trimStart hnil).support.card :=
      dropUntil_support_card_lt (p.trimStart hnil) hx hne
    have hltD' : ((p.trimStart hnil).dropUntil hx).support.card < n :=
      lt_trans hltD hlt
    have hstartD : ((p.trimStart hnil).dropUntil hx).start ∈ B := by
      simpa [dropUntil] using hbB
    have hfinD : ((p.trimStart hnil).dropUntil hx).finish ∉ B := hf'
    have hnoD : NoConsecutive B ((p.trimStart hnil).dropUntil hx) :=
      NoConsecutive_of_edges_subset
        (edges_dropUntil_subset (p.trimStart hnil) hx) hnoT
    have ihD :=
      ih _ hltD' ((p.trimStart hnil).dropUntil hx) rfl hstartD hfinD hnoD
    have htakeB :
        ((p.trimStart hnil).takeUntil hx).support ∩ B =
          {firstB B (p.trimStart hnil) hnone} := by
      ext y
      constructor
      · intro hy
        have hy1 := (mem_inter.1 hy).1
        have hy2 := (mem_inter.1 hy).2
        by_cases hEq : y = firstB B (p.trimStart hnil) hnone
        · simp [hEq]
        · exact (takeUntil_ne_first_not_mem_B hfind' hx hy1 hEq hy2).elim
      · intro hy
        have : y = firstB B (p.trimStart hnil) hnone := mem_singleton.1 hy
        subst this
        exact mem_inter.2 ⟨((p.trimStart hnil).takeUntil hx).finish_mem_support, hbB⟩
    have hunion :=
      support_takeUntil_union_dropUntil (p.trimStart hnil) hx
    have hTD :
        (p.trimStart hnil).support ∩ B =
          ((p.trimStart hnil).dropUntil hx).support ∩ B := by
      have h1 :
          (p.trimStart hnil).support ∩ B =
            (((p.trimStart hnil).takeUntil hx).support ∪
              ((p.trimStart hnil).dropUntil hx).support) ∩ B := by
        rw [hunion]
      rw [h1, union_inter_distrib_right, htakeB, singleton_union]
      ext y
      constructor
      · intro hy
        rcases mem_insert.1 hy with rfl | hy'
        · exact mem_inter.2 ⟨((p.trimStart hnil).dropUntil hx).start_mem_support, hbB⟩
        · exact hy'
      · intro hy
        exact mem_insert.2 (Or.inr hy)
    simp [List.length_cons, ihD, hcard, hTD]

end GraphPath

namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Opened-cycle leftover cover has cardinality `|A|` when the opened path
starts in `A`, finishes outside `A`, and has no consecutive `A`–`A` edge. -/
lemma exists_cycle_leftover_card_eq {U A : Finset V}
    (c : GraphCycle G) (_hc : c.support = U)
    (hA : A ⊆ U) (_hAne : A.Nonempty)
    {p : GraphPath G}
    (hp : p.support = U) (hs : p.start ∈ A) (hf : p.finish ∉ A)
    (hno : NoConsecutive A p) :
    ∃ pc : PathCover G (U \ A),
      pc.card = A.card ∧ pc.paths = leftoverPieces A p ∧
        ∀ Q ∈ pc.paths, Q.walk.IsSubwalk p.walk := by
  have hAU : A ⊆ p.support := by simpa [hp] using hA
  have hinter : p.support ∩ A = A := inter_eq_right.2 hAU
  have hlen := leftoverPieces_length_eq_of_start_mem_finish_not hs hf hno
  let pc0 := leftoverCoverOfPath p A
  have hEq : p.support \ A = U \ A := by rw [hp]
  refine ⟨pc0.cast hEq, ?_, ?_, ?_⟩
  · have : pc0.card = A.card := by
      rw [leftoverCoverOfPath_card, hlen, hinter]
    simpa [PathCover.cast_card] using this
  · rw [PathCover.cast_paths, leftoverCoverOfPath_paths]
  · intro Q hQ
    have hQ' : Q ∈ leftoverPieces A p := by
      rwa [PathCover.cast_paths, leftoverCoverOfPath_paths] at hQ
    exact leftoverPieces_isSubwalk p Q hQ'

end Cograph
end Nikoghosyan
