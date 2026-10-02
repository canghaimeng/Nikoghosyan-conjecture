/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.PathBlockInsertion

/-!
Exact complement-edge retention of a contiguous original subwalk.

Given an actual original path `p` closed by an original edge from finish
to start, and an actual contiguous original subwalk `Q` of `p` supplied
by an `OriginalSubwalkFactor`, construct the complementary original path
`r` that omits `Q`. The vertex support of `r` equals `p.support`
without `Q.support`, including nil suffix and singleton complement.
The undirected edge finset of `r` equals the closed
path-plus-closing finset filtered to edges with both ends outside
`Q.support`.

A subset of a prescribed cycle cannot prove that a chosen old edge
survives in the complement. The exact identity does: if `R` is another
original run with support disjoint from `Q` and with `R.edges ⊆ p.edges`,
every edge of `R` belongs to `r.edges` and therefore admits an actual
directed factor of `r`.

Nil suffix is handled: the successor seam is then the closing edge.
The prefix is required to be non-nil. This module does not import
leftover-piece membership from the cograph stack and does not close
`prof:thm:protected` or `thm:main`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

/-- Both ends of an undirected edge lie outside `S`. -/
def bothEndsOutside (e : Sym2 V) (S : Finset V) : Prop :=
  ∀ x ∈ e, x ∉ S

lemma bothEndsOutside_iff {a b : V} {S : Finset V} :
    bothEndsOutside s(a, b) S ↔ a ∉ S ∧ b ∉ S := by
  constructor
  · intro h
    exact ⟨h a (by simp), h b (by simp)⟩
  · intro ⟨ha, hb⟩ x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact ha
    · exact hb

lemma bothEndsOutside_of_support {p : GraphPath G} {S : Finset V} {e : Sym2 V}
    (he : e ∈ p.edges) (hd : Disjoint p.support S) :
    bothEndsOutside e S := by
  intro x hx
  exact disjoint_left.1 hd (mem_support_of_mem_edge he hx)

lemma not_bothEndsOutside_of_mem_edges {Q : GraphPath G} {e : Sym2 V}
    (he : e ∈ Q.edges) : ¬ bothEndsOutside e Q.support := by
  intro h
  refine Sym2.inductionOn e (fun a b he h => ?_) he h
  exact h a (by simp) (mem_support_of_mem_edge he (by simp))

/-- Genuine contiguous original-subwalk factorization of `Q` inside `p`. -/
structure OriginalSubwalkFactor (p Q : GraphPath G) where
  preWalk : G.Walk p.start Q.start
  sufWalk : G.Walk Q.finish p.finish
  factor : p.walk = (preWalk.append Q.walk).append sufWalk

namespace OriginalSubwalkFactor

variable {p Q : GraphPath G}

lemma mid_isPath (F : OriginalSubwalkFactor p Q) :
    (F.preWalk.append Q.walk).IsPath :=
  Walk.IsPath.of_append_left (by simpa [F.factor] using p.isPath)

lemma preWalk_isPath (F : OriginalSubwalkFactor p Q) : F.preWalk.IsPath :=
  Walk.IsPath.of_append_left F.mid_isPath

lemma sufWalk_isPath (F : OriginalSubwalkFactor p Q) : F.sufWalk.IsPath :=
  Walk.IsPath.of_append_right (by simpa [F.factor] using p.isPath)

lemma support_cat (F : OriginalSubwalkFactor p Q) :
    p.walk.support =
      F.preWalk.support ++ Q.walk.support.tail ++ F.sufWalk.support.tail := by
  rw [F.factor, Walk.support_append, Walk.support_append]

lemma edges_cat (F : OriginalSubwalkFactor p Q) :
    p.walk.edges = F.preWalk.edges ++ Q.walk.edges ++ F.sufWalk.edges := by
  rw [F.factor, Walk.edges_append, Walk.edges_append]

lemma edges_union (F : OriginalSubwalkFactor p Q) :
    p.edges =
      F.preWalk.edges.toFinset ∪ Q.edges ∪ F.sufWalk.edges.toFinset := by
  simp [edges, F.edges_cat, List.toFinset_append]

lemma pre_not_nil_of_start_not_mem (F : OriginalSubwalkFactor p Q)
    (h : p.start ∉ Q.support) : ¬ F.preWalk.Nil := by
  intro hnil
  have heq : p.start = Q.start := Walk.Nil.eq hnil
  exact h (heq ▸ Q.start_mem_support)

/-- Rebuild a simple original path from an already-simple walk. Named
to avoid colliding with G2 `ofWalk`. -/
def pathOfWalk {u v : V} (w : G.Walk u v) (hw : w.IsPath) : GraphPath G where
  start := u
  finish := v
  walk := w
  isPath := hw

def prefixTrim (F : OriginalSubwalkFactor p Q) (hpre : ¬ F.preWalk.Nil) :
    GraphPath G :=
  (pathOfWalk F.preWalk F.preWalk_isPath).trimFinish hpre

lemma prefixTrim_start (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) : (F.prefixTrim hpre).start = p.start :=
  rfl

lemma prefixTrim_finish (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) :
    (F.prefixTrim hpre).finish = F.preWalk.penultimate :=
  rfl

lemma prefixTrim_adj (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) :
    G.Adj (F.prefixTrim hpre).finish Q.start :=
  F.preWalk.adj_penultimate hpre

lemma support_prefixTrim (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) :
    (F.prefixTrim hpre).support = F.preWalk.support.toFinset.erase Q.start :=
  support_trimFinish (pathOfWalk F.preWalk F.preWalk_isPath) hpre

def suffixTrim (F : OriginalSubwalkFactor p Q) (hsuf : ¬ F.sufWalk.Nil) :
    GraphPath G :=
  (pathOfWalk F.sufWalk F.sufWalk_isPath).trimStart hsuf

lemma suffixTrim_start (F : OriginalSubwalkFactor p Q)
    (hsuf : ¬ F.sufWalk.Nil) :
    (F.suffixTrim hsuf).start = F.sufWalk.snd :=
  rfl

lemma suffixTrim_finish (F : OriginalSubwalkFactor p Q)
    (hsuf : ¬ F.sufWalk.Nil) :
    (F.suffixTrim hsuf).finish = p.finish :=
  rfl

lemma suffixTrim_adj (F : OriginalSubwalkFactor p Q)
    (hsuf : ¬ F.sufWalk.Nil) :
    G.Adj Q.finish (F.suffixTrim hsuf).start :=
  F.sufWalk.adj_snd hsuf

lemma support_suffixTrim (F : OriginalSubwalkFactor p Q)
    (hsuf : ¬ F.sufWalk.Nil) :
    (F.suffixTrim hsuf).support = F.sufWalk.support.toFinset.erase Q.finish :=
  support_trimStart (pathOfWalk F.sufWalk F.sufWalk_isPath) hsuf

lemma support_cons_not_nil {u v : V} {w : G.Walk u v} (h : ¬ w.Nil) :
    w.support = u :: w.support.tail := by
  have ht := Walk.support_tail_of_not_nil w h
  simpa [ht] using (Walk.cons_support_tail (p := w) h).symm

lemma disjoint_prefixTrim_suffixTrim (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hsuf : ¬ F.sufWalk.Nil) :
    Disjoint (F.prefixTrim hpre).support (F.suffixTrim hsuf).support := by
  refine disjoint_left.2 ?_
  intro x hxP hxS
  have hxpre : x ∈ F.preWalk.support := by
    have : x ∈ F.preWalk.support.toFinset.erase Q.start := by
      simpa [F.support_prefixTrim hpre] using hxP
    exact List.mem_toFinset.1 (mem_erase.1 this).2
  have hxneS : x ≠ Q.start := by
    have : x ∈ F.preWalk.support.toFinset.erase Q.start := by
      simpa [F.support_prefixTrim hpre] using hxP
    exact (mem_erase.1 this).1
  have hxsuf : x ∈ F.sufWalk.support := by
    have : x ∈ F.sufWalk.support.toFinset.erase Q.finish := by
      simpa [F.support_suffixTrim hsuf] using hxS
    exact List.mem_toFinset.1 (mem_erase.1 this).2
  have hxneF : x ≠ Q.finish := by
    have : x ∈ F.sufWalk.support.toFinset.erase Q.finish := by
      simpa [F.support_suffixTrim hsuf] using hxS
    exact (mem_erase.1 this).1
  have hcons := support_cons_not_nil (w := F.sufWalk) hsuf
  have htail : x ∈ F.sufWalk.support.tail :=
    (List.mem_cons.1 (by rw [hcons] at hxsuf; exact hxsuf)).resolve_left hxneF
  have hcat := F.support_cat
  have hxG : x ∈ p.walk.support := by
    rw [hcat]
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hxpre)))
  have hcnt : 2 ≤ p.walk.support.count x := by
    have h1 : 1 ≤ F.preWalk.support.count x := List.count_pos_iff.mpr hxpre
    have h2 : 1 ≤ F.sufWalk.support.tail.count x := List.count_pos_iff.mpr htail
    rw [hcat, List.count_append, List.count_append]
    omega
  have : p.walk.support.count x = 1 :=
    List.count_eq_one_of_mem p.support_nodup hxG
  omega

/-- Complementary original path omitting the contiguous block `Q`.
Nil suffix uses the closing edge as the successor seam. -/
noncomputable def omitRunComplement (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) : GraphPath G :=
  if hsuf : F.sufWalk.Nil then
    F.prefixTrim hpre
  else
    (F.suffixTrim hsuf).splice (F.prefixTrim hpre)
      (by simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose)
      (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm

lemma omitRunComplement_eq_prefix_of_nil (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    (hsuf : F.sufWalk.Nil) :
    F.omitRunComplement hpre hclose = F.prefixTrim hpre := by
  simp [omitRunComplement, hsuf]

lemma omitRunComplement_eq_splice_of_not_nil (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    (hsuf : ¬ F.sufWalk.Nil) :
    F.omitRunComplement hpre hclose =
      (F.suffixTrim hsuf).splice (F.prefixTrim hpre)
        (by simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose)
        (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm := by
  simp [omitRunComplement, hsuf]

lemma omitRunComplement_start (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).start =
      if F.sufWalk.Nil then p.start else F.sufWalk.snd := by
  by_cases hsuf : F.sufWalk.Nil
  · simp [F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf,
      F.prefixTrim_start, hsuf]
  · simp [F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf,
      suffixTrim, pathOfWalk, trimStart, splice, hsuf]

lemma omitRunComplement_finish (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).finish = F.preWalk.penultimate := by
  by_cases hsuf : F.sufWalk.Nil
  · rw [F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf,
      F.prefixTrim_finish]
  · rw [F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf]
    rfl

lemma omitRunComplement_adj_left (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    G.Adj (F.omitRunComplement hpre hclose).finish Q.start := by
  rw [F.omitRunComplement_finish hpre hclose]
  exact F.prefixTrim_adj hpre

lemma omitRunComplement_adj_right (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    G.Adj Q.finish (F.omitRunComplement hpre hclose).start := by
  by_cases hsuf : F.sufWalk.Nil
  · have hf : Q.finish = p.finish := Walk.Nil.eq hsuf
    have hst : (F.omitRunComplement hpre hclose).start = p.start := by
      simp [F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf,
        F.prefixTrim_start]
    simpa [hst, hf] using hclose
  · have hst : (F.omitRunComplement hpre hclose).start =
        (F.suffixTrim hsuf).start := by
      simp [F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf, splice]
    rw [hst]
    exact F.suffixTrim_adj hsuf

lemma omitRunComplement_start_mem_A (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {A : Finset V} (hs : p.start ∈ A)
    (hsufA : F.sufWalk.Nil ∨ F.sufWalk.snd ∈ A) :
    (F.omitRunComplement hpre hclose).start ∈ A := by
  by_cases hsuf : F.sufWalk.Nil
  · have hst : (F.omitRunComplement hpre hclose).start = p.start := by
      simp [F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf,
        F.prefixTrim_start]
    simpa [hst] using hs
  · have hst : (F.omitRunComplement hpre hclose).start =
        (F.suffixTrim hsuf).start := by
      simp [F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf, splice]
    rw [hst, F.suffixTrim_start]
    exact hsufA.resolve_left hsuf

lemma omitRunComplement_finish_mem_A (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {A : Finset V} (hpreA : F.preWalk.penultimate ∈ A) :
    (F.omitRunComplement hpre hclose).finish ∈ A := by
  rw [F.omitRunComplement_finish hpre hclose]
  exact hpreA

lemma edges_eq_dropLast_concat_last (q : GraphPath G) (h : ¬ q.walk.Nil) :
    q.walk.edges =
      q.walk.edges.dropLast ++ [s(q.walk.penultimate, q.finish)] := by
  have hpos := Walk.not_nil_iff_lt_length.1 h
  have hlen : 0 < q.walk.edges.length := by simp [Walk.length_edges]; omega
  have hne : q.walk.edges ≠ [] := List.ne_nil_of_length_pos hlen
  have hcat := List.dropLast_append_getLast hne
  have hi : q.walk.length - 1 < q.walk.edges.length := by
    simp [Walk.length_edges]; omega
  have hlast : q.walk.edges.getLast hne = s(q.walk.penultimate, q.finish) := by
    have : q.walk.edges.getLast hne = q.walk.edges[q.walk.length - 1] := by
      simp [List.getLast_eq_getElem, Walk.length_edges]
    rw [this, Walk.getElem_edges hi]
    have hlen' : q.walk.length - 1 + 1 = q.walk.length := by omega
    simp [Walk.penultimate, hlen', Walk.getVert_length]
  conv_lhs => rw [← hcat]
  rw [hlast]

lemma edges_trimFinish_erase (q : GraphPath G) (h : ¬ q.walk.Nil) :
    (q.trimFinish h).edges =
      q.edges.erase s(q.walk.penultimate, q.finish) := by
  have hedges := edges_eq_dropLast_concat_last q h
  have hnod := q.isPath.isTrail.edges_nodup
  have hnin : s(q.walk.penultimate, q.finish) ∉ q.walk.edges.dropLast := by
    intro hmem
    have hcnt : 2 ≤ q.walk.edges.count s(q.walk.penultimate, q.finish) := by
      have h1 : 1 ≤ q.walk.edges.dropLast.count s(q.walk.penultimate, q.finish) :=
        List.count_pos_iff.mpr hmem
      rw [hedges, List.count_append]
      simp
      omega
    have : q.walk.edges.count s(q.walk.penultimate, q.finish) = 1 :=
      List.count_eq_one_of_mem hnod (by rw [hedges]; exact List.mem_append_right _ (by simp))
    omega
  simp only [edges, trimFinish, Walk.edges_dropLast]
  ext e
  constructor
  · intro he
    have heL : e ∈ q.walk.edges.dropLast := List.mem_toFinset.1 he
    refine mem_erase.2 ⟨fun heq => hnin (heq ▸ heL), List.mem_toFinset.2 ?_⟩
    rw [hedges]
    exact List.mem_append_left _ heL
  · intro he
    obtain ⟨hne, heq⟩ := mem_erase.1 he
    have heL : e ∈ q.walk.edges := List.mem_toFinset.1 heq
    rw [hedges] at heL
    exact List.mem_toFinset.2
      ((List.mem_append.1 heL).resolve_right (by simp [hne]))

lemma edges_eq_cons_tail (q : GraphPath G) (h : ¬ q.walk.Nil) :
    q.walk.edges = s(q.start, q.walk.snd) :: q.walk.edges.tail := by
  have hpos := Walk.not_nil_iff_lt_length.1 h
  have hlen : 0 < q.walk.edges.length := by simp [Walk.length_edges]; omega
  have hne : q.walk.edges ≠ [] := List.ne_nil_of_length_pos hlen
  have hcons := List.cons_head_tail hne
  have h0 : 0 < q.walk.edges.length := hlen
  have hhead : q.walk.edges.head hne = s(q.start, q.walk.snd) := by
    have : q.walk.edges.head hne = q.walk.edges[0] := List.head_eq_getElem hne
    rw [this, Walk.getElem_edges h0]
    simp [Walk.getVert_zero]
  rw [← hcons, hhead]
  rfl

lemma edges_trimStart_erase (q : GraphPath G) (h : ¬ q.walk.Nil) :
    (q.trimStart h).edges = q.edges.erase s(q.start, q.walk.snd) := by
  have hedges := edges_eq_cons_tail q h
  have hnod := q.isPath.isTrail.edges_nodup
  have hnin : s(q.start, q.walk.snd) ∉ q.walk.edges.tail := by
    have hnod' : (s(q.start, q.walk.snd) :: q.walk.edges.tail).Nodup := by
      rwa [← hedges]
    exact (List.nodup_cons.1 hnod').1
  simp only [edges, trimStart, Walk.edges_tail]
  ext e
  constructor
  · intro he
    have heL : e ∈ q.walk.edges.tail := List.mem_toFinset.1 he
    refine mem_erase.2 ⟨fun heq => hnin (heq ▸ heL), List.mem_toFinset.2 ?_⟩
    rw [hedges]
    exact List.mem_cons_of_mem _ heL
  · intro he
    obtain ⟨hne, heq⟩ := mem_erase.1 he
    have heL : e ∈ q.walk.edges := List.mem_toFinset.1 heq
    rw [hedges] at heL
    exact List.mem_toFinset.2 ((List.mem_cons.1 heL).resolve_left hne)

lemma edges_prefixTrim (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) :
    (F.prefixTrim hpre).edges =
      F.preWalk.edges.toFinset.erase s(F.preWalk.penultimate, Q.start) :=
  edges_trimFinish_erase (pathOfWalk F.preWalk F.preWalk_isPath) hpre

lemma edges_suffixTrim (F : OriginalSubwalkFactor p Q)
    (hsuf : ¬ F.sufWalk.Nil) :
    (F.suffixTrim hsuf).edges =
      F.sufWalk.edges.toFinset.erase s(Q.finish, F.sufWalk.snd) :=
  edges_trimStart_erase (pathOfWalk F.sufWalk F.sufWalk_isPath) hsuf

/-- Closed original-edge set of a path plus the original closing chord. -/
def closedEdges (q : GraphPath G) (_hclose : G.Adj q.finish q.start) :
    Finset (Sym2 V) :=
  q.edges ∪ {s(q.finish, q.start)}

/-- Edges of the closed path with both ends outside `S`. -/
noncomputable def retainedClosedEdges (q : GraphPath G) (S : Finset V)
    (hclose : G.Adj q.finish q.start) : Finset (Sym2 V) :=
  (closedEdges q hclose).filter fun e => bothEndsOutside e S

lemma suf_nil_edges (F : OriginalSubwalkFactor p Q) (hsuf : F.sufWalk.Nil) :
    F.sufWalk.edges.toFinset = ∅ := by
  have h0 : F.sufWalk.length = 0 := (Walk.length_eq_zero_iff).2 hsuf
  have hlen : F.sufWalk.edges.length = 0 := by simp [Walk.length_edges, h0]
  simp [List.length_eq_zero_iff.1 hlen]

lemma inter_pre_Q (F : OriginalSubwalkFactor p Q) :
    F.preWalk.support.toFinset ∩ Q.support ⊆ {Q.start} := by
  intro x hx
  have hxpre : x ∈ F.preWalk.support := List.mem_toFinset.1 (mem_inter.1 hx).1
  have hxQ : x ∈ Q.walk.support := by
    simpa [GraphPath.support] using (mem_inter.1 hx).2
  by_cases hxe : x = Q.start
  · simp [hxe]
  · have hnilQ : ¬ Q.walk.Nil := by
      intro hnil
      have : Q.walk.support = [Q.start] := (Walk.nil_iff_support_eq).1 hnil
      exact hxe (by simpa [this] using hxQ)
    have hcons := support_cons_not_nil (w := Q.walk) hnilQ
    have htail : x ∈ Q.walk.support.tail :=
      (List.mem_cons.1 (by rw [hcons] at hxQ; exact hxQ)).resolve_left hxe
    have hcat := F.support_cat
    have hxG : x ∈ p.walk.support := by
      rw [hcat]
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hxpre)))
    have hcnt : 2 ≤ p.walk.support.count x := by
      have h1 : 1 ≤ F.preWalk.support.count x := List.count_pos_iff.mpr hxpre
      have h2 : 1 ≤ Q.walk.support.tail.count x := List.count_pos_iff.mpr htail
      rw [hcat, List.count_append, List.count_append]
      omega
    have : p.walk.support.count x = 1 :=
      List.count_eq_one_of_mem p.support_nodup hxG
    omega

lemma inter_suf_Q (F : OriginalSubwalkFactor p Q) :
    F.sufWalk.support.toFinset ∩ Q.support ⊆ {Q.finish} := by
  intro x hx
  have hxsuf : x ∈ F.sufWalk.support := List.mem_toFinset.1 (mem_inter.1 hx).1
  have hxQ : x ∈ Q.walk.support := by
    simpa [GraphPath.support] using (mem_inter.1 hx).2
  by_cases hxe : x = Q.finish
  · simp [hxe]
  · have hsuf : ¬ F.sufWalk.Nil := by
      intro hnil
      have : F.sufWalk.support = [Q.finish] := (Walk.nil_iff_support_eq).1 hnil
      exact hxe (by simpa [this] using hxsuf)
    have hcons := support_cons_not_nil (w := F.sufWalk) hsuf
    have htail : x ∈ F.sufWalk.support.tail :=
      (List.mem_cons.1 (by rw [hcons] at hxsuf; exact hxsuf)).resolve_left hxe
    have hcat := F.support_cat
    have hxG : x ∈ p.walk.support := by
      rw [hcat]
      exact List.mem_append.2 (Or.inr htail)
    have hcnt : 2 ≤ p.walk.support.count x := by
      have h2 : 1 ≤ F.sufWalk.support.tail.count x := List.count_pos_iff.mpr htail
      by_cases hxs : x = Q.start
      · subst hxs
        have h1 : 1 ≤ F.preWalk.support.count Q.start :=
          List.count_pos_iff.mpr (Walk.end_mem_support F.preWalk)
        rw [hcat, List.count_append, List.count_append]
        omega
      · have hnilQ : ¬ Q.walk.Nil := by
          intro hnil
          have : Q.walk.support = [Q.start] := (Walk.nil_iff_support_eq).1 hnil
          exact hxs (by simpa [this] using hxQ)
        have hconsQ := support_cons_not_nil (w := Q.walk) hnilQ
        have htailQ : x ∈ Q.walk.support.tail :=
          (List.mem_cons.1 (by rw [hconsQ] at hxQ; exact hxQ)).resolve_left hxs
        have h1 : 1 ≤ Q.walk.support.tail.count x := List.count_pos_iff.mpr htailQ
        rw [hcat, List.count_append, List.count_append]
        omega
    have : p.walk.support.count x = 1 :=
      List.count_eq_one_of_mem p.support_nodup hxG
    omega

lemma start_not_mem_Q_of_pre_not_nil (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) : p.start ∉ Q.support := by
  intro hQ
  have hne : p.start ≠ Q.start := fun heq =>
    hpre ((F.preWalk_isPath.nil_iff_eq).2 heq)
  have hxS : p.start ∈ ({Q.start} : Finset V) :=
    F.inter_pre_Q (mem_inter.2
      ⟨List.mem_toFinset.2 (Walk.start_mem_support F.preWalk), hQ⟩)
  exact hne (mem_singleton.1 hxS)

lemma finish_not_mem_Q_of_suf_not_nil (F : OriginalSubwalkFactor p Q)
    (hsuf : ¬ F.sufWalk.Nil) : p.finish ∉ Q.support := by
  intro hQ
  have hne : p.finish ≠ Q.finish := fun heq =>
    hsuf ((F.sufWalk_isPath.nil_iff_eq).2 heq.symm)
  have hxS : p.finish ∈ ({Q.finish} : Finset V) :=
    F.inter_suf_Q (mem_inter.2
      ⟨List.mem_toFinset.2 (Walk.end_mem_support F.sufWalk), hQ⟩)
  exact hne (mem_singleton.1 hxS)

/-- `Q.start` always sits at the end of the prefix, so every vertex of
`Q` appears in the concatenated support list. -/
lemma mem_concat_of_mem_Q_support (F : OriginalSubwalkFactor p Q) {x : V}
    (hx : x ∈ Q.support) :
    x ∈ F.preWalk.support ++ Q.walk.support.tail ++ F.sufWalk.support.tail := by
  have hxQ : x ∈ Q.walk.support := by simpa [GraphPath.support] using hx
  by_cases hnil : Q.walk.Nil
  · have : x = Q.start := by
      have : Q.walk.support = [Q.start] := (Walk.nil_iff_support_eq).1 hnil
      simpa [this] using hxQ
    subst this
    exact List.mem_append.2
      (Or.inl (List.mem_append.2 (Or.inl (Walk.end_mem_support F.preWalk))))
  · have hcons := support_cons_not_nil (w := Q.walk) hnil
    have : x = Q.start ∨ x ∈ Q.walk.support.tail := by
      rw [hcons] at hxQ
      exact List.mem_cons.1 hxQ
    rcases this with rfl | htail
    · exact List.mem_append.2
        (Or.inl (List.mem_append.2 (Or.inl (Walk.end_mem_support F.preWalk))))
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr htail)))

/-- Exact three-piece support union of an actual contiguous factorization. -/
lemma support_union_of_factor (F : OriginalSubwalkFactor p Q) :
    p.support = F.preWalk.support.toFinset ∪ Q.support ∪
      F.sufWalk.support.toFinset := by
  have hcat := F.support_cat
  ext x
  simp only [GraphPath.support, mem_union, List.mem_toFinset]
  constructor
  · intro hx
    have hx' : x ∈ F.preWalk.support ++ Q.walk.support.tail ++
        F.sufWalk.support.tail := by
      simpa [hcat] using hx
    rcases List.mem_append.1 hx' with h | hrv
    · rcases List.mem_append.1 h with hru | hQt
      · exact Or.inl (Or.inl hru)
      · exact Or.inl (Or.inr (List.mem_of_mem_tail hQt))
    · exact Or.inr (List.mem_of_mem_tail hrv)
  · intro hx
    have hcat' : x ∈ F.preWalk.support ++ Q.walk.support.tail ++
        F.sufWalk.support.tail → x ∈ p.walk.support := fun h => by
      simpa [hcat] using h
    rcases hx with h | hrv
    · rcases h with hru | hQ
      · exact hcat' (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hru))))
      · exact hcat' (F.mem_concat_of_mem_Q_support (by simpa [GraphPath.support] using hQ))
    · have hxR : x ∈ F.sufWalk.support := hrv
      by_cases hnilR : F.sufWalk.Nil
      · have : x = Q.finish := by
          have : F.sufWalk.support = [Q.finish] :=
            (Walk.nil_iff_support_eq).1 hnilR
          simpa [this] using hxR
        subst this
        exact hcat' (F.mem_concat_of_mem_Q_support Q.finish_mem_support)
      · have hcons := support_cons_not_nil (w := F.sufWalk) hnilR
        have : x = Q.finish ∨ x ∈ F.sufWalk.support.tail := by
          rw [hcons] at hxR
          exact List.mem_cons.1 hxR
        rcases this with rfl | htail
        · exact hcat' (F.mem_concat_of_mem_Q_support Q.finish_mem_support)
        · exact hcat' (List.mem_append.2 (Or.inr htail))

lemma Q_support_subset (F : OriginalSubwalkFactor p Q) : Q.support ⊆ p.support := by
  intro x hx
  rw [F.support_union_of_factor]
  exact mem_union.2 (Or.inl (mem_union.2 (Or.inr hx)))

/-- Unique-named support sdiff of this actual factorization. Named to
avoid colliding with G2 `sdiff_eq_prefix_suffix`. -/
lemma omitRun_sdiff_eq_prefix_suffix (F : OriginalSubwalkFactor p Q) :
    p.support \ Q.support =
      F.preWalk.support.toFinset.erase Q.start ∪
        F.sufWalk.support.toFinset.erase Q.finish := by
  have hU := F.support_union_of_factor
  have hruQ := F.inter_pre_Q
  have hrvQ := F.inter_suf_Q
  ext x
  simp only [hU, mem_sdiff, mem_union, mem_erase]
  constructor
  · intro ⟨hx, hxQ⟩
    rcases hx with h | hrv
    · rcases h with hru | hQ
      · exact Or.inl ⟨fun hxe => hxQ (hxe ▸ Q.start_mem_support), hru⟩
      · exact (hxQ hQ).elim
    · exact Or.inr ⟨fun hxe => hxQ (hxe ▸ Q.finish_mem_support), hrv⟩
  · intro hx
    rcases hx with ⟨hne, hru⟩ | ⟨hne, hrv⟩
    · refine ⟨Or.inl (Or.inl hru), ?_⟩
      intro hQ
      have : x ∈ ({Q.start} : Finset V) :=
        hruQ (mem_inter.2 ⟨hru, hQ⟩)
      exact hne (mem_singleton.1 this)
    · refine ⟨Or.inr hrv, ?_⟩
      intro hQ
      have : x ∈ ({Q.finish} : Finset V) :=
        hrvQ (mem_inter.2 ⟨hrv, hQ⟩)
      exact hne (mem_singleton.1 this)

lemma erase_end_of_nil {u v : V} {w : G.Walk u v} (h : w.Nil) :
    w.support.toFinset.erase v = ∅ := by
  have : w.support = [u] := (Walk.nil_iff_support_eq).1 h
  have hv : v = u := (Walk.Nil.eq h).symm
  simp [this, hv]

/-- Exact support identity of this actual complement construction,
including nil suffix (the suffix erase is empty) and the singleton
complement (the sdiff may be a singleton). Edge identity cannot identify
the singleton support. -/
theorem omitRunComplement_support (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).support = p.support \ Q.support := by
  have hsd := F.omitRun_sdiff_eq_prefix_suffix
  by_cases hsuf : F.sufWalk.Nil
  · have hr := F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf
    have hf : Q.finish = p.finish := Walk.Nil.eq hsuf
    have hR : F.sufWalk.support.toFinset.erase Q.finish = ∅ := by
      simpa [hf] using erase_end_of_nil hsuf
    have hsd' : p.support \ Q.support =
        F.preWalk.support.toFinset.erase Q.start := by
      rw [hsd, hR, union_empty]
    rw [hr, F.support_prefixTrim hpre]
    exact hsd'.symm
  · have hr := F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf
    have hdisj := (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm
    have hcl : G.Adj (F.suffixTrim hsuf).finish (F.prefixTrim hpre).start := by
      simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose
    have hsup :
        ((F.suffixTrim hsuf).splice (F.prefixTrim hpre) hcl hdisj).support =
          (F.suffixTrim hsuf).support ∪ (F.prefixTrim hpre).support :=
      support_splice (F.suffixTrim hsuf) (F.prefixTrim hpre) hcl hdisj
    rw [hr, hsup, F.support_suffixTrim hsuf, F.support_prefixTrim hpre,
      union_comm]
    exact hsd.symm

lemma omitRunComplement_disjoint_block (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    Disjoint Q.support (F.omitRunComplement hpre hclose).support := by
  rw [F.omitRunComplement_support hpre hclose]
  exact Finset.disjoint_sdiff

lemma omitRunComplement_subset_host (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).support ⊆ p.support := by
  rw [F.omitRunComplement_support hpre hclose]
  exact sdiff_subset

/-- Singleton complement: if the host-minus-block sdiff is a singleton,
the actual constructed complement is that singleton path. -/
theorem omitRunComplement_support_singleton (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    (hcard : (p.support \ Q.support).card = 1) :
    ∃ v, (F.omitRunComplement hpre hclose).support = {v} ∧
      p.support \ Q.support = {v} := by
  obtain ⟨v, hv⟩ := card_eq_one.1 hcard
  refine ⟨v, ?_, hv⟩
  rw [F.omitRunComplement_support hpre hclose, hv]

lemma omitRunComplement_start_mem_support_sdiff (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).start ∈ p.support \ Q.support := by
  rw [← F.omitRunComplement_support hpre hclose]
  exact start_mem_support _

lemma omitRunComplement_finish_mem_support_sdiff (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).finish ∈ p.support \ Q.support := by
  rw [← F.omitRunComplement_support hpre hclose]
  exact finish_mem_support _

/-- Constructed complement edges lie among the closed original edges. -/
theorem omitRunComplement_edges_subset_closed (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).edges ⊆ closedEdges p hclose := by
  intro e he
  by_cases hsuf : F.sufWalk.Nil
  · have hr := F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf
    have heP : e ∈ (F.prefixTrim hpre).edges := by simpa [hr] using he
    have hePre : e ∈ F.preWalk.edges.toFinset := by
      have := F.edges_prefixTrim hpre
      rw [this] at heP
      exact (mem_erase.1 heP).2
    refine mem_union.2 (Or.inl ?_)
    have : e ∈ p.edges := by
      simp [F.edges_union, hePre]
    exact this
  · have hr := F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf
    have hdisj := (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm
    have hcl : G.Adj (F.suffixTrim hsuf).finish (F.prefixTrim hpre).start := by
      simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose
    have he' : e ∈ (F.suffixTrim hsuf).edges ∪ (F.prefixTrim hpre).edges ∪
        {s((F.suffixTrim hsuf).finish, (F.prefixTrim hpre).start)} := by
      simpa [hr, edges_of_splice_block _ _ hcl hdisj] using he
    rcases mem_union.1 he' with h | hse
    · rcases mem_union.1 h with hsE | hpE
      · have heS : e ∈ F.sufWalk.edges.toFinset := by
          have := F.edges_suffixTrim hsuf
          rw [this] at hsE
          exact (mem_erase.1 hsE).2
        refine mem_union.2 (Or.inl ?_)
        simp [F.edges_union, heS]
      · have heP : e ∈ F.preWalk.edges.toFinset := by
          have := F.edges_prefixTrim hpre
          rw [this] at hpE
          exact (mem_erase.1 hpE).2
        refine mem_union.2 (Or.inl ?_)
        simp [F.edges_union, heP]
    · have : e = s(p.finish, p.start) := by
        simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using
          (mem_singleton.1 hse)
      exact mem_union.2 (Or.inr (mem_singleton.2 this))

lemma prefixTrim_bothOutside (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) {e : Sym2 V}
    (he : e ∈ (F.prefixTrim hpre).edges) :
    bothEndsOutside e Q.support := by
  intro x hx hxQ
  have heP : e ∈ F.preWalk.edges.toFinset := by
    have := F.edges_prefixTrim hpre
    rw [this] at he
    exact (mem_erase.1 he).2
  have hxpre : x ∈ F.preWalk.support :=
    F.preWalk.mem_support_of_mem_edges (List.mem_toFinset.1 heP) hx
  have hxeq : x = Q.start := mem_singleton.1
    (F.inter_pre_Q (mem_inter.2 ⟨List.mem_toFinset.2 hxpre, hxQ⟩))
  subst hxeq
  have heI :
      e ∈ (pathOfWalk F.preWalk F.preWalk_isPath).incidentEdges
        (pathOfWalk F.preWalk F.preWalk_isPath).finish :=
    mem_incidentEdges_iff.2 ⟨by simpa [edges, pathOfWalk] using heP, hx⟩
  have hinc := (pathOfWalk F.preWalk F.preWalk_isPath).incidentEdges_finish hpre
  have heq : e = s(F.preWalk.penultimate, Q.start) := by
    have : e ∈ ({s((pathOfWalk F.preWalk F.preWalk_isPath).walk.penultimate,
        (pathOfWalk F.preWalk F.preWalk_isPath).finish)} : Finset (Sym2 V)) := by
      rw [← hinc]
      exact heI
    simpa [pathOfWalk] using mem_singleton.1 this
  have := F.edges_prefixTrim hpre
  rw [this] at he
  exact (mem_erase.1 he).1 heq

lemma suffixTrim_bothOutside (F : OriginalSubwalkFactor p Q)
    (hsuf : ¬ F.sufWalk.Nil) {e : Sym2 V}
    (he : e ∈ (F.suffixTrim hsuf).edges) :
    bothEndsOutside e Q.support := by
  intro x hx hxQ
  have heS : e ∈ F.sufWalk.edges.toFinset := by
    have := F.edges_suffixTrim hsuf
    rw [this] at he
    exact (mem_erase.1 he).2
  have hxsuf : x ∈ F.sufWalk.support :=
    F.sufWalk.mem_support_of_mem_edges (List.mem_toFinset.1 heS) hx
  have hxeq : x = Q.finish := mem_singleton.1
    (F.inter_suf_Q (mem_inter.2 ⟨List.mem_toFinset.2 hxsuf, hxQ⟩))
  subst hxeq
  have heI :
      e ∈ (pathOfWalk F.sufWalk F.sufWalk_isPath).incidentEdges
        (pathOfWalk F.sufWalk F.sufWalk_isPath).start :=
    mem_incidentEdges_iff.2 ⟨by simpa [edges, pathOfWalk] using heS, hx⟩
  have hinc := (pathOfWalk F.sufWalk F.sufWalk_isPath).incidentEdges_start hsuf
  have heq : e = s(Q.finish, F.sufWalk.snd) := by
    have : e ∈ ({s((pathOfWalk F.sufWalk F.sufWalk_isPath).start,
        (pathOfWalk F.sufWalk F.sufWalk_isPath).walk.snd)} : Finset (Sym2 V)) := by
      rw [← hinc]
      exact heI
    simpa [pathOfWalk] using mem_singleton.1 this
  have := F.edges_suffixTrim hsuf
  rw [this] at he
  exact (mem_erase.1 he).1 heq

theorem omitRunComplement_bothOutside (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {e : Sym2 V} (he : e ∈ (F.omitRunComplement hpre hclose).edges) :
    bothEndsOutside e Q.support := by
  by_cases hsuf : F.sufWalk.Nil
  · have hr := F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf
    exact F.prefixTrim_bothOutside hpre (by simpa [hr] using he)
  · have hr := F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf
    have hdisj := (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm
    have hcl : G.Adj (F.suffixTrim hsuf).finish (F.prefixTrim hpre).start := by
      simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose
    have he' : e ∈ (F.suffixTrim hsuf).edges ∪ (F.prefixTrim hpre).edges ∪
        {s((F.suffixTrim hsuf).finish, (F.prefixTrim hpre).start)} := by
      simpa [hr, edges_of_splice_block _ _ hcl hdisj] using he
    rcases mem_union.1 he' with h | hse
    · rcases mem_union.1 h with hsE | hpE
      · exact F.suffixTrim_bothOutside hsuf hsE
      · exact F.prefixTrim_bothOutside hpre hpE
    · have heq : e = s(p.finish, p.start) := by
        simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using
          (mem_singleton.1 hse)
      rw [heq]
      exact bothEndsOutside_iff.2
        ⟨F.finish_not_mem_Q_of_suf_not_nil hsuf,
          F.start_not_mem_Q_of_pre_not_nil hpre⟩

/-- Exact complement-edge identity. -/
theorem omitRunComplement_edges (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start) :
    (F.omitRunComplement hpre hclose).edges =
      retainedClosedEdges p Q.support hclose := by
  ext e
  constructor
  · intro he
    exact mem_filter.2
      ⟨F.omitRunComplement_edges_subset_closed hpre hclose he,
        F.omitRunComplement_bothOutside hpre hclose he⟩
  · intro he
    obtain ⟨hmem, hout⟩ := mem_filter.1 he
    rcases mem_union.1 hmem with hp | hc
    · have hp' : e ∈ F.preWalk.edges.toFinset ∪ Q.edges ∪
          F.sufWalk.edges.toFinset := by simpa [F.edges_union] using hp
      rcases mem_union.1 hp' with hmid | hsE
      · rcases mem_union.1 hmid with hP | hQ
        · have hne : e ≠ s(F.preWalk.penultimate, Q.start) := by
            intro heq
            subst heq
            exact hout Q.start (by simp) Q.start_mem_support
          have hePre : e ∈ (F.prefixTrim hpre).edges := by
            rw [F.edges_prefixTrim hpre]
            exact mem_erase.2 ⟨hne, hP⟩
          by_cases hsuf : F.sufWalk.Nil
          · simpa [F.omitRunComplement_eq_prefix_of_nil hpre hclose hsuf] using hePre
          · have hr := F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf
            have hdisj := (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm
            have hcl : G.Adj (F.suffixTrim hsuf).finish (F.prefixTrim hpre).start := by
              simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose
            have : e ∈ (F.suffixTrim hsuf).edges ∪ (F.prefixTrim hpre).edges ∪
                {s((F.suffixTrim hsuf).finish, (F.prefixTrim hpre).start)} :=
              mem_union.2 (Or.inl (mem_union.2 (Or.inr hePre)))
            simpa [hr, edges_of_splice_block _ _ hcl hdisj] using this
        · exact (not_bothEndsOutside_of_mem_edges hQ hout).elim
      · by_cases hsuf : F.sufWalk.Nil
        · have : F.sufWalk.edges.toFinset = ∅ := F.suf_nil_edges hsuf
          exact (notMem_empty e (this ▸ hsE)).elim
        · have hne : e ≠ s(Q.finish, F.sufWalk.snd) := by
            intro heq
            subst heq
            exact hout Q.finish (by simp) Q.finish_mem_support
          have heSuf : e ∈ (F.suffixTrim hsuf).edges := by
            rw [F.edges_suffixTrim hsuf]
            exact mem_erase.2 ⟨hne, hsE⟩
          have hr := F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf
          have hdisj := (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm
          have hcl : G.Adj (F.suffixTrim hsuf).finish (F.prefixTrim hpre).start := by
            simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose
          have : e ∈ (F.suffixTrim hsuf).edges ∪ (F.prefixTrim hpre).edges ∪
              {s((F.suffixTrim hsuf).finish, (F.prefixTrim hpre).start)} :=
            mem_union.2 (Or.inl (mem_union.2 (Or.inl heSuf)))
          simpa [hr, edges_of_splice_block _ _ hcl hdisj] using this
    · have heq : e = s(p.finish, p.start) := mem_singleton.1 hc
      by_cases hsuf : F.sufWalk.Nil
      · have hf : Q.finish = p.finish := Walk.Nil.eq hsuf
        subst heq
        exact (bothEndsOutside_iff.1 hout).1 (hf ▸ Q.finish_mem_support) |>.elim
      · have hr := F.omitRunComplement_eq_splice_of_not_nil hpre hclose hsuf
        have hdisj := (F.disjoint_prefixTrim_suffixTrim hpre hsuf).symm
        have hcl : G.Adj (F.suffixTrim hsuf).finish (F.prefixTrim hpre).start := by
          simpa [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre] using hclose
        rw [hr, edges_of_splice_block _ _ hcl hdisj, heq]
        simp [F.suffixTrim_finish hsuf, F.prefixTrim_start hpre]

/-- Another original run disjoint from `Q` has every walk edge retained
in the actual complement. An ambient edge-subset of a prescribed cycle
does not prove this converse. -/
theorem mem_omitRunComplement_of_disjoint_run
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    (R : GraphPath G) (hd : Disjoint R.support Q.support)
    (hsub : R.edges ⊆ p.edges) :
    R.edges ⊆ (F.omitRunComplement hpre hclose).edges := by
  intro e he
  have heP : e ∈ p.edges := hsub he
  have hout : bothEndsOutside e Q.support := bothEndsOutside_of_support he hd
  have : e ∈ retainedClosedEdges p Q.support hclose :=
    mem_filter.2 ⟨mem_union.2 (Or.inl heP), hout⟩
  simpa [F.omitRunComplement_edges hpre hclose] using this

/-- Every retained run edge occurs as an actual directed dart of the
complement, so it admits a `PrefixEdgeFactor`. -/
theorem exists_factor_of_retained_run_edge
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    (R : GraphPath G) (hd : Disjoint R.support Q.support)
    (hsub : R.edges ⊆ p.edges) {e : Sym2 V} (he : e ∈ R.edges) :
    ∃ i, i < (F.omitRunComplement hpre hclose).walk.length ∧
      s((F.omitRunComplement hpre hclose).walk.getVert i,
          (F.omitRunComplement hpre hclose).walk.getVert (i + 1)) = e := by
  have heR : e ∈ (F.omitRunComplement hpre hclose).edges :=
    F.mem_omitRunComplement_of_disjoint_run hpre hclose R hd hsub he
  obtain ⟨i, hiE, hie⟩ := List.mem_iff_getElem.1 (mem_edges_iff.1 heR)
  have hiL : i < (F.omitRunComplement hpre hclose).walk.length := by
    simpa [Walk.length_edges] using hiE
  refine ⟨i, hiL, ?_⟩
  exact (Walk.getElem_edges hiE).symm.trans hie

theorem exists_PrefixEdgeFactor_of_retained_run_edge
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    (R : GraphPath G) (hd : Disjoint R.support Q.support)
    (hsub : R.edges ⊆ p.edges) {e : Sym2 V} (he : e ∈ R.edges) :
    ∃ i, i < (F.omitRunComplement hpre hclose).walk.length ∧
      s((F.omitRunComplement hpre hclose).walk.getVert i,
          (F.omitRunComplement hpre hclose).walk.getVert (i + 1)) = e ∧
        Nonempty (PrefixEdgeFactor (F.omitRunComplement hpre hclose)
          ((F.omitRunComplement hpre hclose).walk.getVert i)
          ((F.omitRunComplement hpre hclose).walk.getVert (i + 1))) := by
  obtain ⟨i, hi, hpair⟩ :=
    F.exists_factor_of_retained_run_edge hpre hclose R hd hsub he
  obtain ⟨Fac, _⟩ := (F.omitRunComplement hpre hclose).exists_factorAtIndex hi
  exact ⟨i, hi, hpair, ⟨Fac⟩⟩

/-- After inserting the omitted block into this actual complement at a
retained dart, the support is the disjoint union of the complement with
`Q`, hence equals the host support. Endpoints remain the complement
endpoints (border `A` membership transports). -/
theorem insertBlock_support_of_omitRunComplement
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {u v : V} (Fac : PrefixEdgeFactor (F.omitRunComplement hpre hclose) u v)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (Fac.insertBlock Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf).support =
      p.support := by
  have hunion :=
    Fac.insertBlock_support Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf
  have hr : (F.omitRunComplement hpre hclose).support = p.support \ Q.support :=
    F.omitRunComplement_support hpre hclose
  have hQ : Q.support ⊆ p.support := F.Q_support_subset
  rw [hunion, hr, sdiff_union_self_eq_union, union_eq_left.2 hQ]

lemma insertBlock_start_of_omitRunComplement
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {u v : V} (Fac : PrefixEdgeFactor (F.omitRunComplement hpre hclose) u v)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (Fac.insertBlock Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf).start =
      (F.omitRunComplement hpre hclose).start :=
  Fac.insertBlock_start Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf

lemma insertBlock_finish_of_omitRunComplement
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {u v : V} (Fac : PrefixEdgeFactor (F.omitRunComplement hpre hclose) u v)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (Fac.insertBlock Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf).finish =
      (F.omitRunComplement hpre hclose).finish :=
  Fac.insertBlock_finish Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf

lemma insertBlock_start_mem_A_of_omitRunComplement
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {u v : V} (Fac : PrefixEdgeFactor (F.omitRunComplement hpre hclose) u v)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (hA : (F.omitRunComplement hpre hclose).start ∈ A) :
    (Fac.insertBlock Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf).start ∈ A := by
  simpa [Fac.insertBlock_start Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf]
    using hA

lemma insertBlock_finish_mem_A_of_omitRunComplement
    (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) (hclose : G.Adj p.finish p.start)
    {u v : V} (Fac : PrefixEdgeFactor (F.omitRunComplement hpre hclose) u v)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (hA : (F.omitRunComplement hpre hclose).finish ∈ A) :
    (Fac.insertBlock Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf).finish ∈ A := by
  simpa [Fac.insertBlock_finish Q (F.omitRunComplement_disjoint_block hpre hclose) hs hf]
    using hA

end OriginalSubwalkFactor

/-- Cycle-filtered form: if the opened path plus its closing edge recovers
the prescribed cycle, the complement edges are exactly the cycle edges
with both ends outside `Q.support`. -/
theorem omitRunComplement_eq_cycle_filter
    {p Q : GraphPath G} (F : OriginalSubwalkFactor p Q)
    (hpre : ¬ F.preWalk.Nil) {c : GraphCycle G}
    (hclose : G.Adj p.finish p.start)
    (hc : p.edges ∪ {s(p.finish, p.start)} = c.edges) :
    (F.omitRunComplement hpre hclose).edges =
      c.edges.filter fun e => bothEndsOutside e Q.support := by
  have h := F.omitRunComplement_edges hpre hclose
  simpa [OriginalSubwalkFactor.retainedClosedEdges,
    OriginalSubwalkFactor.closedEdges, hc] using h

end GraphPath

end Nikoghosyan
