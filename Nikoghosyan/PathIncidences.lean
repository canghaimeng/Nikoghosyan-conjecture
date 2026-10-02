/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.PathRotation

/-!
Exact original walk-edge incidences of a simple path.

`ProtectedAt` only says that every `A`-incident path edge belongs to a
prescribed cycle. This module records the actual walk-edge counts at a
vertex of a simple original path: one edge at each endpoint of a
nonsingleton path, two edges at every internal vertex. Identities name
the predecessor and successor edges of the walk. Ambient `G.degree` is
never used: `G` may have extra edges.

Reversal leaves `A`-incidence and `ProtectedAt` unchanged. Prefix and
suffix factor paths, `takeUntil`/`dropUntil`, and `trimStart`/`trimFinish`
retain a subset of the parent walk edges. An edge of a path meets only
vertices of that path's support.

This module does not construct a spanning `A`–`A` path.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

lemma nil_iff_card_support_eq_one (p : GraphPath G) :
    p.walk.Nil ↔ p.support.card = 1 := by
  constructor
  · intro h
    simpa [support_eq_singleton_of_nil p h] using (card_singleton p.start)
  · intro h
    have hlen : p.walk.length + 1 = 1 := by simpa [card_support] using h
    exact (Walk.length_eq_zero_iff).1 (by omega)

lemma two_le_card_support_iff (p : GraphPath G) :
    2 ≤ p.support.card ↔ ¬ p.walk.Nil := by
  constructor
  · intro h hn
    have : p.support.card = 1 := (nil_iff_card_support_eq_one p).1 hn
    omega
  · intro h
    have hpos : 0 < p.walk.length := Walk.not_nil_iff_lt_length.1 h
    have : 2 ≤ p.walk.length + 1 := by omega
    simpa [card_support] using this

lemma start_ne_finish_of_two_le_card_incidences (p : GraphPath G) (h : 2 ≤ p.support.card) :
    p.start ≠ p.finish := by
  intro heq
  exact (two_le_card_support_iff p).1 h ((nil_iff_start_eq_finish p).2 heq)

lemma two_le_card_of_start_ne_finish (p : GraphPath G) (h : p.start ≠ p.finish) :
    2 ≤ p.support.card :=
  (two_le_card_support_iff p).2 fun hn => h ((nil_iff_start_eq_finish p).1 hn)

/-- Both ends of a path edge lie on the path. Operations off the support
create no path-incident edges. -/
lemma mem_support_of_mem_edge {p : GraphPath G} {e : Sym2 V} {v : V}
    (he : e ∈ p.edges) (hv : v ∈ e) : v ∈ p.support :=
  List.mem_toFinset.2 (p.walk.mem_support_of_mem_edges (mem_edges_iff.1 he) hv)

lemma incidentEdges_subset_edges (p : GraphPath G) (v : V) :
    p.incidentEdges v ⊆ p.edges := by
  intro e he
  exact (mem_incidentEdges_iff.1 he).1

lemma incidentEdges_subset_AIncident (p : GraphPath G) {A : Finset V} {v : V}
    (hv : v ∈ A) : p.incidentEdges v ⊆ p.AIncident A := by
  intro e he
  exact mem_AIncident_iff.2 ⟨(mem_incidentEdges_iff.1 he).1,
    ⟨v, hv, (mem_incidentEdges_iff.1 he).2⟩⟩

lemma first_edge_mem_incidences (p : GraphPath G) (h : ¬ p.walk.Nil) :
    s(p.start, p.walk.snd) ∈ p.edges :=
  mem_edges_iff.2 (p.walk.mk_start_snd_mem_edges h)

lemma last_edge_mem (p : GraphPath G) (h : ¬ p.walk.Nil) :
    s(p.walk.penultimate, p.finish) ∈ p.edges :=
  mem_edges_iff.2 (p.walk.mk_penultimate_end_mem_edges h)

/-- At the start of a nonsingleton original path the unique incident walk
edge is the first dart. -/
theorem incidentEdges_start (p : GraphPath G) (h : ¬ p.walk.Nil) :
    p.incidentEdges p.start = {s(p.start, p.walk.snd)} := by
  ext e
  constructor
  · intro he
    obtain ⟨heE, hse⟩ := mem_incidentEdges_iff.1 he
    have heq : e = s(p.start, Sym2.Mem.other' hse) := (Sym2.other_spec' hse).symm
    have hw : Sym2.Mem.other' hse = p.walk.snd :=
      p.isPath.eq_snd_of_mem_edges (by
        rw [← heq]
        exact mem_edges_iff.1 heE)
    rw [heq, hw]
    exact mem_singleton_self _
  · intro he
    rw [mem_singleton] at he
    subst he
    exact mem_incidentEdges_iff.2 ⟨p.first_edge_mem_incidences h, by simp⟩

/-- At the finish of a nonsingleton original path the unique incident walk
edge is the last dart. -/
theorem incidentEdges_finish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    p.incidentEdges p.finish = {s(p.walk.penultimate, p.finish)} := by
  ext e
  constructor
  · intro he
    obtain ⟨heE, hse⟩ := mem_incidentEdges_iff.1 he
    have heq : e = s(p.finish, Sym2.Mem.other' hse) := (Sym2.other_spec' hse).symm
    have hw : Sym2.Mem.other' hse = p.walk.penultimate :=
      p.isPath.eq_penultimate_of_mem_edges (by
        rw [← heq]
        exact mem_edges_iff.1 heE)
    rw [heq, hw]
    simp
  · intro he
    rw [mem_singleton] at he
    subst he
    exact mem_incidentEdges_iff.2 ⟨p.last_edge_mem h, by simp⟩

theorem incidentEdges_card_start (p : GraphPath G) (h : 2 ≤ p.support.card) :
    (p.incidentEdges p.start).card = 1 := by
  rw [p.incidentEdges_start ((two_le_card_support_iff p).1 h), card_singleton]

theorem incidentEdges_card_finish (p : GraphPath G) (h : 2 ≤ p.support.card) :
    (p.incidentEdges p.finish).card = 1 := by
  rw [p.incidentEdges_finish ((two_le_card_support_iff p).1 h), card_singleton]

lemma takeUntil_not_nil {p : GraphPath G} {x : V} (hx : x ∈ p.support)
    (hne : x ≠ p.start) : ¬ (p.takeUntil hx).walk.Nil := by
  intro h
  exact hne ((takeUntil_nil_iff p hx).1 h)

lemma walk_eq_take_append_drop_incidences (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    p.walk = (p.takeUntil hx).walk.append (p.dropUntil hx).walk := by
  simpa [takeUntil, dropUntil] using
    (Walk.take_spec p.walk (mem_walk_support.1 hx)).symm

lemma edges_eq_takeUntil_union_dropUntil (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) :
    p.edges = (p.takeUntil hx).edges ∪ (p.dropUntil hx).edges := by
  have hx' := mem_walk_support.1 hx
  have hspec := Walk.take_spec p.walk hx'
  have hedges : p.walk.edges =
      (p.walk.takeUntil x hx').edges ++ (p.walk.dropUntil x hx').edges :=
    (congrArg Walk.edges hspec.symm).trans
      (Walk.edges_append (p.walk.takeUntil x hx') (p.walk.dropUntil x hx'))
  simp [edges, takeUntil, dropUntil, hedges, List.toFinset_append]

lemma disjoint_takeUntil_dropUntil_edges (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) :
    Disjoint (p.takeUntil hx).edges (p.dropUntil hx).edges := by
  have h :=
    p.isPath.isTrail.disjoint_edges_takeUntil_dropUntil (mem_walk_support.1 hx)
  refine disjoint_left.2 ?_
  intro e heT heD
  exact h (mem_edges_iff.1 heT) (mem_edges_iff.1 heD)

lemma incidentEdges_eq_take_union_drop (p : GraphPath G) {x v : V}
    (hx : x ∈ p.support) :
    p.incidentEdges v =
      (p.takeUntil hx).incidentEdges v ∪ (p.dropUntil hx).incidentEdges v := by
  simp [incidentEdges, p.edges_eq_takeUntil_union_dropUntil hx, filter_union]

lemma takeUntil_finish {p : GraphPath G} {x : V} (hx : x ∈ p.support) :
    (p.takeUntil hx).finish = x :=
  rfl

lemma dropUntil_start {p : GraphPath G} {x : V} (hx : x ∈ p.support) :
    (p.dropUntil hx).start = x :=
  rfl

/-- At an internal vertex the two incident walk-edges are the incoming
predecessor along `takeUntil` and the outgoing successor along
`dropUntil`. -/
theorem incidentEdges_internal (p : GraphPath G) {v : V}
    (hv : v ∈ p.support) (hs : v ≠ p.start) (hf : v ≠ p.finish) :
    p.incidentEdges v =
      {s((p.takeUntil hv).walk.penultimate, v),
        s(v, (p.dropUntil hv).walk.snd)} := by
  have hTnil := p.takeUntil_not_nil hv hs
  have hDnil := p.dropUntil_not_nil hv hf
  have hT := (p.takeUntil hv).incidentEdges_finish hTnil
  have hD := (p.dropUntil hv).incidentEdges_start hDnil
  have hU := p.incidentEdges_eq_take_union_drop (x := v) (v := v) hv
  have hTf : (p.takeUntil hv).finish = v := p.takeUntil_finish hv
  have hDs : (p.dropUntil hv).start = v := p.dropUntil_start hv
  have hT' : (p.takeUntil hv).incidentEdges v =
      {s((p.takeUntil hv).walk.penultimate, v)} := by
    simpa [hTf] using hT
  have hD' : (p.dropUntil hv).incidentEdges v =
      {s(v, (p.dropUntil hv).walk.snd)} := by
    simpa [hDs] using hD
  rw [hU, hT', hD']
  simp [singleton_union]

theorem incidentEdges_card_internal (p : GraphPath G) {v : V}
    (hv : v ∈ p.support) (hs : v ≠ p.start) (hf : v ≠ p.finish) :
    (p.incidentEdges v).card = 2 := by
  have hTnil := p.takeUntil_not_nil hv hs
  have hDnil := p.dropUntil_not_nil hv hf
  have he1 : s((p.takeUntil hv).walk.penultimate, v) ∈ (p.takeUntil hv).edges := by
    simpa [p.takeUntil_finish hv] using (p.takeUntil hv).last_edge_mem hTnil
  have he2 : s(v, (p.dropUntil hv).walk.snd) ∈ (p.dropUntil hv).edges := by
    simpa [p.dropUntil_start hv] using (p.dropUntil hv).first_edge_mem_incidences hDnil
  have hne :
      s((p.takeUntil hv).walk.penultimate, v) ≠
        s(v, (p.dropUntil hv).walk.snd) := by
    intro heq
    exact (disjoint_left.1 (p.disjoint_takeUntil_dropUntil_edges hv) he1)
      (by simpa [heq] using he2)
  rw [p.incidentEdges_internal hv hs hf]
  exact card_pair hne

/-- Exact 1/2 incidence counts of a simple original path. No hypothesis
on `G.degree`. -/
theorem incidentEdges_card (p : GraphPath G) (h : 2 ≤ p.support.card) {v : V}
    (hv : v ∈ p.support) :
    if v = p.start ∨ v = p.finish then (p.incidentEdges v).card = 1
    else (p.incidentEdges v).card = 2 := by
  by_cases hs : v = p.start
  · simp [hs, p.incidentEdges_card_start h]
  · by_cases hf : v = p.finish
    · simp [hf, p.incidentEdges_card_finish h]
    · simp [hs, hf, p.incidentEdges_card_internal hv hs hf]

lemma pathSucc_eq_snd_dropUntil (p : GraphPath G) {a : V} (ha : a ∈ p.support)
    (hne : a ≠ p.finish) :
    p.pathSucc ha hne = (p.dropUntil ha).walk.snd :=
  rfl

lemma incidentEdges_internal_succ (p : GraphPath G) {v : V}
    (hv : v ∈ p.support) (hs : v ≠ p.start) (hf : v ≠ p.finish) :
    s(v, p.pathSucc hv hf) ∈ p.incidentEdges v := by
  have h := p.incidentEdges_internal hv hs hf
  have : s(v, p.pathSucc hv hf) =
      s(v, (p.dropUntil hv).walk.snd) := by
    simp [pathSucc_eq_snd_dropUntil]
  rw [h, this]
  simp

/-! ### Reversal invariance of original `A` incidence and protection -/

lemma edges_reverse (p : GraphPath G) : p.reverse.edges = p.edges := by
  simp [edges, reverse, Walk.edges_reverse, List.toFinset_reverse]

lemma incidentEdges_reverse (p : GraphPath G) (v : V) :
    p.reverse.incidentEdges v = p.incidentEdges v := by
  simp [incidentEdges, p.edges_reverse]

lemma AIncident_reverse (p : GraphPath G) (A : Finset V) :
    p.reverse.AIncident A = p.AIncident A := by
  simp [AIncident, p.edges_reverse]

theorem ProtectedAt_reverse (p : GraphPath G) (c : GraphCycle G) (A : Finset V) :
    p.reverse.ProtectedAt c A ↔ p.ProtectedAt c A := by
  simp [ProtectedAt, p.AIncident_reverse]

lemma ProtectedAt.mono_cycle_edges {p : GraphPath G} {c : GraphCycle G}
    {A : Finset V} (h : p.ProtectedAt c A) :
    p.AIncident A ⊆ c.walk.edges.toFinset :=
  h

lemma ProtectedAt.incidentEdges_subset {p : GraphPath G} {c : GraphCycle G}
    {A : Finset V} (h : p.ProtectedAt c A) {v : V} (hv : v ∈ A) :
    p.incidentEdges v ⊆ c.walk.edges.toFinset :=
  (p.incidentEdges_subset_AIncident hv).trans h

/-! ### Subwalk / factor / trim original-edge retention -/

lemma edges_of_isSubwalk {p q : GraphPath G}
    (h : p.walk.IsSubwalk q.walk) : p.edges ⊆ q.edges := by
  intro e he
  exact mem_edges_iff.2 (h.edges_subset (mem_edges_iff.1 he))

lemma edges_takeUntil_subset (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.takeUntil hx).edges ⊆ p.edges :=
  edges_of_isSubwalk (by
    simpa [takeUntil] using
      Walk.isSubwalk_takeUntil p.walk (mem_walk_support.1 hx))

lemma edges_dropUntil_subset_incidences (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.dropUntil hx).edges ⊆ p.edges :=
  edges_of_isSubwalk (by
    simpa [dropUntil] using
      Walk.isSubwalk_dropUntil p.walk (mem_walk_support.1 hx))

lemma isSubwalk_trimStart_incidences (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).walk.IsSubwalk p.walk := by
  rw [Walk.isSubwalk_iff_support_isInfix]
  have ht : (p.trimStart h).walk.support = p.walk.support.tail := by
    simp [trimStart, Walk.support_tail_of_not_nil p.walk h]
  rw [ht]
  exact (List.tail_suffix p.walk.support).isInfix

lemma isSubwalk_trimFinish_incidences (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimFinish h).walk.IsSubwalk p.walk := by
  rw [Walk.isSubwalk_iff_support_isInfix]
  have hdl : (p.trimFinish h).walk.support = p.walk.support.dropLast :=
    Walk.support_dropLast (p := p.walk) h
  rw [hdl]
  exact (List.dropLast_prefix p.walk.support).isInfix

lemma edges_trimStart_subset_incidences (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).edges ⊆ p.edges :=
  edges_of_isSubwalk (p.isSubwalk_trimStart_incidences h)

lemma edges_trimFinish_subset_incidences (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimFinish h).edges ⊆ p.edges :=
  edges_of_isSubwalk (p.isSubwalk_trimFinish_incidences h)

lemma PrefixEdgeFactor.prefixPath_edges_subset {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p a x) : F.prefixPath.edges ⊆ p.edges := by
  intro e he
  have : e ∈ F.preWalk.edges := by simpa [prefixPath, edges] using he
  exact mem_edges_iff.2 (by
    rw [F.edges_eq]
    exact List.mem_append.2 (Or.inl this))

lemma PrefixEdgeFactor.suffixPath_edges_subset {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p a x) : F.suffixPath.edges ⊆ p.edges := by
  intro e he
  have : e ∈ F.sufWalk.edges := by simpa [suffixPath, edges] using he
  exact mem_edges_iff.2 (by
    rw [F.edges_eq]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr this))))

/-- After prefix rotation, `a` is an endpoint of the new path. The
factorization already supplies `a ≠ finish`; no extra second-entry
edge is assumed. -/
lemma PrefixEdgeFactor.rotate_start_ne_finish' {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).start ≠ (F.rotate hyx).finish :=
  F.rotate_start_ne_finish hyx

end GraphPath

end Nikoghosyan
