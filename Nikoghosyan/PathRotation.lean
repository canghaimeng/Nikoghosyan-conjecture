/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.PathCoverCuts

/-!
Actual prefix rotation of an original-edge path, with exact undirected
edge-set identity and incidence accounting at a designated vertex set.

Given a genuine factorization
`p.walk = ru.append (Walk.cons oldAdj rv)`
with `ru` from `p.start = y` to `a`, original edge `a—x`, and `rv` from
`x` to `p.finish = z`, together with an original edge `y—x`, reverse the
prefix and splice it to the suffix across `y—x`. The result is a simple
original-edge path from `a` to `z` with the same vertex support as `p`.

The undirected edge identity is
`rotated.edges = p.edges.erase s(a,x) ∪ {s(y,x)}`.
A supplied factorization is a legitimate operation input. Derivation
from a strict walk index `i < p.walk.length`, or from the path successor
of a non-terminal vertex, is exported separately. `getVert` for indices
beyond `p.walk.length` is capped and is not used to claim injectivity.

This module does not construct a spanning `A`–`A` path and does not
close `prof:thm:protected` or `prof:cor:insertion`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

/-- Undirected original edges of a path, as a finset. -/
def edges (p : GraphPath G) : Finset (Sym2 V) :=
  p.walk.edges.toFinset

lemma mem_edges_iff {p : GraphPath G} {e : Sym2 V} :
    e ∈ p.edges ↔ e ∈ p.walk.edges := by
  simp [edges]

lemma edges_subset_edgeSet (p : GraphPath G) : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
  intro e he
  exact p.walk.edges_subset_edgeSet (mem_edges_iff.1 he)

/-- Path edges incident to a designated original vertex. -/
def incidentEdges (p : GraphPath G) (b : V) : Finset (Sym2 V) :=
  p.edges.filter fun e => b ∈ e

lemma mem_incidentEdges_iff {p : GraphPath G} {b : V} {e : Sym2 V} :
    e ∈ p.incidentEdges b ↔ e ∈ p.edges ∧ b ∈ e := by
  simp [incidentEdges]

/-- Path edges that meet a designated original vertex set `A`. -/
def AIncident (p : GraphPath G) (A : Finset V) : Finset (Sym2 V) :=
  p.edges.filter fun e => ∃ b ∈ A, b ∈ e

lemma mem_AIncident_iff {p : GraphPath G} {A : Finset V} {e : Sym2 V} :
    e ∈ p.AIncident A ↔ e ∈ p.edges ∧ ∃ b ∈ A, b ∈ e := by
  simp [AIncident]

/-- Every `A`-incident path edge is an edge of the prescribed original cycle. -/
def ProtectedAt (p : GraphPath G) (c : GraphCycle G) (A : Finset V) : Prop :=
  p.AIncident A ⊆ c.walk.edges.toFinset

/-- Genuine one-edge factorization of an original path at the directed
dart `a → x`. The prefix may be nil (`y = a`); the suffix may be nil
(`x = z`). -/
structure PrefixEdgeFactor (p : GraphPath G) (a x : V) where
  preWalk : G.Walk p.start a
  sufWalk : G.Walk x p.finish
  oldAdj : G.Adj a x
  factor : p.walk = preWalk.append (Walk.cons oldAdj sufWalk)

namespace PrefixEdgeFactor

variable {p : GraphPath G} {a x : V}

lemma prefix_isPath (F : PrefixEdgeFactor p a x) : F.preWalk.IsPath :=
  Walk.IsPath.of_append_left (q := Walk.cons F.oldAdj F.sufWalk)
    (by simpa [F.factor] using p.isPath)

lemma suffix_cons_isPath (F : PrefixEdgeFactor p a x) :
    (Walk.cons F.oldAdj F.sufWalk).IsPath :=
  Walk.IsPath.of_append_right (p := F.preWalk)
    (by simpa [F.factor] using p.isPath)

lemma suffix_isPath (F : PrefixEdgeFactor p a x) : F.sufWalk.IsPath :=
  ((Walk.cons_isPath_iff F.oldAdj F.sufWalk).1 F.suffix_cons_isPath).1

lemma a_not_mem_suffix_support (F : PrefixEdgeFactor p a x) :
    a ∉ F.sufWalk.support :=
  ((Walk.cons_isPath_iff F.oldAdj F.sufWalk).1 F.suffix_cons_isPath).2

lemma support_append_eq (F : PrefixEdgeFactor p a x) :
    p.walk.support = F.preWalk.support ++ F.sufWalk.support := by
  simp [F.factor, Walk.support_append, Walk.support_cons]

lemma nodup_prefix_append_suffix (F : PrefixEdgeFactor p a x) :
    (F.preWalk.support ++ F.sufWalk.support).Nodup := by
  simpa [F.support_append_eq] using p.support_nodup

lemma disjoint_prefix_suffix_list (F : PrefixEdgeFactor p a x)
    {v : V} (hvP : v ∈ F.preWalk.support) : v ∉ F.sufWalk.support := by
  intro hvS
  exact (List.nodup_append.1 F.nodup_prefix_append_suffix).2.2 v hvP v hvS rfl

lemma disjoint_prefix_suffix (F : PrefixEdgeFactor p a x) :
    Disjoint F.preWalk.support.toFinset F.sufWalk.support.toFinset := by
  refine disjoint_left.2 ?_
  intro v hvP hvS
  exact F.disjoint_prefix_suffix_list (List.mem_toFinset.1 hvP)
    (List.mem_toFinset.1 hvS)

lemma x_not_mem_prefix_support (F : PrefixEdgeFactor p a x) :
    x ∉ F.preWalk.support := by
  intro hx
  exact F.disjoint_prefix_suffix_list hx (Walk.start_mem_support F.sufWalk)

lemma start_mem_prefix (F : PrefixEdgeFactor p a x) :
    p.start ∈ F.preWalk.support :=
  Walk.start_mem_support F.preWalk

lemma a_mem_prefix (F : PrefixEdgeFactor p a x) :
    a ∈ F.preWalk.support :=
  Walk.end_mem_support F.preWalk

lemma x_mem_suffix (F : PrefixEdgeFactor p a x) :
    x ∈ F.sufWalk.support :=
  Walk.start_mem_support F.sufWalk

lemma finish_mem_suffix (F : PrefixEdgeFactor p a x) :
    p.finish ∈ F.sufWalk.support :=
  Walk.end_mem_support F.sufWalk

lemma prefix_nil_iff (F : PrefixEdgeFactor p a x) :
    F.preWalk.Nil ↔ p.start = a :=
  F.prefix_isPath.nil_iff_eq

lemma a_ne_start_of_prefix_not_nil (F : PrefixEdgeFactor p a x)
    (h : ¬ F.preWalk.Nil) : a ≠ p.start := by
  intro heq
  exact h ((F.prefix_nil_iff).2 heq.symm)

lemma a_ne_finish (F : PrefixEdgeFactor p a x) : a ≠ p.finish := by
  intro h
  subst h
  exact F.a_not_mem_suffix_support F.finish_mem_suffix

lemma a_ne_x (F : PrefixEdgeFactor p a x) : a ≠ x :=
  F.oldAdj.ne

lemma start_ne_x (F : PrefixEdgeFactor p a x) : p.start ≠ x := by
  intro h
  subst h
  exact F.x_not_mem_prefix_support F.start_mem_prefix

/-- The prefix as an original `GraphPath` from `y` to `a`. -/
def prefixPath (F : PrefixEdgeFactor p a x) : GraphPath G where
  start := p.start
  finish := a
  walk := F.preWalk
  isPath := F.prefix_isPath

/-- The suffix as an original `GraphPath` from `x` to `z`. -/
def suffixPath (F : PrefixEdgeFactor p a x) : GraphPath G where
  start := x
  finish := p.finish
  walk := F.sufWalk
  isPath := F.suffix_isPath

lemma support_prefixPath (F : PrefixEdgeFactor p a x) :
    F.prefixPath.support = F.preWalk.support.toFinset :=
  rfl

lemma support_suffixPath (F : PrefixEdgeFactor p a x) :
    F.suffixPath.support = F.sufWalk.support.toFinset :=
  rfl

lemma disjoint_prefixPath_suffixPath (F : PrefixEdgeFactor p a x) :
    Disjoint F.prefixPath.support F.suffixPath.support := by
  simpa [support_prefixPath, support_suffixPath] using F.disjoint_prefix_suffix

lemma support_eq_union (F : PrefixEdgeFactor p a x) :
    p.support = F.prefixPath.support ∪ F.suffixPath.support := by
  simp [GraphPath.support, prefixPath, suffixPath, F.support_append_eq,
    List.toFinset_append]

lemma edges_eq (F : PrefixEdgeFactor p a x) :
    p.walk.edges = F.preWalk.edges ++ s(a, x) :: F.sufWalk.edges := by
  simp [F.factor, Walk.edges_append, Walk.edges_cons]

lemma edges_nodup (F : PrefixEdgeFactor p a x) :
    (F.preWalk.edges ++ s(a, x) :: F.sufWalk.edges).Nodup := by
  simpa [F.edges_eq] using p.isPath.isTrail.edges_nodup

lemma old_not_mem_prefix_edges (F : PrefixEdgeFactor p a x) :
    s(a, x) ∉ F.preWalk.edges := by
  have h := List.nodup_append.1 F.edges_nodup
  intro he
  exact h.2.2 _ he _ (by simp) rfl

lemma old_not_mem_suffix_edges (F : PrefixEdgeFactor p a x) :
    s(a, x) ∉ F.sufWalk.edges := by
  have h := List.nodup_append.1 F.edges_nodup
  have hcons := List.nodup_cons.1 h.2.1
  exact hcons.1

lemma old_mem_edges (F : PrefixEdgeFactor p a x) :
    s(a, x) ∈ p.edges := by
  simp [edges, F.edges_eq]

lemma edges_toFinset_eq (F : PrefixEdgeFactor p a x) :
    p.edges = F.preWalk.edges.toFinset ∪ insert s(a, x) F.sufWalk.edges.toFinset := by
  simp [edges, F.edges_eq, List.toFinset_append, List.toFinset_cons]

lemma erase_old_eq (F : PrefixEdgeFactor p a x) :
    p.edges.erase s(a, x) =
      F.preWalk.edges.toFinset ∪ F.sufWalk.edges.toFinset := by
  have hP : s(a, x) ∉ F.preWalk.edges.toFinset := by
    simpa using F.old_not_mem_prefix_edges
  have hS : s(a, x) ∉ F.sufWalk.edges.toFinset := by
    simpa using F.old_not_mem_suffix_edges
  rw [F.edges_toFinset_eq, erase_union_distrib, erase_insert hS, erase_eq_of_notMem hP]

/-- Reverse the prefix and splice it to the suffix across the original
edge `y—x`. Nil prefix reconstructs `p` (the added edge equals the
deleted edge). Nil suffix is allowed. -/
def rotate (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    GraphPath G :=
  F.prefixPath.reverse.splice F.suffixPath hyx
    (by simpa [GraphPath.support_reverse] using F.disjoint_prefixPath_suffixPath)

lemma rotate_start (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).start = a :=
  rfl

lemma rotate_finish (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).finish = p.finish :=
  rfl

lemma rotate_support (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).support = p.support := by
  simp [rotate, splice, GraphPath.support, GraphPath.reverse, prefixPath, suffixPath,
    Walk.support_append, Walk.support_cons, Walk.support_reverse, F.support_append_eq,
    List.toFinset_append, List.toFinset_reverse, union_comm]

lemma rotate_walk_eq (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).walk =
      F.preWalk.reverse.append (Walk.cons hyx F.sufWalk) :=
  rfl

lemma rotate_edges_list (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).walk.edges =
      F.preWalk.reverse.edges ++ s(p.start, x) :: F.sufWalk.edges := by
  simp [rotate, splice, prefixPath, suffixPath, GraphPath.reverse,
    Walk.edges_append, Walk.edges_cons]

/-- Exact undirected edge identity: the rotated path drops the old dart
`a—x` and gains the original chord `y—x`. No edge outside `G` is used. -/
theorem rotate_edges (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).edges = p.edges.erase s(a, x) ∪ {s(p.start, x)} := by
  have hrev : F.preWalk.reverse.edges.toFinset = F.preWalk.edges.toFinset := by
    simp [Walk.edges_reverse, List.toFinset_reverse]
  have hrot :
      (F.rotate hyx).edges =
        F.preWalk.edges.toFinset ∪ insert s(p.start, x) F.sufWalk.edges.toFinset := by
    simp [edges, F.rotate_edges_list, List.toFinset_append, List.toFinset_cons, hrev]
  rw [hrot, F.erase_old_eq, insert_eq]
  simp [union_comm, union_left_comm, union_assoc]

lemma rotate_edges_subset_edgeSet (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) :
    ∀ e ∈ (F.rotate hyx).edges, e ∈ G.edgeSet :=
  edges_subset_edgeSet (F.rotate hyx)

lemma new_edge_mem_rotate (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    s(p.start, x) ∈ (F.rotate hyx).edges := by
  simp [F.rotate_edges]

lemma old_not_mem_rotate_of_ne (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) (hne : s(a, x) ≠ s(p.start, x)) :
    s(a, x) ∉ (F.rotate hyx).edges := by
  simp [F.rotate_edges, hne, F.old_not_mem_prefix_edges, F.old_not_mem_suffix_edges]

/-! ### Incidence accounting at an original designated set `A` -/

lemma not_mem_old_of_ne {b : V} (F : PrefixEdgeFactor p a x)
    (hba : b ≠ a) (hbx : b ≠ x) : b ∉ (s(a, x) : Sym2 V) := by
  intro hb
  rcases Sym2.mem_iff.mp hb with h | h
  · exact hba h
  · exact hbx h

lemma not_mem_new_of_ne {b : V} (F : PrefixEdgeFactor p a x)
    (hby : b ≠ p.start) (hbx : b ≠ x) : b ∉ (s(p.start, x) : Sym2 V) := by
  intro hb
  rcases Sym2.mem_iff.mp hb with h | h
  · exact hby h
  · exact hbx h

/-- At every vertex of `A` other than `a`, the incident path-edge set is
unchanged. The hypotheses `a ∈ A` and `y, x ∉ A` force `b ≠ y` and
`b ≠ x` automatically. -/
theorem incidentEdges_rotate_of_mem_A (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) {A : Finset V} {b : V}
    (hbA : b ∈ A) (_haA : a ∈ A) (hyA : p.start ∉ A) (hxA : x ∉ A)
    (hba : b ≠ a) :
    (F.rotate hyx).incidentEdges b = p.incidentEdges b := by
  have hby : b ≠ p.start := fun h => hyA (h ▸ hbA)
  have hbx : b ≠ x := fun h => hxA (h ▸ hbA)
  ext e
  simp only [mem_incidentEdges_iff, F.rotate_edges, mem_union, mem_erase, mem_singleton]
  constructor
  · rintro ⟨hmem, hbe⟩
    rcases hmem with h | rfl
    · exact ⟨h.2, hbe⟩
    · exact (F.not_mem_new_of_ne hby hbx hbe).elim
  · rintro ⟨hmem, hbe⟩
    refine ⟨Or.inl ⟨?_, hmem⟩, hbe⟩
    intro heq
    subst heq
    exact F.not_mem_old_of_ne hba hbx hbe

/-- At `a` the only change is losing the old dart `a—x`. The new chord
`y—x` has no end in `A`, so it is not incident to `a`. -/
theorem incidentEdges_rotate_at_a (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) {A : Finset V}
    (haA : a ∈ A) (hyA : p.start ∉ A) (_hxA : x ∉ A) :
    (F.rotate hyx).incidentEdges a = p.incidentEdges a \ {s(a, x)} := by
  have hay : a ≠ p.start := fun h => hyA (h ▸ haA)
  have hax : a ≠ x := F.a_ne_x
  ext e
  simp only [mem_incidentEdges_iff, F.rotate_edges, mem_sdiff, mem_union, mem_erase,
    mem_singleton]
  constructor
  · rintro ⟨hmem, hae⟩
    rcases hmem with h | rfl
    · exact ⟨⟨h.2, hae⟩, h.1⟩
    · exact (F.not_mem_new_of_ne hay hax hae).elim
  · rintro ⟨⟨hmem, hae⟩, hne⟩
    exact ⟨Or.inl ⟨hne, hmem⟩, hae⟩

lemma new_not_AIncident (F : PrefixEdgeFactor p a x) {A : Finset V}
    (hyA : p.start ∉ A) (hxA : x ∉ A) :
    ¬ ∃ b ∈ A, b ∈ (s(p.start, x) : Sym2 V) := by
  rintro ⟨b, hbA, hbe⟩
  rcases Sym2.mem_iff.mp hbe with h | h
  · exact hyA (h ▸ hbA)
  · exact hxA (h ▸ hbA)

/-- The `A`-incident edge set after rotation is the old `A`-incident set
with `s(a,x)` removed. The new chord meets no vertex of `A`. -/
theorem AIncident_rotate (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) {A : Finset V}
    (_haA : a ∈ A) (hyA : p.start ∉ A) (hxA : x ∉ A) :
    (F.rotate hyx).AIncident A = p.AIncident A \ {s(a, x)} := by
  ext e
  simp only [mem_AIncident_iff, F.rotate_edges, mem_sdiff, mem_union, mem_erase,
    mem_singleton]
  constructor
  · rintro ⟨hmem, ⟨b, hbA, hbe⟩⟩
    rcases hmem with h | rfl
    · exact ⟨⟨h.2, ⟨b, hbA, hbe⟩⟩, h.1⟩
    · exact (F.new_not_AIncident hyA hxA ⟨b, hbA, hbe⟩).elim
  · rintro ⟨⟨hmem, hA⟩, hne⟩
    exact ⟨Or.inl ⟨hne, hmem⟩, hA⟩

/-- If the old path's `A`-incidences are prescribed cycle edges, the
rotated path remains protected at the original set `A`. Protection is
not claimed at any enlarged set containing the old `Y`-endpoint. -/
theorem protectedAt_rotate (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) {c : GraphCycle G} {A : Finset V}
    (haA : a ∈ A) (hyA : p.start ∉ A) (hxA : x ∉ A)
    (hP : p.ProtectedAt c A) :
    (F.rotate hyx).ProtectedAt c A := by
  intro e he
  have he' : e ∈ p.AIncident A \ {s(a, x)} := by
    simpa [F.AIncident_rotate hyx haA hyA hxA] using he
  exact hP (mem_sdiff.1 he').1

lemma rotate_start_mem_A {A : Finset V} (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) (haA : a ∈ A) :
    (F.rotate hyx).start ∈ A := by
  simpa [F.rotate_start] using haA

lemma rotate_finish_eq (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x) :
    (F.rotate hyx).finish = p.finish :=
  F.rotate_finish hyx

/-- Internal status of `a` on the original path: a non-nil prefix makes
`a` distinct from the start, and disjointness of prefix/suffix makes `a`
distinct from the finish. -/
lemma a_internal_of_prefix_not_nil (F : PrefixEdgeFactor p a x)
    (h : ¬ F.preWalk.Nil) :
    a ≠ p.start ∧ a ≠ p.finish :=
  ⟨F.a_ne_start_of_prefix_not_nil h, F.a_ne_finish⟩

lemma rotate_start_ne_finish (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) :
    (F.rotate hyx).start ≠ (F.rotate hyx).finish := by
  simpa [F.rotate_start, F.rotate_finish] using F.a_ne_finish

end PrefixEdgeFactor

/-! ### Deriving a factorization from a path successor or a strict index -/

/-- The original path-successor of a non-terminal vertex: the second
vertex of `dropUntil a`. This is the head of the unique outgoing dart
at `a` on `p`. -/
def pathSucc (p : GraphPath G) {a : V} (ha : a ∈ p.support) (hne : a ≠ p.finish) : V :=
  (p.dropUntil ha).walk.snd

lemma dropUntil_not_nil (p : GraphPath G) {a : V} (ha : a ∈ p.support)
    (hne : a ≠ p.finish) : ¬ (p.dropUntil ha).walk.Nil := by
  intro h
  exact hne ((dropUntil_nil_iff p ha).1 h)

lemma exists_cons_dropUntil (p : GraphPath G) {a : V} (ha : a ∈ p.support)
    (hne : a ≠ p.finish) :
    ∃ (h : G.Adj a (p.pathSucc ha hne)) (q : G.Walk (p.pathSucc ha hne) p.finish),
      (p.dropUntil ha).walk = Walk.cons h q := by
  have hnil := p.dropUntil_not_nil ha hne
  obtain ⟨w, hadj, q, hcons⟩ := (Walk.not_nil_iff).1 hnil
  have hw : w = p.pathSucc ha hne := by
    simp [pathSucc, hcons, Walk.snd]
  subst hw
  exact ⟨hadj, q, hcons⟩

/-- Derive a factorization from the actual outgoing dart at a
non-terminal vertex of `p`. -/
theorem exists_factor_of_pathSucc (p : GraphPath G) {a : V} (ha : a ∈ p.support)
    (hne : a ≠ p.finish) :
    ∃ F : PrefixEdgeFactor p a (p.pathSucc ha hne), True := by
  obtain ⟨hadj, q, hcons⟩ := p.exists_cons_dropUntil ha hne
  have hx := mem_walk_support (p := p) (x := a)
  refine ⟨⟨p.walk.takeUntil a (hx.1 ha), q, hadj, ?_⟩, trivial⟩
  have hspec := Walk.take_spec p.walk (hx.1 ha)
  have hdrop :
      (p.dropUntil ha).walk = p.walk.dropUntil a (hx.1 ha) := rfl
  rw [← hdrop, hcons] at hspec
  exact hspec.symm

/-- On an original path, `getVert` is injective on `0, …, length`.
Indices `≥ length` are capped at the finish and must not be used to
claim injectivity. -/
lemma getVert_injective_of_le_length (p : GraphPath G) {i j : ℕ}
    (hi : i ≤ p.walk.length) (hj : j ≤ p.walk.length)
    (heq : p.walk.getVert i = p.walk.getVert j) : i = j := by
  have hi' : i < p.walk.support.length := by
    rw [Walk.length_support]
    omega
  have hj' : j < p.walk.support.length := by
    rw [Walk.length_support]
    omega
  have hiE := Walk.getVert_eq_support_getElem p.walk hi
  have hjE := Walk.getVert_eq_support_getElem p.walk hj
  have hinj := (Walk.isPath_iff_injective_get_support p.walk).1 p.isPath
  have : p.walk.support.get ⟨i, hi'⟩ = p.walk.support.get ⟨j, hj'⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem, ← hiE, ← hjE, heq]
  exact congrArg Fin.val (hinj this)

lemma getVert_ne_finish_of_lt (p : GraphPath G) {i : ℕ}
    (hi : i < p.walk.length) : p.walk.getVert i ≠ p.finish := by
  intro h
  have hfin : p.walk.getVert p.walk.length = p.finish := Walk.getVert_length p.walk
  have : i = p.walk.length :=
    p.getVert_injective_of_le_length (le_of_lt hi) le_rfl (h.trans hfin.symm)
  omega

lemma idxOf_getVert (p : GraphPath G) {i : ℕ} (hi : i ≤ p.walk.length) :
    p.walk.support.idxOf (p.walk.getVert i) = i := by
  have hlt : i < p.walk.support.length := by
    rw [Walk.length_support]
    omega
  have hget : p.walk.support.get ⟨i, hlt⟩ = p.walk.getVert i := by
    simp [List.get_eq_getElem, Walk.getVert_eq_support_getElem p.walk hi]
  rw [← hget]
  exact List.get_idxOf p.support_nodup ⟨i, hlt⟩

lemma getVert_mem_path_support (p : GraphPath G) (i : ℕ) :
    p.walk.getVert i ∈ p.support :=
  List.mem_toFinset.2 (Walk.getVert_mem_support p.walk i)

/-- Derive a factorization from a strict index `i < p.walk.length`.
The outgoing dart is the actual consecutive pair
`(getVert i, getVert (i+1))`. Capped indices `≥ length` are excluded. -/
theorem exists_factorAtIndex (p : GraphPath G) {i : ℕ} (hi : i < p.walk.length) :
    ∃ F : PrefixEdgeFactor p (p.walk.getVert i) (p.walk.getVert (i + 1)), True := by
  set a := p.walk.getVert i
  have ha : a ∈ p.support := p.getVert_mem_path_support i
  have hne : a ≠ p.finish := p.getVert_ne_finish_of_lt hi
  obtain ⟨F, _⟩ := p.exists_factor_of_pathSucc ha hne
  have hsnd : p.pathSucc ha hne = p.walk.getVert (i + 1) := by
    have hx := mem_walk_support (p := p) (x := a)
    have hspec := Walk.take_spec p.walk (hx.1 ha)
    have hlen : (p.walk.takeUntil a (hx.1 ha)).length = i := by
      rw [Walk.length_takeUntil]
      exact p.idxOf_getVert (le_of_lt hi)
    have happ := Walk.getVert_append (p.walk.takeUntil a (hx.1 ha))
      (p.walk.dropUntil a (hx.1 ha)) (i + 1)
    rw [hspec] at happ
    have hnot : ¬ i + 1 < (p.walk.takeUntil a (hx.1 ha)).length := by omega
    rw [ite_eq_right (by exact hnot)] at happ
    have hsub : i + 1 - (p.walk.takeUntil a (hx.1 ha)).length = 1 := by omega
    rw [hsub] at happ
    simpa [pathSucc, dropUntil, Walk.snd] using happ.symm
  refine ⟨?_, trivial⟩
  convert F
  exact hsnd.symm

/-- If an undirected edge of `p` is presented together with the actual
oriented index at which it occurs, the corresponding factorization
exists. The undirected identity `s(u,v) = s(v,u)` does not by itself
orient the dart: a swapped pair is a different index. -/
theorem exists_factor_of_getVert_edge (p : GraphPath G) {i : ℕ}
    (hi : i < p.walk.length) :
    ∃ F : PrefixEdgeFactor p (p.walk.getVert i) (p.walk.getVert (i + 1)),
      s(p.walk.getVert i, p.walk.getVert (i + 1)) ∈ p.edges := by
  obtain ⟨F, _⟩ := p.exists_factorAtIndex hi
  refine ⟨F, ?_⟩
  simpa using F.old_mem_edges

/-! ### Reorient and apply the same rotation -/

/-- The reverse path carries a corresponding factorization of the
opposite dart `x → a`, with prefix the reversed suffix and suffix the
reversed prefix. Applying `rotate` to this factorization is the
reorientation-then-rotate operation; the second designated `A`-vertex
is an input of that factorization, not an assumed distinctness on an
arbitrary path. -/
def reverseFactor {p : GraphPath G} {a x : V} (F : PrefixEdgeFactor p a x) :
    PrefixEdgeFactor p.reverse x a where
  preWalk := F.sufWalk.reverse
  sufWalk := F.preWalk.reverse
  oldAdj := F.oldAdj.symm
  factor := by
    change p.walk.reverse = _
    rw [F.factor, Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc,
      Walk.cons_nil_append]
    rfl

lemma reverseFactor_rotate {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p a x) (hxy : G.Adj p.finish a) :
    ((reverseFactor F).rotate (by simpa [GraphPath.reverse] using hxy)).start = x ∧
      ((reverseFactor F).rotate (by simpa [GraphPath.reverse] using hxy)).finish = p.start ∧
        ((reverseFactor F).rotate (by simpa [GraphPath.reverse] using hxy)).support =
          p.support := by
  refine ⟨rfl, rfl, ?_⟩
  simpa [GraphPath.support_reverse] using
    (reverseFactor F).rotate_support (by simpa [GraphPath.reverse] using hxy)

/-- Reorient `p` and rotate a factorization of the reverse. This is the
generic operation applied twice; it does not assume that a second
`A`-vertex exists on an arbitrary path. -/
def rotateAfterReorient {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p.reverse a x) (hyx : G.Adj p.finish x) :
    GraphPath G :=
  F.rotate (by simpa [GraphPath.reverse] using hyx)

lemma rotateAfterReorient_start {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p.reverse a x) (hyx : G.Adj p.finish x) :
    (rotateAfterReorient F hyx).start = a :=
  F.rotate_start _

lemma rotateAfterReorient_finish {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p.reverse a x) (hyx : G.Adj p.finish x) :
    (rotateAfterReorient F hyx).finish = p.start := by
  rw [rotateAfterReorient]
  exact F.rotate_finish (by simpa [GraphPath.reverse] using hyx)

lemma rotateAfterReorient_support {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p.reverse a x) (hyx : G.Adj p.finish x) :
    (rotateAfterReorient F hyx).support = p.support := by
  rw [rotateAfterReorient]
  simpa [GraphPath.support_reverse] using
    F.rotate_support (by simpa [GraphPath.reverse] using hyx)

theorem rotateAfterReorient_edges {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p.reverse a x) (hyx : G.Adj p.finish x) :
    (rotateAfterReorient F hyx).edges =
      p.edges.erase s(a, x) ∪ {s(p.finish, x)} := by
  rw [rotateAfterReorient]
  have h := F.rotate_edges (by simpa [GraphPath.reverse] using hyx)
  have hedges : p.reverse.edges = p.edges := by
    simp [edges, GraphPath.reverse, Walk.edges_reverse, List.toFinset_reverse]
  rw [h, hedges]
  rfl

end GraphPath

end Nikoghosyan
