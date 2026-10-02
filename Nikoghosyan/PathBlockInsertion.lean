/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.CycleIncidences

/-!
Whole-path insertion into an actual original path edge.

Given a genuine factorization `PrefixEdgeFactor p u v` at the original
dart `u—v` and an outside original block `q` whose support is disjoint
from `p`, together with original seams `u—q.start` and `q.finish—v`,
splice the prefix, the block, and the suffix. The result is a simple
original-edge path with the same start and finish as `p` and with
support `p.support ∪ q.support`. Nil prefix and nil suffix are allowed;
`q` may be a singleton.

The undirected edge identity is
`new.edges = p.edges.erase s(u,v) ∪ q.edges ∪ {s(u,q.start), s(q.finish,v)}`.
Disjointness of the spliced pieces is derived from the original factor
and the outside-block hypothesis; it is not an extra assumption on the
result. All new edges lie in `G`.

At a designated original set `A` with `q.support` disjoint from `A` and
with `u, v ∉ A`, every `A`-incident walk-edge is unchanged, so
`ProtectedAt` at the original `A` is preserved. If the inserted path
spans a prescribed cycle, the exact internal-2 / endpoint-1 bridge
applies to the result.

A supplied factorization is a legitimate operation input. The same
factor may be derived from the path successor of a non-terminal vertex
or from a strict walk index, reusing the PathRotation APIs. This module
does not assert that an appropriate edge or outside block exists on an
arbitrary path, and it does not close `prof:thm:protected`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

/-- Every `A`-incident edge of an original path whose support is disjoint
from `A` is impossible: both ends of a path edge lie on the path. -/
lemma AIncident_eq_empty_of_disjoint_support (q : GraphPath G) {A : Finset V}
    (hd : Disjoint q.support A) : q.AIncident A = ∅ := by
  ext e
  constructor
  · intro he
    obtain ⟨heE, ⟨b, hbA, hbe⟩⟩ := mem_AIncident_iff.1 he
    exact (disjoint_left.1 hd (mem_support_of_mem_edge heE hbe) hbA).elim
  · intro he
    exact (notMem_empty e he).elim

/-- Local splice-edge identity. Named to avoid colliding with
`GraphPath.edges_splice` from G2 `ProtectedIncidence`. -/
lemma edges_of_splice_block (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) :
    (p.splice q h hd).edges = p.edges ∪ q.edges ∪ {s(p.finish, q.start)} := by
  ext e
  simp [edges, splice, Walk.edges_append, Walk.edges_cons]

namespace PrefixEdgeFactor

variable {p : GraphPath G} {u v : V}

lemma prefixPath_support_subset (F : PrefixEdgeFactor p u v) :
    F.prefixPath.support ⊆ p.support := by
  rw [F.support_eq_union]
  exact subset_union_left

lemma suffixPath_support_subset (F : PrefixEdgeFactor p u v) :
    F.suffixPath.support ⊆ p.support := by
  rw [F.support_eq_union]
  exact subset_union_right

lemma u_mem_support (F : PrefixEdgeFactor p u v) : u ∈ p.support := by
  have : u ∈ F.prefixPath.support := by
    simpa [support_prefixPath] using List.mem_toFinset.2 F.a_mem_prefix
  exact F.prefixPath_support_subset this

lemma v_mem_support (F : PrefixEdgeFactor p u v) : v ∈ p.support := by
  have : v ∈ F.suffixPath.support := by
    simpa [support_suffixPath] using List.mem_toFinset.2 F.x_mem_suffix
  exact F.suffixPath_support_subset this

lemma not_nil (F : PrefixEdgeFactor p u v) : ¬ p.walk.Nil := by
  intro h
  have hsing := support_eq_singleton_of_nil p h
  have hu : u ∈ ({p.start} : Finset V) := by simpa [hsing] using F.u_mem_support
  have hv : v ∈ ({p.start} : Finset V) := by simpa [hsing] using F.v_mem_support
  exact F.a_ne_x ((mem_singleton.1 hu).trans (mem_singleton.1 hv).symm)

lemma two_le_card_support (F : PrefixEdgeFactor p u v) : 2 ≤ p.support.card :=
  (two_le_card_support_iff p).2 F.not_nil

/-- Outside-block disjointness of the prefix is inherited from disjointness
of the block from the original path. -/
lemma disjoint_prefixPath_of_outside (F : PrefixEdgeFactor p u v)
    {q : GraphPath G} (hd : Disjoint q.support p.support) :
    Disjoint F.prefixPath.support q.support :=
  Disjoint.mono_left F.prefixPath_support_subset hd.symm

lemma disjoint_suffixPath_of_outside (F : PrefixEdgeFactor p u v)
    {q : GraphPath G} (hd : Disjoint q.support p.support) :
    Disjoint F.suffixPath.support q.support :=
  Disjoint.mono_left F.suffixPath_support_subset hd.symm

lemma disjoint_prefix_union_block_suffix (F : PrefixEdgeFactor p u v)
    {q : GraphPath G} (hd : Disjoint q.support p.support) :
    Disjoint (F.prefixPath.support ∪ q.support) F.suffixPath.support :=
  disjoint_union_left.2
    ⟨F.disjoint_prefixPath_suffixPath, (F.disjoint_suffixPath_of_outside hd).symm⟩

lemma prefixPath_finish (F : PrefixEdgeFactor p u v) : F.prefixPath.finish = u :=
  rfl

lemma suffixPath_start (F : PrefixEdgeFactor p u v) : F.suffixPath.start = v :=
  rfl

/-- Prefix spliced to the outside block across the original seam `u—q.start`. -/
def insertMid (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support) (hs : G.Adj u q.start) : GraphPath G :=
  F.prefixPath.splice q hs (F.disjoint_prefixPath_of_outside hd)

lemma insertMid_start (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support) (hs : G.Adj u q.start) :
    (F.insertMid q hd hs).start = p.start :=
  rfl

lemma insertMid_finish (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support) (hs : G.Adj u q.start) :
    (F.insertMid q hd hs).finish = q.finish :=
  rfl

lemma insertMid_support (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support) (hs : G.Adj u q.start) :
    (F.insertMid q hd hs).support = F.prefixPath.support ∪ q.support :=
  support_splice F.prefixPath q hs (F.disjoint_prefixPath_of_outside hd)

lemma disjoint_insertMid_suffix (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support) (hs : G.Adj u q.start) :
    Disjoint (F.insertMid q hd hs).support F.suffixPath.support := by
  simpa [F.insertMid_support q hd hs] using F.disjoint_prefix_union_block_suffix hd

lemma insertMid_edges (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support) (hs : G.Adj u q.start) :
    (F.insertMid q hd hs).edges =
      F.prefixPath.edges ∪ q.edges ∪ {s(u, q.start)} := by
  simpa [insertMid, prefixPath] using
    edges_of_splice_block F.prefixPath q hs (F.disjoint_prefixPath_of_outside hd)

/-- Insert the outside block `q` into the original dart `u—v`, keeping the
old start and finish. -/
def insertBlock (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) : GraphPath G :=
  (F.insertMid q hd hs).splice F.suffixPath hf
    (F.disjoint_insertMid_suffix q hd hs)

lemma insertBlock_start (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    (F.insertBlock q hd hs hf).start = p.start :=
  rfl

lemma insertBlock_finish (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    (F.insertBlock q hd hs hf).finish = p.finish :=
  rfl

lemma insertBlock_start_ne_finish (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    (F.insertBlock q hd hs hf).start ≠ (F.insertBlock q hd hs hf).finish := by
  intro heq
  have : p.start = p.finish := by
    simpa [F.insertBlock_start q hd hs hf, F.insertBlock_finish q hd hs hf] using heq
  exact F.not_nil ((nil_iff_start_eq_finish p).2 this)

/-- Exact support identity: the inserted path uses every original vertex of
`p` and every vertex of the outside block. -/
theorem insertBlock_support (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    (F.insertBlock q hd hs hf).support = p.support ∪ q.support := by
  have hmid := support_splice (F.insertMid q hd hs) F.suffixPath hf
    (F.disjoint_insertMid_suffix q hd hs)
  simpa [insertBlock, F.insertMid_support q hd hs, F.support_eq_union,
    union_comm, union_assoc] using hmid

lemma block_support_subset_insertBlock (F : PrefixEdgeFactor p u v)
    (q : GraphPath G) (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    q.support ⊆ (F.insertBlock q hd hs hf).support := by
  rw [F.insertBlock_support q hd hs hf]
  exact subset_union_right

lemma insertBlock_edges_union (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    (F.insertBlock q hd hs hf).edges =
      (F.insertMid q hd hs).edges ∪ F.suffixPath.edges ∪ {s(q.finish, v)} := by
  simpa [insertBlock, suffixPath, F.insertMid_finish q hd hs] using
    edges_of_splice_block (F.insertMid q hd hs) F.suffixPath hf
      (F.disjoint_insertMid_suffix q hd hs)

/-- Exact undirected edge identity: drop the old dart `u—v`, keep every
other original edge of `p`, add the two original seams and every edge of
the outside block. No edge outside `G` is used. -/
theorem insertBlock_edges (F : PrefixEdgeFactor p u v) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    (F.insertBlock q hd hs hf).edges =
      p.edges.erase s(u, v) ∪ q.edges ∪ {s(u, q.start), s(q.finish, v)} := by
  have hpre : F.prefixPath.edges = F.preWalk.edges.toFinset := rfl
  have hsuf : F.suffixPath.edges = F.sufWalk.edges.toFinset := rfl
  rw [F.insertBlock_edges_union q hd hs hf, F.insertMid_edges q hd hs, hpre, hsuf,
    F.erase_old_eq]
  ext e
  simp [edges, mem_union, mem_insert, mem_erase, or_left_comm, or_assoc, or_comm]

lemma insertBlock_edges_subset_edgeSet (F : PrefixEdgeFactor p u v)
    (q : GraphPath G) (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) :
    ∀ e ∈ (F.insertBlock q hd hs hf).edges, e ∈ G.edgeSet :=
  edges_subset_edgeSet (F.insertBlock q hd hs hf)

lemma not_mem_old_of_outside_A {b : V} {A : Finset V}
    (hbA : b ∈ A) (huA : u ∉ A) (hvA : v ∉ A) :
    b ∉ (s(u, v) : Sym2 V) := by
  intro hb
  rcases Sym2.mem_iff.mp hb with h | h
  · exact huA (h ▸ hbA)
  · exact hvA (h ▸ hbA)

lemma not_mem_start_seam_of_A {b : V} {A : Finset V} {q : GraphPath G}
    (hAq : Disjoint q.support A) (hbA : b ∈ A) (huA : u ∉ A) :
    b ∉ (s(u, q.start) : Sym2 V) := by
  intro hb
  rcases Sym2.mem_iff.mp hb with h | h
  · exact huA (h ▸ hbA)
  · exact disjoint_left.1 hAq (h ▸ q.start_mem_support) hbA

lemma not_mem_finish_seam_of_A {b : V} {A : Finset V} {q : GraphPath G}
    (hAq : Disjoint q.support A) (hbA : b ∈ A) (hvA : v ∉ A) :
    b ∉ (s(q.finish, v) : Sym2 V) := by
  intro hb
  rcases Sym2.mem_iff.mp hb with h | h
  · exact disjoint_left.1 hAq (h ▸ q.finish_mem_support) hbA
  · exact hvA (h ▸ hbA)

lemma start_seam_not_AIncident {A : Finset V} {q : GraphPath G}
    (hAq : Disjoint q.support A) (huA : u ∉ A) :
    ¬ ∃ b ∈ A, b ∈ (s(u, q.start) : Sym2 V) := by
  rintro ⟨b, hbA, hbe⟩
  exact not_mem_start_seam_of_A hAq hbA huA hbe

lemma finish_seam_not_AIncident {A : Finset V} {q : GraphPath G}
    (hAq : Disjoint q.support A) (hvA : v ∉ A) :
    ¬ ∃ b ∈ A, b ∈ (s(q.finish, v) : Sym2 V) := by
  rintro ⟨b, hbA, hbe⟩
  exact not_mem_finish_seam_of_A hAq hbA hvA hbe

lemma old_not_AIncident {A : Finset V} (huA : u ∉ A) (hvA : v ∉ A) :
    ¬ ∃ b ∈ A, b ∈ (s(u, v) : Sym2 V) := by
  rintro ⟨b, hbA, hbe⟩
  exact not_mem_old_of_outside_A hbA huA hvA hbe

/-- At every vertex of original `A`, the incident walk-edge set is
unchanged. New seams and block edges meet no vertex of `A`. -/
theorem incidentEdges_insertBlock (F : PrefixEdgeFactor p u v)
    (q : GraphPath G) (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) {A : Finset V} {b : V}
    (hbA : b ∈ A) (huA : u ∉ A) (hvA : v ∉ A)
    (hAq : Disjoint q.support A) :
    (F.insertBlock q hd hs hf).incidentEdges b = p.incidentEdges b := by
  ext e
  simp only [mem_incidentEdges_iff, F.insertBlock_edges q hd hs hf, mem_union,
    mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hmem, hbe⟩
    rcases hmem with (h | hq) | hseam
    · exact ⟨h.2, hbe⟩
    · exact (disjoint_left.1 hAq (mem_support_of_mem_edge hq hbe) hbA).elim
    · rcases hseam with rfl | rfl
      · exact (not_mem_start_seam_of_A hAq hbA huA hbe).elim
      · exact (not_mem_finish_seam_of_A hAq hbA hvA hbe).elim
  · rintro ⟨hmem, hbe⟩
    refine ⟨Or.inl (Or.inl ⟨?_, hmem⟩), hbe⟩
    intro heq
    subst heq
    exact not_mem_old_of_outside_A hbA huA hvA hbe

/-- The `A`-incident edge set is exactly unchanged. The deleted dart and
both new seams meet no vertex of `A`, and the block contributes none. -/
theorem AIncident_insertBlock (F : PrefixEdgeFactor p u v)
    (q : GraphPath G) (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v) {A : Finset V}
    (huA : u ∉ A) (hvA : v ∉ A) (hAq : Disjoint q.support A) :
    (F.insertBlock q hd hs hf).AIncident A = p.AIncident A := by
  ext e
  simp only [mem_AIncident_iff, F.insertBlock_edges q hd hs hf, mem_union,
    mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hmem, hA⟩
    rcases hmem with (h | hq) | hseam
    · exact ⟨h.2, hA⟩
    · rcases hA with ⟨b, hbA, hbe⟩
      exact (disjoint_left.1 hAq (mem_support_of_mem_edge hq hbe) hbA).elim
    · rcases hseam with rfl | rfl
      · exact (start_seam_not_AIncident hAq huA hA).elim
      · exact (finish_seam_not_AIncident hAq hvA hA).elim
  · rintro ⟨hmem, hA⟩
    refine ⟨Or.inl (Or.inl ⟨?_, hmem⟩), hA⟩
    intro heq
    subst heq
    exact old_not_AIncident huA hvA hA

/-- If the old path's `A`-incidences are prescribed cycle edges, the
inserted path remains protected at the original set `A`. -/
theorem protectedAt_insertBlock (F : PrefixEdgeFactor p u v)
    (q : GraphPath G) (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v)
    {c : GraphCycle G} {A : Finset V}
    (huA : u ∉ A) (hvA : v ∉ A) (hAq : Disjoint q.support A)
    (hP : p.ProtectedAt c A) :
    (F.insertBlock q hd hs hf).ProtectedAt c A := by
  intro e he
  have he' : e ∈ p.AIncident A := by
    simpa [F.AIncident_insertBlock q hd hs hf huA hvA hAq] using he
  exact hP he'

/-- If the inserted path spans a prescribed original cycle, the exact
internal-2 / endpoint-1 protection bridge applies. Original-`A`
incidences are those of `p`. Protection is asserted only at the original
set `A`. -/
theorem protected_exact_of_insertBlock (F : PrefixEdgeFactor p u v)
    (q : GraphPath G) (hd : Disjoint q.support p.support)
    (hs : G.Adj u q.start) (hf : G.Adj q.finish v)
    (c : GraphCycle G) {A : Finset V}
    (hsup : (F.insertBlock q hd hs hf).support = c.support)
    (hA : A ⊆ (F.insertBlock q hd hs hf).support)
    (huA : u ∉ A) (hvA : v ∉ A) (hAq : Disjoint q.support A)
    (hP : p.ProtectedAt c A) :
    (F.insertBlock q hd hs hf).ProtectedAt c A ∧
      (F.insertBlock q hd hs hf).start = p.start ∧
        (F.insertBlock q hd hs hf).finish = p.finish ∧
          (∀ b ∈ A,
            (F.insertBlock q hd hs hf).incidentEdges b = p.incidentEdges b) ∧
            (∀ b ∈ A, b ≠ p.start → b ≠ p.finish →
              (F.insertBlock q hd hs hf).incidentEdges b =
                c.incidentEdges b) ∧
              (p.start ∈ A →
                ((F.insertBlock q hd hs hf).incidentEdges p.start).card = 1 ∧
                  (F.insertBlock q hd hs hf).incidentEdges p.start ⊆
                    c.edges) ∧
                (p.finish ∈ A →
                  ((F.insertBlock q hd hs hf).incidentEdges p.finish).card = 1 ∧
                    (F.insertBlock q hd hs hf).incidentEdges p.finish ⊆
                      c.edges) := by
  set r := F.insertBlock q hd hs hf
  have hrProt : r.ProtectedAt c A :=
    F.protectedAt_insertBlock q hd hs hf huA hvA hAq hP
  have hst : r.start = p.start := F.insertBlock_start q hd hs hf
  have hfin : r.finish = p.finish := F.insertBlock_finish q hd hs hf
  have hinc : ∀ b ∈ A, r.incidentEdges b = p.incidentEdges b :=
    fun b hbA => F.incidentEdges_insertBlock q hd hs hf hbA huA hvA hAq
  have hinter : ∀ b ∈ A, b ≠ p.start → b ≠ p.finish →
      r.incidentEdges b = c.incidentEdges b := by
    intro b hbA hs hf
    have hs' : b ≠ r.start := by simpa [hst] using hs
    have hf' : b ≠ r.finish := by simpa [hfin] using hf
    have : r.incidentEdges b = c.incidentEdges b :=
      incidentEdges_eq_cycle_of_internal_protected r c hsup hA hrProt hbA hs' hf'
    exact this
  refine ⟨hrProt, hst, hfin, hinc, hinter, ?_, ?_⟩
  · intro hsA
    simpa [hst] using
      incidentEdges_card_endpoint_protected r c hsup hA hrProt hsA (Or.inl hst)
  · intro hfA
    simpa [hfin] using
      incidentEdges_card_endpoint_protected r c hsup hA hrProt hfA (Or.inr hfin)

end PrefixEdgeFactor

/-- Apply insertion at the actual outgoing dart of a non-terminal vertex. -/
theorem exists_insertBlock_of_pathSucc (p : GraphPath G) {a : V}
    (ha : a ∈ p.support) (hne : a ≠ p.finish) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj a q.start) (hf : G.Adj q.finish (p.pathSucc ha hne)) :
    ∃ r : GraphPath G,
      r.start = p.start ∧
        r.finish = p.finish ∧
          r.support = p.support ∪ q.support ∧
            r.edges =
              p.edges.erase s(a, p.pathSucc ha hne) ∪ q.edges ∪
                {s(a, q.start), s(q.finish, p.pathSucc ha hne)} := by
  obtain ⟨F, _⟩ := p.exists_factor_of_pathSucc ha hne
  refine ⟨F.insertBlock q hd hs hf, F.insertBlock_start q hd hs hf,
    F.insertBlock_finish q hd hs hf, F.insertBlock_support q hd hs hf,
    F.insertBlock_edges q hd hs hf⟩

/-- Apply insertion at a strict walk index `i < p.walk.length`. Capped
indices `≥ length` are excluded. -/
theorem exists_insertBlock_of_index (p : GraphPath G) {i : ℕ}
    (hi : i < p.walk.length) (q : GraphPath G)
    (hd : Disjoint q.support p.support)
    (hs : G.Adj (p.walk.getVert i) q.start)
    (hf : G.Adj q.finish (p.walk.getVert (i + 1))) :
    ∃ r : GraphPath G,
      r.start = p.start ∧
        r.finish = p.finish ∧
          r.support = p.support ∪ q.support ∧
            r.edges =
              p.edges.erase s(p.walk.getVert i, p.walk.getVert (i + 1)) ∪
                q.edges ∪
                  {s(p.walk.getVert i, q.start),
                    s(q.finish, p.walk.getVert (i + 1))} := by
  obtain ⟨F, _⟩ := p.exists_factorAtIndex hi
  refine ⟨F.insertBlock q hd hs hf, F.insertBlock_start q hd hs hf,
    F.insertBlock_finish q hd hs hf, F.insertBlock_support q hd hs hf,
    F.insertBlock_edges q hd hs hf⟩

end GraphPath

end Nikoghosyan
