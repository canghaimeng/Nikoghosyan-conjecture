/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProtectedIncidence

/-!
# Full-cycle pieces after deleting two incoming A-seams

Open a prescribed original cycle, presented as a spanning original path `p`
with original closing edge `p.finish—p.start`, at a vertex `u ≠ p.start`.
The result starts at `u` and ends at the predecessor of `u` along `p`.
Splitting that path at a second vertex `v` by `trimFinish (takeUntil v)`
and `dropUntil v` yields two original paths whose supports are disjoint
and exhaust `p.support`.

Generic `switchStarts` on two leftover *runs* only spans their union.
These two pieces are the whole cycle after the two incoming seams are
removed; switching them produces a full-`U` path.

This module does not close `prof:thm:protected`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma takeUntil_not_nil_cyclePieces {p : GraphPath G} {x : V} (hx : x ∈ p.support)
    (hne : x ≠ p.start) : ¬ (p.takeUntil hx).walk.Nil := by
  intro h
  exact hne ((takeUntil_nil_iff p hx).1 h)

lemma takeUntil_dropUntil_length_add (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) :
    (p.takeUntil hx).walk.length + (p.dropUntil hx).walk.length =
      p.walk.length := by
  have hx' := mem_walk_support.1 hx
  have hT : (p.takeUntil hx).walk.length = p.walk.support.idxOf x := by
    simpa [takeUntil] using Walk.length_takeUntil p.walk hx'
  have hD : (p.dropUntil hx).walk.length =
      p.walk.length - p.walk.support.idxOf x := by
    simpa [dropUntil] using Walk.length_dropUntil p.walk hx'
  have hidx : p.walk.support.idxOf x ≤ p.walk.length := by
    have hlt : p.walk.support.idxOf x < p.walk.support.length :=
      List.idxOf_lt_length_of_mem hx'
    have hlen : p.walk.support.length = p.walk.length + 1 :=
      Walk.length_support p.walk
    omega
  omega

lemma mem_eq_of_mem_takeUntil_dropUntil (p : GraphPath G) {x y : V}
    (hx : x ∈ p.support) (hyT : y ∈ (p.takeUntil hx).support)
    (hyD : y ∈ (p.dropUntil hx).support) : y = x := by
  have hU := support_takeUntil_union_dropUntil p hx
  have hinter_mem :
      x ∈ (p.takeUntil hx).support ∩ (p.dropUntil hx).support :=
    mem_inter.2 ⟨(p.takeUntil hx).finish_mem_support,
      (p.dropUntil hx).start_mem_support⟩
  have hlen := takeUntil_dropUntil_length_add p hx
  have hcardT := card_support (p.takeUntil hx)
  have hcardD := card_support (p.dropUntil hx)
  have hcardP := card_support p
  have hunion := card_union_add_card_inter (p.takeUntil hx).support
    (p.dropUntil hx).support
  have hinter_card :
      ((p.takeUntil hx).support ∩ (p.dropUntil hx).support).card = 1 := by
    have : ((p.takeUntil hx).support ∪ (p.dropUntil hx).support).card =
        p.support.card := by rw [hU]
    omega
  obtain ⟨z, hz⟩ := card_eq_one.1 hinter_card
  have hzx : z = x := (mem_singleton.1 (by simpa [hz] using hinter_mem)).symm
  have hyI : y ∈ (p.takeUntil hx).support ∩ (p.dropUntil hx).support :=
    mem_inter.2 ⟨hyT, hyD⟩
  simpa [hz, hzx] using hyI

lemma disjoint_trimFinish_takeUntil_dropUntil (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hne : x ≠ p.start) :
    Disjoint
      ((p.takeUntil hx).trimFinish (takeUntil_not_nil_cyclePieces hx hne)).support
      (p.dropUntil hx).support := by
  refine disjoint_left.2 ?_
  intro y hyT hyD
  have hyT' : y ∈ (p.takeUntil hx).support.erase x := by
    simpa [support_trimFinish, takeUntil] using hyT
  have hyTsup : y ∈ (p.takeUntil hx).support := (mem_erase.1 hyT').2
  have hyne : y ≠ x := (mem_erase.1 hyT').1
  exact hyne (mem_eq_of_mem_takeUntil_dropUntil p hx hyTsup hyD)

lemma support_trimFinish_takeUntil_union_dropUntil (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hne : x ≠ p.start) :
    ((p.takeUntil hx).trimFinish (takeUntil_not_nil_cyclePieces hx hne)).support ∪
      (p.dropUntil hx).support = p.support := by
  have hU := support_takeUntil_union_dropUntil p hx
  have hxD : x ∈ (p.dropUntil hx).support := by
    simpa [dropUntil] using (p.dropUntil hx).start_mem_support
  rw [support_trimFinish, takeUntil]
  ext y
  constructor
  · intro hy
    have : y ∈ (p.takeUntil hx).support ∪ (p.dropUntil hx).support := by
      rcases mem_union.1 hy with h | h
      · exact mem_union.2 (Or.inl (mem_erase.1 h).2)
      · exact mem_union.2 (Or.inr h)
    simpa [hU] using this
  · intro hy
    have hy' : y ∈ (p.takeUntil hx).support ∪ (p.dropUntil hx).support := by
      simpa [hU] using hy
    rcases mem_union.1 hy' with hT | hD
    · by_cases hxy : y = x
      · exact mem_union.2 (Or.inr (hxy ▸ hxD))
      · exact mem_union.2 (Or.inl (mem_erase.2 ⟨hxy, hT⟩))
    · exact mem_union.2 (Or.inr hD)

/-- Re-open `p` with original closing edge at `u ≠ p.start`. The result
starts at `u` and ends at the predecessor of `u` along `p`. -/
def openAtStart (p : GraphPath G) {u : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start) : GraphPath G :=
  (p.dropUntil hu).splice
    ((p.takeUntil hu).trimFinish (takeUntil_not_nil_cyclePieces hu hne))
    (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
    (disjoint_trimFinish_takeUntil_dropUntil p hu hne).symm

lemma openAtStart_start (p : GraphPath G) {u : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start) :
    (openAtStart p hu hclose hne).start = u :=
  rfl

lemma openAtStart_finish (p : GraphPath G) {u : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start) :
    (openAtStart p hu hclose hne).finish =
      (p.takeUntil hu).walk.penultimate :=
  rfl

lemma openAtStart_support (p : GraphPath G) {u : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start) :
    (openAtStart p hu hclose hne).support = p.support := by
  rw [openAtStart, support_splice, union_comm]
  exact support_trimFinish_takeUntil_union_dropUntil p hu hne

def incomingSeam (p : GraphPath G) {u : V} (hu : u ∈ p.support)
    (_hne : u ≠ p.start) : Sym2 V :=
  s((p.takeUntil hu).walk.penultimate, u)

lemma last_edge_mem_cyclePieces (p : GraphPath G) (h : ¬ p.walk.Nil) :
    s(p.walk.penultimate, p.finish) ∈ p.edges :=
  mem_edges_iff.2 (p.walk.mk_penultimate_end_mem_edges h)

lemma incomingSeam_mem_takeUntil (p : GraphPath G) {u : V} (hu : u ∈ p.support)
    (hne : u ≠ p.start) :
    incomingSeam p hu hne ∈ (p.takeUntil hu).edges := by
  simpa [incomingSeam, takeUntil] using
    last_edge_mem_cyclePieces (p.takeUntil hu) (takeUntil_not_nil_cyclePieces hu hne)

lemma penultimate_ne_finish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    p.walk.penultimate ≠ p.finish := by
  have hpos : 0 < p.walk.length := Walk.not_nil_iff_lt_length.1 h
  have hlt : p.walk.length - 1 < p.walk.length := by omega
  simpa [Walk.penultimate] using p.getVert_ne_finish_of_lt hlt

lemma incomingSeam_not_mem_dropUntil (p : GraphPath G) {u : V}
    (hu : u ∈ p.support) (hne : u ≠ p.start) :
    incomingSeam p hu hne ∉ (p.dropUntil hu).edges := by
  intro he
  have hnn := takeUntil_not_nil_cyclePieces hu hne
  have hpred :
      (p.takeUntil hu).walk.penultimate ∈ (p.dropUntil hu).support :=
    List.mem_toFinset.2
      ((p.dropUntil hu).walk.mem_support_of_mem_edges (mem_edges_iff.1 he)
        (by simp [incomingSeam]))
  have hpredT :
      (p.takeUntil hu).walk.penultimate ∈ (p.takeUntil hu).support :=
    List.mem_toFinset.2
      (Walk.getVert_mem_support (p.takeUntil hu).walk
        ((p.takeUntil hu).walk.length - 1))
  have heq :=
    mem_eq_of_mem_takeUntil_dropUntil p hu hpredT hpred
  exact (penultimate_ne_finish (p.takeUntil hu) hnn) (heq.trans (by simp [takeUntil]))

lemma openAtStart_edges_subset (p : GraphPath G) {u : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start) :
    (openAtStart p hu hclose hne).edges ⊆
      p.edges ∪ {s(p.finish, p.start)} := by
  have hnn := takeUntil_not_nil_cyclePieces hu hne
  have hspl :=
    edges_splice (p.dropUntil hu)
      ((p.takeUntil hu).trimFinish hnn)
      (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
      (disjoint_trimFinish_takeUntil_dropUntil p hu hne).symm
  intro e he
  have he' :
      e ∈ (p.dropUntil hu).edges ∪ ((p.takeUntil hu).trimFinish hnn).edges ∪
        {s((p.dropUntil hu).finish, ((p.takeUntil hu).trimFinish hnn).start)} := by
    simpa [openAtStart, hspl] using he
  have hcloseE :
      s((p.dropUntil hu).finish, ((p.takeUntil hu).trimFinish hnn).start) =
        s(p.finish, p.start) := by
    simp [dropUntil, takeUntil, trimFinish]
  have hsubD : (p.dropUntil hu).edges ⊆ p.edges :=
    edges_dropUntil_subset p hu
  have hsubT : ((p.takeUntil hu).trimFinish hnn).edges ⊆ p.edges :=
    (edges_trimFinish_subset (p.takeUntil hu) hnn).trans (by
      intro e he
      have hsub : (p.takeUntil hu).walk.IsSubwalk p.walk := by
        simpa [takeUntil] using
          Walk.isSubwalk_takeUntil p.walk (mem_walk_support.1 hu)
      exact mem_edges_iff.2 (hsub.edges_subset (mem_edges_iff.1 he)))
  rcases mem_union.1 he' with h | hs0
  · rcases mem_union.1 h with hD | hT
    · exact mem_union.2 (Or.inl (hsubD hD))
    · exact mem_union.2 (Or.inl (hsubT hT))
  · simpa [hcloseE] using mem_union.2 (Or.inr hs0)

lemma openAtStart_edges_subset_cycle (p : GraphPath G) {u : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) {c : GraphCycle G}
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset) :
    (openAtStart p hu hclose hne).edges ⊆ c.walk.edges.toFinset := by
  intro e he
  have : e ∈ p.edges ∪ {s(p.finish, p.start)} :=
    openAtStart_edges_subset p hu hclose hne he
  simpa [hedges] using this

/-- The two whole cycle pieces obtained by opening at `u` and splitting at
`v`. Their starts are `u` and `v`; their finishes are the predecessors of
`v` and of `u` along the opened path. -/
def pieceBefore (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) : GraphPath G :=
  ((openAtStart p hu hclose hne).takeUntil hv).trimFinish
    (takeUntil_not_nil_cyclePieces (p := openAtStart p hu hclose hne) hv
      (by simpa [openAtStart_start p hu hclose hne] using hnv))

def pieceAfter (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) : GraphPath G :=
  (openAtStart p hu hclose hne).dropUntil hv

lemma pieceBefore_start (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u) :
    (pieceBefore p hu hclose hne hv hnv).start = u := by
  simp [pieceBefore, trimFinish, takeUntil, openAtStart_start]

lemma pieceAfter_start (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) :
    (pieceAfter p hu hclose hne hv).start = v := by
  simp [pieceAfter, dropUntil]

lemma pieceAfter_finish (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) :
    (pieceAfter p hu hclose hne hv).finish =
      (p.takeUntil hu).walk.penultimate := by
  simp [pieceAfter, dropUntil, openAtStart_finish]

lemma pieceBefore_finish (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u) :
    (pieceBefore p hu hclose hne hv hnv).finish =
      ((openAtStart p hu hclose hne).takeUntil hv).walk.penultimate := by
  simp [pieceBefore, trimFinish]

lemma disjoint_pieces (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u) :
    Disjoint (pieceBefore p hu hclose hne hv hnv).support
      (pieceAfter p hu hclose hne hv).support := by
  simpa [pieceBefore, pieceAfter, openAtStart_start p hu hclose hne] using
    disjoint_trimFinish_takeUntil_dropUntil (openAtStart p hu hclose hne) hv
      (by simpa [openAtStart_start p hu hclose hne] using hnv)

lemma support_pieces_union (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u) :
    (pieceBefore p hu hclose hne hv hnv).support ∪
      (pieceAfter p hu hclose hne hv).support = p.support := by
  have h :=
    support_trimFinish_takeUntil_union_dropUntil (openAtStart p hu hclose hne)
      hv (by simpa [openAtStart_start p hu hclose hne] using hnv)
  simpa [pieceBefore, pieceAfter, openAtStart_support p hu hclose hne] using h

lemma edges_takeUntil_subset_cyclePieces (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.takeUntil hx).edges ⊆ p.edges := by
  intro e he
  have hsub : (p.takeUntil hx).walk.IsSubwalk p.walk := by
    simpa [takeUntil] using Walk.isSubwalk_takeUntil p.walk (mem_walk_support.1 hx)
  exact mem_edges_iff.2 (hsub.edges_subset (mem_edges_iff.1 he))

lemma pieces_edges_subset_open (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u) :
    (pieceBefore p hu hclose hne hv hnv).edges ⊆
      (openAtStart p hu hclose hne).edges ∧
        (pieceAfter p hu hclose hne hv).edges ⊆
          (openAtStart p hu hclose hne).edges := by
  constructor
  · intro e he
    have hnn := takeUntil_not_nil_cyclePieces (p := openAtStart p hu hclose hne) hv
      (by simpa [openAtStart_start p hu hclose hne] using hnv)
    have hsub :=
      (edges_trimFinish_subset ((openAtStart p hu hclose hne).takeUntil hv) hnn).trans
        (edges_takeUntil_subset_cyclePieces (openAtStart p hu hclose hne) hv)
    exact hsub (by simpa [pieceBefore] using he)
  · intro e he
    have hsub :=
      edges_dropUntil_subset (openAtStart p hu hclose hne) hv
    exact hsub (by simpa [pieceAfter] using he)

end GraphPath
end Nikoghosyan

