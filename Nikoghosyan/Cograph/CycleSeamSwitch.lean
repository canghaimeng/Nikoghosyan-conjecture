/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProtectedCyclePieces

/-!
# Full-U same-sign switch of two leftover starts or ends

When two leftover-run starts on a prescribed original cycle are adjacent
in `G`, switch the two *whole cycle pieces* obtained by deleting their
incoming seams. Adjacent leftover *finishes* are the same construction on
`p.reverse`, with reverse incoming seams derived from original outgoing
seams; a nil suffix uses the actual closing edge. Generic `switchStarts`
on the two small leftover runs is not a full-`U` path.

This is the adjacent-start and adjacent-end case of `prof:thm:protected`,
not the full induction.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma leftover_start_not_mem {A : Finset V} {p Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) : Q.start ∉ A :=
  Finset.disjoint_left.1 (leftoverPieces_disjoint_B p Q hQ) Q.start_mem_support

lemma leftover_finish_not_mem {A : Finset V} {p Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) : Q.finish ∉ A :=
  Finset.disjoint_left.1 (leftoverPieces_disjoint_B p Q hQ) Q.finish_mem_support

/-- Switch the two whole cycle pieces at adjacent leftover starts. -/
def switchOpenStarts (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u)
    (hadj : G.Adj u v) : GraphPath G :=
  switchStarts (pieceBefore p hu hclose hne hv hnv)
    (pieceAfter p hu hclose hne hv)
    (by
      simpa [pieceBefore_start p hu hclose hne hv hnv,
        pieceAfter_start p hu hclose hne hv] using hadj)
    (disjoint_pieces p hu hclose hne hv hnv)

lemma switchOpenStarts_start (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u)
    (hadj : G.Adj u v) :
    (switchOpenStarts p hu hclose hne hv hnv hadj).start =
      (pieceBefore p hu hclose hne hv hnv).finish :=
  rfl

lemma switchOpenStarts_finish (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u)
    (hadj : G.Adj u v) :
    (switchOpenStarts p hu hclose hne hv hnv hadj).finish =
      (p.takeUntil hu).walk.penultimate := by
  simpa [switchOpenStarts, switchStarts_finish, pieceAfter_finish]

lemma switchOpenStarts_support (p : GraphPath G) {u v : V} (hu : u ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u)
    (hadj : G.Adj u v) :
    (switchOpenStarts p hu hclose hne hv hnv hadj).support = p.support := by
  rw [switchOpenStarts, switchStarts_support]
  exact support_pieces_union p hu hclose hne hv hnv

lemma switchOpenStarts_ProtectedAt (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u)
    (hadj : G.Adj u v) {A : Finset V} (huA : u ∉ A) (hvA : v ∉ A)
    {c : GraphCycle G}
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset) :
    (switchOpenStarts p hu hclose hne hv hnv hadj).ProtectedAt c A := by
  intro e he
  have hAI :=
    switchStarts_AIncident (pieceBefore p hu hclose hne hv hnv)
      (pieceAfter p hu hclose hne hv)
      (by simpa [pieceBefore_start p hu hclose hne hv hnv,
        pieceAfter_start p hu hclose hne hv] using hadj)
      (disjoint_pieces p hu hclose hne hv hnv) huA hvA
  have he' : e ∈
      (pieceBefore p hu hclose hne hv hnv).AIncident A ∪
        (pieceAfter p hu hclose hne hv).AIncident A := by
    simpa [switchOpenStarts, hAI] using he
  have hsub := pieces_edges_subset_open p hu hclose hne hv hnv
  have hopen := openAtStart_edges_subset_cycle p hu hclose hne hedges
  rcases mem_union.1 he' with h | h
  · exact hopen (hsub.1 (mem_AIncident_iff.1 h).1)
  · exact hopen (hsub.2 (mem_AIncident_iff.1 h).1)

lemma switchOpenStarts_start_eq (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hv : v ∈ (openAtStart p hu hclose hne).support) (hnv : v ≠ u)
    (hadj : G.Adj u v) :
    (switchOpenStarts p hu hclose hne hv hnv hadj).start =
      ((openAtStart p hu hclose hne).takeUntil hv).walk.penultimate := by
  simpa [switchOpenStarts_start p hu hclose hne hv hnv hadj] using
    pieceBefore_finish p hu hclose hne hv hnv

/-- Coordinator leftover-predecessor interface, uniquely named. -/
lemma leftoverPred_takeUntil_walk_eq_self {u v : V} (w : G.Walk u v)
    (hw : w.IsPath) :
    w.takeUntil v w.end_mem_support = w := by
  have hn : (w.dropUntil v w.end_mem_support).Nil :=
    Walk.isPath_iff_nil.mp (hw.dropUntil w.end_mem_support)
  have heq := Walk.take_spec w w.end_mem_support
  rw [hn.eq_nil, Walk.append_nil] at heq
  exact heq

lemma leftoverPred_takeUntil_walk_eq_factor_prefix {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv)
    (hQstart : Q.start ∈ p.support) :
    (p.takeUntil hQstart).walk = ru := by
  have htake :=
    Walk.takeUntil_append_of_mem_left ru (Q.walk.append rv) ru.end_mem_support
  have hend := leftoverPred_takeUntil_walk_eq_self ru (isPath_of_factor_left heq)
  simpa only [takeUntil, heq, Walk.append_assoc] using htake.trans hend

lemma leftoverPred_start_predecessor_mem {A : Finset V} {p Q : GraphPath G}
    (hs : p.start ∈ A) (hQ : Q ∈ leftoverPieces A p) :
    (p.takeUntil (leftoverPieces_start_mem hQ)).walk.penultimate ∈ A := by
  obtain ⟨ru, rv, heq, hruA, _⟩ := leftoverPieces_factor p Q hQ
  have hru := leftoverPieces_factor_ru_not_nil hs hQ heq
  rw [leftoverPred_takeUntil_walk_eq_factor_prefix heq]
  exact hruA.resolve_left hru

lemma leftoverPred_takeUntil_support_subset (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) : (p.takeUntil hx).support ⊆ p.support := by
  intro y hy
  have : y ∈ (p.takeUntil hx).support ∪ (p.dropUntil hx).support :=
    mem_union.2 (Or.inl hy)
  rwa [support_takeUntil_union_dropUntil] at this

lemma leftoverPred_takeUntil_append_of_notMem_left {u v w x : V}
    (p : G.Walk u v) (q : G.Walk v w) (hxq : x ∈ q.support)
    (hxp : x ∉ p.support) :
    (p.append q).takeUntil x ((Walk.mem_support_append_iff p q).2 (Or.inr hxq)) =
      p.append (q.takeUntil x hxq) := by
  induction p with
  | nil =>
    simp
  | cons =>
    grind [Walk.cons_append, Walk.takeUntil]

lemma leftoverPred_takeUntil_of_dropLast {u v x : V} (w : G.Walk u v)
    (hnn : ¬ w.Nil) (hx : x ∈ w.dropLast.support) :
    w.dropLast.takeUntil x hx =
      w.takeUntil x (by
        have hcat := Walk.support_dropLast_concat hnn
        exact (hcat.symm ▸ List.mem_append_left _ hx)) := by
  refine Walk.ext_support ?_
  have hcat := Walk.support_dropLast_concat (p := w) hnn
  have hidx : w.dropLast.support.idxOf x = w.support.idxOf x := by
    rw [← hcat, List.idxOf_append_of_mem hx]
  simp only [Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take, hidx]
  have hk : w.support.idxOf x + 1 ≤ w.dropLast.support.length := by
    rw [← hidx]
    exact Nat.succ_le_of_lt (List.idxOf_lt_length_of_mem hx)
  conv =>
    rhs
    arg 2
    rw [show w.support = w.dropLast.support ++ [v] from hcat.symm]
  exact (List.take_append_of_le_length hk).symm

lemma leftoverPred_openAtStart_takeUntil_of_mem_dropUntil
    (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hvD : v ∈ (p.dropUntil hu).support) :
    ((openAtStart p hu hclose hne).takeUntil
        (by
          rw [openAtStart_support p hu hclose hne]
          exact dropUntil_support_subset p hu hvD)).walk =
      ((p.dropUntil hu).takeUntil hvD).walk := by
  have hvW : v ∈ (p.dropUntil hu).walk.support := mem_walk_support.1 hvD
  have htake :=
    Walk.takeUntil_append_of_mem_left (p.dropUntil hu).walk
      (Walk.cons
        (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
        ((p.takeUntil hu).trimFinish
          (takeUntil_not_nil_cyclePieces hu hne)).walk)
      hvW
  simpa [takeUntil, openAtStart, splice] using htake

lemma leftoverPred_penultimate_takeUntil_of_mem_dropUntil
    (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hvD : v ∈ (p.dropUntil hu).support)
    (hvu : v ≠ u) :
    (p.takeUntil (dropUntil_support_subset p hu hvD)).walk.penultimate =
      ((p.dropUntil hu).takeUntil hvD).walk.penultimate := by
  have hvT : v ∉ (p.takeUntil hu).support := by
    intro hvT
    exact hvu (mem_eq_of_mem_takeUntil_dropUntil p hu hvT hvD)
  have hvW : v ∈ (p.dropUntil hu).walk.support := mem_walk_support.1 hvD
  have hxp : v ∉ (p.takeUntil hu).walk.support := by
    simpa [takeUntil, support, List.mem_toFinset] using hvT
  have happend :=
    leftoverPred_takeUntil_append_of_notMem_left (p.takeUntil hu).walk
      (p.dropUntil hu).walk hvW hxp
  have hspec := walk_eq_take_append_drop p hu
  have hnn : ¬ ((p.dropUntil hu).takeUntil hvD).walk.Nil := by
    intro hn
    exact hvu ((takeUntil_nil_iff (p.dropUntil hu) hvD).1 hn)
  have hpen :=
    penultimate_append_of_not_nil (p.takeUntil hu).walk
      ((p.dropUntil hu).takeUntil hvD).walk hnn
  change (p.walk.takeUntil v
      (mem_walk_support.1 (dropUntil_support_subset p hu hvD))).penultimate = _
  simp_rw [hspec]
  exact (congrArg Walk.penultimate happend).trans hpen

lemma leftoverPred_takeUntil_eq_trimFinish_takeUntil
    (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hnn : ¬ (p.takeUntil hu).walk.Nil)
    (hvT : v ∈ ((p.takeUntil hu).trimFinish hnn).support) :
    (((p.takeUntil hu).trimFinish hnn).takeUntil hvT).walk =
      (p.takeUntil (leftoverPred_takeUntil_support_subset p hu
        ((mem_erase.1 (by
          simpa [support_trimFinish, takeUntil] using hvT)).2))).walk := by
  have hvU : v ∈ (p.takeUntil hu).support :=
    (mem_erase.1 (by simpa [support_trimFinish, takeUntil] using hvT)).2
  have hdl : v ∈ (p.takeUntil hu).walk.dropLast.support := by
    simpa [trimFinish, support, List.mem_toFinset] using hvT
  have hdrop :=
    leftoverPred_takeUntil_of_dropLast (p.takeUntil hu).walk hnn hdl
  have htake :=
    Walk.takeUntil_takeUntil p.walk (mem_walk_support.1 hu)
      (mem_walk_support.1 hvU)
  simpa [takeUntil, trimFinish] using hdrop.trans htake

lemma leftoverPred_openAtStart_takeUntil_of_mem_trimFinish
    (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start)
    (hnn : ¬ (p.takeUntil hu).walk.Nil)
    (hvT : v ∈ ((p.takeUntil hu).trimFinish hnn).support) :
    ((openAtStart p hu hclose hne).takeUntil
        (by
          rw [openAtStart_support p hu hclose hne]
          exact leftoverPred_takeUntil_support_subset p hu
            ((mem_erase.1 (by
              simpa [support_trimFinish, takeUntil] using hvT)).2))).walk =
      (p.dropUntil hu).walk.append
        (Walk.cons
          (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
          (((p.takeUntil hu).trimFinish hnn).takeUntil hvT).walk) := by
  have hvU : v ∈ (p.takeUntil hu).support :=
    (mem_erase.1 (by simpa [support_trimFinish, takeUntil] using hvT)).2
  have hvu : v ≠ u := by
    have := (mem_erase.1 (by simpa [support_trimFinish, takeUntil] using hvT)).1
    simpa [takeUntil] using this
  have hvD : v ∉ (p.dropUntil hu).support := by
    intro hvD
    exact hvu (mem_eq_of_mem_takeUntil_dropUntil p hu hvU hvD)
  have hvf : v ≠ p.finish := by
    intro hvf
    exact hvD (by
      simpa [dropUntil, hvf] using (p.dropUntil hu).finish_mem_support)
  have hvW : v ∈
      (Walk.cons
        (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
        ((p.takeUntil hu).trimFinish hnn).walk).support := by
    simp [Walk.support_cons]
    exact Or.inr (mem_walk_support.1 hvT)
  have hxp : v ∉ (p.dropUntil hu).walk.support := by
    simpa [dropUntil, support, List.mem_toFinset] using hvD
  have happend :=
    leftoverPred_takeUntil_append_of_notMem_left (p.dropUntil hu).walk
      (Walk.cons
        (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
        ((p.takeUntil hu).trimFinish hnn).walk)
      hvW hxp
  have htrimW : v ∈ ((p.takeUntil hu).trimFinish hnn).walk.support :=
    mem_walk_support.1 hvT
  have hcons :
      (Walk.cons
          (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
          ((p.takeUntil hu).trimFinish hnn).walk).takeUntil v hvW =
        Walk.cons
          (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
          (((p.takeUntil hu).trimFinish hnn).walk.takeUntil v htrimW) := by
    simp [Walk.takeUntil]
    split_ifs with hf
    · exact (hvf hf.symm).elim
    · rfl
  have happend' :
      ((p.dropUntil hu).walk.append
          (Walk.cons
            (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
            ((p.takeUntil hu).trimFinish hnn).walk)).takeUntil v
          ((Walk.mem_support_append_iff _ _).2 (Or.inr hvW)) =
        (p.dropUntil hu).walk.append
          (Walk.cons
            (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
            (((p.takeUntil hu).trimFinish hnn).walk.takeUntil v htrimW)) := by
    exact (happend.trans (congrArg _ hcons))
  simpa [takeUntil, openAtStart, splice] using happend'

lemma leftoverPred_openAtStart_predecessor_mem {A : Finset V}
    {p Q R : GraphPath G}
    (hs : p.start ∈ A) (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hclose : G.Adj p.finish p.start) (hneQR : Q.start ≠ R.start) :
    ((openAtStart p (leftoverPieces_start_mem hQ) hclose
        (leftoverPieces_start_ne hs hQ)).takeUntil
      (by
        rw [openAtStart_support]
        exact leftoverPieces_start_mem hR)).walk.penultimate ∈ A := by
  have hu : Q.start ∈ p.support := leftoverPieces_start_mem hQ
  have hne : Q.start ≠ p.start := leftoverPieces_start_ne hs hQ
  have hv : R.start ∈ p.support := leftoverPieces_start_mem hR
  have hvs : R.start ≠ p.start := leftoverPieces_start_ne hs hR
  have hpredR := leftoverPred_start_predecessor_mem hs hR
  have hU := support_takeUntil_union_dropUntil p hu
  have hvUD : R.start ∈ (p.takeUntil hu).support ∪ (p.dropUntil hu).support := by
    simpa [hU] using hv
  rcases mem_union.1 hvUD with hvT | hvD
  · have hvu : R.start ≠ Q.start := hneQR.symm
    have hnn := takeUntil_not_nil_cyclePieces hu hne
    have hvTrim : R.start ∈ ((p.takeUntil hu).trimFinish hnn).support := by
      have hneFin : R.start ≠ (p.takeUntil hu).finish := by
        simpa [takeUntil] using hvu
      simpa [support_trimFinish] using mem_erase.2 ⟨hneFin, hvT⟩
    have hopen :=
      leftoverPred_openAtStart_takeUntil_of_mem_trimFinish p hu hclose hne hnn
        hvTrim
    have hnnC :
        ¬ (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk.Nil := by
      intro hn
      exact hvs
        ((takeUntil_nil_iff ((p.takeUntil hu).trimFinish hnn) hvTrim).1 hn)
    have hpenCons :=
      Walk.penultimate_cons_of_not_nil
        (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
        (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk hnnC
    have hpenApp :=
      penultimate_append_of_not_nil (p.dropUntil hu).walk
        (Walk.cons
          (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
          (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk)
        Walk.not_nil_cons
    have htrim :=
      leftoverPred_takeUntil_eq_trimFinish_takeUntil p hu hnn hvTrim
    have hpen :
        ((openAtStart p hu hclose hne).takeUntil
            (by
              rw [openAtStart_support p hu hclose hne]
              exact hv)).walk.penultimate =
          (p.takeUntil (leftoverPieces_start_mem hR)).walk.penultimate := by
      rw [hopen]
      exact hpenApp.trans (hpenCons.trans (congrArg Walk.penultimate htrim))
    simpa [hpen] using hpredR
  · have hvu : R.start ≠ Q.start := hneQR.symm
    have hopen :=
      leftoverPred_openAtStart_takeUntil_of_mem_dropUntil p hu hclose hne hvD
    have hpenD :=
      leftoverPred_penultimate_takeUntil_of_mem_dropUntil p hu hvD hvu
    have hpen :
        ((openAtStart p hu hclose hne).takeUntil
            (by
              rw [openAtStart_support p hu hclose hne]
              exact hv)).walk.penultimate =
          (p.takeUntil (leftoverPieces_start_mem hR)).walk.penultimate := by
      rw [hopen]
      exact hpenD.symm
    simpa [hpen] using hpredR

lemma leftoverPred_reverse_edges (p : GraphPath G) :
    p.reverse.edges = p.edges := by
  simp [edges, reverse, Walk.edges_reverse, List.toFinset_reverse]

lemma leftoverPred_penultimate_reverse_eq_snd {u v : V} (w : G.Walk u v)
    (h : ¬ w.Nil) : w.reverse.penultimate = w.snd := by
  have hpos : 0 < w.length := Walk.not_nil_iff_lt_length.1 h
  have hlen : w.reverse.length = w.length := Walk.length_reverse w
  have hsub : w.length - (w.length - 1) = 1 := by omega
  simp only [Walk.penultimate, Walk.snd, Walk.getVert_reverse, hlen, hsub]

lemma leftoverPred_takeUntil_reverse_eq (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) :
    (p.reverse.takeUntil (by simpa [support_reverse] using hx)).walk =
      (p.dropUntil hx).walk.reverse := by
  have hxW := mem_walk_support.1 hx
  have hspec := Walk.take_spec p.walk hxW
  have hrev : p.walk.reverse =
      (p.walk.dropUntil x hxW).reverse.append
        (p.walk.takeUntil x hxW).reverse := by
    rw [← Walk.reverse_append, hspec]
  have hxL : x ∈ (p.walk.dropUntil x hxW).reverse.support := by
    simp [Walk.support_reverse]
  have htake :=
    Walk.takeUntil_append_of_mem_left
      (p.walk.dropUntil x hxW).reverse
      (p.walk.takeUntil x hxW).reverse
      hxL
  have hend := leftoverPred_takeUntil_walk_eq_self
      (p.walk.dropUntil x hxW).reverse
      ((p.dropUntil hx).isPath.reverse)
  simp only [takeUntil, dropUntil, reverse]
  convert htake.trans hend

lemma leftoverPred_factor_rv_not_nil {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (_heq : p.walk = (ru.append Q.walk).append rv)
    (hne : Q.finish ≠ p.finish) : ¬ rv.Nil := by
  intro h
  exact hne (Walk.Nil.eq h)

/-- Outgoing leftover seam along reverse: the predecessor of a leftover
finish on `p.reverse` is the original suffix successor, which lies in `A`.
Requires the suffix to be non-nil, i.e. the leftover does not end at
`p.finish`. -/
lemma leftoverPred_reverse_finish_predecessor_mem {A : Finset V}
    {p Q : GraphPath G} (hQ : Q ∈ leftoverPieces A p)
    (hneFin : Q.finish ≠ p.finish) :
    (p.reverse.takeUntil
        (by simpa [support_reverse] using leftoverPieces_finish_mem hQ)).walk.penultimate ∈
      A := by
  obtain ⟨ru, rv, heq, _hruA, hrvA⟩ := leftoverPieces_factor p Q hQ
  have hrv : ¬ rv.Nil := leftoverPred_factor_rv_not_nil heq hneFin
  have hsuc : rv.snd ∈ A := hrvA.resolve_left hrv
  have hx : Q.finish ∈ p.support := leftoverPieces_finish_mem hQ
  have hxW := mem_walk_support.1 hx
  have hrev : p.walk.reverse =
      rv.reverse.append (Q.walk.reverse.append ru.reverse) := by
    rw [heq, Walk.reverse_append, Walk.reverse_append]
  have hxL : Q.finish ∈ rv.reverse.support := by
    simp [Walk.support_reverse]
  have htake :=
    Walk.takeUntil_append_of_mem_left rv.reverse
      (Q.walk.reverse.append ru.reverse) hxL
  have hend := leftoverPred_takeUntil_walk_eq_self rv.reverse
      ((isPath_of_factor_right heq).reverse)
  have hwalk :
      (p.reverse.takeUntil
          (by simpa [support_reverse] using hx)).walk = rv.reverse := by
    simp only [reverse, takeUntil]
    convert htake.trans hend
  have hpen :
      (p.reverse.takeUntil
          (by simpa [support_reverse] using hx)).walk.penultimate = rv.snd := by
    rw [hwalk]
    exact leftoverPred_penultimate_reverse_eq_snd rv hrv
  simpa [hpen] using hsuc

/-- Transport of a predecessor-in-`A` certificate along `openAtStart`.
If `v = p.start`, the opened incoming seam is the original closing edge,
so the predecessor is `p.finish` (nil-suffix / closing-seam case). -/
lemma leftoverPred_openAtStart_predecessor_mem_of_pred {A : Finset V}
    (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hv : v ∈ p.support)
    (hclose : G.Adj p.finish p.start) (hne : u ≠ p.start) (hneuv : u ≠ v)
    (hpredV : v ≠ p.start → (p.takeUntil hv).walk.penultimate ∈ A)
    (hcloseA : v = p.start → p.finish ∈ A) :
    ((openAtStart p hu hclose hne).takeUntil
        (by rw [openAtStart_support p hu hclose hne]; exact hv)).walk.penultimate ∈
      A := by
  have hU := support_takeUntil_union_dropUntil p hu
  have hvUD : v ∈ (p.takeUntil hu).support ∪ (p.dropUntil hu).support := by
    simpa [hU] using hv
  rcases mem_union.1 hvUD with hvT | hvD
  · have hvu : v ≠ u := hneuv.symm
    have hnn := takeUntil_not_nil_cyclePieces hu hne
    have hvTrim : v ∈ ((p.takeUntil hu).trimFinish hnn).support := by
      have hneFin : v ≠ (p.takeUntil hu).finish := by
        simpa [takeUntil] using hvu
      simpa [support_trimFinish] using mem_erase.2 ⟨hneFin, hvT⟩
    by_cases hvs : v = p.start
    · have hfinA : p.finish ∈ A := hcloseA hvs
      have hopen :=
        leftoverPred_openAtStart_takeUntil_of_mem_trimFinish p hu hclose hne hnn
          hvTrim
      have hnil :
          (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk.Nil :=
        (takeUntil_nil_iff ((p.takeUntil hu).trimFinish hnn) hvTrim).2
          (by simpa [trimFinish, takeUntil] using hvs)
      have hpenApp :=
        penultimate_append_of_not_nil (p.dropUntil hu).walk
          (Walk.cons
            (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
            (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk)
          Walk.not_nil_cons
      have hpenCons :
          (Walk.cons
              (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
              (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk).penultimate =
            p.finish := by
        have hlen0 :
            (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk.length = 0 :=
          Walk.length_eq_zero_iff.2 hnil
        simp [Walk.penultimate, Walk.length_cons, hlen0]
      have hpen :
          ((openAtStart p hu hclose hne).takeUntil
              (by rw [openAtStart_support p hu hclose hne]; exact hv)).walk.penultimate =
            p.finish := by
        rw [hopen]
        exact hpenApp.trans hpenCons
      simpa [hpen] using hfinA
    · have hpred := hpredV hvs
      have hopen :=
        leftoverPred_openAtStart_takeUntil_of_mem_trimFinish p hu hclose hne hnn
          hvTrim
      have hnnC :
          ¬ (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk.Nil := by
        intro hn
        exact hvs
          ((takeUntil_nil_iff ((p.takeUntil hu).trimFinish hnn) hvTrim).1 hn)
      have hpenCons :=
        Walk.penultimate_cons_of_not_nil
          (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
          (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk hnnC
      have hpenApp :=
        penultimate_append_of_not_nil (p.dropUntil hu).walk
          (Walk.cons
            (by simpa [dropUntil, takeUntil, trimFinish] using hclose)
            (((p.takeUntil hu).trimFinish hnn).takeUntil hvTrim).walk)
          Walk.not_nil_cons
      have htrim :=
        leftoverPred_takeUntil_eq_trimFinish_takeUntil p hu hnn hvTrim
      have hpen :
          ((openAtStart p hu hclose hne).takeUntil
              (by rw [openAtStart_support p hu hclose hne]; exact hv)).walk.penultimate =
            (p.takeUntil hv).walk.penultimate := by
        rw [hopen]
        exact hpenApp.trans (hpenCons.trans (congrArg Walk.penultimate htrim))
      simpa [hpen] using hpred
  · have hvu : v ≠ u := hneuv.symm
    have hvs : v ≠ p.start := by
      intro hvs
      have hst : p.start ∈ (p.takeUntil hu).support := by
        simpa [takeUntil] using (p.takeUntil hu).start_mem_support
      have hvD' : p.start ∈ (p.dropUntil hu).support := by
        simpa [hvs] using hvD
      exact hne (mem_eq_of_mem_takeUntil_dropUntil p hu hst hvD').symm
    have hpred := hpredV hvs
    have hopen :=
      leftoverPred_openAtStart_takeUntil_of_mem_dropUntil p hu hclose hne hvD
    have hpenD :=
      leftoverPred_penultimate_takeUntil_of_mem_dropUntil p hu hvD hvu
    have hpen :
        ((openAtStart p hu hclose hne).takeUntil
            (by rw [openAtStart_support p hu hclose hne]; exact hv)).walk.penultimate =
          (p.takeUntil hv).walk.penultimate := by
      rw [hopen]
      exact hpenD.symm
    simpa [hpen] using hpred

end GraphPath

namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Adjacent leftover-run starts on an opened prescribed cycle yield a
full-`U` original spanning path that is `ProtectedAt` the prescribed
cycle, with both endpoints in `A`. Works for `|A| = 2` and for larger
`A`. Distinctness follows from the cycle having order at least three. -/
lemma exists_switchOpenStarts_of_adj_leftover_starts {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.start ≠ R.start) (hadj : G.Adj Q.start R.start) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hu : Q.start ∈ p.support := leftoverPieces_start_mem hQ
  have hne : Q.start ≠ p.start := leftoverPieces_start_ne hs hQ
  have huA : Q.start ∉ A := leftover_start_not_mem hQ
  have hvA : R.start ∉ A := leftover_start_not_mem hR
  have hvOpen : R.start ∈ (openAtStart p hu hclose hne).support := by
    rw [openAtStart_support p hu hclose hne]
    exact leftoverPieces_start_mem hR
  let q := switchOpenStarts p hu hclose hne hvOpen hneQR.symm hadj
  have hqU : q.support = U := by
    simpa [q, hp] using
      switchOpenStarts_support p hu hclose hne hvOpen hneQR.symm hadj
  refine ⟨q, hqU, ?_, ?_, ?_, ?_⟩
  · exact switchOpenStarts_ProtectedAt p hu hclose hne hvOpen hneQR.symm hadj
      huA hvA hedges
  · have hst := switchOpenStarts_start_eq p hu hclose hne hvOpen hneQR.symm hadj
    have hpred :=
      leftoverPred_openAtStart_predecessor_mem hs hQ hR hclose hneQR
    simpa [q, hst] using hpred
  · have hfin := switchOpenStarts_finish p hu hclose hne hvOpen hneQR.symm hadj
    have hpred := leftoverPred_start_predecessor_mem hs hQ
    simpa [q, hfin] using hpred
  · intro hst
    have hnil : q.walk.Nil := (nil_iff_start_eq_finish q).2 hst
    have hsing : q.support = {q.start} := support_eq_singleton_of_nil q hnil
    have hcard : q.support.card = 1 := by simp [hsing]
    have h3 : 3 ≤ q.support.card := by
      simpa [hqU, hc] using c.three_le_card_support
    omega

/-- Same-sign full-cycle start switch from predecessor certificates,
without requiring `p.start ∈ A`. Used for the reverse-orientation
leftover-end branch. -/
lemma exists_switchOpenStarts_AA_of_preds {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    {p : GraphPath G} (hp : p.support = U)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {u v : V} (hu : u ∈ p.support) (hv : v ∈ p.support)
    (hne : u ≠ p.start) (hneuv : u ≠ v) (hadj : G.Adj u v)
    (huA : u ∉ A) (hvA : v ∉ A)
    (hfinA : (p.takeUntil hu).walk.penultimate ∈ A)
    (hstartA :
      ((openAtStart p hu hclose hne).takeUntil
        (by rw [openAtStart_support p hu hclose hne]; exact hv)).walk.penultimate ∈ A) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hvOpen : v ∈ (openAtStart p hu hclose hne).support := by
    rw [openAtStart_support p hu hclose hne]; exact hv
  let q := switchOpenStarts p hu hclose hne hvOpen hneuv.symm hadj
  have hqU : q.support = U := by
    simpa [q, hp] using
      switchOpenStarts_support p hu hclose hne hvOpen hneuv.symm hadj
  refine ⟨q, hqU, ?_, ?_, ?_, ?_⟩
  · exact switchOpenStarts_ProtectedAt p hu hclose hne hvOpen hneuv.symm hadj
      huA hvA hedges
  · have hst := switchOpenStarts_start_eq p hu hclose hne hvOpen hneuv.symm hadj
    simpa [q, hst] using hstartA
  · have hfin := switchOpenStarts_finish p hu hclose hne hvOpen hneuv.symm hadj
    simpa [q, hfin] using hfinA
  · intro hst
    have hnil : q.walk.Nil := (nil_iff_start_eq_finish q).2 hst
    have hsing : q.support = {q.start} := support_eq_singleton_of_nil q hnil
    have hcard : q.support.card = 1 := by simp [hsing]
    have h3 : 3 ≤ q.support.card := by
      simpa [hqU, hc] using c.three_le_card_support
    omega

/-- Reverse-orientation helper: open `p.reverse` at a leftover finish
other than `p.finish`, then apply the predecessor-input callback. -/
lemma exists_switchOpenStarts_of_adj_leftover_ends_of_ne_finish {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.finish ≠ R.finish) (hadj : G.Adj Q.finish R.finish)
    (hneFin : Q.finish ≠ p.finish) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  let pr := p.reverse
  have hpR : pr.support = U := by simpa [pr, support_reverse] using hp
  have hcloseR : G.Adj pr.finish pr.start := by
    simpa [pr, reverse] using hclose.symm
  have hedgesR : pr.edges ∪ {s(pr.finish, pr.start)} = c.walk.edges.toFinset := by
    rw [leftoverPred_reverse_edges p]
    change p.edges ∪ {s(p.start, p.finish)} = _
    rw [show s(p.start, p.finish) = s(p.finish, p.start) from Sym2.eq_swap]
    exact hedges
  have hu : Q.finish ∈ pr.support := by
    simpa [pr, support_reverse] using leftoverPieces_finish_mem hQ
  have hv : R.finish ∈ pr.support := by
    simpa [pr, support_reverse] using leftoverPieces_finish_mem hR
  have hne : Q.finish ≠ pr.start := by simpa [pr, reverse] using hneFin
  have huA : Q.finish ∉ A := leftover_finish_not_mem hQ
  have hvA : R.finish ∉ A := leftover_finish_not_mem hR
  have hfinA :
      (pr.takeUntil hu).walk.penultimate ∈ A := by
    simpa [pr] using leftoverPred_reverse_finish_predecessor_mem hQ hneFin
  have hstartA :
      ((openAtStart pr hu hcloseR hne).takeUntil
        (by rw [openAtStart_support pr hu hcloseR hne]; exact hv)).walk.penultimate ∈
        A :=
    leftoverPred_openAtStart_predecessor_mem_of_pred (A := A) pr hu hv
      hcloseR hne hneQR
      (fun hvs =>
        leftoverPred_reverse_finish_predecessor_mem hR
          (by simpa [pr, reverse] using hvs))
      (fun _ => by simpa [pr, reverse] using hs)
  exact exists_switchOpenStarts_AA_of_preds c hc hpR hcloseR hedgesR
    hu hv hne hneQR hadj huA hvA hfinA hstartA

/-- Adjacent leftover-run finishes on an opened prescribed cycle yield a
full-`U` original spanning path that is `ProtectedAt` the prescribed
cycle, with both endpoints in `A`. Reverse orientation of leftover
incoming seams is derived from original outgoing seams; a nil suffix
uses the actual closing edge. Distinctness follows from cycle order at
least three. Works for `|A| = 2`. -/
lemma exists_switchOpenStarts_of_adj_leftover_ends {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.finish ≠ R.finish) (hadj : G.Adj Q.finish R.finish) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  by_cases hneFin : Q.finish = p.finish
  · have hRfin : R.finish ≠ p.finish := by
      intro h
      exact hneQR (hneFin.trans h.symm)
    exact exists_switchOpenStarts_of_adj_leftover_ends_of_ne_finish c hc hp hs
      hclose hedges hR hQ hneQR.symm hadj.symm hRfin
  · exact exists_switchOpenStarts_of_adj_leftover_ends_of_ne_finish c hc hp hs
      hclose hedges hQ hR hneQR hadj hneFin

end Cograph
end Nikoghosyan
