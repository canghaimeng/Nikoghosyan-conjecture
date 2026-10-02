/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProtectedComponent
import Nikoghosyan.Cograph.ProtectedPaths
import Nikoghosyan.CycleEdgeRetention
import Nikoghosyan.CycleEdgePieces

/-!
# Complete-join insertion of leftover runs

Manuscript `prof:thm:protected`, join step. Independent leftover starts
(resp. ends) of a saving component lie on a single child of a binary
complete join. When those children differ, a first-departure edge of one
old `U0`-run is retained in the exact omit-run complement of another, and
the second run is inserted across original join seams.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Convert a leftover-run factorisation into the common
`OriginalSubwalkFactor` used by `omitRunComplement`. -/
noncomputable def originalSubwalkFactor_of_leftover {B : Finset V}
    {p Q : GraphPath G} (hQ : Q ∈ leftoverPieces B p) :
    OriginalSubwalkFactor p Q :=
  let h := leftoverPieces_factor (B := B) p Q hQ
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1⟩

lemma originalSubwalkFactor_of_leftover_pre_not_nil {B : Finset V}
    {p Q : GraphPath G} (hs : p.start ∈ B) (hQ : Q ∈ leftoverPieces B p) :
    ¬ (originalSubwalkFactor_of_leftover hQ).preWalk.Nil :=
  leftoverPieces_factor_ru_not_nil (B := B) hs hQ
    (originalSubwalkFactor_of_leftover hQ).factor

lemma originalSubwalkFactor_of_leftover_seams {B : Finset V}
    {p Q : GraphPath G} (hQ : Q ∈ leftoverPieces B p) :
    let F := originalSubwalkFactor_of_leftover hQ
    (F.preWalk.Nil ∨ F.preWalk.penultimate ∈ B) ∧
      (F.sufWalk.Nil ∨ F.sufWalk.snd ∈ B) :=
  (leftoverPieces_factor (B := B) p Q hQ).choose_spec.choose_spec.2

/-- First original edge of a leftover run that leaves `X`. -/
lemma exists_first_departure {Q : GraphPath G} {X : Finset V}
    (hs : Q.start ∈ X) (hf : Q.finish ∉ X) :
    ∃ u v : V, u ∈ X ∧ v ∉ X ∧ G.Adj u v ∧ s(u, v) ∈ Q.edges := by
  let B : Finset V := univ.filter (fun x => x ∉ X)
  have hfB : Q.finish ∈ B := by simp [B, hf]
  have hsB : Q.start ∉ B := by simp [B, hs]
  have hnone : Q.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
    intro hnone
    have hnot : ¬ decide (Q.finish ∈ B) :=
      (List.find?_eq_none (p := fun x : V => decide (x ∈ B))).1 hnone Q.finish
        ((mem_walk_support (p := Q)).1 Q.finish_mem_support)
    exact hnot (decide_eq_true hfB)
  have hfind := firstB_spec (B := B) (p := Q) hnone
  have hx : firstB B Q hnone ∈ Q.support := (mem_find?_B (B := B) hfind).1
  have hbB : firstB B Q hnone ∈ B := (mem_find?_B (B := B) hfind).2
  have hv : firstB B Q hnone ∉ X := by simpa [B] using hbB
  have hne : firstB B Q hnone ≠ Q.start := find?_B_ne_start hsB hfind
  have hnn : ¬ (Q.takeUntil hx).walk.Nil := fun hn =>
    hne ((takeUntil_nil_iff Q hx).1 hn)
  let pre := (Q.takeUntil hx).trimFinish hnn
  have hu : pre.finish ∈ X := by
    have hpen : pre.finish ∈ (Q.takeUntil hx).support := by
      have : pre.support ⊆ (Q.takeUntil hx).support := by
        rw [support_trimFinish]
        exact erase_subset _ _
      exact this pre.finish_mem_support
    have hneP : pre.finish ≠ firstB B Q hnone := by
      have hmem : pre.finish ∈ (Q.takeUntil hx).support.erase (Q.takeUntil hx).finish := by
        rw [← support_trimFinish (Q.takeUntil hx) hnn]
        exact pre.finish_mem_support
      have : (Q.takeUntil hx).finish = firstB B Q hnone := by simp [takeUntil]
      exact this ▸ (mem_erase.1 hmem).1
    have hnotB : pre.finish ∉ B :=
      takeUntil_ne_first_not_mem_B (B := B) hfind hx hpen hneP
    simpa [B] using hnotB
  have hadj : G.Adj pre.finish (Q.takeUntil hx).finish :=
    adj_trimFinish_finish (Q.takeUntil hx) hnn
  have hePre : s(pre.finish, (Q.takeUntil hx).finish) ∈ (Q.takeUntil hx).edges :=
    last_edge_mem (Q.takeUntil hx) hnn
  refine ⟨pre.finish, firstB B Q hnone, hu, hv, by simpa [takeUntil] using hadj, ?_⟩
  exact edges_takeUntil_subset Q hx (by simpa [takeUntil] using hePre)

end GraphPath

namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma leftoverPieces_nodup {B : Finset V} (p : GraphPath G) :
    (leftoverPieces B p).Nodup := by
  refine List.Pairwise.imp ?_ (leftoverPieces_pairwise (B := B) p)
  intro a b hdisj hab
  subst hab
  have : a.support ∩ a.support = ∅ := disjoint_iff_inter_eq_empty.1 hdisj
  simp only [inter_self] at this
  exact (nonempty_iff_ne_empty.1 a.support_nonempty) this

lemma exists_two_leftover_in {A U0 : Finset V} {p : GraphPath G}
    (h2 : 2 ≤ (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p)).length) :
    ∃ Q R, Q ∈ leftoverPieces A p ∧ R ∈ leftoverPieces A p ∧
      Q.start ∈ U0 ∧ R.start ∈ U0 ∧ Q ≠ R := by
  have hn : (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p)).Nodup :=
    (leftoverPieces_nodup (B := A) p).filter _
  match hl : List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p) with
  | [] => simp [hl] at h2
  | [_] => simp [hl] at h2
  | Q :: R :: rest =>
    have hQ : Q ∈ leftoverPieces A p ∧ Q.start ∈ U0 := by
      have : Q ∈ List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p) := by
        simp [hl]
      obtain ⟨hmem, hdec⟩ := List.mem_filter.1 this
      exact ⟨hmem, of_decide_eq_true hdec⟩
    have hR : R ∈ leftoverPieces A p ∧ R.start ∈ U0 := by
      have : R ∈ List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p) := by
        simp [hl]
      obtain ⟨hmem, hdec⟩ := List.mem_filter.1 this
      exact ⟨hmem, of_decide_eq_true hdec⟩
    refine ⟨Q, R, hQ.1, hR.1, hQ.2, hR.2, ?_⟩
    intro heq
    subst heq
    have hn' : (Q :: Q :: rest).Nodup := by simpa [hl] using hn
    exact (List.nodup_cons.1 hn').1 (List.mem_cons.2 (Or.inl rfl))

/-- Independent leftover starts inside a complete join all lie on one child. -/
lemma leftover_starts_in_one_join_side {A U0 X Y : Finset V}
    {p : GraphPath G}
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    (hInd : ∀ Q ∈ leftoverPieces A p, ∀ R ∈ leftoverPieces A p,
      Q.start ∈ U0 → R.start ∈ U0 → Q.start ≠ R.start → ¬ G.Adj Q.start R.start)
    {Q0 : GraphPath G}
    (hQ0 : Q0 ∈ leftoverPieces A p) (hs0 : Q0.start ∈ U0) :
    (∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X) ∨
      (∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ Y) := by
  have hdisj := disjoint_of_completeBetween hjoin
  have hsXY : Q0.start ∈ X ∨ Q0.start ∈ Y := by
    have : Q0.start ∈ X ∪ Y := by simpa [hcover] using hs0
    simpa [mem_union] using this
  rcases hsXY with hsX | hsY
  · refine Or.inl ?_
    intro Q hQ hsU
    have hsXY' : Q.start ∈ X ∨ Q.start ∈ Y := by
      have : Q.start ∈ X ∪ Y := by simpa [hcover] using hsU
      simpa [mem_union] using this
    rcases hsXY' with hX | hY
    · exact hX
    · have hne : Q0.start ≠ Q.start := fun heq =>
        (disjoint_left.1 hdisj (heq ▸ hsX) hY).elim
      exact (hInd Q0 hQ0 Q hQ hs0 hsU hne (hjoin hsX hY)).elim
  · refine Or.inr ?_
    intro Q hQ hsU
    have hsXY' : Q.start ∈ X ∨ Q.start ∈ Y := by
      have : Q.start ∈ X ∪ Y := by simpa [hcover] using hsU
      simpa [mem_union] using this
    rcases hsXY' with hX | hY
    · have hne : Q0.start ≠ Q.start := fun heq =>
        (disjoint_left.1 hdisj hX (heq ▸ hsY)).elim
      exact (hInd Q0 hQ0 Q hQ hs0 hsU hne (hjoin hX hsY).symm).elim
    · exact hY

/-- Independent leftover finishes inside a complete join all lie on one child. -/
lemma leftover_finishes_in_one_join_side {A U0 X Y : Finset V}
    {p : GraphPath G}
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    (hInd : ∀ Q ∈ leftoverPieces A p, ∀ R ∈ leftoverPieces A p,
      Q.finish ∈ U0 → R.finish ∈ U0 → Q.finish ≠ R.finish →
        ¬ G.Adj Q.finish R.finish)
    {Q0 : GraphPath G}
    (hQ0 : Q0 ∈ leftoverPieces A p) (hf0 : Q0.finish ∈ U0) :
    (∀ Q ∈ leftoverPieces A p, Q.finish ∈ U0 → Q.finish ∈ X) ∨
      (∀ Q ∈ leftoverPieces A p, Q.finish ∈ U0 → Q.finish ∈ Y) := by
  have hdisj := disjoint_of_completeBetween hjoin
  have hfXY : Q0.finish ∈ X ∨ Q0.finish ∈ Y := by
    have : Q0.finish ∈ X ∪ Y := by simpa [hcover] using hf0
    simpa [mem_union] using this
  rcases hfXY with hfX | hfY
  · refine Or.inl ?_
    intro Q hQ hfU
    have hfXY' : Q.finish ∈ X ∨ Q.finish ∈ Y := by
      have : Q.finish ∈ X ∪ Y := by simpa [hcover] using hfU
      simpa [mem_union] using this
    rcases hfXY' with hX | hY
    · exact hX
    · have hne : Q0.finish ≠ Q.finish := fun heq =>
        (disjoint_left.1 hdisj (heq ▸ hfX) hY).elim
      exact (hInd Q0 hQ0 Q hQ hf0 hfU hne (hjoin hfX hY)).elim
  · refine Or.inr ?_
    intro Q hQ hfU
    have hfXY' : Q.finish ∈ X ∨ Q.finish ∈ Y := by
      have : Q.finish ∈ X ∪ Y := by simpa [hcover] using hfU
      simpa [mem_union] using this
    rcases hfXY' with hX | hY
    · have hne : Q0.finish ≠ Q.finish := fun heq =>
        (disjoint_left.1 hdisj hX (heq ▸ hfY)).elim
      exact (hInd Q0 hQ0 Q hQ hf0 hfU hne (hjoin hX hfY).symm).elim
    · exact hY

/-- `X ≠ Z` join insertion: insert one leftover run into a first-departure
edge of another, retained in the exact omit-run complement. -/
lemma exists_protectedAt_of_join_insert_XZ {U A U0 X Y : Finset V}
    (c : GraphCycle G) (_hc : c.support = U)
    (hU0 : U0 ⊆ U \ A)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q ≠ R)
    (hQsup : Q.support ⊆ U0) (_hRsup : R.support ⊆ U0)
    (hQs : Q.start ∈ X) (hQf : Q.finish ∈ Y)
    (hRs : R.start ∈ X) (hRf : R.finish ∈ Y) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hRA : Disjoint R.support A := leftoverPieces_disjoint_B p R hR
  have hQe : Q.edges ⊆ p.edges :=
    edges_of_isSubwalk (leftoverPieces_isSubwalk p Q hQ)
  have hdisjQR : Disjoint Q.support R.support :=
    PathCover.pairwise_disjoint_of_mem (leftoverPieces_pairwise (B := A) p)
      hQ hR hneQR
  have hXf : Q.finish ∉ X := fun hX =>
    (disjoint_left.1 (disjoint_of_completeBetween hjoin) hX hQf).elim
  obtain ⟨u, v, huX, hvX, hadjuv, huvQ⟩ :=
    exists_first_departure (Q := Q) (X := X) hQs hXf
  have hvQ : v ∈ Q.support := mem_support_of_mem_edge huvQ (by simp)
  have hvY : v ∈ Y := by
    have hvU0 : v ∈ U0 := hQsup hvQ
    have : v ∈ X ∪ Y := by simpa [hcover] using hvU0
    rcases mem_union.1 this with hX | hY
    · exact (hvX hX).elim
    · exact hY
  have huA : u ∉ A :=
    (mem_sdiff.1 (hU0 (hQsup (mem_support_of_mem_edge huvQ (by simp))))).2
  have hvA : v ∉ A := (mem_sdiff.1 (hU0 (hQsup hvQ))).2
  let F := originalSubwalkFactor_of_leftover (B := A) hR
  have hpre : ¬ F.preWalk.Nil :=
    originalSubwalkFactor_of_leftover_pre_not_nil (B := A) hs hR
  have hseams := originalSubwalkFactor_of_leftover_seams (B := A) hR
  have hstA : (F.omitRunComplement hpre hclose).start ∈ A :=
    F.omitRunComplement_start_mem_A hpre hclose hs hseams.2
  have hfinA : (F.omitRunComplement hpre hclose).finish ∈ A :=
    F.omitRunComplement_finish_mem_A hpre hclose (hseams.1.resolve_left hpre)
  have hrProt : (F.omitRunComplement hpre hclose).ProtectedAt c A := by
    intro e he
    have heE : e ∈ (F.omitRunComplement hpre hclose).edges :=
      (mem_AIncident_iff.1 he).1
    have hsub := F.omitRunComplement_edges_subset_closed hpre hclose heE
    have : e ∈ p.edges ∪ {s(p.finish, p.start)} := by
      simpa [OriginalSubwalkFactor.closedEdges] using hsub
    simpa [hedges] using this
  have hdBlock : Disjoint R.support (F.omitRunComplement hpre hclose).support :=
    F.omitRunComplement_disjoint_block hpre hclose
  have hsupEq : (F.omitRunComplement hpre hclose).support ∪ R.support =
      p.support := by
    rw [F.omitRunComplement_support hpre hclose, sdiff_union_self_eq_union,
      union_eq_left.2 (leftoverPieces_support_subset p R hR)]
  obtain ⟨i, hi, hpair, hFac⟩ :=
    F.exists_PrefixEdgeFactor_of_retained_run_edge hpre hclose Q hdisjQR hQe huvQ
  obtain ⟨Fac⟩ := hFac
  have huv : u ≠ v := hadjuv.ne
  have hdir : (F.omitRunComplement hpre hclose).walk.getVert i = u ∧
      (F.omitRunComplement hpre hclose).walk.getVert (i + 1) = v ∨
      (F.omitRunComplement hpre hclose).walk.getVert i = v ∧
        (F.omitRunComplement hpre hclose).walk.getVert (i + 1) = u := by
    exact (Sym2.eq_iff.mp hpair)
  have hcloseU (qBlk : GraphPath G)
      (hEq : qBlk.support = R.support)
      (hd : Disjoint qBlk.support (F.omitRunComplement hpre hclose).support)
      (hsu : G.Adj ((F.omitRunComplement hpre hclose).walk.getVert i) qBlk.start)
      (hfv : G.Adj qBlk.finish
        ((F.omitRunComplement hpre hclose).walk.getVert (i + 1))) :
      ∃ q : GraphPath G,
        q.support = U ∧ q.ProtectedAt c A ∧
          q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
    have htiA : (F.omitRunComplement hpre hclose).walk.getVert i ∉ A := by
      rcases hdir with ⟨h, _⟩ | ⟨h, _⟩
      · simpa [h] using huA
      · simpa [h] using hvA
    have hhiA : (F.omitRunComplement hpre hclose).walk.getVert (i + 1) ∉ A := by
      rcases hdir with ⟨_, h⟩ | ⟨_, h⟩
      · simpa [h] using hvA
      · simpa [h] using huA
    have hAq : Disjoint qBlk.support A := by simpa [hEq] using hRA
    let q := insertOmittedBlock Fac qBlk hd hsu hfv
    refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
    · have : q.support =
          (F.omitRunComplement hpre hclose).support ∪ qBlk.support :=
        insertOmittedBlock_support Fac qBlk hd hsu hfv
      rw [this, hEq, hsupEq, hp]
    · exact protectedAt_insertOmittedBlock Fac qBlk hd hsu hfv htiA hhiA hAq
        hrProt
    · simpa [q, insertOmittedBlock_start] using hstA
    · simpa [q, insertOmittedBlock_finish] using hfinA
    · change (insertOmittedBlock Fac qBlk hd hsu hfv).start ≠
          (insertOmittedBlock Fac qBlk hd hsu hfv).finish
      simpa [insertOmittedBlock] using
        Fac.insertBlock_start_ne_finish qBlk hd hsu hfv
  rcases hdir with ⟨hiU, hiV⟩ | ⟨hiV, hiU⟩
  · have hd : Disjoint R.reverse.support
        (F.omitRunComplement hpre hclose).support := by
      simpa [support_reverse] using hdBlock
    have hsu : G.Adj ((F.omitRunComplement hpre hclose).walk.getVert i)
        R.reverse.start := by
      simpa [hiU, GraphPath.reverse] using hjoin huX hRf
    have hfv : G.Adj R.reverse.finish
        ((F.omitRunComplement hpre hclose).walk.getVert (i + 1)) := by
      simpa [hiV, GraphPath.reverse] using hjoin hRs hvY
    exact hcloseU R.reverse (by simp) hd hsu hfv
  · have hd : Disjoint R.support
        (F.omitRunComplement hpre hclose).support := hdBlock
    have hsu : G.Adj ((F.omitRunComplement hpre hclose).walk.getVert i)
        R.start := by
      simpa [hiV] using (hjoin hRs hvY).symm
    have hfv : G.Adj R.finish
        ((F.omitRunComplement hpre hclose).walk.getVert (i + 1)) := by
      simpa [hiU] using (hjoin huX hRf).symm
    exact hcloseU R rfl hd hsu hfv

/-- `X ≠ Z` wrapper: every leftover run of `U0` starts in `X` and finishes
in `Y`, so any two leftover runs of `U0` supply the first-departure
insertion. -/
lemma exists_protectedAt_of_join_insert_XZ_of_saving {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (h2 : 2 ≤ (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p)).length)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinY : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ Y) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  obtain ⟨Q, R, hQ, hR, hQs, hRs, hneQR⟩ := exists_two_leftover_in h2
  exact exists_protectedAt_of_join_insert_XZ (c := c) hc hU0 hjoin hcover
    hp hs hclose hedges hQ hR hneQR (hstay Q hQ hQs) (hstay R hR hRs)
    (hstartX Q hQ hQs) (hfinY Q hQ hQs) (hstartX R hR hRs) (hfinY R hR hRs)

/-- `X = Z` join insertion along an actual leftover `Y`–`Y` edge: the
retained dart lives on one leftover run, and a distinct leftover run
with both ends in `X` is inserted across original complete-join seams.
Both dart orientations use the same `X`-ended block; reverse is chosen
only so the ordered seams match the unordered retained edge. -/
lemma exists_protectedAt_of_join_insert_YY {U A U0 X Y : Finset V}
    (c : GraphCycle G) (_hc : c.support = U)
    (hU0 : U0 ⊆ U \ A)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q ≠ R)
    (_hQsup : Q.support ⊆ U0) (_hRsup : R.support ⊆ U0)
    (hRs : R.start ∈ X) (hRf : R.finish ∈ X)
    {u v : V} (huY : u ∈ Y) (hvY : v ∈ Y)
    (_hadjuv : G.Adj u v) (huvQ : s(u, v) ∈ Q.edges) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hRA : Disjoint R.support A := leftoverPieces_disjoint_B p R hR
  have hQe : Q.edges ⊆ p.edges :=
    edges_of_isSubwalk (leftoverPieces_isSubwalk p Q hQ)
  have hdisjQR : Disjoint Q.support R.support :=
    PathCover.pairwise_disjoint_of_mem (leftoverPieces_pairwise (B := A) p)
      hQ hR hneQR
  have hYsub : Y ⊆ U0 := by
    intro y hy
    have : y ∈ X ∪ Y := mem_union.2 (Or.inr hy)
    simpa [hcover] using this
  have huU0 : u ∈ U0 := hYsub huY
  have hvU0 : v ∈ U0 := hYsub hvY
  have huA : u ∉ A := (mem_sdiff.1 (hU0 huU0)).2
  have hvA : v ∉ A := (mem_sdiff.1 (hU0 hvU0)).2
  let F := originalSubwalkFactor_of_leftover (B := A) hR
  have hpre : ¬ F.preWalk.Nil :=
    originalSubwalkFactor_of_leftover_pre_not_nil (B := A) hs hR
  have hseams := originalSubwalkFactor_of_leftover_seams (B := A) hR
  have hstA : (F.omitRunComplement hpre hclose).start ∈ A :=
    F.omitRunComplement_start_mem_A hpre hclose hs hseams.2
  have hfinA : (F.omitRunComplement hpre hclose).finish ∈ A :=
    F.omitRunComplement_finish_mem_A hpre hclose (hseams.1.resolve_left hpre)
  have hrProt : (F.omitRunComplement hpre hclose).ProtectedAt c A := by
    intro e he
    have heE : e ∈ (F.omitRunComplement hpre hclose).edges :=
      (mem_AIncident_iff.1 he).1
    have hsub := F.omitRunComplement_edges_subset_closed hpre hclose heE
    have : e ∈ p.edges ∪ {s(p.finish, p.start)} := by
      simpa [OriginalSubwalkFactor.closedEdges] using hsub
    simpa [hedges] using this
  have hdBlock : Disjoint R.support (F.omitRunComplement hpre hclose).support :=
    F.omitRunComplement_disjoint_block hpre hclose
  have hsupEq : (F.omitRunComplement hpre hclose).support ∪ R.support =
      p.support := by
    rw [F.omitRunComplement_support hpre hclose, sdiff_union_self_eq_union,
      union_eq_left.2 (leftoverPieces_support_subset p R hR)]
  obtain ⟨i, hi, hpair, hFac⟩ :=
    F.exists_PrefixEdgeFactor_of_retained_run_edge hpre hclose Q hdisjQR hQe huvQ
  obtain ⟨Fac⟩ := hFac
  have hdir : (F.omitRunComplement hpre hclose).walk.getVert i = u ∧
      (F.omitRunComplement hpre hclose).walk.getVert (i + 1) = v ∨
      (F.omitRunComplement hpre hclose).walk.getVert i = v ∧
        (F.omitRunComplement hpre hclose).walk.getVert (i + 1) = u := by
    exact (Sym2.eq_iff.mp hpair)
  have hcloseU (qBlk : GraphPath G)
      (hEq : qBlk.support = R.support)
      (hd : Disjoint qBlk.support (F.omitRunComplement hpre hclose).support)
      (hsu : G.Adj ((F.omitRunComplement hpre hclose).walk.getVert i) qBlk.start)
      (hfv : G.Adj qBlk.finish
        ((F.omitRunComplement hpre hclose).walk.getVert (i + 1))) :
      ∃ q : GraphPath G,
        q.support = U ∧ q.ProtectedAt c A ∧
          q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
    have htiA : (F.omitRunComplement hpre hclose).walk.getVert i ∉ A := by
      rcases hdir with ⟨h, _⟩ | ⟨h, _⟩
      · simpa [h] using huA
      · simpa [h] using hvA
    have hhiA : (F.omitRunComplement hpre hclose).walk.getVert (i + 1) ∉ A := by
      rcases hdir with ⟨_, h⟩ | ⟨_, h⟩
      · simpa [h] using hvA
      · simpa [h] using huA
    have hAq : Disjoint qBlk.support A := by simpa [hEq] using hRA
    let q := insertOmittedBlock Fac qBlk hd hsu hfv
    refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
    · have : q.support =
          (F.omitRunComplement hpre hclose).support ∪ qBlk.support :=
        insertOmittedBlock_support Fac qBlk hd hsu hfv
      rw [this, hEq, hsupEq, hp]
    · exact protectedAt_insertOmittedBlock Fac qBlk hd hsu hfv htiA hhiA hAq
        hrProt
    · simpa [q, insertOmittedBlock_start] using hstA
    · simpa [q, insertOmittedBlock_finish] using hfinA
    · change (insertOmittedBlock Fac qBlk hd hsu hfv).start ≠
          (insertOmittedBlock Fac qBlk hd hsu hfv).finish
      simpa [insertOmittedBlock] using
        Fac.insertBlock_start_ne_finish qBlk hd hsu hfv
  -- Both ends of `R` lie in `X`, both ends of the retained dart in `Y`,
  -- so each orientation of the unordered edge is a pair of original
  -- complete-join seams. Reverse of `R` is used only to match dart order.
  rcases hdir with ⟨hiU, hiV⟩ | ⟨hiV, hiU⟩
  · have hd : Disjoint R.support
        (F.omitRunComplement hpre hclose).support := hdBlock
    have hsu : G.Adj ((F.omitRunComplement hpre hclose).walk.getVert i)
        R.start := by
      simpa [hiU] using (hjoin hRs huY).symm
    have hfv : G.Adj R.finish
        ((F.omitRunComplement hpre hclose).walk.getVert (i + 1)) := by
      simpa [hiV] using hjoin hRf hvY
    exact hcloseU R rfl hd hsu hfv
  · have hd : Disjoint R.reverse.support
        (F.omitRunComplement hpre hclose).support := by
      simpa [support_reverse] using hdBlock
    have hsu : G.Adj ((F.omitRunComplement hpre hclose).walk.getVert i)
        R.reverse.start := by
      simpa [hiV, GraphPath.reverse] using (hjoin hRf hvY).symm
    have hfv : G.Adj R.reverse.finish
        ((F.omitRunComplement hpre hclose).walk.getVert (i + 1)) := by
      simpa [hiU, GraphPath.reverse] using hjoin hRs huY
    exact hcloseU R.reverse (by simp) hd hsu hfv

/-- Given a leftover `Y`–`Y` edge on one `U0`-run and at least two leftover
runs in `U0` with both ends in `X`, insert the other `X`-ended run. -/
lemma exists_protectedAt_of_join_insert_YY_of_saving {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (h2 : 2 ≤ (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p)).length)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    {Q : GraphPath G} (hQ : Q ∈ leftoverPieces A p) (hQs : Q.start ∈ U0)
    {u v : V} (huY : u ∈ Y) (hvY : v ∈ Y)
    (hadjuv : G.Adj u v) (huvQ : s(u, v) ∈ Q.edges) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  obtain ⟨Q1, Q2, hQ1, hQ2, hs1, hs2, hne12⟩ := exists_two_leftover_in h2
  have hpick : ∃ R, R ∈ leftoverPieces A p ∧ R.start ∈ U0 ∧ R ≠ Q := by
    by_cases h : Q1 = Q
    · exact ⟨Q2, hQ2, hs2, fun heq => hne12 (h.trans heq.symm)⟩
    · exact ⟨Q1, hQ1, hs1, h⟩
  obtain ⟨R, hR, hRsU0, hneQR⟩ := hpick
  exact exists_protectedAt_of_join_insert_YY (c := c) hc hU0 hjoin hcover
    hp hs hclose hedges hQ hR hneQR.symm (hstay Q hQ hQs) (hstay R hR hRsU0)
    (hstartX R hR hRsU0) (hfinX R hR hRsU0) huY hvY hadjuv huvQ

/-- Symmetric `X ≠ Z` wrapper: leftover runs of `U0` start in `Y` and
finish in `X`. -/
lemma exists_protectedAt_of_join_insert_YX_of_saving {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (h2 : 2 ≤ (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p)).length)
    (hstartY : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ Y)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hjoinYX : G.IsCompleteBetween (Y : Set V) (X : Set V) :=
    fun {y} hy {x} hx => (hjoin hx hy).symm
  have hcoverYX : Y ∪ X = U0 := by rw [union_comm, hcover]
  exact exists_protectedAt_of_join_insert_XZ_of_saving (c := c) hc hU0 hjoinYX
    hcoverYX hp hs hclose hedges hstay h2 hstartY hfinX

/-- Symmetric `X = Z` wrapper along an actual leftover `X`–`X` edge, when
both leftover ends lie in `Y`. -/
lemma exists_protectedAt_of_join_insert_XX_of_saving {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = U0)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (h2 : 2 ≤ (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces A p)).length)
    (hfinY : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ Y)
    (hstartY : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ Y)
    {Q : GraphPath G} (hQ : Q ∈ leftoverPieces A p) (hQs : Q.start ∈ U0)
    {u v : V} (huX : u ∈ X) (hvX : v ∈ X)
    (hadjuv : G.Adj u v) (huvQ : s(u, v) ∈ Q.edges) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hjoinYX : G.IsCompleteBetween (Y : Set V) (X : Set V) :=
    fun {y} hy {x} hx => (hjoin hx hy).symm
  have hcoverYX : Y ∪ X = U0 := by rw [union_comm, hcover]
  exact exists_protectedAt_of_join_insert_YY_of_saving (c := c) hc hU0 hjoinYX
    hcoverYX hp hs hclose hedges hstay h2 hfinY hstartY hQ hQs huX hvX hadjuv huvQ

end Cograph
end Nikoghosyan



