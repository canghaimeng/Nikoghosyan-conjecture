/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProfileEndpoints
import Nikoghosyan.Cograph.ProtectedIncidence
import Nikoghosyan.Cograph.CycleSeamSwitch

/-!
# Protected spanning paths under strict slack: necessity and A–A cycle edge

Manuscript `prof:thm:protected`, partial. Necessity of `p(K) < |A|` for a
spanning original `A`–`A` path, the A–A cycle-neighbour base with
extensional `ProtectedAt`, complementary leftover `r` with exported
`r.edges ⊆ p.edges ∪ {closing}` (ProtectedIncidence), and exact leftover
count when the opened path has no consecutive `A`–`A` edge. Same-sign full-cycle start switch of two leftover
starts is kernel-checked as `exists_switchOpenStarts_of_adj_leftover_starts`.
Same-sign full-cycle finish switch of two leftover ends is
`exists_switchOpenStarts_of_adj_leftover_ends`.
Join insertion, `A'=A∪Y` deletion, and Y-to-A rotations stay OPEN.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A path with both ends in `B` contributes at most `|support ∩ B| - 1`
leftover runs. Consecutive `B`–`B` edges are allowed (no independence). -/
lemma leftoverPieces_length_succ_le_of_both_ends {B : Finset V}
    (p : GraphPath G) (hs : p.start ∈ B) (hf : p.finish ∈ B) :
    (leftoverPieces B p).length + 1 ≤ (p.support ∩ B).card := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        p.start ∈ B → p.finish ∈ B →
          (leftoverPieces B p).length + 1 ≤ (p.support ∩ B).card)
    p.support.card ?_ p rfl hs hf
  intro n ih p hn hs' hf'
  by_cases hnil : p.walk.Nil
  · have hlist : leftoverPieces B p = [] :=
      leftoverPieces_of_start_mem_nil hs' hnil
    have hsing : p.support = {p.start} :=
      support_eq_singleton_of_nil p hnil
    simp [hlist, hsing, hs']
  · rw [leftoverPieces_of_start_mem_cons hs' hnil]
    have hlt : (p.trimStart hnil).support.card < n := by
      simpa [hn, support_trimStart] using
        card_erase_lt_of_mem p.start_mem_support
    have hfT : (p.trimStart hnil).finish ∈ B := hf'
    have hps : p.support = insert p.start (p.trimStart hnil).support := by
      rw [support_trimStart, insert_erase p.start_mem_support]
    have hstart_not : p.start ∉ (p.trimStart hnil).support := by
      rw [support_trimStart]; exact notMem_erase _ _
    have hcard : (p.support ∩ B).card =
        ((p.trimStart hnil).support ∩ B).card + 1 := by
      rw [hps, insert_inter_of_mem hs', card_insert_of_notMem]
      exact fun hz => hstart_not (mem_inter.1 hz).1
    by_cases hsT : (p.trimStart hnil).start ∈ B
    · have ih' := ih _ hlt (p.trimStart hnil) rfl hsT hfT
      omega
    · cases hfind :
        (p.trimStart hnil).walk.support.find? (fun x => decide (x ∈ B)) with
      | none =>
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
        have hfW : (p.trimStart hnil).finish ∈
            (p.trimStart hnil).support ∩ B :=
          mem_inter.2 ⟨(p.trimStart hnil).finish_mem_support, hfT⟩
        rw [hemp] at hfW
        exact (notMem_empty _ hfW).elim
      | some _ =>
        have hnone :
            (p.trimStart hnil).walk.support.find?
              (fun x => decide (x ∈ B)) ≠ none := by
          simp [hfind]
        rw [leftoverPieces.eq_def]
        simp [hsT, hnone]
        have hfind' := firstB_spec (B := B) (p := p.trimStart hnil) hnone
        have hx : firstB B (p.trimStart hnil) hnone ∈
            (p.trimStart hnil).support :=
          (mem_find?_B (B := B) hfind').1
        have hbB : firstB B (p.trimStart hnil) hnone ∈ B :=
          (mem_find?_B (B := B) hfind').2
        have hne : firstB B (p.trimStart hnil) hnone ≠
            (p.trimStart hnil).start :=
          find?_B_ne_start hsT hfind'
        have hltD :
            ((p.trimStart hnil).dropUntil hx).support.card <
              (p.trimStart hnil).support.card :=
          dropUntil_support_card_lt (p.trimStart hnil) hx hne
        have hltD' : ((p.trimStart hnil).dropUntil hx).support.card < n :=
          lt_trans hltD hlt
        have hstartD : ((p.trimStart hnil).dropUntil hx).start ∈ B := by
          simpa [dropUntil] using hbB
        have hfinD : ((p.trimStart hnil).dropUntil hx).finish ∈ B := hfT
        have ihD :=
          ih _ hltD' ((p.trimStart hnil).dropUntil hx) rfl hstartD hfinD
        have hsub :
            ((p.trimStart hnil).dropUntil hx).support ∩ B ⊆
              (p.trimStart hnil).support ∩ B :=
          inter_subset_inter
            (dropUntil_support_subset (p.trimStart hnil) hx) subset_rfl
        have hle := card_le_card hsub
        omega

end GraphPath

namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Deleting `A` from a spanning original `U`-path with both ends in `A`
leaves at most `|A| - 1` leftover runs, hence `p(U \ A) < |A|`. -/
lemma pathCoverNumber_lt_of_spanning_AA {U A : Finset V}
    (hA : A ⊆ U) (hAne : A.Nonempty)
    {p : GraphPath G} (hp : p.support = U)
    (hs : p.start ∈ A) (hf : p.finish ∈ A) :
    pathCoverNumber G (U \ A) < A.card := by
  have hAU : A ⊆ p.support := by simpa [hp] using hA
  have hinter : p.support ∩ A = A := inter_eq_right.2 hAU
  have hlen := leftoverPieces_length_succ_le_of_both_ends (B := A) p hs hf
  have hcard : (leftoverCoverOfPath p A).card + 1 ≤ A.card := by
    simpa [leftoverCoverOfPath_card, hinter] using hlen
  have hEq : p.support \ A = U \ A := by rw [hp]
  have hle :=
    pathCoverNumber_le (G := G) ((leftoverCoverOfPath p A).cast hEq)
  have : PathCover.card ((leftoverCoverOfPath p A).cast hEq) + 1 ≤ A.card := by
    simpa [PathCover.cast_card] using hcard
  omega

lemma pathCoverNumber_lt_of_spanningPathCompatible_AA {U A : Finset V}
    (hA : A ⊆ U) (hAne : A.Nonempty) {x y : V}
    (hx : x ∈ A) (hy : y ∈ A)
    (hR : SpanningPathCompatible (G := G) U x y) :
    pathCoverNumber G (U \ A) < A.card := by
  obtain ⟨q, hq, qst, qfin⟩ := exists_oriented_path_from hR
  exact pathCoverNumber_lt_of_spanning_AA hA hAne hq
    (by simpa [qst] using hx) (by simpa [qfin] using hy)

/-- Opening `c` at `x` produces a spanning path from `x` to the forward
successor, whose edges plus the dropped successor edge recover `c`. -/
lemma exists_open_at_succ (c : GraphCycle G) {x : V} (hx : x ∈ c.support) :
    ∃ p : GraphPath G,
      p.support = c.support ∧ p.start = x ∧
        p.finish = cycleSucc (rotateTo c hx) ∧ G.Adj p.finish x ∧
          (p.walk.edges.toFinset ∪ {s(p.finish, x)}) =
            c.walk.edges.toFinset := by
  let c' := rotateTo c hx
  have hnil : ¬ c'.walk.Nil := c'.isCycle.not_nil
  obtain ⟨w, hadj, q, hwalk⟩ := Walk.not_nil_iff.1 hnil
  have hq : q.IsPath :=
    ((Walk.cons_isCycle_iff q hadj).1 (by simpa [hwalk] using c'.isCycle)).1
  let p0 : GraphPath G := ⟨w, c'.start, q, hq⟩
  have hp0 : p0.support = c'.support := by
    have hstart : c'.start ∈ q.support := Walk.end_mem_support q
    simp [p0, GraphPath.support, GraphCycle.support, hwalk, Walk.support_cons,
      insert_eq_of_mem (List.mem_toFinset.2 hstart)]
  have hx' : c'.start = x := start_rotateTo c hx
  have hw : w = cycleSucc c' := by
    simp [cycleSucc, hwalk]
  refine ⟨p0.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GraphPath.support_reverse, hp0, support_rotateTo]
  · simp [p0, GraphPath.reverse, hx']
  · simp [p0, GraphPath.reverse, hw, c']
  · simpa [p0, GraphPath.reverse, hx'] using hadj.symm
  · have hqE : p0.reverse.walk.edges.toFinset = q.edges.toFinset := by
      simp [p0, GraphPath.reverse, Walk.edges_reverse, List.toFinset_reverse]
    have hcE : c'.walk.edges.toFinset =
        insert s(c'.start, w) q.edges.toFinset := by
      simp [hwalk, Walk.edges_cons]
    have hfin : p0.reverse.finish = w := by simp [p0, GraphPath.reverse]
    have hedges :
        p0.reverse.walk.edges.toFinset ∪ {s(p0.reverse.finish, x)} =
          c'.walk.edges.toFinset := by
      rw [hqE, hcE, hfin]
      have : s(w, x) = s(c'.start, w) := by
        rw [hx']
        exact Sym2.eq_swap
      rw [this]
      simp [singleton_union]
    have hperm : c'.walk.edges.Perm c.walk.edges :=
      (Walk.rotate_edges c.walk x (mem_walk_support_of_mem_cycle hx)).perm
    rw [hedges]
    simpa [rotateTo] using toFinset_eq_of_perm hperm

/-- Base case of protected paths: the forward cycle successor of `a ∈ A`
also lies in `A`, so deleting that original cycle edge yields a spanning
`A`–`A` path whose remaining edges are exactly the other cycle edges. -/
lemma exists_protected_of_succ_mem_A {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) {a : V} (haA : a ∈ A)
    (hsucc : cycleSucc (rotateTo c (by simpa [hc] using hA haA)) ∈ A) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧
          (p.walk.edges.toFinset ∪ {s(p.finish, p.start)}) =
            c.walk.edges.toFinset := by
  have haU : a ∈ c.support := by simpa [hc] using hA haA
  obtain ⟨p, hp, hs, hfin, _hadj, hedges⟩ := exists_open_at_succ c haU
  refine ⟨p, hp.trans hc, by simpa [hs] using haA, ?_, ?_, ?_⟩
  · simpa [hfin] using hsucc
  · rw [hs, hfin]
    intro h
    exact cycleSucc_ne_start (rotateTo c haU)
      (h.symm.trans (start_rotateTo c haU).symm)
  · simpa [hs] using hedges

/-- Symmetric base case using the reverse cycle, so the predecessor of
`a` on `c` lies in `A`. -/
lemma exists_protected_of_pred_mem_A {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) {a : V} (haA : a ∈ A)
    (hpred : cycleSucc (rotateTo c.reverse
        (by simpa [hc, GraphCycle.support_reverse] using hA haA)) ∈ A) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧
          (p.walk.edges.toFinset ∪ {s(p.finish, p.start)}) =
            c.walk.edges.toFinset := by
  have haU : a ∈ c.reverse.support := by
    simpa [GraphCycle.support_reverse, hc] using hA haA
  obtain ⟨p, hp, hs, hfin, _hadj, hedges⟩ :=
    exists_open_at_succ c.reverse haU
  have hperm : c.reverse.walk.edges.Perm c.walk.edges := by
    simpa [GraphCycle.reverse, Walk.edges_reverse] using
      (List.reverse_perm c.walk.edges)
  refine ⟨p, ?_, by simpa [hs] using haA, ?_, ?_, ?_⟩
  · simpa [GraphCycle.support_reverse, hc] using hp
  · simpa [hfin] using hpred
  · rw [hs, hfin]
    intro h
    exact cycleSucc_ne_start (rotateTo c.reverse haU)
      (h.symm.trans (start_rotateTo c.reverse haU).symm)
  · have : p.walk.edges.toFinset ∪ {s(p.finish, p.start)} =
        c.reverse.walk.edges.toFinset := by
      simpa [hs] using hedges
    rw [this]
    exact toFinset_eq_of_perm hperm

/-- Combined base case: some vertex of `A` has a cycle neighbour in `A`. -/
lemma exists_protected_of_cycle_neighbor_in_A {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) {a : V} (haA : a ∈ A)
    (hn : cycleSucc (rotateTo c (by simpa [hc] using hA haA)) ∈ A ∨
      cycleSucc (rotateTo c.reverse
        (by simpa [hc, GraphCycle.support_reverse] using hA haA)) ∈ A) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧
          (p.walk.edges.toFinset ∪ {s(p.finish, p.start)}) =
            c.walk.edges.toFinset := by
  rcases hn with h | h
  · exact exists_protected_of_succ_mem_A c hc hA haA h
  · exact exists_protected_of_pred_mem_A c hc hA haA h

/-- The A–A cycle-neighbour path is protected: every `A`-incident path
edge is an original cycle edge. -/
lemma exists_protectedAt_of_cycle_neighbor_in_A {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) {a : V} (haA : a ∈ A)
    (hn : cycleSucc (rotateTo c (by simpa [hc] using hA haA)) ∈ A ∨
      cycleSucc (rotateTo c.reverse
        (by simpa [hc, GraphCycle.support_reverse] using hA haA)) ∈ A) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧ p.ProtectedAt c A ∧
          (p.walk.edges.toFinset ∪ {s(p.finish, p.start)}) =
            c.walk.edges.toFinset := by
  obtain ⟨p, hp, hs, hf, hne, hedges⟩ :=
    exists_protected_of_cycle_neighbor_in_A c hc hA haA hn
  refine ⟨p, hp, hs, hf, hne, ?_, hedges⟩
  intro e he
  have heP : e ∈ p.edges := (mem_AIncident_iff.1 he).1
  have : e ∈ p.walk.edges.toFinset ∪ {s(p.finish, p.start)} :=
    mem_union.2 (Or.inl heP)
  simpa [hedges] using this

/-- Adjacent leftover starts: full-`U` `ProtectedAt` path from the two
whole cycle pieces, with both endpoints in `A`. -/
lemma exists_protectedAt_of_adj_leftover_starts {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.start ≠ R.start) (hadj : G.Adj Q.start R.start) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish :=
  exists_switchOpenStarts_of_adj_leftover_starts c hc hp hs hclose hedges
    hQ hR hneQR hadj

/-- Adjacent leftover finishes: full-`U` `ProtectedAt` path from the two
whole cycle pieces of the reverse orientation, with both endpoints in `A`. -/
lemma exists_protectedAt_of_adj_leftover_ends {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.finish ≠ R.finish) (hadj : G.Adj Q.finish R.finish) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish :=
  exists_switchOpenStarts_of_adj_leftover_ends c hc hp hs hclose hedges
    hQ hR hneQR hadj

/-- Combined same-sign leftover switch: adjacent leftover starts or
adjacent leftover finishes both yield a full-`U` `ProtectedAt` path
with both endpoints in `A`. -/
lemma exists_protectedAt_of_adj_leftover_start_or_end {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hor : (Q.start ≠ R.start ∧ G.Adj Q.start R.start) ∨
      (Q.finish ≠ R.finish ∧ G.Adj Q.finish R.finish)) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.ProtectedAt c A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  rcases hor with ⟨hne, hadj⟩ | ⟨hne, hadj⟩
  · exact exists_protectedAt_of_adj_leftover_starts c hc hp hs hclose hedges
      hQ hR hne hadj
  · exact exists_protectedAt_of_adj_leftover_ends c hc hp hs hclose hedges
      hQ hR hne hadj

end Cograph
end Nikoghosyan
