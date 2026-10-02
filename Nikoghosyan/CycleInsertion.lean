/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.CycleAssembly

/-!
Elementary original-edge one-vertex cycle insertion.

Given an actual original path whose two distinct endpoints are original
neighbours of an outside vertex `x`, concatenate `x` at the start and
close by the original edge from the finish back to `x`. The result is a
genuine simple cycle of order at least three whose support is
`insert x p.support`.

This construction takes the path as input. It does not prove that such a
path exists, and it is not the manuscript one-vertex insertion corollary.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

lemma two_le_card_support_of_ne_ends {p : GraphPath G}
    (hne : p.start ≠ p.finish) : 2 ≤ p.support.card := by
  have hnil : ¬ p.walk.Nil := fun h => hne (p.isPath.nil_iff_eq.1 h)
  have hpos : 0 < p.walk.length := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hnil (Walk.length_eq_zero_iff.1 h0)
  have hcard := p.card_support
  omega

lemma three_le_card_insert_of_ne_ends {p : GraphPath G} {x : V}
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    3 ≤ (insert x p.support).card := by
  have h2 := two_le_card_support_of_ne_ends hne
  have hcard : (insert x p.support).card = p.support.card + 1 :=
    card_insert_of_notMem hx
  omega

/-- Concatenate an outside vertex at the start of an original path and
close by the original edge from the finish to that vertex. -/
noncomputable def insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) : GraphCycle G :=
  (p.consAdj hs hx).toCycle hf (by
    simpa [support_consAdj] using three_le_card_insert_of_ne_ends hx hne)

lemma support_insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    (p.insertVertexCycle hs hf hx hne).support = insert x p.support := by
  simpa [insertVertexCycle, support_consAdj] using
    support_toCycle (p.consAdj hs hx) hf
      (by simpa [support_consAdj] using three_le_card_insert_of_ne_ends hx hne)

lemma three_le_card_support_insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    3 ≤ (p.insertVertexCycle hs hf hx hne).support.card := by
  rw [support_insertVertexCycle]
  exact three_le_card_insert_of_ne_ends hx hne

lemma card_support_insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    (p.insertVertexCycle hs hf hx hne).support.card = p.support.card + 1 := by
  rw [support_insertVertexCycle, card_insert_of_notMem hx]

end GraphPath

/-- Existence form of the elementary insertion: an original path with
distinct endpoints adjacent to an outside vertex yields a genuine original
cycle through that vertex. -/
theorem exists_graphCycle_insert (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    ∃ c : GraphCycle G,
      c.support = insert x p.support ∧
        3 ≤ c.support.card ∧
        c.support.card = p.support.card + 1 :=
  ⟨p.insertVertexCycle hs hf hx hne,
    p.support_insertVertexCycle hs hf hx hne,
    p.three_le_card_support_insertVertexCycle hs hf hx hne,
    p.card_support_insertVertexCycle hs hf hx hne⟩

/-- If the input path spans `univ.erase x`, the inserted cycle is spanning. -/
theorem exists_spanning_graphCycle_insert (p : GraphPath G) {x : V}
    (hp : p.support = univ.erase x)
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hne : p.start ≠ p.finish) :
    ∃ c : GraphCycle G, c.support = univ := by
  have hx : x ∉ p.support := by simp [hp]
  obtain ⟨c, hc, _h3, _hcard⟩ := exists_graphCycle_insert p hs hf hx hne
  refine ⟨c, ?_⟩
  simpa [hp, insert_erase (mem_univ x)] using hc

end Nikoghosyan
