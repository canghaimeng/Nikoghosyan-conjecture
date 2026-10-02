import Nikoghosyan.Basic

/-!
Original-edge paths: nonempty simple walks in `G`, including singletons.
-/

set_option linter.unusedSectionVars false

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A simple path of `G` using only original edges. The nil walk is the
singleton path at its unique vertex. -/
structure GraphPath where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace GraphPath

variable {G}

/-- Vertex support of a path, as an original-vertex finset. -/
def support (p : GraphPath G) : Finset V :=
  p.walk.support.toFinset

lemma start_mem_support (p : GraphPath G) : p.start ∈ p.support := by
  simp [support, Walk.start_mem_support]

lemma finish_mem_support (p : GraphPath G) : p.finish ∈ p.support := by
  simp [support, Walk.end_mem_support]

lemma support_nonempty (p : GraphPath G) : p.support.Nonempty :=
  ⟨p.start, p.start_mem_support⟩

/-- The singleton path at `v`. -/
def singleton (v : V) : GraphPath G where
  start := v
  finish := v
  walk := Walk.nil
  isPath := Walk.IsPath.nil

@[simp]
lemma support_singleton (v : V) : (singleton (G := G) v).support = {v} := by
  simp [singleton, support]

/-- Reversal preserves the original-edge path structure. -/
def reverse (p : GraphPath G) : GraphPath G where
  start := p.finish
  finish := p.start
  walk := p.walk.reverse
  isPath := p.isPath.reverse

@[simp]
lemma support_reverse (p : GraphPath G) : p.reverse.support = p.support := by
  simp [reverse, support, Walk.support_reverse]

lemma not_mem_list_support {x : V} {p : GraphPath G} (hx : x ∉ p.support) :
    x ∉ p.walk.support := by
  simpa [support] using hx

/-- Concatenate an original edge at the start of a path. -/
def consAdj {x : V} (p : GraphPath G) (h : G.Adj x p.start) (hx : x ∉ p.support) :
    GraphPath G where
  start := x
  finish := p.finish
  walk := Walk.cons h p.walk
  isPath := p.isPath.cons (not_mem_list_support hx)

@[simp]
lemma support_consAdj {x : V} (p : GraphPath G) (h : G.Adj x p.start)
    (hx : x ∉ p.support) :
    (p.consAdj h hx).support = insert x p.support := by
  simp [consAdj, support]

/-- Concatenate an original edge at the finish of a path. -/
def concatAdj {x : V} (p : GraphPath G) (h : G.Adj p.finish x) (hx : x ∉ p.support) :
    GraphPath G where
  start := p.start
  finish := x
  walk := p.walk.concat h
  isPath := p.isPath.concat (not_mem_list_support hx) h

@[simp]
lemma support_concatAdj {x : V} (p : GraphPath G) (h : G.Adj p.finish x)
    (hx : x ∉ p.support) :
    (p.concatAdj h hx).support = insert x p.support := by
  simp [concatAdj, support]

end GraphPath

end Nikoghosyan
