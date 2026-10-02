/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Data.Fintype.Card

/-!
Unrestricted-color edge colorings, properly colored genuine cycles, and
Yeo splitting vertices. Ordinary undirected edge colors only: the color of
an adjacency is independent of orientation and of the adjacency proof.

Source: Di Guardia–Laurent–Tortora de Falco–Vaux Auclair, FSCD 2025,
Sections 2–3 and 6.1 (ordinary-edge specialization of local coloring).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan
namespace Yeo

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [DecidableEq C]
variable {G : SimpleGraph V}

/-- Color of actual undirected edges of `G`. The accessor is invariant under
reversing the edge. Because `G.Adj` is a proposition, it is also invariant
under replacing the adjacency proof. -/
structure EdgeColoring (G : SimpleGraph V) (C : Type*) where
  color : ∀ {u v : V}, G.Adj u v → C
  color_symm : ∀ {u v : V} (h : G.Adj u v), color h = color h.symm

namespace EdgeColoring

variable (c : EdgeColoring G C)

lemma color_proof {u v : V} (h h' : G.Adj u v) : c.color h = c.color h' :=
  congrArg c.color (Subsingleton.elim h h')

/-- Color of a dart: the color of its underlying undirected edge. -/
def dartColor (d : G.Dart) : C :=
  c.color d.adj

lemma dartColor_symm (d : G.Dart) : c.dartColor d.symm = c.dartColor d :=
  (c.color_symm d.adj).symm

lemma dartColor_eq_of_edge {d e : G.Dart} (h : d.edge = e.edge) :
    c.dartColor d = c.dartColor e := by
  obtain rfl | rfl := (dart_edge_eq_iff d e).1 h
  · rfl
  · exact c.dartColor_symm e

/-- Finite set of colors that actually occur on edges of `G`. Isolated
vertices contribute nothing; an edgeless graph has empty used-color set. -/
noncomputable def usedColors : Finset C :=
  (univ : Finset V).biUnion fun u =>
    (univ : Finset V).biUnion fun w =>
      if h : G.Adj u w then {c.color h} else ∅

lemma mem_usedColors_color {u v : V} (h : G.Adj u v) : c.color h ∈ c.usedColors := by
  rw [usedColors, mem_biUnion]
  refine ⟨u, mem_univ u, ?_⟩
  rw [mem_biUnion]
  refine ⟨v, mem_univ v, ?_⟩
  simp [h]

lemma mem_usedColors_dartColor (d : G.Dart) : c.dartColor d ∈ c.usedColors :=
  c.mem_usedColors_color d.adj

end EdgeColoring

/-- Consecutive darts of a walk have pairwise distinct colors. This is the
open-path (no wrap-around) alternating condition. -/
def IsAlternating {u v : V} (w : G.Walk u v) (c : EdgeColoring G C) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < w.darts.length),
    c.dartColor (w.darts[i]'(Nat.lt_of_succ_lt hi)) ≠
      c.dartColor (w.darts[i + 1]'hi)

/-- A genuine simple cycle whose consecutive edge colors, including last
versus first, are all distinct. A backtracking length-two closed walk is
excluded by `Walk.IsCycle`. -/
def IsProperlyColored {u : V} (w : G.Walk u u) (c : EdgeColoring G C) : Prop :=
  w.IsCycle ∧
    IsAlternating w c ∧
      ∀ (h : ¬ w.Nil), c.dartColor (w.firstDart h) ≠ c.dartColor (w.lastDart h)

def HasProperlyColoredCycle (c : EdgeColoring G C) : Prop :=
  ∃ (u : V) (w : G.Walk u u), IsProperlyColored w c

/-- Vertex set of `G - v`. -/
abbrev deleteSet (v : V) : Set V := {w | w ≠ v}

/-- The graph `G - v`. -/
abbrev deleteGraph (G : SimpleGraph V) (v : V) : SimpleGraph {w // w ≠ v} :=
  G.induce (deleteSet v)

/-- Yeo splitting vertex: every connected component of `G - v` receives only
one color of edges from `v`. Isolated `v` (no incident edges) satisfies this
vacuously. -/
def SplittingVertex (c : EdgeColoring G C) (v : V) : Prop :=
  ∀ (x y : {w : V // w ≠ v}),
    ∀ (hx : G.Adj v x.1) (hy : G.Adj v y.1),
      (deleteGraph G v).Reachable x y → c.color hx = c.color hy

/-- Cycle form of splitting: every genuine simple cycle through `v` has a
cusp at `v`, i.e. the two cycle-edges incident to `v` have the same color. -/
def CycleSplittingVertex (c : EdgeColoring G C) (v : V) : Prop :=
  ∀ {u : V} (w : G.Walk u u) (hcyc : w.IsCycle) (hv : v ∈ w.support),
    c.dartColor ((w.rotate v hv).firstDart (hcyc.rotate hv).not_nil) =
      c.dartColor ((w.rotate v hv).lastDart (hcyc.rotate hv).not_nil)

lemma isProperlyColored_not_nil {u : V} {w : G.Walk u u} {c : EdgeColoring G C}
    (h : IsProperlyColored w c) : ¬ w.Nil :=
  h.1.not_nil

lemma isProperlyColored_three_le_length {u : V} {w : G.Walk u u} {c : EdgeColoring G C}
    (h : IsProperlyColored w c) : 3 ≤ w.length :=
  h.1.three_le_length

lemma SplittingVertex.of_not_adj (c : EdgeColoring G C) (v : V)
    (h : ∀ w : V, ¬ G.Adj v w) : SplittingVertex c v := by
  intro x y hx _hy
  exact (h x.1 hx).elim

lemma SplittingVertex.of_edgeless (c : EdgeColoring G C)
    (h : G = ⊥) (v : V) : SplittingVertex c v :=
  SplittingVertex.of_not_adj c v (by intro w hw; simp [h] at hw)

end Yeo
end Nikoghosyan
