/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.CycleIncidences

/-!
Same-vertex-type graph inclusion and internal-edge suppression.

If `G' ≤ G` on the same vertex type, original-edge `GraphPath` /
`GraphCycle` / `PathCover` transport in both directions: the supergraph
direction is unrestricted, and the subgraph direction requires every
undirected walk edge to survive in `G'`. Start, finish, support, and
undirected edge finsets are identical.

The concrete suppression `suppressInternal G A'` keeps every original
edge except those with both ends in `A'`. On the carrier `U \ A'`
adjacency is exactly the original adjacency, so the canonical cograph
predicate and the ordinary path-cover number `p` are unchanged. This
module does not inherit toughness, does not assume `G' = G`, and does
not construct a Hamilton path.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Generic `G' ≤ G` transport on the same vertex type -/

namespace GraphPath

/-- Map an original-edge path into a supergraph on the same vertices. -/
def ofLE {G G' : SimpleGraph V} (h : G ≤ G') (p : GraphPath G) : GraphPath G' where
  start := p.start
  finish := p.finish
  walk := p.walk.mapLe h
  isPath := (Walk.isPath_mapLe h).2 p.isPath

lemma ofLE_start {G G' : SimpleGraph V} (h : G ≤ G') (p : GraphPath G) :
    (p.ofLE h).start = p.start :=
  rfl

lemma ofLE_finish {G G' : SimpleGraph V} (h : G ≤ G') (p : GraphPath G) :
    (p.ofLE h).finish = p.finish :=
  rfl

lemma ofLE_support {G G' : SimpleGraph V} (h : G ≤ G') (p : GraphPath G) :
    (p.ofLE h).support = p.support := by
  simp [ofLE, support, Walk.support_mapLe_eq_support]

lemma ofLE_edges {G G' : SimpleGraph V} (h : G ≤ G') (p : GraphPath G) :
    (p.ofLE h).edges = p.edges := by
  simp [ofLE, edges, Walk.edges_mapLe_eq_edges]

/-- Transfer an original-edge path into another graph on the same vertices
that contains every undirected walk edge. -/
def transferEdges {G G' : SimpleGraph V} (p : GraphPath G)
    (h : ∀ e ∈ p.edges, e ∈ G'.edgeSet) : GraphPath G' where
  start := p.start
  finish := p.finish
  walk := p.walk.transfer G' fun e he => h e (mem_edges_iff.2 he)
  isPath := by
    simpa [Walk.isPath_def, Walk.support_transfer] using p.isPath

lemma transferEdges_start {G G' : SimpleGraph V} (p : GraphPath G)
    (h : ∀ e ∈ p.edges, e ∈ G'.edgeSet) :
    (p.transferEdges h).start = p.start :=
  rfl

lemma transferEdges_finish {G G' : SimpleGraph V} (p : GraphPath G)
    (h : ∀ e ∈ p.edges, e ∈ G'.edgeSet) :
    (p.transferEdges h).finish = p.finish :=
  rfl

lemma transferEdges_support {G G' : SimpleGraph V} (p : GraphPath G)
    (h : ∀ e ∈ p.edges, e ∈ G'.edgeSet) :
    (p.transferEdges h).support = p.support := by
  simp [transferEdges, support]

lemma transferEdges_edges {G G' : SimpleGraph V} (p : GraphPath G)
    (h : ∀ e ∈ p.edges, e ∈ G'.edgeSet) :
    (p.transferEdges h).edges = p.edges := by
  simp [transferEdges, edges]

end GraphPath

namespace GraphCycle

def ofLE {G G' : SimpleGraph V} (h : G ≤ G') (c : GraphCycle G) : GraphCycle G' where
  start := c.start
  walk := c.walk.mapLe h
  isCycle := (Walk.isCycle_mapLe h).2 c.isCycle

lemma ofLE_start {G G' : SimpleGraph V} (h : G ≤ G') (c : GraphCycle G) :
    (c.ofLE h).start = c.start :=
  rfl

lemma ofLE_support {G G' : SimpleGraph V} (h : G ≤ G') (c : GraphCycle G) :
    (c.ofLE h).support = c.support := by
  simp [ofLE, support, Walk.support_mapLe_eq_support]

lemma ofLE_edges {G G' : SimpleGraph V} (h : G ≤ G') (c : GraphCycle G) :
    (c.ofLE h).edges = c.edges := by
  simp [ofLE, edges, Walk.edges_mapLe_eq_edges]

lemma isCycle_transferEdges {G G' : SimpleGraph V} {u : V}
    {w : G.Walk u u} (hw : w.IsCycle)
    (h : ∀ e ∈ w.edges, e ∈ G'.edgeSet) :
    (w.transfer G' h).IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · simpa [Walk.edges_transfer] using hw.edges_nodup
  · intro heq
    have : (w.transfer G' h).Nil := by simp [heq]
    exact hw.not_nil ((Walk.nil_transfer (p := w) (h := h)).1 this)
  · simpa [Walk.support_transfer] using hw.support_nodup

def transferEdges {G G' : SimpleGraph V} (c : GraphCycle G)
    (h : ∀ e ∈ c.edges, e ∈ G'.edgeSet) : GraphCycle G' where
  start := c.start
  walk := c.walk.transfer G' fun e he => h e (mem_edges_iff.2 he)
  isCycle :=
    isCycle_transferEdges c.isCycle fun e he => h e (mem_edges_iff.2 he)

lemma transferEdges_start {G G' : SimpleGraph V} (c : GraphCycle G)
    (h : ∀ e ∈ c.edges, e ∈ G'.edgeSet) :
    (c.transferEdges h).start = c.start :=
  rfl

lemma transferEdges_support {G G' : SimpleGraph V} (c : GraphCycle G)
    (h : ∀ e ∈ c.edges, e ∈ G'.edgeSet) :
    (c.transferEdges h).support = c.support := by
  simp [transferEdges, support]

lemma transferEdges_edges {G G' : SimpleGraph V} (c : GraphCycle G)
    (h : ∀ e ∈ c.edges, e ∈ G'.edgeSet) :
    (c.transferEdges h).edges = c.edges := by
  simp [transferEdges, edges]

end GraphCycle

namespace PathCover

/-- Supergraph transport of a path cover; supports and counts are exact. -/
def ofLE {G G' : SimpleGraph V} (h : G ≤ G') {U : Finset V}
    (pc : PathCover G U) : PathCover G' U where
  paths := pc.paths.map (GraphPath.ofLE h)
  disjoint := by
    rw [List.pairwise_map]
    refine pc.disjoint.imp ?_
    intro p q hd
    simpa [GraphPath.ofLE_support] using hd
  mem_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, hp, hx'⟩ := (pc.mem_iff x).1 hx
      refine ⟨p.ofLE h, List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
      simpa [GraphPath.ofLE_support] using hx'
    · intro ⟨p', hp', hx'⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hp'
      exact (pc.mem_iff x).2 ⟨p, hp, by simpa [GraphPath.ofLE_support] using hx'⟩

lemma ofLE_card {G G' : SimpleGraph V} (h : G ≤ G') {U : Finset V}
    (pc : PathCover G U) : (pc.ofLE h).card = pc.card := by
  simp [ofLE, card]

lemma pairwise_attach_disjoint {G : SimpleGraph V}
    (l : List (GraphPath G))
    (hdis : l.Pairwise fun p q => Disjoint p.support q.support) :
    l.attach.Pairwise fun a b => Disjoint a.1.support b.1.support := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.attach_cons, List.pairwise_cons]
    have hdis' := List.pairwise_cons.1 hdis
    constructor
    · intro q hq
      rcases List.mem_map.1 hq with ⟨⟨q0, hq0⟩, _, rfl⟩
      exact hdis'.1 q0 hq0
    · exact (List.pairwise_map.2 (ih hdis'.2))

/-- Subgraph transport of a path cover whose every walk edge survives. -/
def transferEdges {G G' : SimpleGraph V} {U : Finset V} (pc : PathCover G U)
    (h : ∀ p ∈ pc.paths, ∀ e ∈ p.edges, e ∈ G'.edgeSet) :
    PathCover G' U where
  paths := pc.paths.attach.map fun x => x.1.transferEdges (h x.1 x.2)
  disjoint := by
    rw [List.pairwise_map]
    refine (pairwise_attach_disjoint pc.paths pc.disjoint).imp ?_
    intro a b hd
    simpa [GraphPath.transferEdges_support] using hd
  mem_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, hp, hx'⟩ := (pc.mem_iff x).1 hx
      refine ⟨p.transferEdges (h p hp), ?_, ?_⟩
      · exact List.mem_map.2 ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩
      · simpa [GraphPath.transferEdges_support] using hx'
    · intro ⟨p', hp', hx'⟩
      obtain ⟨⟨p, hp⟩, _, rfl⟩ := List.mem_map.1 hp'
      exact (pc.mem_iff x).2 ⟨p, hp, by simpa [GraphPath.transferEdges_support] using hx'⟩

lemma transferEdges_card {G G' : SimpleGraph V} {U : Finset V}
    (pc : PathCover G U)
    (h : ∀ p ∈ pc.paths, ∀ e ∈ p.edges, e ∈ G'.edgeSet) :
    (pc.transferEdges h).card = pc.card := by
  simp [transferEdges, card]

end PathCover

/-! ### Internal-edge suppression on a designated set `A'` -/

variable (G : SimpleGraph V)

/-- Delete every original edge with both ends in `A'`. Same vertex type. -/
def suppressInternal (A' : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ (u ∈ A' ∧ v ∈ A')
  symm := ⟨fun u v ⟨hadj, hn⟩ => ⟨hadj.symm, fun h => hn ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨fun v ⟨hadj, _⟩ => G.loopless.irrefl v hadj⟩

lemma suppressInternal_le (A' : Finset V) : suppressInternal G A' ≤ G :=
  fun _ _ h => h.1

lemma adj_suppressInternal_iff {A' : Finset V} {u v : V} :
    (suppressInternal G A').Adj u v ↔ G.Adj u v ∧ ¬ (u ∈ A' ∧ v ∈ A') :=
  Iff.rfl

/-- On the carrier outside `A'`, original adjacency is exactly unchanged. -/
lemma adj_eq_on_carrier {A' : Finset V} {u v : V}
    (hu : u ∉ A') (hv : v ∉ A') :
    (suppressInternal G A').Adj u v ↔ G.Adj u v := by
  simp [suppressInternal, hu, hv]

lemma adj_eq_on_sdiff {U A' : Finset V} {u v : V}
    (hu : u ∈ U \ A') (hv : v ∈ U \ A') :
    (suppressInternal G A').Adj u v ↔ G.Adj u v :=
  adj_eq_on_carrier G (mem_sdiff.1 hu).2 (mem_sdiff.1 hv).2

lemma mem_edgeSet_suppressInternal {A' : Finset V} {u v : V}
    (hadj : G.Adj u v) (hu : u ∉ A') (hv : v ∉ A') :
    s(u, v) ∈ (suppressInternal G A').edgeSet := by
  simpa [SimpleGraph.mem_edgeSet, adj_eq_on_carrier G hu hv] using hadj

lemma edges_subset_suppressInternal_of_disjoint {A' : Finset V}
    (p : GraphPath G) (hd : Disjoint p.support A') :
    ∀ e ∈ p.edges, e ∈ (suppressInternal G A').edgeSet := by
  intro e he
  refine Sym2.inductionOn e (fun a b he => ?_) he
  have ha : a ∈ p.support := GraphPath.mem_support_of_mem_edge he (by simp)
  have hb : b ∈ p.support := GraphPath.mem_support_of_mem_edge he (by simp)
  have ha' : a ∉ A' := disjoint_left.1 hd ha
  have hb' : b ∉ A' := disjoint_left.1 hd hb
  have hadj : G.Adj a b := by
    simpa [SimpleGraph.mem_edgeSet] using p.edges_subset_edgeSet _ he
  exact mem_edgeSet_suppressInternal G hadj ha' hb'

lemma cycle_edges_subset_suppressInternal_of_disjoint {A' : Finset V}
    (c : GraphCycle G) (hd : Disjoint c.support A') :
    ∀ e ∈ c.edges, e ∈ (suppressInternal G A').edgeSet := by
  intro e he
  refine Sym2.inductionOn e (fun a b he => ?_) he
  have ha : a ∈ c.support := by
    simpa [GraphCycle.support] using
      List.mem_toFinset.2
        (c.walk.mem_support_of_mem_edges (GraphCycle.mem_edges_iff.1 he) (by simp))
  have hb : b ∈ c.support := by
    simpa [GraphCycle.support] using
      List.mem_toFinset.2
        (c.walk.mem_support_of_mem_edges (GraphCycle.mem_edges_iff.1 he) (by simp))
  have ha' : a ∉ A' := disjoint_left.1 hd ha
  have hb' : b ∉ A' := disjoint_left.1 hd hb
  have hadj : G.Adj a b := by
    simpa [SimpleGraph.mem_edgeSet] using
      c.walk.edges_subset_edgeSet (GraphCycle.mem_edges_iff.1 he)
  exact mem_edgeSet_suppressInternal G hadj ha' hb'

namespace GraphPath

/-- A host path whose support avoids `A'` is a path of the suppressed graph. -/
def toSuppressInternal {A' : Finset V} (p : GraphPath G)
    (hd : Disjoint p.support A') : GraphPath (suppressInternal G A') :=
  p.transferEdges (edges_subset_suppressInternal_of_disjoint G p hd)

lemma toSuppressInternal_start {A' : Finset V} (p : GraphPath G)
    (hd : Disjoint p.support A') :
    (toSuppressInternal (G := G) p hd).start = p.start :=
  rfl

lemma toSuppressInternal_finish {A' : Finset V} (p : GraphPath G)
    (hd : Disjoint p.support A') :
    (toSuppressInternal (G := G) p hd).finish = p.finish :=
  rfl

lemma toSuppressInternal_support {A' : Finset V} (p : GraphPath G)
    (hd : Disjoint p.support A') :
    (toSuppressInternal (G := G) p hd).support = p.support :=
  transferEdges_support p _

lemma toSuppressInternal_edges {A' : Finset V} (p : GraphPath G)
    (hd : Disjoint p.support A') :
    (toSuppressInternal (G := G) p hd).edges = p.edges :=
  transferEdges_edges p _

/-- A suppressed-graph path is an original-edge path of the host. -/
def ofSuppressInternal {A' : Finset V}
    (p : GraphPath (suppressInternal G A')) : GraphPath G :=
  p.ofLE (suppressInternal_le G A')

lemma ofSuppressInternal_start {A' : Finset V}
    (p : GraphPath (suppressInternal G A')) :
    (ofSuppressInternal (G := G) p).start = p.start :=
  rfl

lemma ofSuppressInternal_finish {A' : Finset V}
    (p : GraphPath (suppressInternal G A')) :
    (ofSuppressInternal (G := G) p).finish = p.finish :=
  rfl

lemma ofSuppressInternal_support {A' : Finset V}
    (p : GraphPath (suppressInternal G A')) :
    (ofSuppressInternal (G := G) p).support = p.support :=
  ofLE_support _ p

lemma ofSuppressInternal_edges {A' : Finset V}
    (p : GraphPath (suppressInternal G A')) :
    (ofSuppressInternal (G := G) p).edges = p.edges :=
  ofLE_edges _ p

end GraphPath

namespace GraphCycle

def toSuppressInternal {A' : Finset V} (c : GraphCycle G)
    (hd : Disjoint c.support A') : GraphCycle (suppressInternal G A') :=
  c.transferEdges (cycle_edges_subset_suppressInternal_of_disjoint G c hd)

lemma toSuppressInternal_start {A' : Finset V} (c : GraphCycle G)
    (hd : Disjoint c.support A') :
    (toSuppressInternal (G := G) c hd).start = c.start :=
  rfl

lemma toSuppressInternal_support {A' : Finset V} (c : GraphCycle G)
    (hd : Disjoint c.support A') :
    (toSuppressInternal (G := G) c hd).support = c.support :=
  transferEdges_support c _

lemma toSuppressInternal_edges {A' : Finset V} (c : GraphCycle G)
    (hd : Disjoint c.support A') :
    (toSuppressInternal (G := G) c hd).edges = c.edges :=
  transferEdges_edges c _

def ofSuppressInternal {A' : Finset V}
    (c : GraphCycle (suppressInternal G A')) : GraphCycle G :=
  c.ofLE (suppressInternal_le G A')

lemma ofSuppressInternal_start {A' : Finset V}
    (c : GraphCycle (suppressInternal G A')) :
    (ofSuppressInternal (G := G) c).start = c.start :=
  rfl

lemma ofSuppressInternal_support {A' : Finset V}
    (c : GraphCycle (suppressInternal G A')) :
    (ofSuppressInternal (G := G) c).support = c.support :=
  ofLE_support _ c

lemma ofSuppressInternal_edges {A' : Finset V}
    (c : GraphCycle (suppressInternal G A')) :
    (ofSuppressInternal (G := G) c).edges = c.edges :=
  ofLE_edges _ c

end GraphCycle

lemma PathCover.paths_support_disjoint_of_carrier {U A' : Finset V}
    (hU : Disjoint U A') (pc : PathCover G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) : Disjoint p.support A' :=
  disjoint_of_subset_left (pc.support_subset hp) hU

/-- Host path covers of a carrier disjoint from `A'` are path covers of
the suppressed graph, with identical path count. -/
def PathCover.toSuppressInternal {U A' : Finset V} (hU : Disjoint U A')
    (pc : PathCover G U) : PathCover (suppressInternal G A') U :=
  pc.transferEdges fun p hp e he =>
    edges_subset_suppressInternal_of_disjoint G p
      (PathCover.paths_support_disjoint_of_carrier (G := G) hU pc hp) e he

lemma PathCover.toSuppressInternal_card {U A' : Finset V} (hU : Disjoint U A')
    (pc : PathCover G U) :
    (pc.toSuppressInternal (G := G) hU).card = pc.card :=
  PathCover.transferEdges_card pc _

/-- Suppressed-graph path covers of any carrier are host path covers. -/
def PathCover.ofSuppressInternal {U A' : Finset V}
    (pc : PathCover (suppressInternal G A') U) : PathCover G U :=
  pc.ofLE (suppressInternal_le G A')

lemma PathCover.ofSuppressInternal_card {U A' : Finset V}
    (pc : PathCover (suppressInternal G A') U) :
    (PathCover.ofSuppressInternal (G := G) pc).card = pc.card :=
  PathCover.ofLE_card _ pc

/-- Ordinary path-cover number of a carrier disjoint from `A'` is
unchanged by internal-edge suppression. -/
theorem pathCoverNumber_suppressInternal {U A' : Finset V}
    (hU : Disjoint U A') :
    pathCoverNumber (suppressInternal G A') U = pathCoverNumber G U := by
  apply le_antisymm
  · obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
    have := pathCoverNumber_le (G := suppressInternal G A')
      (pc.toSuppressInternal (G := G) hU)
    simpa [PathCover.toSuppressInternal_card, hpc] using this
  · obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := suppressInternal G A') U
    have := pathCoverNumber_le (G := G)
      (PathCover.ofSuppressInternal (G := G) pc)
    simpa [PathCover.ofSuppressInternal_card, hpc] using this

theorem pathCoverNumber_carrier (U A' : Finset V) :
    pathCoverNumber (suppressInternal G A') (U \ A') =
      pathCoverNumber G (U \ A') :=
  pathCoverNumber_suppressInternal G (Finset.disjoint_sdiff).symm

lemma InducedP4_suppressInternal {A' : Finset V} {a b c d : V}
    (ha : a ∉ A') (hb : b ∉ A') (hc : c ∉ A') (hd : d ∉ A') :
    InducedP4 (suppressInternal G A') a b c d ↔ InducedP4 G a b c d := by
  simp [InducedP4, adj_eq_on_carrier G ha hb, adj_eq_on_carrier G hb hc,
    adj_eq_on_carrier G hc hd, adj_eq_on_carrier G ha hc,
    adj_eq_on_carrier G ha hd, adj_eq_on_carrier G hb hd]

/-- Canonical cograph predicate on a carrier disjoint from `A'` is
unchanged: every induced `P₄` uses only carrier vertices, hence only
original edges that survive suppression. -/
theorem IsCograph_suppressInternal {U A' : Finset V} (hU : Disjoint U A') :
    IsCograph (suppressInternal G A') U ↔ IsCograph G U := by
  constructor
  · intro h a b c d ha hb hc hd hp
    have ha' : a ∉ A' := disjoint_left.1 hU ha
    have hb' : b ∉ A' := disjoint_left.1 hU hb
    have hc' : c ∉ A' := disjoint_left.1 hU hc
    have hd' : d ∉ A' := disjoint_left.1 hU hd
    exact h ha hb hc hd ((InducedP4_suppressInternal G ha' hb' hc' hd').2 hp)
  · intro h a b c d ha hb hc hd hp
    have ha' : a ∉ A' := disjoint_left.1 hU ha
    have hb' : b ∉ A' := disjoint_left.1 hU hb
    have hc' : c ∉ A' := disjoint_left.1 hU hc
    have hd' : d ∉ A' := disjoint_left.1 hU hd
    exact h ha hb hc hd ((InducedP4_suppressInternal G ha' hb' hc' hd').1 hp)

theorem IsCograph_carrier (U A' : Finset V) :
    IsCograph (suppressInternal G A') (U \ A') ↔ IsCograph G (U \ A') :=
  IsCograph_suppressInternal G (Finset.disjoint_sdiff).symm

end Nikoghosyan
