import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching
import Nikoghosyan.Factor

/-!
Original-edge path splice, genuine cycle closing, Mathlib Hamiltonian
witnesses, and the spanning degree-two ↔ cycle-factor bridge.

Gadget edges are never used: every walk below lives in the original `G`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

lemma support_nodup (p : GraphPath G) : p.walk.support.Nodup :=
  (Walk.isPath_def _).1 p.isPath

lemma card_support (p : GraphPath G) : p.support.card = p.walk.length + 1 := by
  simp [support, List.toFinset_card_of_nodup p.support_nodup, Walk.length_support]

/-- Join two vertex-disjoint original-edge paths by an original edge from
the finish of the first to the start of the second. -/
def splice (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) : GraphPath G where
  start := p.start
  finish := q.finish
  walk := p.walk.append (Walk.cons h q.walk)
  isPath := by
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons]
    refine p.support_nodup.append q.support_nodup ?_
    intro x hxp hxq
    exact Finset.disjoint_left.1 hd
      (List.mem_toFinset.2 hxp) (List.mem_toFinset.2 hxq)

@[simp]
lemma support_splice (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) :
    (p.splice q h hd).support = p.support ∪ q.support := by
  simp [splice, GraphPath.support, Walk.support_append, Walk.support_cons]

lemma reverse_splice_start (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) :
    (p.splice q h hd).reverse.start = q.finish :=
  rfl

lemma reverse_splice_finish (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) :
    (p.splice q h hd).reverse.finish = p.start :=
  rfl

/-- If a path contains the chord between its endpoints, it is a single edge. -/
lemma length_eq_one_of_mem_edges_start_finish :
    ∀ (p : GraphPath G), s(p.start, p.finish) ∈ p.walk.edges → p.walk.length = 1 := by
  intro p he
  rcases p with ⟨start, finish, walk, isPath⟩
  change s(start, finish) ∈ walk.edges at he
  have hneSF : start ≠ finish := by
    intro heq
    subst heq
    have : walk.Nil := (Walk.isPath_iff_nil).1 isPath
    cases this
    simp at he
  obtain ⟨w, hadj, q, hp⟩ := Walk.exists_eq_cons_of_ne hneSF walk
  subst hp
  have hq : q.IsPath ∧ start ∉ q.support := (Walk.cons_isPath_iff hadj q).1 isPath
  have he' : s(start, finish) = s(start, w) ∨ s(start, finish) ∈ q.edges :=
    List.mem_cons.1 he
  rcases he' with hfirst | hrest
  · have hfin : w = finish := by
      obtain ⟨_, h2⟩ | ⟨_, h2⟩ := Sym2.eq_iff.mp hfirst
      · exact h2.symm
      · exact (hneSF h2.symm).elim
    subst hfin
    have hlen0 : q.length = 0 :=
      Walk.length_eq_zero_iff.2 ((Walk.isPath_iff_nil).1 hq.1)
    simp [hlen0]
  · exact (hq.2 (q.mem_support_of_mem_edges hrest (by simp))).elim

/-- Close a path of order at least three by an original edge from finish to
start. Two-vertex closed walks are not admitted. -/
def toCycle (p : GraphPath G) (h : G.Adj p.finish p.start)
    (h3 : 3 ≤ p.support.card) : GraphCycle G where
  start := p.start
  walk := p.walk.concat h
  isCycle := by
    have hrev : (Walk.cons h.symm p.walk.reverse).IsCycle := by
      rw [Walk.cons_isCycle_iff]
      refine ⟨p.isPath.reverse, ?_⟩
      intro he
      have he' : s(p.start, p.finish) ∈ p.walk.edges := by
        simpa [Walk.edges_reverse] using he
      have hlen := length_eq_one_of_mem_edges_start_finish p he'
      have hcard : p.support.card = 2 := by
        rw [p.card_support, hlen]
      omega
    have : (p.walk.concat h).reverse.IsCycle := by
      rwa [Walk.reverse_concat]
    exact (Walk.isCycle_reverse).1 this

@[simp]
lemma support_toCycle (p : GraphPath G) (h : G.Adj p.finish p.start)
    (h3 : 3 ≤ p.support.card) :
    (p.toCycle h h3).support = p.support := by
  simp [toCycle, GraphCycle.support, GraphPath.support, Walk.support_concat]

end GraphPath

namespace GraphCycle

lemma isHamiltonianCycle_of_support_eq_univ (c : GraphCycle G)
    (h : c.support = univ) : c.walk.IsHamiltonianCycle := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨c.isCycle, ?_⟩
  have hlen : c.walk.length = c.support.card := c.card_support.symm
  have hcard : c.support.card = Fintype.card V := by simp [h]
  exact hlen.trans hcard

lemma isHamiltonian_of_support_eq_univ (c : GraphCycle G)
    (h : c.support = univ) : G.IsHamiltonian := by
  intro _
  exact ⟨c.start, c.walk, c.isHamiltonianCycle_of_support_eq_univ h⟩

end GraphCycle

/-- Under order at least three, Mathlib Hamiltonicity is equivalent to the
existence of a genuine spanning original-edge cycle. -/
lemma isHamiltonian_iff_exists_spanning_graphCycle
    (hord : 3 ≤ Fintype.card V) :
    G.IsHamiltonian ↔ ∃ c : GraphCycle G, c.support = univ := by
  constructor
  · intro hH
    have hne : Fintype.card V ≠ 1 := by omega
    obtain ⟨a, w, hw⟩ := hH hne
    refine ⟨⟨a, w, hw.isCycle⟩, ?_⟩
    ext x
    simp [GraphCycle.support, hw.mem_support x]
  · rintro ⟨c, hc⟩
    exact c.isHamiltonian_of_support_eq_univ hc

/-- Spanning subgraph in which every vertex has degree exactly two. -/
def IsSpanningDegreeTwo (F : G.Subgraph) : Prop :=
  F.IsSpanning ∧ ∀ v : V, (F.neighborSet v).ncard = 2

lemma spanningCoe_neighborSet (F : G.Subgraph) (v : V) :
    F.spanningCoe.neighborSet v = F.neighborSet v :=
  rfl

lemma isCycles_of_degree_two {F : G.Subgraph}
    (hdeg : ∀ v : V, (F.neighborSet v).ncard = 2) :
    F.spanningCoe.IsCycles := by
  intro v _
  simpa [spanningCoe_neighborSet] using hdeg v

lemma neighborSet_nonempty_of_degree_two {F : G.Subgraph}
    (hdeg : ∀ v : V, (F.neighborSet v).ncard = 2) (v : V) :
    (F.neighborSet v).Nonempty := by
  have hpos : 0 < (F.neighborSet v).ncard := by
    rw [hdeg v]
    exact two_pos
  exact (Set.ncard_pos (Set.toFinite _)).1 hpos

lemma connectedComponent_supp_nonempty (c : G.ConnectedComponent) :
    c.supp.Nonempty :=
  c.ind fun v => ⟨v, by simp [ConnectedComponent.mem_supp_iff]⟩

lemma connectedComponent_disjoint_supp {c d : G.ConnectedComponent} (h : c ≠ d) :
    Disjoint c.supp d.supp := by
  rw [Set.disjoint_iff]
  intro x hx
  apply h
  simp [ConnectedComponent.mem_supp_iff] at hx
  rw [← hx.1, hx.2]

lemma pairwise_disjoint_of_mem {α} {s : α → Finset V} {l : List α}
    (h : l.Pairwise fun a b => Disjoint (s a) (s b))
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    Disjoint (s a) (s b) := by
  induction l generalizing a b with
  | nil => cases ha
  | cons x xs ih =>
    have h' := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact (hne rfl).elim
    · exact h'.1 b hb'
    · exact (h'.1 a ha').symm
    · exact ih h'.2 ha' hb' hne

lemma exists_graphCycle_of_component (F : G.Subgraph)
    (hdeg : ∀ v : V, (F.neighborSet v).ncard = 2)
    (c : F.spanningCoe.ConnectedComponent) :
    ∃ cy : GraphCycle G, (cy.support : Set V) = c.supp := by
  obtain ⟨v, hv⟩ := connectedComponent_supp_nonempty (G := F.spanningCoe) c
  have hn : (F.spanningCoe.neighborSet v).Nonempty := by
    simpa [spanningCoe_neighborSet] using neighborSet_nonempty_of_degree_two hdeg v
  obtain ⟨p, hp, hverts⟩ :=
    (isCycles_of_degree_two hdeg).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  refine ⟨⟨v, p.mapLe F.spanningCoe_le, (Walk.isCycle_mapLe F.spanningCoe_le).2 hp⟩, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ p.support := by
      simpa [GraphCycle.support, Walk.support_mapLe_eq_support] using hx
    have : x ∈ p.toSubgraph.verts := (Walk.mem_verts_toSubgraph p).2 hx'
    exact hverts ▸ this
  · intro hx
    have : x ∈ p.toSubgraph.verts := hverts ▸ hx
    have hx' : x ∈ p.support := (Walk.mem_verts_toSubgraph p).1 this
    simpa [GraphCycle.support, Walk.support_mapLe_eq_support] using hx'

noncomputable def graphCycleOfComponent (F : G.Subgraph)
    (hdeg : ∀ v : V, (F.neighborSet v).ncard = 2)
    (c : F.spanningCoe.ConnectedComponent) : GraphCycle G :=
  Classical.choose (exists_graphCycle_of_component F hdeg c)

lemma mem_graphCycleOfComponent_support (F : G.Subgraph)
    (hdeg : ∀ v : V, (F.neighborSet v).ncard = 2)
    (c : F.spanningCoe.ConnectedComponent) {x : V} :
    x ∈ (graphCycleOfComponent F hdeg c).support ↔ x ∈ c.supp := by
  have h := Classical.choose_spec (exists_graphCycle_of_component F hdeg c)
  constructor
  · intro hx
    have : x ∈ ((graphCycleOfComponent F hdeg c).support : Set V) := hx
    exact h ▸ this
  · intro hx
    have : x ∈ ((graphCycleOfComponent F hdeg c).support : Set V) := h ▸ hx
    exact this

namespace CycleFactor

/-- From a spanning degree-two subgraph, take the Mathlib cycle of each
selected-subgraph component and transport it along `spanningCoe ≤ G`. -/
noncomputable def ofSpanningDegreeTwo {F : G.Subgraph}
    (hF : IsSpanningDegreeTwo F) : CycleFactor G where
  cycles :=
    (univ : Finset F.spanningCoe.ConnectedComponent).toList.map
      (graphCycleOfComponent F hF.2)
  disjoint := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_
      (univ : Finset F.spanningCoe.ConnectedComponent).nodup_toList
    intro c d hne
    rw [Finset.disjoint_left]
    intro x hxc hxd
    have hxcS : x ∈ c.supp := (mem_graphCycleOfComponent_support F hF.2 c).1 hxc
    have hxdS : x ∈ d.supp := (mem_graphCycleOfComponent_support F hF.2 d).1 hxd
    exact (connectedComponent_disjoint_supp (G := F.spanningCoe) hne).le_bot ⟨hxcS, hxdS⟩
  mem_iff := by
    intro x
    let c := F.spanningCoe.connectedComponentMk x
    refine ⟨graphCycleOfComponent F hF.2 c, ?_, ?_⟩
    · exact List.mem_map.2 ⟨c, Finset.mem_toList.2 (mem_univ c), rfl⟩
    · exact (mem_graphCycleOfComponent_support F hF.2 c).2
        (by simp [c, ConnectedComponent.mem_supp_iff])

lemma eq_of_mem_support (F : CycleFactor G) {c d : GraphCycle G}
    (hc : c ∈ F.cycles) (hd : d ∈ F.cycles) {x : V}
    (hxc : x ∈ c.support) (hxd : x ∈ d.support) : c = d := by
  by_contra hne
  have : Disjoint c.support d.support :=
    pairwise_disjoint_of_mem (s := fun c : GraphCycle G => c.support) F.disjoint hc hd hne
  exact Finset.disjoint_left.1 this hxc hxd

/-- The spanning subgraph whose edges are the original cycle edges of `F`. -/
def toSubgraph (F : CycleFactor G) : G.Subgraph where
  verts := Set.univ
  Adj := fun x y => ∃ c ∈ F.cycles, c.walk.toSubgraph.Adj x y
  adj_sub := by
    intro x y hxy
    obtain ⟨c, _, hc⟩ := hxy
    exact c.walk.toSubgraph.adj_sub hc
  edge_vert := by
    intro _ _ _
    trivial
  symm := ⟨fun a b h =>
    match h with
    | ⟨c, hc, hadj⟩ => ⟨c, hc, hadj.symm⟩⟩

lemma toSubgraph_isSpanning (F : CycleFactor G) : F.toSubgraph.IsSpanning :=
  fun _ => trivial

lemma toSubgraph_ncard_eq_two (F : CycleFactor G) (x : V) :
    (F.toSubgraph.neighborSet x).ncard = 2 := by
  obtain ⟨c, hc, hx⟩ := F.mem_iff x
  have hxL : x ∈ c.walk.support := by simpa [GraphCycle.support] using hx
  have hneigh :
      F.toSubgraph.neighborSet x = c.walk.toSubgraph.neighborSet x := by
    ext y
    constructor
    · intro hy
      obtain ⟨d, hd, hadj⟩ := hy
      have hxD : x ∈ d.support := by
        have : x ∈ d.walk.toSubgraph.verts := d.walk.toSubgraph.edge_vert hadj
        simpa [GraphCycle.support, List.mem_toFinset, Walk.mem_verts_toSubgraph] using this
      have : d = c := F.eq_of_mem_support hd hc hxD hx
      subst this
      exact hadj
    · intro hy
      exact ⟨c, hc, hy⟩
  rw [hneigh]
  exact Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two c.isCycle hxL

lemma toSubgraph_isSpanningDegreeTwo (F : CycleFactor G) :
    IsSpanningDegreeTwo F.toSubgraph :=
  ⟨F.toSubgraph_isSpanning, F.toSubgraph_ncard_eq_two⟩

end CycleFactor

lemma exists_cycleFactor_iff_spanningDegreeTwo :
    Nonempty (CycleFactor G) ↔ ∃ F : G.Subgraph, IsSpanningDegreeTwo F := by
  constructor
  · intro ⟨CF⟩
    exact ⟨CF.toSubgraph, CF.toSubgraph_isSpanningDegreeTwo⟩
  · intro ⟨F, hF⟩
    exact ⟨CycleFactor.ofSpanningDegreeTwo hF⟩

lemma exists_cycleFactor_of_spanningDegreeTwo {F : G.Subgraph}
    (hF : IsSpanningDegreeTwo F) : Nonempty (CycleFactor G) :=
  ⟨CycleFactor.ofSpanningDegreeTwo hF⟩

end Nikoghosyan

