/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.FactorAssembly
import Nikoghosyan.Prerequisites.YeoGeneral

/-!
Physical-cross-edge auxiliary graph of an original cycle factor.

Vertices: one block-index vertex per factor cycle, together with one
subdivision vertex for EACH physical original cross edge. Distinct original
edges joining the same two blocks remain distinct vertices. The graph is
simple and bipartite: each physical vertex is joined only to its two actual
endpoint blocks.

Incidence `block — physical` is coloured by the pair `(block index, port
class of the original endpoint in that block)`, so palettes of different
blocks are disjoint. Port-class / spanning-path realisation is a generic
helper (`PortData`); the actual cograph `R` theorem is not assumed.

A properly coloured four-edge auxiliary cycle on two blocks realises
opposite ports in each block; assembling those spanning original paths
with the two physical cross edges yields a group replacement that
contradicts a globally minimum cycle count.

Original 1-toughness of order ≥ 3 excludes bridges. Original walks map to
auxiliary routes by holding internal block steps stationary and replacing
each physical cross edge by its own two-edge route. A physical vertex has
two differently coloured block-neighbours, so it cannot be a Yeo splitter
once those neighbours remain in one component of the deletion.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite partition of the original vertex set into nonempty blocks. -/
structure BlockPartition (V : Type*) [DecidableEq V] (ι : Type*) where
  blocks : ι → Finset V
  pairwise : Pairwise fun i j => Disjoint (blocks i) (blocks j)
  cover : ∀ v : V, ∃ i : ι, v ∈ blocks i
  nonempty : ∀ i : ι, (blocks i).Nonempty

namespace BlockPartition

variable (P : BlockPartition V ι)

noncomputable def index (v : V) : ι :=
  Classical.choose (P.cover v)

lemma mem_index (v : V) : v ∈ P.blocks (P.index v) :=
  Classical.choose_spec (P.cover v)

lemma index_eq {v : V} {i : ι} (hv : v ∈ P.blocks i) : P.index v = i := by
  by_contra hne
  have : Disjoint (P.blocks (P.index v)) (P.blocks i) := P.pairwise hne
  exact Finset.disjoint_left.1 this (P.mem_index v) hv

lemma nonempty_index (P : BlockPartition V ι) [Nonempty V] : Nonempty ι :=
  ⟨P.index (Classical.arbitrary V)⟩

end BlockPartition

/-- A physical original edge whose ends lie in different blocks. -/
def IsCross (P : BlockPartition V ι) (e : Sym2 V) : Prop :=
  ∃ a b : V, e = s(a, b) ∧ P.index a ≠ P.index b

abbrev PhysEdge (P : BlockPartition V ι) :=
  { e : Sym2 V // e ∈ G.edgeSet ∧ IsCross P e }

lemma PhysEdge.eq_mk {P : BlockPartition V ι} (e : PhysEdge (G := G) P) :
    ∃ a b : V, e.1 = s(a, b) ∧ G.Adj a b ∧ P.index a ≠ P.index b := by
  rcases e with ⟨e, he, hc⟩
  obtain ⟨a, b, rfl, hne⟩ := hc
  exact ⟨a, b, rfl, by simpa [mem_edgeSet] using he, hne⟩

/-- Incidence of a block vertex with a physical cross-edge vertex. -/
def incident (P : BlockPartition V ι) (i : ι) (e : PhysEdge (G := G) P) : Prop :=
  ∃ x : V, x ∈ e.1 ∧ x ∈ P.blocks i

lemma incident_of_eq {P : BlockPartition V ι} {a b : V}
    (e : PhysEdge (G := G) P) (he : e.1 = s(a, b)) :
    incident (G := G) P (P.index a) e :=
  ⟨a, by simp [he], P.mem_index a⟩

noncomputable def endpointOf (P : BlockPartition V ι) (i : ι)
    (e : PhysEdge (G := G) P) (h : incident (G := G) P i e) : V :=
  Classical.choose h

lemma endpointOf_mem_edge (P : BlockPartition V ι) (i : ι)
    (e : PhysEdge (G := G) P) (h : incident (G := G) P i e) :
    endpointOf (G := G) P i e h ∈ e.1 :=
  (Classical.choose_spec h).1

lemma endpointOf_mem_block (P : BlockPartition V ι) (i : ι)
    (e : PhysEdge (G := G) P) (h : incident (G := G) P i e) :
    endpointOf (G := G) P i e h ∈ P.blocks i :=
  (Classical.choose_spec h).2

def auxAdj (P : BlockPartition V ι) :
    ι ⊕ PhysEdge (G := G) P → ι ⊕ PhysEdge (G := G) P → Prop
  | .inl i, .inr e => incident (G := G) P i e
  | .inr e, .inl i => incident (G := G) P i e
  | _, _ => False

lemma auxAdj_of_symm {P : BlockPartition V ι}
    {u v : ι ⊕ PhysEdge (G := G) P} :
    auxAdj (G := G) P u v → auxAdj (G := G) P v u := by
  cases u <;> cases v <;> intro h <;> exact h

lemma auxAdj_of_irrefl {P : BlockPartition V ι}
    (u : ι ⊕ PhysEdge (G := G) P) : ¬ auxAdj (G := G) P u u := by
  cases u <;> intro h <;> exact h

/-- Simple bipartite auxiliary graph: block vertices and one physical
subdivision vertex per original cross edge. -/
def aux (P : BlockPartition V ι) : SimpleGraph (ι ⊕ PhysEdge (G := G) P) where
  Adj := auxAdj (G := G) P
  symm := { symm := fun {_ _} => auxAdj_of_symm }
  loopless := { irrefl := auxAdj_of_irrefl }

lemma aux_not_adj_inl {P : BlockPartition V ι} (i j : ι) :
    ¬ (aux (G := G) P).Adj (.inl i) (.inl j) := id

lemma aux_not_adj_inr {P : BlockPartition V ι}
    (e f : PhysEdge (G := G) P) :
    ¬ (aux (G := G) P).Adj (.inr e) (.inr f) := id

lemma aux_adj_inl_inr {P : BlockPartition V ι} {i : ι}
    {e : PhysEdge (G := G) P} :
    (aux (G := G) P).Adj (.inl i) (.inr e) ↔ incident (G := G) P i e :=
  Iff.rfl

lemma aux_adj_inr_inl {P : BlockPartition V ι} {i : ι}
    {e : PhysEdge (G := G) P} :
    (aux (G := G) P).Adj (.inr e) (.inl i) ↔ incident (G := G) P i e :=
  Iff.rfl

/-- Generic port-class / spanning-path realisation on a block. Opposite
ports are realised by an original spanning path of the block. This helper
must be derived from the cograph `R` theorem before closing
`all:thm:all-cograph`. -/
structure PortData (U : Finset V) (Port : Type*) where
  port : V → Port
  realize : ∀ {x y : V}, x ∈ U → y ∈ U → port x ≠ port y →
    ∃ p : GraphPath G, p.start = x ∧ p.finish = y ∧ p.support = U

variable {Port : Type*} [DecidableEq Port]

noncomputable def auxColor (P : BlockPartition V ι) (port : V → Port)
    {u v : ι ⊕ PhysEdge (G := G) P} (h : (aux (G := G) P).Adj u v) :
    ι × Port :=
  match u, v with
  | .inl i, .inr e => (i, port (endpointOf (G := G) P i e h))
  | .inr e, .inl i => (i, port (endpointOf (G := G) P i e h))
  | .inl i, .inl j => (aux_not_adj_inl (G := G) i j h).elim
  | .inr e, .inr f => (aux_not_adj_inr (G := G) e f h).elim

lemma auxColor_symm (P : BlockPartition V ι) (port : V → Port)
    {u v : ι ⊕ PhysEdge (G := G) P} (h : (aux (G := G) P).Adj u v) :
    auxColor (G := G) P port h = auxColor (G := G) P port (adj_symm _ h) := by
  cases u with
  | inl i =>
    cases v with
    | inl j => exact (aux_not_adj_inl (G := G) i j h).elim
    | inr e => rfl
  | inr e =>
    cases v with
    | inl i => rfl
    | inr f => exact (aux_not_adj_inr (G := G) e f h).elim

noncomputable def auxColoring (P : BlockPartition V ι) (port : V → Port) :
    Yeo.EdgeColoring (aux (G := G) P) (ι × Port) where
  color := fun {_ _} h => auxColor (G := G) P port h
  color_symm := fun {_ _} h => auxColor_symm (G := G) P port h

lemma auxColor_fst_inl {P : BlockPartition V ι} (port : V → Port)
    {i : ι} {e : PhysEdge (G := G) P}
    (h : (aux (G := G) P).Adj (.inl i) (.inr e)) :
    (auxColor (G := G) P port h).1 = i :=
  rfl

/-- Build the physical vertex of an original cross edge. -/
def toPhys (P : BlockPartition V ι) {a b : V} (h : G.Adj a b)
    (hne : P.index a ≠ P.index b) : PhysEdge (G := G) P :=
  ⟨s(a, b), ⟨by simpa [mem_edgeSet] using h, ⟨a, b, rfl, hne⟩⟩⟩

lemma toPhys_incident_left (P : BlockPartition V ι) {a b : V} (h : G.Adj a b)
    (hne : P.index a ≠ P.index b) :
    (aux (G := G) P).Adj (.inl (P.index a)) (.inr (toPhys (G := G) P h hne)) :=
  ⟨a, by simp [toPhys], P.mem_index a⟩

lemma toPhys_incident_right (P : BlockPartition V ι) {a b : V} (h : G.Adj a b)
    (hne : P.index a ≠ P.index b) :
    (aux (G := G) P).Adj (.inl (P.index b)) (.inr (toPhys (G := G) P h hne)) :=
  ⟨b, by simp [toPhys], P.mem_index b⟩

/-- Map an original walk to an auxiliary walk on block vertices: internal
block steps are stationary, and each physical cross edge is replaced by its
own two-edge route through its subdivision vertex. -/
noncomputable def mapWalk (P : BlockPartition V ι) :
    ∀ {u v : V}, G.Walk u v →
      (aux (G := G) P).Walk (.inl (P.index u)) (.inl (P.index v))
  | _, _, Walk.nil => Walk.nil
  | u, _, Walk.cons (v := w) h p =>
      if hEq : P.index u = P.index w then
        hEq ▸ mapWalk P p
      else
        let e := toPhys (G := G) P h hEq
        have had1 : (aux (G := G) P).Adj (.inl (P.index u)) (.inr e) :=
          toPhys_incident_left (G := G) P h hEq
        have had2 : (aux (G := G) P).Adj (.inr e) (.inl (P.index w)) :=
          (toPhys_incident_right (G := G) P h hEq).symm
        Walk.cons had1 (Walk.cons had2 (mapWalk P p))

lemma reachable_blocks_of_reachable (P : BlockPartition V ι)
    {u v : V} (h : G.Reachable u v) :
    (aux (G := G) P).Reachable (.inl (P.index u)) (.inl (P.index v)) := by
  obtain ⟨w⟩ := h
  exact ⟨mapWalk (G := G) P w⟩

lemma reachable_phys_of_adj {P : BlockPartition V ι} {a b : V}
    (e : PhysEdge (G := G) P) (he : e.1 = s(a, b)) :
    (aux (G := G) P).Reachable (.inl (P.index a)) (.inr e) := by
  refine Adj.reachable ?_
  exact incident_of_eq (G := G) e he

/-- If `G` is connected and `ι` is nonempty, the auxiliary graph is connected. -/
lemma aux_connected (P : BlockPartition V ι) [Nonempty ι] (hG : G.Connected) :
    (aux (G := G) P).Connected := by
  refine (connected_iff _).2 ⟨?_, inferInstance⟩
  intro x y
  have block_reach : ∀ i j : ι,
      (aux (G := G) P).Reachable (.inl i) (.inl j) := by
    intro i j
    obtain ⟨ui, hui⟩ := P.nonempty i
    obtain ⟨uj, huj⟩ := P.nonempty j
    have hi : P.index ui = i := P.index_eq hui
    have hj : P.index uj = j := P.index_eq huj
    have hR := reachable_blocks_of_reachable (G := G) P (hG.preconnected ui uj)
    exact hi ▸ hj ▸ hR
  have phys_block : ∀ e : PhysEdge (G := G) P,
      ∃ i : ι, (aux (G := G) P).Adj (.inl i) (.inr e) := by
    intro e
    obtain ⟨a, b, he, _, _⟩ := PhysEdge.eq_mk (G := G) e
    exact ⟨P.index a, incident_of_eq (G := G) e he⟩
  cases x with
  | inl i =>
    cases y with
    | inl j => exact block_reach i j
    | inr e =>
      obtain ⟨k, hk⟩ := phys_block e
      exact Reachable.trans (block_reach i k) hk.reachable
  | inr e =>
    cases y with
    | inl j =>
      obtain ⟨k, hk⟩ := phys_block e
      exact Reachable.trans hk.symm.reachable (block_reach k j)
    | inr f =>
      obtain ⟨k, hk⟩ := phys_block e
      obtain ⟨k', hk'⟩ := phys_block f
      exact Reachable.trans hk.symm.reachable
        (Reachable.trans (block_reach k k') hk'.reachable)

/-- The two block-neighbours of a physical vertex receive colours with
distinct first components (the two endpoint block indices). If those
neighbours remain in one component of the deletion, the physical vertex
is not a Yeo splitter. -/
lemma not_splittingVertex_phys (P : BlockPartition V ι) (port : V → Port)
    {a b : V} (hab : G.Adj a b) (hne : P.index a ≠ P.index b)
    (hconn :
      (Yeo.deleteGraph (aux (G := G) P)
        (.inr (toPhys (G := G) P hab hne))).Reachable
        ⟨.inl (P.index a), by intro h; cases h⟩
        ⟨.inl (P.index b), by intro h; cases h⟩) :
    ¬ Yeo.SplittingVertex (auxColoring (G := G) P port)
        (.inr (toPhys (G := G) P hab hne)) := by
  intro hsplit
  let e := toPhys (G := G) P hab hne
  have hada : (aux (G := G) P).Adj (.inl (P.index a)) (.inr e) :=
    toPhys_incident_left (G := G) P hab hne
  have hadb : (aux (G := G) P).Adj (.inl (P.index b)) (.inr e) :=
    toPhys_incident_right (G := G) P hab hne
  let xa : {w // w ≠ Sum.inr e} := ⟨.inl (P.index a), by intro h; cases h⟩
  let yb : {w // w ≠ Sum.inr e} := ⟨.inl (P.index b), by intro h; cases h⟩
  have hcol := hsplit xa yb hada hadb hconn
  have : (auxColor (G := G) P port hada).1 = (auxColor (G := G) P port hadb).1 :=
    congrArg Prod.fst hcol
  exact hne this

/-- Factor blocks of an original cycle factor form a block partition. -/
noncomputable def CycleFactor.partition (F : CycleFactor G) :
    BlockPartition V (Fin F.card) where
  blocks := fun i => (F.getCycle i).support
  pairwise := by
    intro i j hij
    exact F.disjoint_getCycle hij
  cover := by
    intro v
    obtain ⟨c, hc, hv⟩ := F.mem_iff v
    obtain ⟨n, hn⟩ := List.get_of_mem hc
    refine ⟨⟨n.1, by simp [CycleFactor.card]⟩, ?_⟩
    have : F.getCycle ⟨n.1, by simp [CycleFactor.card]⟩ = c := by
      simpa [CycleFactor.getCycle] using hn
    simpa [this] using hv
  nonempty := fun i => (F.getCycle i).support_nonempty

/-- Two-block four-edge auxiliary cycle: opposite-port spanning paths of two
distinct factor blocks, joined by two physical original cross edges, cannot
occur in a globally minimum original-edge cycle factor. -/
lemma minFactor_not_twoBlock_portData (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {i j : Fin F.card} (hij : i ≠ j)
    (Di : PortData (G := G) (F.getCycle i).support Port)
    (Dj : PortData (G := G) (F.getCycle j).support Port)
    {xi yi xj yj : V}
    (hxi : xi ∈ (F.getCycle i).support) (hyi : yi ∈ (F.getCycle i).support)
    (hxj : xj ∈ (F.getCycle j).support) (hyj : yj ∈ (F.getCycle j).support)
    (hpi : Di.port xi ≠ Di.port yi)
    (hpj : Dj.port xj ≠ Dj.port yj)
    (hxy : G.Adj yi xj) (hyx : G.Adj yj xi) : False := by
  obtain ⟨p, hp1, hp2, hp3⟩ := Di.realize hxi hyi hpi
  obtain ⟨q, hq1, hq2, hq3⟩ := Dj.realize hxj hyj hpj
  have hfwd : G.Adj p.finish q.start := by simpa [hp2, hq1] using hxy
  have hback : G.Adj q.finish p.start := by simpa [hq2, hp1] using hyx
  exact F.not_exists_two_block_merge_of_min hmin hij p q hp3 hq3 hfwd hback

/-- From 1-toughness of order at least three, an original cross edge is not
a bridge, so `G - e` remains connected. -/
lemma deleteEdges_connected_of_oneTough (hT : OneTough G)
    (hord : 3 ≤ Fintype.card V) {a b : V} (hab : G.Adj a b) :
    (G.deleteEdges {s(a, b)}).Connected := by
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  have hG := hT.connected
  have hbr := OneTough.not_isBridge (G := G) hT hord hab
  exact hG.preconnected.connected_deleteEdges_of_not_isBridge hbr

end Nikoghosyan
