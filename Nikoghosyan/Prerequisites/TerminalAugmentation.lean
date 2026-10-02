/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Nikoghosyan.FactorAssembly
import Nikoghosyan.PathCoverCuts
import Nikoghosyan.PathCoverGraphEmbedding
import Nikoghosyan.Cograph.Operations
import Nikoghosyan.Cograph.PathCoverUnion
import Nikoghosyan.Prerequisites.TerminalCover

/-!
# Concrete terminal augmentation graph and actual Hamilton cycle

Given an actual `B`-terminal original-edge cover of `K` of cardinality
`q ≥ 1` with `p(K \ B) + q < |B|`, form the finite graph on `V ⊕ Fin q`
whose old–old edges are exactly the edges of `G`, whose `q` fresh vertices
are independent, and whose only fresh–old edges are the complete join from
each fresh vertex to the image of `B`.

Orienting the cover paths and inserting the `i`-th fresh vertex between
`finish_i` and `start_{i+1}` (indices modulo `q`) produces an actual simple
cycle of order at least three on the old image of `K` together with the
fresh vertices. No desired cycle and no surrogate old edge is supplied.

The remainder after deleting the image of `B` is the old image of `K \ B`
disjoint-union the `q` fresh isolates, a cograph whenever `G[K]` is, with
exact path-cover number `p_G(K \ B) + q`. Toughness of the host is not
assumed.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Augmented vertex type: old original vertices plus `q` fresh connectors. -/
abbrev AugVertex (q : ℕ) := V ⊕ Fin q

/-- Concrete augmentation graph: old–old edges copy `G`, each fresh vertex
is adjacent exactly to the image of `B`, and fresh vertices are independent. -/
def augRel (B : Finset V) (q : ℕ) : (V ⊕ Fin q) → (V ⊕ Fin q) → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr _ => a ∈ B
  | .inr _, .inl b => b ∈ B
  | .inr _, .inr _ => False

def augGraph (B : Finset V) (q : ℕ) : SimpleGraph (V ⊕ Fin q) :=
  SimpleGraph.fromRel (augRel (G := G) B q)

variable {B : Finset V} {q : ℕ}

@[simp]
lemma augGraph_adj_inl_inl {a b : V} :
    (augGraph (G := G) B q).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  simp only [augGraph, augRel, SimpleGraph.fromRel_adj]
  constructor
  · intro ⟨_, h⟩
    rcases h with h | h
    · exact h
    · exact h.symm
  · intro h
    exact ⟨fun hij => (SimpleGraph.Adj.ne h) (Sum.inl_injective hij), Or.inl h⟩

@[simp]
lemma augGraph_adj_inl_inr {a : V} {i : Fin q} :
    (augGraph (G := G) B q).Adj (.inl a) (.inr i) ↔ a ∈ B := by
  simp [augGraph, augRel, SimpleGraph.fromRel_adj, Sum.inl_ne_inr]

@[simp]
lemma augGraph_adj_inr_inl {b : V} {i : Fin q} :
    (augGraph (G := G) B q).Adj (.inr i) (.inl b) ↔ b ∈ B := by
  simp [augGraph, augRel, SimpleGraph.fromRel_adj, Sum.inr_ne_inl]

lemma augGraph_not_adj_inr_inr {i j : Fin q} :
    ¬ (augGraph (G := G) B q).Adj (.inr i) (.inr j) := by
  simp [augGraph, augRel, SimpleGraph.fromRel_adj]

/-- Old-copy homomorphism. -/
def augOldHom : G →g augGraph (G := G) B q where
  toFun := Sum.inl
  map_rel' := fun hab => (augGraph_adj_inl_inl (B := B) (q := q)).2 hab

lemma augOldHom_injective :
    Function.Injective
      (augOldHom (G := G) (B := B) (q := q) : V → V ⊕ Fin q) :=
  Sum.inl_injective

/-- Image of an original vertex set in the augmentation. -/
def augOldImage (U : Finset V) : Finset (V ⊕ Fin q) :=
  U.map ⟨Sum.inl, Sum.inl_injective⟩

/-- The `q` fresh connector vertices. -/
def augFresh : Finset (V ⊕ Fin q) :=
  (univ : Finset (Fin q)).map ⟨Sum.inr, Sum.inr_injective⟩

/-- Image of the designated terminal set. -/
def augA : Finset (V ⊕ Fin q) :=
  augOldImage (q := q) B

/-- Carrier of the constructed cycle: old image of `K` plus the fresh vertices. -/
def augCarrier (K : Finset V) : Finset (V ⊕ Fin q) :=
  augOldImage (q := q) K ∪ augFresh (V := V) (q := q)

lemma mem_augOldImage {U : Finset V} {x : V ⊕ Fin q} :
    x ∈ augOldImage (q := q) U ↔ ∃ a ∈ U, x = .inl a := by
  constructor
  · intro hx
    obtain ⟨a, ha, hfa⟩ := Finset.mem_map.mp hx
    exact ⟨a, ha, hfa.symm⟩
  · intro ⟨a, ha, hxa⟩
    exact Finset.mem_map.mpr ⟨a, ha, hxa.symm⟩

lemma mem_augFresh {x : V ⊕ Fin q} :
    x ∈ augFresh (V := V) (q := q) ↔ ∃ i : Fin q, x = .inr i := by
  constructor
  · intro hx
    obtain ⟨i, _, hfi⟩ := Finset.mem_map.mp hx
    exact ⟨i, hfi.symm⟩
  · intro ⟨i, hxi⟩
    exact Finset.mem_map.mpr ⟨i, mem_univ i, hxi.symm⟩

lemma mem_augA {x : V ⊕ Fin q} :
    x ∈ augA (B := B) (q := q) ↔ ∃ a ∈ B, x = .inl a :=
  mem_augOldImage (q := q)

@[simp]
lemma card_augOldImage (U : Finset V) :
    (augOldImage (q := q) U).card = U.card :=
  Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩

@[simp]
lemma card_augFresh : (augFresh (V := V) (q := q)).card = q := by
  change ((univ : Finset (Fin q)).map
      (⟨Sum.inr, Sum.inr_injective⟩ : Fin q ↪ V ⊕ Fin q)).card = q
  rw [Finset.card_map, card_univ, Fintype.card_fin]

lemma disjoint_augOldImage_fresh (U : Finset V) :
    Disjoint (augOldImage (q := q) U) (augFresh (V := V) (q := q)) := by
  refine disjoint_left.2 ?_
  intro x hx hy
  obtain ⟨a, _, rfl⟩ := (mem_augOldImage (q := q)).1 hx
  obtain ⟨i, hi⟩ := (mem_augFresh (V := V) (q := q)).1 hy
  exact Sum.inl_ne_inr hi

lemma card_augCarrier (K : Finset V) :
    (augCarrier (q := q) K).card = K.card + q := by
  simp [augCarrier, card_union_of_disjoint (disjoint_augOldImage_fresh (q := q) K)]

lemma three_le_card_augCarrier {K : Finset V} (hBK : B ⊆ K) (hq : 1 ≤ q)
    (hstrict : pathCoverNumber G (K \ B) + q < B.card) :
    3 ≤ (augCarrier (q := q) K).card := by
  have hB : q + 1 ≤ B.card := by
    have : q ≤ pathCoverNumber G (K \ B) + q := Nat.le_add_left _ _
    omega
  have hK : B.card ≤ K.card := card_le_card hBK
  have hcard := card_augCarrier (q := q) K
  omega

/-- Map an original-edge path into the old copy. -/
def GraphPath.augMap (p : GraphPath G) : GraphPath (augGraph (G := G) B q) where
  start := augOldHom (G := G) (B := B) (q := q) p.start
  finish := augOldHom (G := G) (B := B) (q := q) p.finish
  walk := p.walk.map (augOldHom (G := G) (B := B) (q := q))
  isPath :=
    (Walk.isPath_map_iff_of_injective
      (f := augOldHom (G := G) (B := B) (q := q))
      (augOldHom_injective (G := G) (B := B) (q := q))).2 p.isPath

lemma GraphPath.support_augMap (p : GraphPath G) :
    (p.augMap (B := B) (q := q)).support =
      augOldImage (q := q) p.support := by
  simp only [GraphPath.augMap, GraphPath.support, augOldImage]
  ext x
  constructor
  · intro hx
    have hxL : x ∈ (p.walk.map (augOldHom (G := G) (B := B) (q := q))).support :=
      List.mem_toFinset.mp hx
    rw [Walk.support_map (f := augOldHom (G := G) (B := B) (q := q))
      (p := p.walk)] at hxL
    obtain ⟨a, ha, hax⟩ := List.mem_map.mp hxL
    exact Finset.mem_map.mpr ⟨a, List.mem_toFinset.mpr ha, hax⟩
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hx
    apply List.mem_toFinset.mpr
    rw [Walk.support_map (f := augOldHom (G := G) (B := B) (q := q))
      (p := p.walk)]
    exact List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha, hax⟩

lemma GraphPath.start_augMap (p : GraphPath G) :
    (p.augMap (B := B) (q := q)).start = .inl p.start :=
  rfl

lemma GraphPath.finish_augMap (p : GraphPath G) :
    (p.augMap (B := B) (q := q)).finish = .inl p.finish :=
  rfl

lemma GraphPath.augMap_not_mem_fresh (p : GraphPath G) {i : Fin q} :
    Sum.inr i ∉ (p.augMap (B := B) (q := q)).support := by
  intro h
  rw [GraphPath.support_augMap] at h
  obtain ⟨a, _, ha⟩ := (mem_augOldImage (q := q)).1 h
  exact Sum.inr_ne_inl ha

/-- Append the `i`-th fresh vertex after an old `B`-ended path. -/
def GraphPath.augExtend (p : GraphPath G) (i : Fin q) (hf : p.finish ∈ B) :
    GraphPath (augGraph (G := G) B q) :=
  (p.augMap (B := B) (q := q)).concatAdj
    (x := .inr i)
    (by exact (augGraph_adj_inl_inr (a := p.finish) (i := i)).2 hf)
    (p.augMap_not_mem_fresh (B := B) (q := q))

lemma GraphPath.support_augExtend (p : GraphPath G) (i : Fin q)
    (hf : p.finish ∈ B) :
    (p.augExtend (B := B) i hf).support =
      insert (.inr i) (augOldImage (q := q) p.support) := by
  ext x
  unfold GraphPath.augExtend GraphPath.concatAdj GraphPath.support
  erw [Walk.support_concat (p := (p.augMap (B := B) (q := q)).walk)]
  simp [List.mem_toFinset, mem_insert]
  apply or_congr Iff.rfl
  constructor
  · intro h
    have : x ∈ (p.augMap (B := B) (q := q)).support := List.mem_toFinset.mpr h
    rwa [GraphPath.support_augMap] at this
  · intro h
    have : x ∈ (p.augMap (B := B) (q := q)).support := by
      rwa [GraphPath.support_augMap]
    exact List.mem_toFinset.mp this

lemma GraphPath.start_augExtend (p : GraphPath G) (i : Fin q)
    (hf : p.finish ∈ B) :
    (p.augExtend (B := B) i hf).start = .inl p.start :=
  rfl

lemma GraphPath.finish_augExtend (p : GraphPath G) (i : Fin q)
    (hf : p.finish ∈ B) :
    (p.augExtend (B := B) i hf).finish = .inr i :=
  rfl

lemma PathCover.card_eq_paths_length {U : Finset V} (pc : PathCover G U) :
    pc.card = pc.paths.length :=
  rfl

lemma PathCover.paths_length_eq_q {U : Finset V} {pc : PathCover G U}
    (hq : pc.card = q) : pc.paths.length = q :=
  pc.card_eq_paths_length.symm.trans hq

def PathCover.getPath {U : Finset V} (pc : PathCover G U)
    (i : Fin pc.paths.length) : GraphPath G :=
  pc.paths.get i

lemma PathCover.getPath_mem {U : Finset V} (pc : PathCover G U)
    (i : Fin pc.paths.length) : pc.getPath i ∈ pc.paths :=
  List.get_mem pc.paths i

lemma PathCover.get_mem {U : Finset V} (pc : PathCover G U)
    (i : Fin pc.card) : pc.getPath (Fin.cast pc.card_eq_paths_length i) ∈ pc.paths :=
  pc.getPath_mem _

lemma PathCover.get_terminal {U : Finset V} {pc : PathCover G U}
    (hterm : IsTerminalCover (G := G) B pc) (i : Fin pc.card) :
    IsTerminalPath (G := G) B (pc.getPath (Fin.cast pc.card_eq_paths_length i)) :=
  hterm _ (pc.get_mem i)

/-- Indexed list of old paths, each extended by its private fresh vertex. -/
def PathCover.augExtended {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q) :
    List (GraphPath (augGraph (G := G) B q)) :=
  (List.finRange q).map fun i =>
    (pc.getPath (Fin.cast (hq.symm.trans pc.card_eq_paths_length) i)).augExtend
      (B := B) i (pc.get_terminal (B := B) hterm (Fin.cast hq.symm i)).2

lemma PathCover.augExtended_length {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q) :
    (pc.augExtended (B := B) hterm hq).length = q := by
  simp [PathCover.augExtended]

lemma PathCover.augExtended_get {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q)
    (i : Fin q) :
    (pc.augExtended (B := B) hterm hq).get
        (Fin.cast (pc.augExtended_length (B := B) hterm hq).symm i) =
      (pc.getPath (Fin.cast (hq.symm.trans pc.card_eq_paths_length) i)).augExtend
        (B := B) i (pc.get_terminal (B := B) hterm (Fin.cast hq.symm i)).2 := by
  simp [PathCover.augExtended, Fin.cast, List.get_eq_getElem, List.getElem_map,
    List.getElem_finRange]

lemma PathCover.augExtended_ne_nil {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q) (hqpos : 1 ≤ q) :
    pc.augExtended (B := B) hterm hq ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  have : q = 0 := by
    simpa [pc.augExtended_length hterm hq] using hlen
  omega

lemma disjoint_augExtend_of_ne {p r : GraphPath G} {i j : Fin q}
    (hp : p.finish ∈ B) (hr : r.finish ∈ B) (hne : i ≠ j)
    (hd : Disjoint p.support r.support) :
    Disjoint (p.augExtend (B := B) i hp).support
      (r.augExtend (B := B) j hr).support := by
  refine disjoint_left.2 ?_
  intro x hx hy
  rw [GraphPath.support_augExtend] at hx hy
  rcases mem_insert.mp hx with hxi | hxold
  · subst hxi
    rcases mem_insert.mp hy with hyi | hyold
    · exact hne (Sum.inr_injective hyi)
    · obtain ⟨a, _, ha⟩ := (mem_augOldImage (q := q)).1 hyold
      exact Sum.inr_ne_inl ha
  · rcases mem_insert.mp hy with hyi | hyold
    · subst hyi
      obtain ⟨a, _, ha⟩ := (mem_augOldImage (q := q)).1 hxold
      exact Sum.inr_ne_inl ha
    · obtain ⟨a, haP, rfl⟩ := (mem_augOldImage (q := q)).1 hxold
      obtain ⟨b, hbR, hba⟩ := (mem_augOldImage (q := q)).1 hyold
      have hba' : a = b := Sum.inl_injective hba
      subst hba'
      exact disjoint_left.1 hd haP hbR

lemma PathCover.pairwise_support {U : Finset V} (pc : PathCover G U)
    {i j : Fin pc.paths.length} (hne : i ≠ j) :
    Disjoint (pc.getPath i).support (pc.getPath j).support := by
  have h := List.pairwise_iff_getElem.mp pc.disjoint
  have hij : i.val ≠ j.val := fun hval => hne (Fin.ext hval)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact h i.val j.val i.isLt j.isLt hlt
  · exact (h j.val i.val j.isLt i.isLt hgt).symm

lemma PathCover.augExtended_pairwise {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q) :
    (pc.augExtended (B := B) hterm hq).Pairwise
      fun p r => Disjoint p.support r.support := by
  rw [PathCover.augExtended, List.pairwise_map]
  refine (List.nodup_iff_pairwise_ne.1 (List.nodup_finRange q)).imp ?_
  intro i j hne
  have hd :=
    pc.pairwise_support
      (i := Fin.cast (hq.symm.trans pc.card_eq_paths_length) i)
      (j := Fin.cast (hq.symm.trans pc.card_eq_paths_length) j)
      (by
        intro h
        exact hne (Fin.ext (by
          have := congrArg Fin.val h
          simpa using this)))
  exact disjoint_augExtend_of_ne (B := B) (q := q)
    (pc.get_terminal (B := B) hterm (Fin.cast hq.symm i)).2
    (pc.get_terminal (B := B) hterm (Fin.cast hq.symm j)).2 hne hd

lemma PathCover.augExtended_edges {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q)
    {i : ℕ} (hi : i + 1 < (pc.augExtended (B := B) hterm hq).length) :
    (augGraph (G := G) B q).Adj
      ((pc.augExtended (B := B) hterm hq).get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
      ((pc.augExtended (B := B) hterm hq).get ⟨i + 1, hi⟩).start := by
  have hlenE : (pc.augExtended (B := B) hterm hq).length = q :=
    pc.augExtended_length hterm hq
  have hiq : i + 1 < q := by omega
  have i_lt : i < q := Nat.lt_of_succ_lt hiq
  let i0 : Fin q := ⟨i, i_lt⟩
  let i1 : Fin q := ⟨i + 1, hiq⟩
  have h0 := pc.augExtended_get hterm hq i0
  have h1 := pc.augExtended_get hterm hq i1
  have hidx0 :
      (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (pc.augExtended (B := B) hterm hq).length) =
        Fin.cast hlenE.symm i0 := Fin.ext rfl
  have hidx1 :
      (⟨i + 1, hi⟩ : Fin (pc.augExtended (B := B) hterm hq).length) =
        Fin.cast hlenE.symm i1 := Fin.ext rfl
  have hfin :
      ((pc.augExtended (B := B) hterm hq).get ⟨i, Nat.lt_of_succ_lt hi⟩).finish =
        .inr i0 := by
    rw [hidx0]
    simpa [GraphPath.finish_augExtend] using congrArg GraphPath.finish h0
  have hst :
      ((pc.augExtended (B := B) hterm hq).get ⟨i + 1, hi⟩).start =
        .inl (pc.getPath (Fin.cast pc.card_eq_paths_length (Fin.cast hq.symm i1))).start := by
    have hcast :
        Fin.cast (hq.symm.trans pc.card_eq_paths_length) i1 =
          Fin.cast pc.card_eq_paths_length (Fin.cast hq.symm i1) :=
      Fin.ext rfl
    rw [hidx1, h1, GraphPath.start_augExtend, hcast]
  rw [hfin, hst]
  exact (augGraph_adj_inr_inl (B := B) (q := q)).2
    (pc.get_terminal (B := B) hterm (Fin.cast hq.symm i1)).1

lemma PathCover.augExtended_close {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q)
    (hne : pc.augExtended (B := B) hterm hq ≠ []) :
    (augGraph (G := G) B q).Adj
      ((pc.augExtended (B := B) hterm hq).getLast hne).finish
      ((pc.augExtended (B := B) hterm hq).head hne).start := by
  have hlen : 0 < (pc.augExtended (B := B) hterm hq).length :=
    List.length_pos_of_ne_nil hne
  have hqpos : 0 < q := by
    simpa [pc.augExtended_length hterm hq] using hlen
  have hlenE : (pc.augExtended (B := B) hterm hq).length = q :=
    pc.augExtended_length hterm hq
  have hlastIdx : q - 1 < (pc.augExtended (B := B) hterm hq).length := by
    have : q - 1 < q := Nat.sub_one_lt_of_lt hqpos
    omega
  have hlast :
      (pc.augExtended (B := B) hterm hq).getLast hne =
        (pc.augExtended (B := B) hterm hq).get ⟨q - 1, hlastIdx⟩ := by
    rw [List.getLast_eq_getElem]
    congr 1
    omega
  have hhead :
      (pc.augExtended (B := B) hterm hq).head hne =
        (pc.augExtended (B := B) hterm hq).get ⟨0, hlen⟩ :=
    List.head_eq_getElem hne
  rw [hlast, hhead]
  let iLast : Fin q := ⟨q - 1, Nat.sub_one_lt_of_lt hqpos⟩
  let i0 : Fin q := ⟨0, hqpos⟩
  have hf := pc.augExtended_get hterm hq iLast
  have hs := pc.augExtended_get hterm hq i0
  have hidxL :
      (⟨q - 1, hlastIdx⟩ : Fin (pc.augExtended (B := B) hterm hq).length) =
        Fin.cast hlenE.symm iLast := Fin.ext rfl
  have hidx0 :
      (⟨0, hlen⟩ : Fin (pc.augExtended (B := B) hterm hq).length) =
        Fin.cast hlenE.symm i0 := Fin.ext rfl
  have hfin :
      ((pc.augExtended (B := B) hterm hq).get ⟨q - 1, hlastIdx⟩).finish =
        Sum.inr iLast := by
    rw [hidxL]
    simpa [GraphPath.finish_augExtend] using congrArg GraphPath.finish hf
  have hst :
      ((pc.augExtended (B := B) hterm hq).get ⟨0, hlen⟩).start =
        Sum.inl (pc.getPath (Fin.cast pc.card_eq_paths_length (Fin.cast hq.symm i0))).start := by
    have hcast :
        Fin.cast (hq.symm.trans pc.card_eq_paths_length) i0 =
          Fin.cast pc.card_eq_paths_length (Fin.cast hq.symm i0) :=
      Fin.ext rfl
    rw [hidx0, hs, GraphPath.start_augExtend, hcast]
  rw [hfin, hst]
  exact (augGraph_adj_inr_inl (B := B) (q := q)).2
    (pc.get_terminal (B := B) hterm (Fin.cast hq.symm i0)).1

lemma PathCover.mem_supportUnion_augExtended {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q)
    {x : V ⊕ Fin q} :
    x ∈ GraphPath.supportUnion (pc.augExtended (B := B) hterm hq) ↔
      x ∈ augCarrier (q := q) K := by
  constructor
  · intro hx
    obtain ⟨r, hr, hxr⟩ := GraphPath.mem_supportUnion.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    rw [GraphPath.support_augExtend] at hxr
    rcases mem_insert.mp hxr with hxi | hxold
    · cases hxi
      exact mem_union.2 (Or.inr ((mem_augFresh (V := V) (q := q)).2 ⟨i, rfl⟩))
    · obtain ⟨a, haP, rfl⟩ := (mem_augOldImage (q := q)).1 hxold
      have haK : a ∈ K :=
        (pc.mem_iff a).2
          ⟨pc.getPath (Fin.cast (hq.symm.trans pc.card_eq_paths_length) i),
            pc.getPath_mem _, haP⟩
      exact mem_union.2 (Or.inl ((mem_augOldImage (q := q)).2 ⟨a, haK, rfl⟩))
  · intro hx
    rcases mem_union.1 hx with hxK | hxF
    · obtain ⟨a, haK, rfl⟩ := (mem_augOldImage (q := q)).1 hxK
      obtain ⟨p, hp, haP⟩ := (pc.mem_iff a).1 haK
      obtain ⟨n, hn, hpn⟩ := List.mem_iff_getElem.mp hp
      have hlenP : pc.paths.length = q := pc.paths_length_eq_q hq
      have nq : n < q := by omega
      let i : Fin q := ⟨n, nq⟩
      refine GraphPath.mem_supportUnion.2
        ⟨(pc.getPath (Fin.cast (hq.symm.trans pc.card_eq_paths_length) i)).augExtend
          (B := B) i (pc.get_terminal (B := B) hterm (Fin.cast hq.symm i)).2, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
      · rw [GraphPath.support_augExtend]
        have hpget : p = pc.getPath ⟨n, hn⟩ := hpn.symm
        have hidx :
            (⟨n, hn⟩ : Fin pc.paths.length) =
              Fin.cast (hq.symm.trans pc.card_eq_paths_length) i := Fin.ext rfl
        have haP' : a ∈
            (pc.getPath (Fin.cast (hq.symm.trans pc.card_eq_paths_length) i)).support := by
          simpa [hpget, PathCover.getPath, hidx] using haP
        exact mem_insert_of_mem ((mem_augOldImage (q := q)).2 ⟨a, haP', rfl⟩)
    · obtain ⟨i, rfl⟩ := (mem_augFresh (V := V) (q := q)).1 hxF
      refine GraphPath.mem_supportUnion.2
        ⟨(pc.getPath (Fin.cast (hq.symm.trans pc.card_eq_paths_length) i)).augExtend
          (B := B) i (pc.get_terminal (B := B) hterm (Fin.cast hq.symm i)).2, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
      · rw [GraphPath.support_augExtend]
        exact mem_insert_self _ _

/-- Cyclic assembly of a nonempty list of pairwise-disjoint original-edge
paths, including the one-path case `q = 1`. -/
noncomputable def assembleCyclePos {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (ps : List (GraphPath H)) (hne : ps ≠ [])
    (hdisj : ps.Pairwise fun p r => Disjoint p.support r.support)
    (hedges : ∀ i (hi : i + 1 < ps.length),
      H.Adj (ps.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (ps.get ⟨i + 1, hi⟩).start)
    (hclose : H.Adj (ps.getLast hne).finish (ps.head hne).start)
    (h3 : 3 ≤ (GraphPath.supportUnion ps).card) : GraphCycle H :=
  let r := Classical.choose (GraphPath.exists_spliceChain ps hne hdisj hedges)
  let hr := Classical.choose_spec (GraphPath.exists_spliceChain ps hne hdisj hedges)
  r.toCycle (by
    have hst : r.start = (ps.head hne).start := hr.1
    have hfn : r.finish = (ps.getLast hne).finish := hr.2.1
    rw [hst, hfn]
    exact hclose) (by
    have hs : r.support = GraphPath.supportUnion ps := hr.2.2
    rw [hs]
    exact h3)

lemma support_assembleCyclePos {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (ps : List (GraphPath H)) (hne : ps ≠ [])
    (hdisj : ps.Pairwise fun p r => Disjoint p.support r.support)
    (hedges : ∀ i (hi : i + 1 < ps.length),
      H.Adj (ps.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (ps.get ⟨i + 1, hi⟩).start)
    (hclose : H.Adj (ps.getLast hne).finish (ps.head hne).start)
    (h3 : 3 ≤ (GraphPath.supportUnion ps).card) :
    (assembleCyclePos ps hne hdisj hedges hclose h3).support =
      GraphPath.supportUnion ps := by
  simp [assembleCyclePos, GraphPath.support_toCycle]
  exact (Classical.choose_spec
    (GraphPath.exists_spliceChain ps hne hdisj hedges)).2.2

/-- Actual Hamilton cycle of the augmentation carrier, built from the given
`B`-terminal cover by inserting one fresh vertex after each old path. -/
noncomputable def PathCover.augCycle {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q)
    (hqpos : 1 ≤ q)
    (h3 : 3 ≤ (augCarrier (q := q) K).card) :
    GraphCycle (augGraph (G := G) B q) :=
  let ps := pc.augExtended (B := B) hterm hq
  let hne : ps ≠ [] := pc.augExtended_ne_nil (B := B) hterm hq hqpos
  assembleCyclePos ps hne
    (pc.augExtended_pairwise (B := B) hterm hq)
    (fun i hi => pc.augExtended_edges (B := B) hterm hq hi)
    (pc.augExtended_close (B := B) hterm hq hne)
    (by
      have hEq : GraphPath.supportUnion ps = augCarrier (q := q) K := by
        ext x
        exact pc.mem_supportUnion_augExtended (B := B) hterm hq
      simpa [hEq] using h3)

lemma PathCover.support_augCycle {K : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q)
    (hqpos : 1 ≤ q)
    (h3 : 3 ≤ (augCarrier (q := q) K).card) :
    (pc.augCycle (B := B) hterm hq hqpos h3).support = augCarrier (q := q) K := by
  simp [PathCover.augCycle, support_assembleCyclePos]
  ext x
  exact pc.mem_supportUnion_augExtended (B := B) hterm hq

lemma PathCover.exists_augCycle {K : Finset V} (pc : PathCover G K)
    (hBK : B ⊆ K)
    (hterm : IsTerminalCover (G := G) B pc) (hq : pc.card = q)
    (hqpos : 1 ≤ q)
    (hstrict : pathCoverNumber G (K \ B) + q < B.card) :
    ∃ c : GraphCycle (augGraph (G := G) B q),
      c.support = augCarrier (q := q) K :=
  ⟨pc.augCycle (B := B) hterm hq hqpos
      (three_le_card_augCarrier (B := B) (q := q) hBK hqpos hstrict),
    pc.support_augCycle (B := B) hterm hq hqpos _⟩

/-! ### Remainder after deleting the image of `B` -/

lemma augRemainder_eq {K : Finset V} (_hBK : B ⊆ K) :
    augCarrier (q := q) K \ augA (B := B) (q := q) =
      augOldImage (q := q) (K \ B) ∪ augFresh (V := V) (q := q) := by
  ext x
  constructor
  · intro hx
    have hxC := (mem_sdiff.1 hx).1
    have hxA := (mem_sdiff.1 hx).2
    rcases mem_union.1 hxC with hxK | hxF
    · obtain ⟨a, haK, rfl⟩ := (mem_augOldImage (q := q)).1 hxK
      have haB : a ∉ B := fun haB =>
        hxA ((mem_augA (B := B) (q := q)).2 ⟨a, haB, rfl⟩)
      exact mem_union.2 (Or.inl ((mem_augOldImage (q := q)).2 ⟨a, mem_sdiff.2 ⟨haK, haB⟩, rfl⟩))
    · exact mem_union.2 (Or.inr hxF)
  · intro hx
    rcases mem_union.1 hx with hxL | hxF
    · obtain ⟨a, ha, rfl⟩ := (mem_augOldImage (q := q)).1 hxL
      have haK : a ∈ K := (mem_sdiff.1 ha).1
      have haB : a ∉ B := (mem_sdiff.1 ha).2
      refine mem_sdiff.2 ⟨mem_union.2 (Or.inl ((mem_augOldImage (q := q)).2 ⟨a, haK, rfl⟩)), ?_⟩
      intro hA
      obtain ⟨b, hb, hba⟩ := (mem_augA (B := B) (q := q)).1 hA
      exact haB (by cases hba; exact hb)
    · refine mem_sdiff.2 ⟨mem_union.2 (Or.inr hxF), ?_⟩
      intro hA
      obtain ⟨a, _, ha⟩ := (mem_augA (B := B) (q := q)).1 hA
      obtain ⟨i, hi⟩ := (mem_augFresh (V := V) (q := q)).1 hxF
      exact Sum.inl_ne_inr (ha.symm.trans hi)

lemma no_cross_oldRemainder_fresh {K : Finset V} :
    ∀ a ∈ augOldImage (q := q) (K \ B),
      ∀ b ∈ augFresh (V := V) (q := q),
        ¬ (augGraph (G := G) B q).Adj a b := by
  intro a ha b hb hadj
  obtain ⟨v, hv, rfl⟩ := (mem_augOldImage (q := q)).1 ha
  obtain ⟨i, rfl⟩ := (mem_augFresh (V := V) (q := q)).1 hb
  have hvB : v ∈ B := by simpa using hadj
  exact (mem_sdiff.1 hv).2 hvB

lemma Independent.augFresh :
    Independent (G := augGraph (G := G) B q) (augFresh (V := V) (q := q)) := by
  intro x y hx hy hxy
  obtain ⟨i, rfl⟩ := (mem_augFresh (V := V) (q := q)).1 hx
  obtain ⟨j, rfl⟩ := (mem_augFresh (V := V) (q := q)).1 hy
  exact (augGraph_not_adj_inr_inr (B := B) (q := q)) hxy

lemma Independent.augA (hInd : Independent (G := G) B) :
    Independent (G := augGraph (G := G) B q) (augA (B := B) (q := q)) := by
  intro x y hx hy hxy
  obtain ⟨a, ha, rfl⟩ := (mem_augA (B := B) (q := q)).1 hx
  obtain ⟨b, hb, rfl⟩ := (mem_augA (B := B) (q := q)).1 hy
  exact hInd ha hb (by simpa using hxy)

lemma adj_fresh_iff {i : Fin q} {x : V ⊕ Fin q} :
    (augGraph (G := G) B q).Adj (.inr i) x ↔ ∃ a ∈ B, x = .inl a := by
  cases x with
  | inl a =>
    constructor
    · intro h
      exact ⟨a, by simpa using h, rfl⟩
    · intro ⟨b, hb, hba⟩
      cases hba
      simpa using hb
  | inr j =>
    constructor
    · intro h
      exact (augGraph_not_adj_inr_inr (B := B) (q := q) h).elim
    · intro ⟨_, _, h⟩
      cases h

/-! ### Path-cover number of the remainder -/

lemma PathCover.supportUnion_eq_aug {U : Finset V} (pc : PathCover G U) :
    GraphPath.supportUnion pc.paths = U := by
  ext x
  exact GraphPath.mem_supportUnion.trans (pc.mem_iff x).symm

lemma card_supportUnion_of_pairwise {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W}
    (ps : List (GraphPath H))
    (h : ps.Pairwise fun p q => Disjoint p.support q.support) :
    (GraphPath.supportUnion ps).card = (ps.map fun p => p.support.card).sum := by
  induction ps with
  | nil => simp [GraphPath.supportUnion]
  | cons p ps ih =>
    have hd : Disjoint p.support (GraphPath.supportUnion ps) := by
      refine disjoint_left.2 ?_
      intro x hx hxU
      obtain ⟨r, hr, hxr⟩ := GraphPath.mem_supportUnion.1 hxU
      exact disjoint_left.1 ((List.pairwise_cons.1 h).1 r hr) hx hxr
    rw [GraphPath.supportUnion_cons, card_union_of_disjoint hd, List.map_cons,
      List.sum_cons, ih (List.pairwise_cons.1 h).2]

lemma GraphPath.nil_of_independent {U : Finset V}
    (hInd : Independent (G := G) U) (p : GraphPath G) (hsub : p.support ⊆ U) :
    p.walk.Nil := by
  by_contra hnil
  have hadj := GraphPath.adj_start_trimStart p hnil
  have hs : p.start ∈ U := hsub p.start_mem_support
  have ht : (p.trimStart hnil).start ∈ U := by
    apply hsub
    have hmem : (p.trimStart hnil).start ∈ (p.trimStart hnil).support :=
      GraphPath.start_mem_support _
    have hsub' : (p.trimStart hnil).support ⊆ p.support := by
      rw [GraphPath.support_trimStart]
      exact erase_subset _ _
    exact hsub' hmem
  exact hInd hs ht hadj

lemma pathCoverNumber_eq_card_of_independent_aug {U : Finset V}
    (hInd : Independent (G := G) U) :
    pathCoverNumber G U = U.card := by
  refine Nat.le_antisymm (pathCoverNumber_le_card (G := G) U) ?_
  obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
  have h1 : ∀ p ∈ pc.paths, p.support.card = 1 := fun p hp => by
    have hnil := GraphPath.nil_of_independent hInd p (pc.support_subset hp)
    simp [GraphPath.support_eq_singleton_of_nil p hnil]
  have hsum := card_supportUnion_of_pairwise pc.paths pc.disjoint
  have hU : GraphPath.supportUnion pc.paths = U := pc.supportUnion_eq_aug
  have hmap : (pc.paths.map fun p => p.support.card).sum = pc.paths.length := by
    have : pc.paths.map (fun p => p.support.card) = pc.paths.map (fun _ => 1) :=
      List.map_congr_left fun p hp => h1 p hp
    simp [this]
  have : pc.card = U.card := by
    simp [PathCover.card, ← hmap, ← hsum, hU]
  omega

def PathCover.augMap {U : Finset V} (pc : PathCover G U) :
    PathCover (augGraph (G := G) B q) (augOldImage (q := q) U) where
  paths := pc.paths.map fun p => p.augMap (B := B) (q := q)
  disjoint := by
    rw [List.pairwise_map]
    refine pc.disjoint.imp ?_
    intro p r hd
    rw [GraphPath.support_augMap, GraphPath.support_augMap]
    refine disjoint_left.2 ?_
    intro x hx hy
    obtain ⟨a, haP, rfl⟩ := (mem_augOldImage (q := q)).1 hx
    obtain ⟨b, hbR, hba⟩ := (mem_augOldImage (q := q)).1 hy
    have : a = b := Sum.inl_injective hba
    subst this
    exact disjoint_left.1 hd haP hbR
  mem_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, haU, rfl⟩ := (mem_augOldImage (q := q)).1 hx
      obtain ⟨p, hp, haP⟩ := (pc.mem_iff a).1 haU
      refine ⟨p.augMap (B := B) (q := q), List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
      rw [GraphPath.support_augMap]
      exact (mem_augOldImage (q := q)).2 ⟨a, haP, rfl⟩
    · intro ⟨p', hp', hx'⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hp'
      rw [GraphPath.support_augMap] at hx'
      obtain ⟨a, haP, rfl⟩ := (mem_augOldImage (q := q)).1 hx'
      exact (mem_augOldImage (q := q)).2 ⟨a, (pc.mem_iff a).2 ⟨p, hp, haP⟩, rfl⟩

lemma PathCover.augMap_card {U : Finset V} (pc : PathCover G U) :
    (pc.augMap (B := B) (q := q)).card = pc.card := by
  simp [PathCover.augMap, PathCover.card]

lemma pathCoverNumber_augOldImage_le (U : Finset V) :
    pathCoverNumber (augGraph (G := G) B q) (augOldImage (q := q) U) ≤
      pathCoverNumber G U := by
  obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
  have hle := pathCoverNumber_le (G := augGraph (G := G) B q)
    (pc.augMap (B := B) (q := q))
  simpa [PathCover.augMap_card, hpc] using hle

lemma pathCoverNumber_augFresh :
    pathCoverNumber (augGraph (G := G) B q) (augFresh (V := V) (q := q)) = q := by
  simpa [card_augFresh] using
    pathCoverNumber_eq_card_of_independent_aug
      (U := augFresh (V := V) (q := q))
      (Independent.augFresh (G := G) (B := B) (q := q))

lemma pathCoverNumber_augRemainder_le {K : Finset V} :
    pathCoverNumber (augGraph (G := G) B q)
        (augOldImage (q := q) (K \ B) ∪ augFresh (V := V) (q := q)) ≤
      pathCoverNumber G (K \ B) + q := by
  have hdisj := disjoint_augOldImage_fresh (q := q) (K \ B)
  have hnc := no_cross_oldRemainder_fresh (G := G) (B := B) (q := q) (K := K)
  have hadd := Cograph.pathCoverNumber_disjoint_union (G := augGraph (G := G) B q)
    hdisj hnc
  have hle := pathCoverNumber_augOldImage_le (G := G) (B := B) (q := q) (K \ B)
  have hf := pathCoverNumber_augFresh (G := G) (B := B) (q := q)
  omega

/-! Inverse transport uses the checked old-range embedding. No total map
from fresh vertices to a default old vertex is used. -/

lemma augOldImage_eq_image (U : Finset V) :
    augOldImage (q := q) U = U.image (Sum.inl : V → V ⊕ Fin q) :=
  Finset.map_eq_image _ _

lemma GraphPath.support_subset_range_of_oldImage {U : Finset V}
    {p : GraphPath (augGraph (G := G) B q)}
    (hsub : p.support ⊆ augOldImage (q := q) U) :
    (p.support : Set (V ⊕ Fin q)) ⊆ Set.range (Sum.inl : V → V ⊕ Fin q) := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := (mem_augOldImage (q := q)).1 (hsub hx)
  exact ⟨a, rfl⟩

lemma GraphPath.support_subset_range_inl (p : GraphPath G) :
    (p.augMap (B := B) (q := q)).support ⊆
      augOldImage (q := q) (univ : Finset V) := by
  intro x hx
  rw [GraphPath.support_augMap] at hx
  obtain ⟨a, _, rfl⟩ := (mem_augOldImage (q := q)).1 hx
  exact (mem_augOldImage (q := q)).2 ⟨a, mem_univ a, rfl⟩

lemma GraphPath.support_augMap_subset_range (p : GraphPath G) :
    ∀ x ∈ (p.augMap (B := B) (q := q)).support,
      x ∈ Set.range (Sum.inl : V → V ⊕ Fin q) :=
  fun _ hx =>
    GraphPath.support_subset_range_of_oldImage
      (p.support_subset_range_inl (B := B) (q := q)) hx

/-- Inverse of an old-range-supported augmentation path, via
`GraphPath.ofCarrierRange_inl` and `augGraph_adj_inl_inl`. -/
noncomputable def GraphPath.ofAugOld
    (p : GraphPath (augGraph (G := G) B q))
    (hsup : (p.support : Set (V ⊕ Fin q)) ⊆
      Set.range (Sum.inl : V → V ⊕ Fin q)) : GraphPath G :=
  GraphPath.ofCarrierRange_inl
    (H := augGraph (G := G) B q)
    (fun u v =>
      (augGraph_adj_inl_inl (B := B) (q := q) :
        (augGraph (G := G) B q).Adj (Embedding.inl u) (Embedding.inl v) ↔
          G.Adj u v)) p hsup

/-- Inverse of an old-image path cover, via `PathCover.ofCarrierImage_inl`. -/
noncomputable def PathCover.ofAugOldImage {U : Finset V}
    (pc : PathCover (augGraph (G := G) B q) (augOldImage (q := q) U)) :
    PathCover G U :=
  let pc' : PathCover (augGraph (G := G) B q)
      (U.image (Sum.inl : V → V ⊕ Fin q)) :=
    { paths := pc.paths
      disjoint := pc.disjoint
      mem_iff := by
        intro x
        simpa [augOldImage_eq_image] using pc.mem_iff x }
  pc'.ofCarrierImage_inl (H := augGraph (G := G) B q)
    (fun u v =>
      (augGraph_adj_inl_inl (B := B) (q := q) :
        (augGraph (G := G) B q).Adj (Embedding.inl u) (Embedding.inl v) ↔
          G.Adj u v))

lemma PathCover.ofAugOldImage_card {U : Finset V}
    (pc : PathCover (augGraph (G := G) B q) (augOldImage (q := q) U)) :
    (pc.ofAugOldImage (B := B) (q := q)).card = pc.card := by
  simp [PathCover.ofAugOldImage, PathCover.ofCarrierImage_inl,
    PathCover.ofCarrierImage, PathCover.card]

lemma pathCoverNumber_augOldImage (U : Finset V) :
    pathCoverNumber (augGraph (G := G) B q) (augOldImage (q := q) U) =
      pathCoverNumber G U := by
  simpa [augOldImage_eq_image] using
    pathCoverNumber_mapCarrier_inl
      (G := G) (H := augGraph (G := G) B q)
      (fun u v => augGraph_adj_inl_inl (B := B) (q := q)) U

lemma isCograph_augOldImage_canonical {U : Finset V} :
    IsCograph (augGraph (G := G) B q) (augOldImage (q := q) U) ↔
      IsCograph G U := by
  simpa [augOldImage_eq_image] using
    IsCograph_mapCarrier_inl
      (G := G) (H := augGraph (G := G) B q)
      (fun u v => augGraph_adj_inl_inl (B := B) (q := q)) U

lemma pathCoverNumber_augRemainder {K : Finset V} :
    pathCoverNumber (augGraph (G := G) B q)
        (augOldImage (q := q) (K \ B) ∪ augFresh (V := V) (q := q)) =
      pathCoverNumber G (K \ B) + q := by
  have hdisj := disjoint_augOldImage_fresh (q := q) (K \ B)
  have hnc := no_cross_oldRemainder_fresh (G := G) (B := B) (q := q) (K := K)
  have hadd := Cograph.pathCoverNumber_disjoint_union (G := augGraph (G := G) B q)
    hdisj hnc
  have hold := pathCoverNumber_augOldImage (G := G) (B := B) (q := q) (K \ B)
  have hf := pathCoverNumber_augFresh (G := G) (B := B) (q := q)
  omega

lemma pathCoverNumber_augRemainder_eq {K : Finset V} (hBK : B ⊆ K) :
    pathCoverNumber (augGraph (G := G) B q)
        (augCarrier (q := q) K \ augA (B := B) (q := q)) =
      pathCoverNumber G (K \ B) + q := by
  simpa [augRemainder_eq hBK] using
    pathCoverNumber_augRemainder (K := K)

lemma isCograph_augOldImage {U : Finset V} (h : Cograph.IsCograph G U) :
    Cograph.IsCograph (augGraph (G := G) B q) (augOldImage (q := q) U) := by
  intro a b c d ha hb hc hd hp
  obtain ⟨a0, ha0, rfl⟩ := (mem_augOldImage (q := q)).1 ha
  obtain ⟨b0, hb0, rfl⟩ := (mem_augOldImage (q := q)).1 hb
  obtain ⟨c0, hc0, rfl⟩ := (mem_augOldImage (q := q)).1 hc
  obtain ⟨d0, hd0, rfl⟩ := (mem_augOldImage (q := q)).1 hd
  refine h ha0 hb0 hc0 hd0 ?_
  exact
    { ne_ab := mt (congrArg Sum.inl) hp.ne_ab
      ne_ac := mt (congrArg Sum.inl) hp.ne_ac
      ne_ad := mt (congrArg Sum.inl) hp.ne_ad
      ne_bc := mt (congrArg Sum.inl) hp.ne_bc
      ne_bd := mt (congrArg Sum.inl) hp.ne_bd
      ne_cd := mt (congrArg Sum.inl) hp.ne_cd
      adj_ab := by simpa using hp.adj_ab
      adj_bc := by simpa using hp.adj_bc
      adj_cd := by simpa using hp.adj_cd
      not_ac := by simpa using hp.not_ac
      not_ad := by simpa using hp.not_ad
      not_bd := by simpa using hp.not_bd }

lemma isCograph_augFresh :
    Cograph.IsCograph (augGraph (G := G) B q) (augFresh (V := V) (q := q)) := by
  intro a b c d ha hb hc hd hp
  obtain ⟨i, rfl⟩ := (mem_augFresh (V := V) (q := q)).1 ha
  obtain ⟨j, rfl⟩ := (mem_augFresh (V := V) (q := q)).1 hb
  exact (augGraph_not_adj_inr_inr (B := B) (q := q)) hp.adj_ab

lemma isCograph_augRemainder {K : Finset V} (hK : Cograph.IsCograph G K) :
    Cograph.IsCograph (augGraph (G := G) B q)
      (augOldImage (q := q) (K \ B) ∪ augFresh (V := V) (q := q)) :=
  Cograph.isCograph_union_of_no_cross
    (no_cross_oldRemainder_fresh (K := K))
    (isCograph_augOldImage (Cograph.isCograph_mono hK sdiff_subset))
    isCograph_augFresh

lemma isCograph_augRemainder_carrier {K : Finset V} (hBK : B ⊆ K)
    (hK : Cograph.IsCograph G K) :
    Cograph.IsCograph (augGraph (G := G) B q)
      (augCarrier (q := q) K \ augA (B := B) (q := q)) := by
  simpa [augRemainder_eq hBK] using isCograph_augRemainder hK

lemma pathCoverNumber_augRemainder_lt_A {K : Finset V} (hBK : B ⊆ K)
    (hstrict : pathCoverNumber G (K \ B) + q < B.card) :
    pathCoverNumber (augGraph (G := G) B q)
        (augCarrier (q := q) K \ augA (B := B) (q := q)) <
      (augA (B := B) (q := q)).card := by
  rw [pathCoverNumber_augRemainder_eq hBK, augA, card_augOldImage]
  exact hstrict

end Nikoghosyan
