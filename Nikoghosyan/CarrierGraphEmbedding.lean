/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.PathGraphRestriction

/-!
Injective carrier embedding between different vertex types.

Given an injective `f : V ↪ W` and graphs `G` on `V`, `H` on `W` with
old-adjacency equivalence
`H.Adj (f u) (f v) ↔ G.Adj u v`, the map is a genuine graph embedding
`G ↪g H`. Original-edge `GraphPath` / `GraphCycle` lift to `H` with
mapped endpoints, support `Finset.image f`, and undirected edges the
`Sym2.map f` images of original `G`-edges. Injectivity of `f` supplies
simple-path / simple-cycle no-repeat.

Conversely, an `H`-path or `H`-cycle whose vertex support lies in
`Set.range f` is reconstructed on `G` by applying a left inverse of `f`
only to those support vertices. Every surviving undirected edge is the
image of an original `G`-edge. A total map sending foreign vertices to
an arbitrary old vertex is not a graph homomorphism and is not used
to certify edges that meet an auxiliary vertex.

The range isomorphism `G ≃g H.induce (Set.range f)` is exported for
induced-carrier reasoning. `Sum.inl` is the specialization used by an
auxiliary graph on old vertices plus a fresh finite type. The generic
adjacency hypothesis is an input, not a Hamilton-cycle premise.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Graph embedding of `G` into `H` from an injective vertex map that
reflects original adjacency on the image. -/
def carrierEmbedding (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) : G ↪g H where
  __ := f
  map_rel_iff' := hadj _ _

@[simp]
lemma coe_carrierEmbedding (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    ⇑(carrierEmbedding (G := G) (H := H) f hadj) = ⇑f :=
  rfl

@[simp]
lemma coe_carrierHom (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    ⇑(carrierEmbedding (G := G) (H := H) f hadj).toHom = ⇑f :=
  rfl

lemma carrierEmbedding_injective (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    Injective (carrierEmbedding (G := G) (H := H) f hadj) :=
  (carrierEmbedding (G := G) (H := H) f hadj).injective

lemma carrierAdj_iff (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {u v : V} :
    H.Adj (f u) (f v) ↔ G.Adj u v :=
  hadj u v

lemma carrier_mem_edgeSet (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {u v : V}
    (h : G.Adj u v) : s(f u, f v) ∈ H.edgeSet := by
  simpa [SimpleGraph.mem_edgeSet, hadj] using h

/-- Domain of the embedding is isomorphic to the induced graph on the
old image. Inverse transport is used only on this induced carrier. -/
noncomputable def carrierRangeIso (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    G ≃g H.induce (Set.range (f : V → W)) :=
  (carrierEmbedding (G := G) (H := H) f hadj).isoInduceRange

lemma carrierRangeIso_apply (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (u : V) :
    ((carrierRangeIso (G := G) (H := H) f hadj u : W) = f u) :=
  rfl

lemma carrierRangeIso_symm_coe (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (x : W) (hx : x ∈ Set.range (f : V → W)) :
    f ((carrierRangeIso (G := G) (H := H) f hadj).symm ⟨x, hx⟩) = x := by
  have := (carrierRangeIso (G := G) (H := H) f hadj).apply_symm_apply ⟨x, hx⟩
  exact congrArg Subtype.val this

lemma nonempty_of_mem_range (f : V ↪ W) {x : W}
    (hx : x ∈ Set.range (f : V → W)) : Nonempty V :=
  ⟨Classical.choose hx⟩

lemma leftInverse_invFun_carrier [Nonempty V] (f : V ↪ W) :
    LeftInverse (invFun (⇑f)) (⇑f) :=
  leftInverse_invFun f.injective

lemma invFun_carrier_eq [Nonempty V] (f : V ↪ W) {x : W}
    (hx : x ∈ Set.range (f : V → W)) : f (invFun (⇑f) x) = x :=
  invFun_eq hx

lemma support_subset_range_of_finset {p : GraphPath H} {f : V ↪ W}
    (hsup : (p.support : Set W) ⊆ Set.range (f : V → W)) :
    ∀ x ∈ p.walk.support, x ∈ Set.range (f : V → W) := by
  intro x hx
  exact hsup (List.mem_toFinset.2 hx)

lemma cycle_support_subset_range_of_finset {c : GraphCycle H} {f : V ↪ W}
    (hsup : (c.support : Set W) ⊆ Set.range (f : V → W)) :
    ∀ x ∈ c.walk.support, x ∈ Set.range (f : V → W) := by
  intro x hx
  exact hsup (List.mem_toFinset.2 hx)

/-- Reconstruct an `H`-walk whose vertices all lie in the old image.
`invFun f` is applied only to those vertices; it is not treated as a
global homomorphism on auxiliary vertices. -/
noncomputable def walkOfCarrierRange [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    ∀ {x y : W} (w : H.Walk x y),
      (∀ z ∈ w.support, z ∈ Set.range (f : V → W)) →
      G.Walk (invFun (⇑f) x) (invFun (⇑f) y)
  | _, _, Walk.nil, _ => Walk.nil
  | x, _, Walk.cons (v := y') h p, hw =>
    Walk.cons
      (by
        have hx : x ∈ Set.range (f : V → W) := hw x (by simp)
        have hy : y' ∈ Set.range (f : V → W) := hw y' (by simp)
        have hH : H.Adj (f (invFun (⇑f) x)) (f (invFun (⇑f) y')) := by
          rwa [invFun_eq hx, invFun_eq hy]
        exact (hadj (invFun (⇑f) x) (invFun (⇑f) y')).1 hH)
      (walkOfCarrierRange f hadj p fun z hz => hw z (by simp [hz]))

lemma walkOfCarrierRange_nil [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {x : W}
    (hw : ∀ z ∈ (Walk.nil : H.Walk x x).support, z ∈ Set.range (f : V → W)) :
    walkOfCarrierRange (G := G) (H := H) f hadj Walk.nil hw = Walk.nil :=
  rfl

lemma walkOfCarrierRange_support [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    ∀ {x y : W} (w : H.Walk x y)
      (hw : ∀ z ∈ w.support, z ∈ Set.range (f : V → W)),
      (walkOfCarrierRange (G := G) (H := H) f hadj w hw).support =
        w.support.map (invFun (⇑f))
  | _, _, Walk.nil, hw => by simp [walkOfCarrierRange]
  | _, _, Walk.cons h p, hw => by
    simp [walkOfCarrierRange, walkOfCarrierRange_support f hadj p]

lemma walkOfCarrierRange_edges [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    ∀ {x y : W} (w : H.Walk x y)
      (hw : ∀ z ∈ w.support, z ∈ Set.range (f : V → W)),
      (walkOfCarrierRange (G := G) (H := H) f hadj w hw).edges =
        w.edges.map (Sym2.map (invFun (⇑f)))
  | _, _, Walk.nil, hw => by simp [walkOfCarrierRange]
  | _, _, Walk.cons h p, hw => by
    simp [walkOfCarrierRange, walkOfCarrierRange_edges f hadj p]

lemma walkOfCarrierRange_nil_iff [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) :
    ∀ {x y : W} (w : H.Walk x y)
      (hw : ∀ z ∈ w.support, z ∈ Set.range (f : V → W)),
      (walkOfCarrierRange (G := G) (H := H) f hadj w hw).Nil ↔ w.Nil
  | _, _, Walk.nil, hw => by simp [walkOfCarrierRange]
  | _, _, Walk.cons h p, hw => by simp [walkOfCarrierRange]

lemma nodup_map_invFun_on_range [Nonempty V] (f : V ↪ W) {l : List W}
    (hl : ∀ x ∈ l, x ∈ Set.range (f : V → W)) (hnd : l.Nodup) :
    (l.map (invFun (⇑f))).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd' := List.nodup_cons.1 hnd
    refine List.nodup_cons.2 ⟨?_, ih (fun x hx => hl x (by simp [hx])) hnd'.2⟩
    intro hmem
    rcases List.mem_map.1 hmem with ⟨b, hb, hinv⟩
    have ha : a ∈ Set.range (f : V → W) := hl a (by simp)
    have hb' : b ∈ Set.range (f : V → W) := hl b (by simp [hb])
    have : a = b := by
      have h := congrArg (⇑f) hinv
      simpa [invFun_eq ha, invFun_eq hb'] using h.symm
    subst this
    exact hnd'.1 hb

lemma walkOfCarrierRange_isPath [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    {x y : W} {w : H.Walk x y}
    (hw : ∀ z ∈ w.support, z ∈ Set.range (f : V → W)) (hp : w.IsPath) :
    (walkOfCarrierRange (G := G) (H := H) f hadj w hw).IsPath := by
  rw [Walk.isPath_def, walkOfCarrierRange_support]
  exact nodup_map_invFun_on_range f hw ((Walk.isPath_def w).1 hp)

lemma sym2_map_invFun_cancel [Nonempty V] (f : V ↪ W) {e : Sym2 W}
    (hends : ∀ x ∈ e, x ∈ Set.range (f : V → W)) :
    Sym2.map (⇑f) (Sym2.map (invFun (⇑f)) e) = e := by
  revert hends
  refine Sym2.inductionOn e (fun a b hends => ?_)
  have ha : a ∈ Set.range (f : V → W) := hends a (by simp)
  have hb : b ∈ Set.range (f : V → W) := hends b (by simp)
  simp [Sym2.map_mk, invFun_eq ha, invFun_eq hb]

lemma walkOfCarrierRange_isTrail [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    {x y : W} {w : H.Walk x y}
    (hw : ∀ z ∈ w.support, z ∈ Set.range (f : V → W)) (ht : w.IsTrail) :
    (walkOfCarrierRange (G := G) (H := H) f hadj w hw).IsTrail := by
  rw [Walk.isTrail_def, walkOfCarrierRange_edges]
  refine ht.edges_nodup.map_on ?_
  intro e he e' he' hmap
  have hends : ∀ x ∈ e, x ∈ Set.range (f : V → W) := fun x hx =>
    hw x (w.mem_support_of_mem_edges he hx)
  have hends' : ∀ x ∈ e', x ∈ Set.range (f : V → W) := fun x hx =>
    hw x (w.mem_support_of_mem_edges he' hx)
  have h := congrArg (Sym2.map (⇑f)) hmap
  simpa [sym2_map_invFun_cancel f hends, sym2_map_invFun_cancel f hends'] using h

lemma walkOfCarrierRange_isCycle [Nonempty V] (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    {x : W} {w : H.Walk x x}
    (hw : ∀ z ∈ w.support, z ∈ Set.range (f : V → W)) (hc : w.IsCycle) :
    (walkOfCarrierRange (G := G) (H := H) f hadj w hw).IsCycle := by
  refine ⟨⟨walkOfCarrierRange_isTrail (G := G) (H := H) f hadj hw hc.isTrail, ?_⟩, ?_⟩
  · intro hnil
    have : (walkOfCarrierRange (G := G) (H := H) f hadj w hw).Nil := by
      simp [hnil]
    exact hc.not_nil ((walkOfCarrierRange_nil_iff (G := G) (H := H) f hadj w hw).1 this)
  · have hsup := walkOfCarrierRange_support (G := G) (H := H) f hadj w hw
    have : (w.support.map (invFun (⇑f))).tail.Nodup := by
      rw [← Walk.cons_tail_support w, List.map_cons, List.tail_cons]
      refine nodup_map_invFun_on_range f ?_ hc.support_nodup
      intro z hz
      exact hw z (by
        rw [← Walk.cons_tail_support w]
        exact List.mem_cons_of_mem _ hz)
    simpa [hsup] using this

namespace GraphPath

/-- Lift an original-edge path along an injective old-carrier embedding. -/
def mapCarrier (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (p : GraphPath G) :
    GraphPath H where
  start := f p.start
  finish := f p.finish
  walk := p.walk.map (carrierEmbedding (G := G) (H := H) f hadj).toHom
  isPath :=
    (Walk.isPath_map_iff_of_injective
        (carrierEmbedding_injective (G := G) (H := H) f hadj)).2 p.isPath

lemma mapCarrier_start (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (p : GraphPath G) :
    (p.mapCarrier f hadj).start = f p.start :=
  rfl

lemma mapCarrier_finish (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (p : GraphPath G) :
    (p.mapCarrier f hadj).finish = f p.finish :=
  rfl

lemma mapCarrier_support (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (p : GraphPath G) :
    (p.mapCarrier f hadj).support = p.support.image f := by
  ext x
  simp [mapCarrier, support, Walk.support_map, List.mem_toFinset, List.mem_map,
    mem_image, carrierEmbedding]

lemma mapCarrier_edges (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (p : GraphPath G) :
    (p.mapCarrier f hadj).edges = p.edges.image (Sym2.map ⇑f) := by
  ext e
  simp [mapCarrier, edges, Walk.edges_map, List.mem_toFinset, List.mem_map,
    mem_image, carrierEmbedding]

lemma mapCarrier_edges_subset_edgeSet (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (p : GraphPath G) :
    ∀ e ∈ (p.mapCarrier f hadj).edges, e ∈ H.edgeSet :=
  (p.mapCarrier f hadj).edges_subset_edgeSet

lemma mapCarrier_mem_edge_iff (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (p : GraphPath G)
    {u v : V} :
    s(f u, f v) ∈ (p.mapCarrier f hadj).edges ↔ s(u, v) ∈ p.edges := by
  have hinj : Injective (Sym2.map (⇑f)) := Sym2.map.injective f.injective
  constructor
  · intro he
    have himg : s(f u, f v) ∈ p.edges.image (Sym2.map ⇑f) := by
      simpa [mapCarrier_edges] using he
    rcases mem_image.1 himg with ⟨e, hee, hmap⟩
    have : e = s(u, v) :=
      hinj (by simpa [Sym2.map_mk] using hmap)
    simpa [this] using hee
  · intro he
    have : (Sym2.map ⇑f) s(u, v) ∈ p.edges.image (Sym2.map ⇑f) :=
      mem_image_of_mem _ he
    simpa [mapCarrier_edges, Sym2.map_mk] using this

lemma disjoint_mapCarrier_support (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    {p q : GraphPath G} (hd : Disjoint p.support q.support) :
    Disjoint (p.mapCarrier f hadj).support (q.mapCarrier f hadj).support := by
  rw [mapCarrier_support, mapCarrier_support]
  refine disjoint_left.2 ?_
  intro x hx hy
  rcases mem_image.1 hx with ⟨a, ha, rfl⟩
  rcases mem_image.1 hy with ⟨b, hb, hba⟩
  have : a = b := f.injective hba.symm
  subst this
  exact disjoint_left.1 hd ha hb

/-- Project an `H`-path whose support lies in the old image back to `G`.
The left inverse of `f` is applied only to vertices already in
`Set.range f`. -/
noncomputable def ofCarrierRange (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (p : GraphPath H) (hsup : (p.support : Set W) ⊆ Set.range (f : V → W)) :
    GraphPath G :=
  haveI : Nonempty V := nonempty_of_mem_range f (hsup p.start_mem_support)
  { start := invFun (⇑f) p.start
    finish := invFun (⇑f) p.finish
    walk := walkOfCarrierRange (G := G) (H := H) f hadj p.walk
        (support_subset_range_of_finset (f := f) hsup)
    isPath :=
      walkOfCarrierRange_isPath (G := G) (H := H) f hadj
        (support_subset_range_of_finset (f := f) hsup) p.isPath }

lemma ofCarrierRange_start_spec (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (p : GraphPath H) (hsup : (p.support : Set W) ⊆ Set.range (f : V → W)) :
    f (ofCarrierRange (G := G) (H := H) f hadj p hsup).start = p.start := by
  haveI : Nonempty V := nonempty_of_mem_range f (hsup p.start_mem_support)
  exact invFun_eq (hsup p.start_mem_support)

lemma ofCarrierRange_finish_spec (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (p : GraphPath H) (hsup : (p.support : Set W) ⊆ Set.range (f : V → W)) :
    f (ofCarrierRange (G := G) (H := H) f hadj p hsup).finish = p.finish := by
  haveI : Nonempty V := nonempty_of_mem_range f (hsup p.start_mem_support)
  exact invFun_eq (hsup p.finish_mem_support)

lemma mem_ofCarrierRange_support_iff (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (p : GraphPath H) (hsup : (p.support : Set W) ⊆ Set.range (f : V → W))
    {y : V} :
    y ∈ (ofCarrierRange (G := G) (H := H) f hadj p hsup).support ↔
      f y ∈ p.support := by
  haveI : Nonempty V := nonempty_of_mem_range f (hsup p.start_mem_support)
  constructor
  · intro hy
    have : y ∈ (p.walk.support.map (invFun (⇑f))).toFinset := by
      simpa [ofCarrierRange, support, walkOfCarrierRange_support] using hy
    rcases List.mem_map.1 (List.mem_toFinset.1 this) with ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.range (f : V → W) :=
      support_subset_range_of_finset (f := f) hsup x hx
    have : f (invFun (⇑f) x) = x := invFun_eq hx'
    simpa [support, this] using List.mem_toFinset.2 hx
  · intro hy
    have hyw : f y ∈ p.walk.support := List.mem_toFinset.1 hy
    have : invFun (⇑f) (f y) = y := leftInverse_invFun_carrier f y
    simpa [ofCarrierRange, support, walkOfCarrierRange_support] using
      List.mem_toFinset.2 (List.mem_map.2 ⟨f y, hyw, this⟩)

lemma ofCarrierRange_support_image (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (p : GraphPath H) (hsup : (p.support : Set W) ⊆ Set.range (f : V → W)) :
    (ofCarrierRange (G := G) (H := H) f hadj p hsup).support.image f = p.support := by
  ext x
  constructor
  · intro hx
    rcases mem_image.1 hx with ⟨y, hy, rfl⟩
    exact (mem_ofCarrierRange_support_iff (G := G) (H := H) f hadj p hsup).1 hy
  · intro hx
    rcases hsup hx with ⟨y, rfl⟩
    exact mem_image_of_mem _
      ((mem_ofCarrierRange_support_iff (G := G) (H := H) f hadj p hsup).2 hx)

lemma ofCarrierRange_support_card (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (p : GraphPath H) (hsup : (p.support : Set W) ⊆ Set.range (f : V → W)) :
    (ofCarrierRange (G := G) (H := H) f hadj p hsup).support.card = p.support.card := by
  rw [← Finset.card_image_of_injective _ f.injective,
    ofCarrierRange_support_image (G := G) (H := H) f hadj p hsup]

/-- Every undirected edge of an old-range-supported `H`-path is the image
of an original `G`-edge. Auxiliary vertices never appear. -/
theorem carrierRange_surviving_edge (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    {p : GraphPath H} (hsup : (p.support : Set W) ⊆ Set.range (f : V → W))
    {x y : W} (he : s(x, y) ∈ p.edges) :
    ∃ u v : V, x = f u ∧ y = f v ∧ G.Adj u v := by
  have hx : x ∈ p.support := mem_support_of_mem_edge he (by simp)
  have hy : y ∈ p.support := mem_support_of_mem_edge he (by simp)
  rcases hsup hx with ⟨u, rfl⟩
  rcases hsup hy with ⟨v, rfl⟩
  have hadjH : H.Adj (f u) (f v) := by
    simpa [SimpleGraph.mem_edgeSet] using p.edges_subset_edgeSet _ he
  exact ⟨u, v, rfl, rfl, (hadj u v).1 hadjH⟩

lemma ofCarrierRange_edges_original (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (p : GraphPath H) (hsup : (p.support : Set W) ⊆ Set.range (f : V → W)) :
    ∀ e ∈ (ofCarrierRange (G := G) (H := H) f hadj p hsup).edges, e ∈ G.edgeSet :=
  (ofCarrierRange (G := G) (H := H) f hadj p hsup).edges_subset_edgeSet

end GraphPath

namespace GraphCycle

def mapCarrier (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (c : GraphCycle G) :
    GraphCycle H where
  start := f c.start
  walk := c.walk.map (carrierEmbedding (G := G) (H := H) f hadj).toHom
  isCycle :=
    (Walk.isCycle_map_iff_of_injective
        (carrierEmbedding_injective (G := G) (H := H) f hadj)).2 c.isCycle

lemma mapCarrier_start (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (c : GraphCycle G) :
    (c.mapCarrier f hadj).start = f c.start :=
  rfl

lemma mapCarrier_support (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (c : GraphCycle G) :
    (c.mapCarrier f hadj).support = c.support.image f := by
  ext x
  simp [mapCarrier, support, Walk.support_map, List.mem_toFinset, List.mem_map,
    mem_image, carrierEmbedding]

lemma mapCarrier_edges (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (c : GraphCycle G) :
    (c.mapCarrier f hadj).edges = c.edges.image (Sym2.map ⇑f) := by
  ext e
  simp [mapCarrier, edges, Walk.edges_map, List.mem_toFinset, List.mem_map,
    mem_image, carrierEmbedding]

lemma mapCarrier_edges_subset_edgeSet (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (c : GraphCycle G) :
    ∀ e ∈ (c.mapCarrier f hadj).edges, e ∈ H.edgeSet := by
  intro e he
  exact (c.mapCarrier f hadj).walk.edges_subset_edgeSet (mem_edges_iff.1 he)

noncomputable def ofCarrierRange (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (c : GraphCycle H) (hsup : (c.support : Set W) ⊆ Set.range (f : V → W)) :
    GraphCycle G :=
  haveI : Nonempty V := nonempty_of_mem_range f (hsup c.start_mem_support)
  { start := invFun (⇑f) c.start
    walk := walkOfCarrierRange (G := G) (H := H) f hadj c.walk
        (cycle_support_subset_range_of_finset (f := f) hsup)
    isCycle :=
      walkOfCarrierRange_isCycle (G := G) (H := H) f hadj
        (cycle_support_subset_range_of_finset (f := f) hsup) c.isCycle }

lemma ofCarrierRange_start_spec (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    (c : GraphCycle H) (hsup : (c.support : Set W) ⊆ Set.range (f : V → W)) :
    f (ofCarrierRange (G := G) (H := H) f hadj c hsup).start = c.start := by
  haveI : Nonempty V := nonempty_of_mem_range f (hsup c.start_mem_support)
  exact invFun_eq (hsup c.start_mem_support)

theorem carrierRange_surviving_edge (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v)
    {c : GraphCycle H} (hsup : (c.support : Set W) ⊆ Set.range (f : V → W))
    {x y : W} (he : s(x, y) ∈ c.edges) :
    ∃ u v : V, x = f u ∧ y = f v ∧ G.Adj u v := by
  have hx : x ∈ c.support := by
    simpa [support] using
      List.mem_toFinset.2
        (c.walk.mem_support_of_mem_edges (mem_edges_iff.1 he) (by simp))
  have hy : y ∈ c.support := by
    simpa [support] using
      List.mem_toFinset.2
        (c.walk.mem_support_of_mem_edges (mem_edges_iff.1 he) (by simp))
  rcases hsup hx with ⟨u, rfl⟩
  rcases hsup hy with ⟨v, rfl⟩
  have hadjH : H.Adj (f u) (f v) := by
    simpa [SimpleGraph.mem_edgeSet] using
      c.walk.edges_subset_edgeSet (mem_edges_iff.1 he)
  exact ⟨u, v, rfl, rfl, (hadj u v).1 hadjH⟩

end GraphCycle

/-! ### `Sum.inl` specialization (old vertices of an auxiliary graph) -/

variable {α : Type*} [Fintype α] [DecidableEq α]

def carrierEmbedding_inl {H : SimpleGraph (V ⊕ α)}
    (hadj : ∀ u v : V, H.Adj (.inl u) (.inl v) ↔ G.Adj u v) : G ↪g H :=
  carrierEmbedding (G := G) (H := H) Embedding.inl hadj

lemma mem_range_sumInl {x : V ⊕ α} :
    x ∈ Set.range (Sum.inl : V → V ⊕ α) ↔ ∃ u : V, x = .inl u := by
  simp [Set.mem_range, eq_comm]

def GraphPath.mapCarrier_inl {H : SimpleGraph (V ⊕ α)}
    (hadj : ∀ u v : V, H.Adj (.inl u) (.inl v) ↔ G.Adj u v) (p : GraphPath G) :
    GraphPath H :=
  p.mapCarrier (G := G) (H := H) Embedding.inl hadj

noncomputable def GraphPath.ofCarrierRange_inl {H : SimpleGraph (V ⊕ α)}
    (hadj : ∀ u v : V, H.Adj (.inl u) (.inl v) ↔ G.Adj u v)
    (p : GraphPath H)
    (hsup : (p.support : Set (V ⊕ α)) ⊆ Set.range (Sum.inl : V → V ⊕ α)) :
    GraphPath G :=
  GraphPath.ofCarrierRange (G := G) (H := H) Embedding.inl hadj p hsup

end Nikoghosyan
