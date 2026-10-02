/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.CarrierGraphEmbedding

/-!
Path-cover, ordinary `p`, and canonical cograph transport along an
injective old-carrier embedding.

An original-edge `PathCover` of `U` lifts to a path cover of `U.image f`
with identical cardinality. Conversely, a path cover of the image whose
paths live on the old range projects to a path cover of `U`, again with
exact count. Consequently
`pathCoverNumber H (U.image f) = pathCoverNumber G U`.

The canonical `IsCograph` predicate is likewise invariant, via genuine
induced-`P₄` / adjacency equivalence on the image, not a numerical
rewrite. `Sum.inl` is recorded as the auxiliary-graph specialization.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

lemma PathCover.support_subset_range_of_image (f : V ↪ W) {U : Finset V}
    (pc : PathCover H (U.image f)) {p : GraphPath H} (hp : p ∈ pc.paths) :
    (p.support : Set W) ⊆ Set.range (f : V → W) := by
  intro x hx
  have : x ∈ U.image f := pc.support_subset hp hx
  rcases mem_image.1 this with ⟨u, _, rfl⟩
  exact ⟨u, rfl⟩

namespace PathCover

/-- Lift a path cover along an injective old-carrier embedding.
Supports are `Finset.image f` and the cover cardinality is exact. -/
def mapCarrier (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {U : Finset V}
    (pc : PathCover G U) : PathCover H (U.image f) where
  paths := pc.paths.map (GraphPath.mapCarrier (G := G) (H := H) f hadj)
  disjoint := by
    rw [List.pairwise_map]
    refine pc.disjoint.imp ?_
    intro p q hd
    exact GraphPath.disjoint_mapCarrier_support (G := G) (H := H) f hadj hd
  mem_iff := by
    intro x
    constructor
    · intro hx
      rcases mem_image.1 hx with ⟨u, hu, rfl⟩
      rcases (pc.mem_iff u).1 hu with ⟨p, hp, hpu⟩
      refine ⟨p.mapCarrier (G := G) (H := H) f hadj,
        List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
      simpa [GraphPath.mapCarrier_support] using mem_image_of_mem f hpu
    · intro ⟨p', hp', hx'⟩
      rcases List.mem_map.1 hp' with ⟨p, hp, rfl⟩
      have : x ∈ p.support.image f := by
        simpa [GraphPath.mapCarrier_support] using hx'
      rcases mem_image.1 this with ⟨u, hu, rfl⟩
      exact mem_image_of_mem f ((pc.mem_iff u).2 ⟨p, hp, hu⟩)

lemma mapCarrier_card (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {U : Finset V}
    (pc : PathCover G U) :
    (pc.mapCarrier (G := G) (H := H) f hadj).card = pc.card := by
  simp [mapCarrier, card]

/-- Project a path cover of the old image back to the original carrier.
Every path support is contained in `Set.range f`, so no auxiliary vertex
is ever projected. -/
noncomputable def ofCarrierImage (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {U : Finset V}
    (pc : PathCover H (U.image f)) : PathCover G U where
  paths :=
    pc.paths.attach.map fun x =>
      GraphPath.ofCarrierRange (G := G) (H := H) f hadj x.1
        (PathCover.support_subset_range_of_image f pc x.2)
  disjoint := by
    rw [List.pairwise_map]
    refine (pairwise_attach_disjoint pc.paths pc.disjoint).imp ?_
    intro a b hd
    refine disjoint_left.2 ?_
    intro y hy hy'
    have hyf : f y ∈ a.1.support :=
      (GraphPath.mem_ofCarrierRange_support_iff (G := G) (H := H) f hadj a.1
        (PathCover.support_subset_range_of_image f pc a.2)).1 hy
    have hyf' : f y ∈ b.1.support :=
      (GraphPath.mem_ofCarrierRange_support_iff (G := G) (H := H) f hadj b.1
        (PathCover.support_subset_range_of_image f pc b.2)).1 hy'
    exact disjoint_left.1 hd hyf hyf'
  mem_iff := by
    intro y
    have hyimg : y ∈ U ↔ f y ∈ U.image f := by
      constructor
      · exact mem_image_of_mem f
      · intro hy
        rcases mem_image.1 hy with ⟨y', hy', hfy⟩
        have : y = y' := f.injective hfy.symm
        subst this
        exact hy'
    constructor
    · intro hy
      have : f y ∈ U.image f := (hyimg).1 hy
      rcases (pc.mem_iff (f y)).1 this with ⟨p, hp, hpy⟩
      refine ⟨GraphPath.ofCarrierRange (G := G) (H := H) f hadj p
          (PathCover.support_subset_range_of_image f pc hp), ?_, ?_⟩
      · exact List.mem_map.2 ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩
      · exact (GraphPath.mem_ofCarrierRange_support_iff (G := G) (H := H) f hadj p
            (PathCover.support_subset_range_of_image f pc hp)).2 hpy
    · intro ⟨p', hp', hy'⟩
      rcases List.mem_map.1 hp' with ⟨⟨p, hp⟩, _, rfl⟩
      have : f y ∈ p.support :=
        (GraphPath.mem_ofCarrierRange_support_iff (G := G) (H := H) f hadj p
          (PathCover.support_subset_range_of_image f pc hp)).1 hy'
      exact (hyimg).2 ((pc.mem_iff (f y)).2 ⟨p, hp, this⟩)

lemma ofCarrierImage_card (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {U : Finset V}
    (pc : PathCover H (U.image f)) :
    (pc.ofCarrierImage (G := G) (H := H) f hadj).card = pc.card := by
  simp [ofCarrierImage, card]

end PathCover

/-- Ordinary path-cover number is invariant under injective old-carrier
embedding of the carrier. Real covers transport in both directions. -/
theorem pathCoverNumber_mapCarrier (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (U : Finset V) :
    pathCoverNumber H (U.image f) = pathCoverNumber G U := by
  apply le_antisymm
  · obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
    have := pathCoverNumber_le (G := H)
      (pc.mapCarrier (G := G) (H := H) f hadj)
    simpa [PathCover.mapCarrier_card, hpc] using this
  · obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := H) (U.image f)
    have := pathCoverNumber_le (G := G)
      (pc.ofCarrierImage (G := G) (H := H) f hadj)
    simpa [PathCover.ofCarrierImage_card, hpc] using this

lemma InducedP4_mapCarrier (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) {a b c d : V} :
    InducedP4 H (f a) (f b) (f c) (f d) ↔ InducedP4 G a b c d := by
  simp [InducedP4, f.injective.eq_iff, hadj]

/-- Canonical cograph predicate on an embedded old carrier. Equivalence
uses actual induced-`P₄` transport, not a numerical assertion. -/
theorem IsCograph_mapCarrier (f : V ↪ W)
    (hadj : ∀ u v : V, H.Adj (f u) (f v) ↔ G.Adj u v) (U : Finset V) :
    IsCograph H (U.image f) ↔ IsCograph G U := by
  constructor
  · intro h a b c d ha hb hc hd hp
    exact h (mem_image_of_mem f ha) (mem_image_of_mem f hb)
      (mem_image_of_mem f hc) (mem_image_of_mem f hd)
      ((InducedP4_mapCarrier (G := G) (H := H) f hadj).2 hp)
  · intro h a b c d ha hb hc hd hp
    rcases mem_image.1 ha with ⟨a', ha', rfl⟩
    rcases mem_image.1 hb with ⟨b', hb', rfl⟩
    rcases mem_image.1 hc with ⟨c', hc', rfl⟩
    rcases mem_image.1 hd with ⟨d', hd', rfl⟩
    exact h ha' hb' hc' hd'
      ((InducedP4_mapCarrier (G := G) (H := H) f hadj).1 hp)

/-! ### `Sum.inl` specialization -/

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem pathCoverNumber_mapCarrier_inl {H : SimpleGraph (V ⊕ α)}
    (hadj : ∀ u v : V, H.Adj (.inl u) (.inl v) ↔ G.Adj u v) (U : Finset V) :
    pathCoverNumber H (U.image (Sum.inl : V → V ⊕ α)) = pathCoverNumber G U :=
  pathCoverNumber_mapCarrier (G := G) (H := H) Embedding.inl hadj U

theorem IsCograph_mapCarrier_inl {H : SimpleGraph (V ⊕ α)}
    (hadj : ∀ u v : V, H.Adj (.inl u) (.inl v) ↔ G.Adj u v) (U : Finset V) :
    IsCograph H (U.image (Sum.inl : V → V ⊕ α)) ↔ IsCograph G U :=
  IsCograph_mapCarrier (G := G) (H := H) Embedding.inl hadj U

def PathCover.mapCarrier_inl {H : SimpleGraph (V ⊕ α)}
    (hadj : ∀ u v : V, H.Adj (.inl u) (.inl v) ↔ G.Adj u v) {U : Finset V}
    (pc : PathCover G U) : PathCover H (U.image (Sum.inl : V → V ⊕ α)) :=
  pc.mapCarrier (G := G) (H := H) Embedding.inl hadj

noncomputable def PathCover.ofCarrierImage_inl {H : SimpleGraph (V ⊕ α)}
    (hadj : ∀ u v : V, H.Adj (.inl u) (.inl v) ↔ G.Adj u v) {U : Finset V}
    (pc : PathCover H (U.image (Sum.inl : V → V ⊕ α))) : PathCover G U :=
  pc.ofCarrierImage (G := G) (H := H) Embedding.inl hadj

end Nikoghosyan
