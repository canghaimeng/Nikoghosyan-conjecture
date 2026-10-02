/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.PathCoverCuts

/-!
Support-cut transport for induced original vertex sets.

`OneToughOn G J` is conditional 1-toughness on the original support `J`:
for every `S ⊆ J`, if `c(J \ S) ≥ 2` then `c(J \ S) ≤ |S|`. This is
proved equivalent to `OneTough` of the actual induced graph `G.induce J`
by an original-vertex-preserving isomorphism of remainder graphs. No extra
graph hypothesis is introduced.

Component tools used by traceable-extension toughness:
* `c(U ∪ W) ≤ c(U)` when every vertex of `W` has an original neighbour in
  `U`, via a surjective inclusion map of components;
* `c(R \ T) ≤ |T| + 1` for the support of an actual original path;
* remainder identity `(H ∪ R) \ (S ∪ T) = (H \ S) ∪ (R \ T)` on a
  disjoint partition.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Conditional 1-toughness on an original vertex support `J`. -/
def OneToughOn (G : SimpleGraph V) (J : Finset V) : Prop :=
  ∀ S : Finset V,
    S ⊆ J →
      2 ≤ componentCount G (J \ S) →
        componentCount G (J \ S) ≤ S.card

lemma OneToughOn.univ_iff : OneToughOn G univ ↔ OneTough G := by
  constructor
  · intro h S h2
    simpa using h S (subset_univ S) (by simpa using h2)
  · intro h S _hS h2
    simpa using h S (by simpa using h2)

/-- Original vertices of an induced support, as a subtype. -/
abbrev VertexSet (J : Finset V) := {x : V // x ∈ (J : Set V)}

lemma mem_image_subtype_iff {J : Finset V} {S : Finset (VertexSet J)} {x : V} :
    x ∈ S.image Subtype.val ↔ ∃ hx : x ∈ (J : Set V), (⟨x, hx⟩ : VertexSet J) ∈ S := by
  simp [mem_image]

lemma card_image_subtype (J : Finset V) (S : Finset (VertexSet J)) :
    (S.image Subtype.val).card = S.card :=
  card_image_of_injective S Subtype.val_injective

lemma image_subtype_subset (J : Finset V) (S : Finset (VertexSet J)) :
    S.image Subtype.val ⊆ J := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := mem_image.1 hx
  exact y.property

lemma filter_subtype_image {J T : Finset V} (hT : T ⊆ J) :
    ((univ : Finset (VertexSet J)).filter fun x => x.val ∈ T).image Subtype.val = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    exact (mem_filter.1 hy).2
  · intro hx
    have hxJ : x ∈ J := hT hx
    refine mem_image.2 ⟨⟨x, hxJ⟩, ?_, rfl⟩
    exact mem_filter.2 ⟨mem_univ _, hx⟩

lemma card_filter_subtype {J T : Finset V} (hT : T ⊆ J) :
    ((univ : Finset (VertexSet J)).filter fun x => x.val ∈ T).card = T.card := by
  rw [← card_image_subtype J, filter_subtype_image hT]

/-- Remainder of an induced support after deleting a subtype finset is
isomorphic to the original induced remainder. -/
noncomputable def cutIso (J : Finset V) (S : Finset (VertexSet J)) :
    (G.induce (J : Set V)).induce
        (((univ : Finset (VertexSet J)) \ S : Finset (VertexSet J)) : Set (VertexSet J)) ≃g
      G.induce ((J \ S.image Subtype.val : Finset V) : Set V) where
  toFun x :=
    ⟨x.1.1, by
      have hxJ : x.1.1 ∈ J := x.1.2
      have hxS : x.1 ∉ S := (mem_sdiff.1 x.2).2
      have himg : x.1.1 ∉ S.image Subtype.val := by
        intro h
        obtain ⟨y, hyS, hy⟩ := mem_image.1 h
        have : y = x.1 := Subtype.ext hy
        exact hxS (this ▸ hyS)
      exact mem_sdiff.2 ⟨hxJ, himg⟩⟩
  invFun y :=
    ⟨⟨y.1, (mem_sdiff.1 y.2).1⟩, by
      refine mem_sdiff.2 ⟨mem_univ _, ?_⟩
      intro hyS
      have : y.1 ∈ S.image Subtype.val :=
        mem_image.2 ⟨⟨y.1, (mem_sdiff.1 y.2).1⟩, hyS, rfl⟩
      exact (mem_sdiff.1 y.2).2 this⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  map_rel_iff' := by
    intro a b
    exact Iff.rfl

lemma componentCount_cutIso (J : Finset V) (S : Finset (VertexSet J)) :
    componentCount (G.induce (J : Set V)) ((univ : Finset (VertexSet J)) \ S) =
      componentCount G (J \ S.image Subtype.val) := by
  simpa [componentCount] using
    Nat.card_congr (cutIso (G := G) J S).connectedComponentEquiv

/-- `OneToughOn G J` is exactly `OneTough` of the induced graph on `J`. -/
lemma OneToughOn_iff_OneTough_induce (J : Finset V) :
    OneToughOn G J ↔ OneTough (G.induce (J : Set V)) := by
  constructor
  · intro h S h2
    have hTsub : S.image Subtype.val ⊆ J := image_subtype_subset J S
    have hcount := componentCount_cutIso (G := G) J S
    have h2' : 2 ≤ componentCount G (J \ S.image Subtype.val) := by
      rw [← hcount]
      exact h2
    have hle := h (S.image Subtype.val) hTsub h2'
    rw [← hcount, card_image_subtype] at hle
    exact hle
  · intro h T hT h2
    let S : Finset (VertexSet J) :=
      (univ : Finset (VertexSet J)).filter fun x => x.val ∈ T
    have himg : S.image Subtype.val = T := filter_subtype_image hT
    have hcount := componentCount_cutIso (G := G) J S
    have h2' : 2 ≤ componentCount (G.induce (J : Set V)) (univ \ S) := by
      rw [hcount, himg]
      exact h2
    have hle := h S h2'
    rw [hcount, himg, card_filter_subtype hT] at hle
    exact hle

/-! ### Component maps on disjoint original supports -/

/-- If every vertex of `W` has an original neighbour in `U`, then every
component of `G[U ∪ W]` meets `U`, so the inclusion map of components is
surjective. -/
lemma componentCount_union_le_of_adj {U W : Finset V}
    (h : ∀ w ∈ W, ∃ u ∈ U, G.Adj w u) :
    componentCount G (U ∪ W) ≤ componentCount G U := by
  let f : (G.induce (U : Set V)).ConnectedComponent →
      (G.induce ((U ∪ W : Finset V) : Set V)).ConnectedComponent :=
    fun C => C.map (induceIncl G (subset_union_left (s₁ := U) (s₂ := W)))
  have hf : Surjective f := by
    intro C
    refine C.ind fun x => ?_
    rcases mem_union.mp x.property with hxU | hxW
    · refine ⟨(G.induce (U : Set V)).connectedComponentMk ⟨x.val, hxU⟩, ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
    · obtain ⟨u, huU, hadj⟩ := h x.val hxW
      refine ⟨(G.induce (U : Set V)).connectedComponentMk ⟨u, huU⟩, ?_⟩
      apply ConnectedComponent.sound
      have hu' :
          induceIncl G (subset_union_left (s₁ := U) (s₂ := W)) ⟨u, huU⟩ =
            ⟨u, mem_union.2 (Or.inl huU)⟩ := rfl
      rw [hu']
      exact Adj.reachable <| by simpa [induce_adj] using hadj.symm
  haveI : Fintype (G.induce (U : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce ((U ∪ W : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  exact Nat.card_le_card_of_surjective f hf

lemma union_sdiff_of_disjoint {H R S T : Finset V}
    (hHR : Disjoint H R) (hS : S ⊆ H) (hT : T ⊆ R) :
    (H ∪ R) \ (S ∪ T) = (H \ S) ∪ (R \ T) := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro ⟨hxHR, hxST⟩
    rcases hxHR with hxH | hxR
    · exact Or.inl ⟨hxH, fun hxS => hxST (Or.inl hxS)⟩
    · exact Or.inr ⟨hxR, fun hxT => hxST (Or.inr hxT)⟩
  · intro hx
    rcases hx with ⟨hxH, hxS⟩ | ⟨hxR, hxT⟩
    · refine ⟨Or.inl hxH, ?_⟩
      intro hST
      rcases hST with hxS' | hxT'
      · exact hxS hxS'
      · exact (disjoint_left.1 hHR hxH (hT hxT')).elim
    · refine ⟨Or.inr hxR, ?_⟩
      intro hST
      rcases hST with hxS' | hxT'
      · exact (disjoint_right.1 hHR hxR (hS hxS')).elim
      · exact hxT hxT'

lemma disjoint_sdiff_of_disjoint {H R S T : Finset V}
    (hHR : Disjoint H R) :
    Disjoint (H \ S) (R \ T) :=
  hHR.mono sdiff_subset sdiff_subset

lemma inter_union_eq_of_subset_union {H R ST : Finset V}
    (hST : ST ⊆ H ∪ R) :
    ST = ST ∩ H ∪ ST ∩ R := by
  ext x
  simp only [mem_union, mem_inter]
  constructor
  · intro hx
    rcases mem_union.1 (hST hx) with hH | hR
    · exact Or.inl ⟨hx, hH⟩
    · exact Or.inr ⟨hx, hR⟩
  · intro hx
    rcases hx with h | h
    · exact h.1
    · exact h.1

lemma disjoint_inter_of_disjoint {H R ST : Finset V}
    (hHR : Disjoint H R) :
    Disjoint (ST ∩ H) (ST ∩ R) :=
  hHR.mono inter_subset_right inter_subset_right

lemma card_cut_split {H R ST : Finset V}
    (hHR : Disjoint H R) (hST : ST ⊆ H ∪ R) :
    ST.card = (ST ∩ H).card + (ST ∩ R).card := by
  nth_rw 1 [inter_union_eq_of_subset_union hST]
  exact card_union_of_disjoint (disjoint_inter_of_disjoint hHR)

/-! ### Path deletion bounds -/

lemma pathCoverNumber_eq_one_of_path (p : GraphPath G) :
    pathCoverNumber G p.support = 1 := by
  have hle : pathCoverNumber G p.support ≤ 1 := by
    simpa [PathCover.ofPath_card] using
      pathCoverNumber_le (G := G) (PathCover.ofPath p)
  have hge := one_le_pathCoverNumber_of_nonempty (G := G) p.support_nonempty
  omega

lemma componentCount_eq_one_of_path (p : GraphPath G) :
    componentCount G p.support = 1 := by
  have hle := componentCount_le_pathCover_card (PathCover.ofPath p)
  have hcard : (PathCover.ofPath p).card = 1 := PathCover.ofPath_card p
  haveI : Nonempty (p.support : Set V) := ⟨⟨p.start, p.start_mem_support⟩⟩
  haveI : Nonempty (G.induce (p.support : Set V)).ConnectedComponent :=
    inferInstance
  have hpos : 0 < componentCount G p.support := Nat.card_pos
  omega

lemma Eligible_of_path_ends (p : GraphPath G) :
    Eligible G p.support p.start ∧ Eligible G p.support p.finish := by
  have hmin : (PathCover.ofPath p).card = pathCoverNumber G p.support := by
    rw [PathCover.ofPath_card, pathCoverNumber_eq_one_of_path p]
  exact ⟨⟨PathCover.ofPath p, hmin, p, List.mem_singleton.mpr rfl, Or.inl rfl⟩,
    ⟨PathCover.ofPath p, hmin, p, List.mem_singleton.mpr rfl, Or.inr rfl⟩⟩

/-- Deleting `T ⊆ R` from an original spanning path of `R` leaves at most
`|T| + 1` components. -/
lemma componentCount_path_sdiff_le (p : GraphPath G) {T : Finset V}
    (hT : T ⊆ p.support) :
    componentCount G (p.support \ T) ≤ T.card + 1 := by
  have h := componentCount_sdiff_le (G := G) p.support T hT
  have hp := pathCoverNumber_eq_one_of_path p
  omega

/-- Endpoint deletion: if `T` contains an endpoint of the path, the bound
sharpens by one. -/
lemma componentCount_path_sdiff_le_of_endpoint (p : GraphPath G) {T : Finset V}
    (hT : T ⊆ p.support) {x : V}
    (hxT : x ∈ T) (hxend : x = p.start ∨ x = p.finish) :
    componentCount G (p.support \ T) ≤ T.card := by
  have hE : Eligible G p.support x := by
    rcases hxend with rfl | rfl
    · exact (Eligible_of_path_ends p).1
    · exact (Eligible_of_path_ends p).2
  have h := componentCount_sdiff_le_of_eligible (G := G) hT hxT hE
  have hp := pathCoverNumber_eq_one_of_path p
  have hpos : 1 ≤ T.card := Nat.succ_le_of_lt (card_pos.2 ⟨x, hxT⟩)
  omega

end Nikoghosyan
