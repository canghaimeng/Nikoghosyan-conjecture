/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.CarrierGraphEmbedding
import Nikoghosyan.Cograph.TwoBlockProfiles
import Nikoghosyan.InsertionCompletion
import Nikoghosyan.NoncographUnion
import Nikoghosyan.Prerequisites.AllCographCompletion

/-!
# Manuscript `thm:two-cycles`

An actual spanning two-cycle original-edge factor of a 1-tough cofree
host of order at least three is Hamiltonian. The exported theorems do
not take a minimum-factor hypothesis or a non-Hamiltonian hypothesis.

The non-Hamiltonian case is used only internally: a spanning two-cycle
factor is then globally minimum, the all-cograph case applies if both
blocks are cographs, and otherwise the spanning two-block strict-row
theorem plus the Hamiltonian prefix theorem produce a spanning original
cycle. An induced-support caller transports the same argument along the
subtype carrier embedding of `H ∪ D`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Concrete spanning two-cycle original-edge factor. -/
def CycleFactor.ofTwo (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) : CycleFactor G where
  cycles := [cH, cD]
  disjoint := by
    simp [List.pairwise_cons, hdisj]
  mem_iff := by
    intro x
    have hx : x ∈ cH.support ∪ cD.support := by
      simpa [hspan] using mem_univ x
    rcases mem_union.1 hx with h | h
    · exact ⟨cH, by simp, h⟩
    · exact ⟨cD, by simp, h⟩

lemma CycleFactor.ofTwo_card (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) :
    (CycleFactor.ofTwo cH cD hdisj hspan).card = 2 :=
  rfl

lemma CycleFactor.ofTwo_zero_lt (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) :
    0 < (CycleFactor.ofTwo cH cD hdisj hspan).card := by
  rw [CycleFactor.ofTwo_card]; exact Nat.zero_lt_two

lemma CycleFactor.ofTwo_one_lt (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) :
    1 < (CycleFactor.ofTwo cH cD hdisj hspan).card := by
  rw [CycleFactor.ofTwo_card]; exact Nat.one_lt_two

lemma CycleFactor.ofTwo_getCycle_zero (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) :
    (CycleFactor.ofTwo cH cD hdisj hspan).getCycle
      ⟨0, CycleFactor.ofTwo_zero_lt cH cD hdisj hspan⟩ = cH :=
  rfl

lemma CycleFactor.ofTwo_getCycle_one (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) :
    (CycleFactor.ofTwo cH cD hdisj hspan).getCycle
      ⟨1, CycleFactor.ofTwo_one_lt cH cD hdisj hspan⟩ = cD :=
  rfl

lemma CycleFactor.one_le_card (F : CycleFactor G)
    (hord : 3 ≤ Fintype.card V) : 1 ≤ F.card := by
  have hpos : 0 < Fintype.card V := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨c, hc, _⟩ := F.mem_iff x
  exact List.length_pos_of_mem hc

lemma CycleFactor.isHamiltonian_of_card_one (F : CycleFactor G)
    (hF : F.card = 1) : G.IsHamiltonian := by
  obtain ⟨a, w, hw, hsupp, _⟩ := F.exists_hamiltonian_cycle_of_card_one hF
  exact (⟨a, w, hw⟩ : GraphCycle G).isHamiltonian_of_support_eq_univ hsupp

/-- Internally: a spanning two-cycle factor of a non-Hamiltonian host is
globally minimum, because the only smaller positive cardinal is one. -/
lemma CycleFactor.two_cycle_is_min (F : CycleFactor G) (hF : F.card = 2)
    (hord : 3 ≤ Fintype.card V) (hNonHam : ¬ G.IsHamiltonian) :
    ∀ F' : CycleFactor G, F.card ≤ F'.card := by
  intro F'
  have h1 : 1 ≤ F'.card := F'.one_le_card hord
  by_contra hlt
  have hF1 : F'.card = 1 := by omega
  exact hNonHam (F'.isHamiltonian_of_card_one hF1)

lemma CycleFactor.ofTwo_isCograph_getCycle (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ)
    (hH : IsCograph G cH.support) (hD : IsCograph G cD.support)
    (i : Fin (CycleFactor.ofTwo cH cD hdisj hspan).card) :
    IsCograph G ((CycleFactor.ofTwo cH cD hdisj hspan).getCycle i).support := by
  have hi : i.1 < 2 := by
    have := i.2
    simpa [CycleFactor.ofTwo_card] using this
  have h01 : i.1 = 0 ∨ i.1 = 1 := by omega
  rcases h01 with h0 | h1
  · have hi0 : i = ⟨0, CycleFactor.ofTwo_zero_lt cH cD hdisj hspan⟩ := Fin.ext h0
    simpa [hi0, CycleFactor.ofTwo_getCycle_zero] using hH
  · have hi1 : i = ⟨1, CycleFactor.ofTwo_one_lt cH cD hdisj hspan⟩ := Fin.ext h1
    simpa [hi1, CycleFactor.ofTwo_getCycle_one] using hD

/-- Noncograph host block of a spanning two-cycle factor: open the other
cycle and apply the Hamiltonian prefix theorem. -/
theorem exists_univ_cycle_of_two_cycles_of_noncograph_host
    (hT : OneTough G) (hpat : NoInducedP4UnionP1 G)
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ)
    (hH : ¬ IsCograph G cH.support)
    (hNonHam : ¬ G.IsHamiltonian) :
    ∃ c : GraphCycle G, c.support = univ := by
  obtain ⟨hstrict, _⟩ :=
    strict_profiles_of_spanning_two_cycles cH cD hdisj hspan hH hpat hT hNonHam
  obtain ⟨r, hr, _, _⟩ := exists_path_open_succ cD cD.start_mem_support
  have hdisj' : Disjoint cH.support r.support := by simpa [hr] using hdisj
  have hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        NoTightContainer G cH.support (rowProfile (G := G) cH.support v) := by
    intro v hv
    have hvD : v ∈ cD.support := by simpa [hr] using hv
    obtain ⟨hAne, _hcog, hlt⟩ := hstrict v hvD
    refine ⟨hAne, ?_⟩
    exact (noTightContainer_iff_strict_pathCover_of_host
      cH r hdisj' hv hAne hpat).2 hlt
  obtain ⟨γ, hγ⟩ :=
    exists_original_cycle_of_hamiltonian_prefix_of_global
      cH r hdisj' hrow hpat
  refine ⟨γ, hγ.trans ?_⟩
  simpa [hr] using hspan

/-- Manuscript `thm:two-cycles`, concrete disjoint spanning pair form.
No minimum-factor or non-Hamiltonian hypothesis. -/
theorem exists_univ_cycle_of_two_cycles
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) :
    ∃ c : GraphCycle G, c.support = univ := by
  by_cases hHam : G.IsHamiltonian
  · exact (isHamiltonian_iff_exists_spanning_graphCycle hord).1 hHam
  let F := CycleFactor.ofTwo cH cD hdisj hspan
  have hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card :=
    F.two_cycle_is_min (CycleFactor.ofTwo_card cH cD hdisj hspan) hord hHam
  by_cases hHcog : IsCograph G cH.support
  · by_cases hDcog : IsCograph G cD.support
    · exact all_cograph_hamiltonian hT hord hpat F hmin
        (CycleFactor.ofTwo_isCograph_getCycle cH cD hdisj hspan hHcog hDcog)
    · exact exists_univ_cycle_of_two_cycles_of_noncograph_host
        hT hpat cD cH hdisj.symm (by simpa [union_comm] using hspan) hDcog hHam
  · exact exists_univ_cycle_of_two_cycles_of_noncograph_host
      hT hpat cH cD hdisj hspan hHcog hHam

theorem two_cycles_isHamiltonian
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hspan : cH.support ∪ cD.support = univ) :
    G.IsHamiltonian :=
  (isHamiltonian_iff_exists_spanning_graphCycle hord).2
    (exists_univ_cycle_of_two_cycles hT hord hpat cH cD hdisj hspan)

lemma CycleFactor.support_union_of_card_two (F : CycleFactor G)
    (hF : F.card = 2) :
    (F.getCycle ⟨0, by simp [hF]⟩).support ∪
      (F.getCycle ⟨1, by simp [hF]⟩).support = univ := by
  ext x
  constructor
  · intro; exact mem_univ x
  · intro _
    obtain ⟨c, hc, hx⟩ := F.mem_iff x
    obtain ⟨i, rfl⟩ := (List.mem_iff_get).1 hc
    have hlen : F.cycles.length = 2 := hF
    have hi : i.1 < 2 := by
      have := i.2
      omega
    have h01 : i.1 = 0 ∨ i.1 = 1 := by omega
    have hx' : x ∈ (F.cycles.get i).support := hx
    rcases h01 with h0 | h1
    · have : F.getCycle ⟨0, by simp [hF]⟩ = F.cycles.get i := by
        simp [getCycle, h0]
      simpa [this] using Or.inl hx'
    · have : F.getCycle ⟨1, by simp [hF]⟩ = F.cycles.get i := by
        simp [getCycle, h1]
      simpa [this] using Or.inr hx'

lemma CycleFactor.disjoint_zero_one_of_card_two (F : CycleFactor G)
    (hF : F.card = 2) :
    Disjoint (F.getCycle ⟨0, by simp [hF]⟩).support
      (F.getCycle ⟨1, by simp [hF]⟩).support :=
  F.disjoint_getCycle (by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    cases this)

/-- Caller form on an actual `CycleFactor` of cardinality two. -/
theorem exists_univ_cycle_of_two_cycle_factor
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G) (hF : F.card = 2) :
    ∃ c : GraphCycle G, c.support = univ :=
  exists_univ_cycle_of_two_cycles hT hord hpat
    (F.getCycle ⟨0, by simp [hF]⟩) (F.getCycle ⟨1, by simp [hF]⟩)
    (F.disjoint_zero_one_of_card_two hF)
    (F.support_union_of_card_two hF)

theorem two_cycle_factor_isHamiltonian
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G) (hF : F.card = 2) :
    G.IsHamiltonian :=
  (isHamiltonian_iff_exists_spanning_graphCycle hord).2
    (exists_univ_cycle_of_two_cycle_factor hT hord hpat F hF)

/-! ### Induced-support / `OneToughOn` caller -/

lemma induce_adj {J : Finset V} {a b : VertexSet J} :
    (G.induce (J : Set V)).Adj a b ↔ G.Adj a.val b.val :=
  Iff.rfl

lemma subtype_carrier_hadj (J : Finset V) :
    ∀ u v : VertexSet J,
      G.Adj ((Embedding.subtype (J : Set V)) u)
          ((Embedding.subtype (J : Set V)) v) ↔
        (G.induce (J : Set V)).Adj u v := by
  intro u v
  exact Iff.rfl

lemma support_subset_range_subtype {J : Finset V} {c : GraphCycle G}
    (h : c.support ⊆ J) :
    (c.support : Set V) ⊆ Set.range (Embedding.subtype (J : Set V)) := by
  intro x hx
  exact ⟨⟨x, h (by exact hx)⟩, rfl⟩

lemma GraphCycle.ofCarrierRange_mem_support_iff
    {V' W' : Type u} [Fintype V'] [DecidableEq V'] [Fintype W'] [DecidableEq W']
    {G' : SimpleGraph V'} {H : SimpleGraph W'} (f : V' ↪ W')
    (hadj : ∀ u v : V', H.Adj (f u) (f v) ↔ G'.Adj u v)
    (c : GraphCycle H)
    (hsup : (c.support : Set W') ⊆ Set.range (f : V' → W')) {y : V'} :
    y ∈ (GraphCycle.ofCarrierRange (G := G') (H := H) f hadj c hsup).support ↔
      f y ∈ c.support := by
  haveI : Nonempty V' := nonempty_of_mem_range f (hsup c.start_mem_support)
  constructor
  · intro hy
    have : y ∈ (c.walk.support.map (invFun (⇑f))).toFinset := by
      simpa [GraphCycle.ofCarrierRange, GraphCycle.support,
        walkOfCarrierRange_support] using hy
    rcases List.mem_map.1 (List.mem_toFinset.1 this) with ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.range (f : V' → W') :=
      cycle_support_subset_range_of_finset (f := f) hsup x hx
    have : f (invFun (⇑f) x) = x := invFun_eq hx'
    simpa [GraphCycle.support, this] using List.mem_toFinset.2 hx
  · intro hy
    have hyw : f y ∈ c.walk.support := List.mem_toFinset.1 hy
    have : invFun (⇑f) (f y) = y := leftInverse_invFun_carrier f y
    simpa [GraphCycle.ofCarrierRange, GraphCycle.support,
      walkOfCarrierRange_support] using
      List.mem_toFinset.2 (List.mem_map.2 ⟨f y, hyw, this⟩)

lemma inducedP4_induce_iff {J : Finset V} {a b c d : VertexSet J} :
    InducedP4 (G.induce (J : Set V)) a b c d ↔
      InducedP4 G a.val b.val c.val d.val := by
  constructor
  · intro h
    rcases h with ⟨nab, nac, nad, nbc, nbd, ncd, eab, ebc, ecd, nac', nad', nbd'⟩
    exact ⟨mt Subtype.ext nab, mt Subtype.ext nac, mt Subtype.ext nad,
      mt Subtype.ext nbc, mt Subtype.ext nbd, mt Subtype.ext ncd,
      eab, ebc, ecd, nac', nad', nbd'⟩
  · intro h
    rcases h with ⟨nab, nac, nad, nbc, nbd, ncd, eab, ebc, ecd, nac', nad', nbd'⟩
    exact ⟨mt (congrArg Subtype.val) nab, mt (congrArg Subtype.val) nac,
      mt (congrArg Subtype.val) nad, mt (congrArg Subtype.val) nbc,
      mt (congrArg Subtype.val) nbd, mt (congrArg Subtype.val) ncd,
      eab, ebc, ecd, nac', nad', nbd'⟩

lemma NoInducedP4UnionP1_induce_of {J : Finset V}
    (h : NoInducedP4UnionP1On G J) :
    NoInducedP4UnionP1 (G.induce (J : Set V)) := by
  intro a b c d x hp hxa hxb hxc hxd
  have hpG : InducedP4 G a.val b.val c.val d.val :=
    (inducedP4_induce_iff (G := G) (J := J)).1 hp
  have hxa' : x.val ≠ a.val := mt Subtype.ext hxa
  have hxb' : x.val ≠ b.val := mt Subtype.ext hxb
  have hxc' : x.val ≠ c.val := mt Subtype.ext hxc
  have hxd' : x.val ≠ d.val := mt Subtype.ext hxd
  have := h a.property b.property c.property d.property x.property
    hpG hxa' hxb' hxc' hxd'
  simpa [induce_adj] using this

lemma three_le_card_vertexSet_of_cycle {J : Finset V} (c : GraphCycle G)
    (h : c.support ⊆ J) : 3 ≤ Fintype.card (VertexSet J) := by
  have hJ : 3 ≤ J.card := c.three_le_card_support.trans (card_le_card h)
  simpa [Fintype.card_coe] using hJ

/-- Induced-support two-cycle theorem: `OneToughOn` of the original union
`H ∪ D` yields an original cycle spanning exactly that union. Pattern
inheritance is the induced forbidden-pattern predicate; inverse
projection is range-guarded `ofCarrierRange` along the subtype embedding. -/
theorem exists_original_cycle_of_two_cycles_on
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hOn : OneToughOn G (cH.support ∪ cD.support))
    (hpat : NoInducedP4UnionP1 G) :
    ∃ c : GraphCycle G, c.support = cH.support ∪ cD.support := by
  set J := cH.support ∪ cD.support
  let G' := G.induce (J : Set V)
  let f : VertexSet J ↪ V := Embedding.subtype (J : Set V)
  have hadj := subtype_carrier_hadj (G := G) J
  have hsupH : (cH.support : Set V) ⊆ Set.range (f : VertexSet J → V) :=
    support_subset_range_subtype (J := J) subset_union_left
  have hsupD : (cD.support : Set V) ⊆ Set.range (f : VertexSet J → V) :=
    support_subset_range_subtype (J := J) subset_union_right
  let cH' : GraphCycle G' :=
    GraphCycle.ofCarrierRange (G := G') (H := G) f hadj cH hsupH
  let cD' : GraphCycle G' :=
    GraphCycle.ofCarrierRange (G := G') (H := G) f hadj cD hsupD
  have hdisj' : Disjoint cH'.support cD'.support := by
    refine disjoint_left.2 ?_
    intro y hyH hyD
    have hyH' : f y ∈ cH.support :=
      (GraphCycle.ofCarrierRange_mem_support_iff (G' := G') (H := G) f hadj cH hsupH).1 hyH
    have hyD' : f y ∈ cD.support :=
      (GraphCycle.ofCarrierRange_mem_support_iff (G' := G') (H := G) f hadj cD hsupD).1 hyD
    exact disjoint_left.1 hdisj hyH' hyD'
  have hspan' : cH'.support ∪ cD'.support = (univ : Finset (VertexSet J)) := by
    ext y
    constructor
    · intro; exact mem_univ y
    · intro _
      have hyJ : y.val ∈ J := y.property
      rcases mem_union.1 hyJ with hH | hD
      · refine mem_union.2 (Or.inl ?_)
        exact (GraphCycle.ofCarrierRange_mem_support_iff
          (G' := G') (H := G) f hadj cH hsupH).2 hH
      · refine mem_union.2 (Or.inr ?_)
        exact (GraphCycle.ofCarrierRange_mem_support_iff
          (G' := G') (H := G) f hadj cD hsupD).2 hD
  have hT' : OneTough G' := (OneToughOn_iff_OneTough_induce J).1 hOn
  have hpat' : NoInducedP4UnionP1 G' :=
    NoInducedP4UnionP1_induce_of (NoInducedP4UnionP1On.of_global hpat J)
  have hord' : 3 ≤ Fintype.card (VertexSet J) :=
    three_le_card_vertexSet_of_cycle cH subset_union_left
  obtain ⟨γ', hγ'⟩ :=
    exists_univ_cycle_of_two_cycles (G := G') hT' hord' hpat' cH' cD' hdisj' hspan'
  let γ : GraphCycle G := γ'.mapCarrier (H := G) f hadj
  refine ⟨γ, ?_⟩
  have himg : γ.support = γ'.support.image f :=
    GraphCycle.mapCarrier_support (G := G') (H := G) f hadj γ'
  have huniv : (univ : Finset (VertexSet J)).image f = J := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, _, rfl⟩ := mem_image.1 hx
      exact y.property
    · intro hx
      exact mem_image.2 ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  simpa [himg, hγ', huniv]

/-- Two actual pairwise-disjoint original noncograph cycles admit an
original cycle spanning their union, via pair toughness of the union
and the induced two-cycle theorem. -/
theorem exists_original_cycle_of_two_noncograph_cycles
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hpat : NoInducedP4UnionP1 G)
    (hH : ¬ IsCograph G cH.support)
    (hD : ¬ IsCograph G cD.support) :
    ∃ c : GraphCycle G, c.support = cH.support ∪ cD.support :=
  exists_original_cycle_of_two_cycles_on cH cD hdisj
    (oneToughOn_of_two_noncograph_cycles cH cD hdisj hpat hH hD) hpat

end Nikoghosyan
