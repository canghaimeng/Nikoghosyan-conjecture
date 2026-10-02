/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Set.Card
import Nikoghosyan.Prerequisites.TwoFactorDefs
import Nikoghosyan.Prerequisites.TwoFactorGadget

/-!
# Vertex-return monotonicity of Tutte deficiency

Generic finite-graph helper for two-clone cut normalization
(`reports/TWO_FACTOR_GADGET_INTERFACE.md` §3).

For a deletion set `Z` the signed deficiency is
`oddComponentCount(G−Z) − |Z|`. If `z ∈ Z` meets at most two components of
`G−Z`, returning `z` cannot decrease this quantity: the odd-component count
drops by at most one while `|Z|` drops by one.
-/

universe u

namespace Nikoghosyan
namespace TwoFactor

open Classical
open scoped BigOperators
open SimpleGraph Set

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option linter.unusedSectionVars false

/-- Odd-order component count of `G − Z`. -/
noncomputable def oddComponentCount (Z : Set V) : ℕ :=
  (G.induce Zᶜ).oddComponents.ncard

/-- Signed Tutte deficiency `oddComponentCount(G−Z) − |Z|`. -/
noncomputable def signedDeficiency (Z : Set V) : ℤ :=
  (oddComponentCount G Z : ℤ) - (Z.ncard : ℤ)

lemma subset_return_compl {Z : Set V} {z : V} : Zᶜ ⊆ (Z \ {z})ᶜ := by
  intro x hx
  simp only [mem_compl_iff, mem_diff, mem_singleton_iff] at hx ⊢
  exact fun h => hx h.1

lemma z_mem_return_compl {Z : Set V} {z : V} : z ∈ (Z \ {z})ᶜ := by
  simp [mem_compl_iff, mem_diff]

lemma mem_compl_of_mem_return_compl_ne {Z : Set V} {z x : V}
    (hx : x ∈ (Z \ {z})ᶜ) (hne : x ≠ z) : x ∈ Zᶜ := by
  intro hxz
  exact hx ⟨hxz, hne⟩

/-- Inclusion of surviving vertices of `G−Z` into those of `G−(Z \ {z})`. -/
def remainIncl (Z : Set V) (z : V) (v : {x // x ∈ Zᶜ}) :
    {x // x ∈ (Z \ {z})ᶜ} :=
  ⟨v.1, subset_return_compl v.2⟩

lemma remainIncl_injective (Z : Set V) (z : V) :
    Function.Injective (remainIncl Z z) := by
  intro a b h
  exact Subtype.ext (congrArg (fun t : {x // x ∈ (Z \ {z})ᶜ} => (t : V)) h)

/-- The returned vertex as a vertex of `G − (Z \ {z})`. -/
def returnedVert (Z : Set V) (z : V) : {x // x ∈ (Z \ {z})ᶜ} :=
  ⟨z, z_mem_return_compl⟩

lemma remainIncl_ne_returned {Z : Set V} {z : V} (hz : z ∈ Z) (v : {x // x ∈ Zᶜ}) :
    remainIncl Z z v ≠ returnedVert Z z := by
  intro h
  exact v.property (congrArg Subtype.val h ▸ hz)

/-- Graph homomorphism from `G−Z` into `G−(Z\{z})`. -/
def remainHom (Z : Set V) (z : V) :
    G.induce Zᶜ →g G.induce (Z \ {z})ᶜ :=
  (G.induceHomOfLE (subset_return_compl (Z := Z) (z := z))).toHom

lemma reachable_remainIncl {Z : Set V} {z : V} {u v : {x // x ∈ Zᶜ}}
    (h : (G.induce Zᶜ).Reachable u v) :
    (G.induce (Z \ {z})ᶜ).Reachable
      (remainIncl Z z u) (remainIncl Z z v) :=
  h.map (remainHom G Z z)

/-- Components of `G−Z` adjacent to `z`. -/
def neighborComponentSet (Z : Set V) (z : V) :
    Set (G.induce Zᶜ).ConnectedComponent :=
  {c | ∃ v : {x // x ∈ Zᶜ}, G.Adj z v ∧ (G.induce Zᶜ).connectedComponentMk v = c}

lemma mem_neighborComponentSet_iff {Z : Set V} {z : V}
    {c : (G.induce Zᶜ).ConnectedComponent} :
    c ∈ neighborComponentSet G Z z ↔
      ∃ v : {x // x ∈ Zᶜ}, v ∈ c.supp ∧ G.Adj z v := by
  constructor
  · rintro ⟨v, hadj, hv⟩
    exact ⟨v, by simp [ConnectedComponent.mem_supp_iff, hv], hadj⟩
  · rintro ⟨v, hv, hadj⟩
    exact ⟨v, hadj, by simpa [ConnectedComponent.mem_supp_iff] using hv⟩

/-- Image of a `G−Z` component in `G−(Z\{z})`. -/
def mapRemainComp (Z : Set V) (z : V)
    (c : (G.induce Zᶜ).ConnectedComponent) :
    (G.induce (Z \ {z})ᶜ).ConnectedComponent :=
  c.map (remainHom G Z z)

lemma mapRemainComp_mk {Z : Set V} {z : V} (v : {x // x ∈ Zᶜ}) :
    mapRemainComp G Z z ((G.induce Zᶜ).connectedComponentMk v) =
      (G.induce (Z \ {z})ᶜ).connectedComponentMk
        (remainIncl Z z v) :=
  rfl

/-- Component of the returned vertex. -/
def returnedComp (Z : Set V) (z : V) :
    (G.induce (Z \ {z})ᶜ).ConnectedComponent :=
  (G.induce (Z \ {z})ᶜ).connectedComponentMk (returnedVert Z z)

lemma adj_returned_remainIncl {Z : Set V} {z : V} {v : {x // x ∈ Zᶜ}} (h : G.Adj z v) :
    (G.induce (Z \ {z})ᶜ).Adj
      (returnedVert Z z) (remainIncl Z z v) :=
  h

lemma eq_remainIncl_of_ne_z {Z : Set V} {z : V} (x : {w // w ∈ (Z \ {z})ᶜ})
    (hx : (x : V) ≠ z) :
    ∃ hx' : (x : V) ∈ Zᶜ,
      x = remainIncl Z z ⟨x, hx'⟩ := by
  refine ⟨mem_compl_of_mem_return_compl_ne x.property hx, ?_⟩
  ext
  rfl

/-- A walk in `G−(Z\{z})` that never visits `z` descends to `G−Z`. -/
lemma reachable_of_avoid_returned {Z : Set V} {z : V}
    {x y : {w // w ∈ (Z \ {z})ᶜ}}
    (p : (G.induce (Z \ {z})ᶜ).Walk x y)
    (hp : ∀ w ∈ p.support, (w : V) ≠ z)
    (hx : (x : V) ∈ Zᶜ) (hy : (y : V) ∈ Zᶜ) :
    (G.induce Zᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  cases p with
  | nil =>
      have : (⟨x, hx⟩ : {t // t ∈ Zᶜ}) = ⟨x, hy⟩ := Subtype.ext rfl
      exact this ▸ Reachable.rfl
  | @cons _ w _ hadj q =>
      have hwz : (w : V) ≠ z := hp w (by
        simp [Walk.support_cons, Walk.start_mem_support])
      have hw' : (w : V) ∈ Zᶜ :=
        mem_compl_of_mem_return_compl_ne w.property hwz
      have hadj0 : (G.induce Zᶜ).Adj ⟨x, hx⟩ ⟨w, hw'⟩ := hadj
      have hq : ∀ t ∈ q.support, (t : V) ≠ z := by
        intro t ht
        exact hp t (by simp [Walk.support_cons, ht])
      exact hadj0.reachable.trans
        (reachable_of_avoid_returned (Z := Z) (z := z) q hq hw' hy)

lemma reachable_of_avoid_remainIncl {Z : Set V} {z : V} {u v : {x // x ∈ Zᶜ}}
    (p : (G.induce (Z \ {z})ᶜ).Walk
      (remainIncl Z z u) (remainIncl Z z v))
    (hp : ∀ x ∈ p.support, (x : V) ≠ z) :
    (G.induce Zᶜ).Reachable u v := by
  have h :=
    reachable_of_avoid_returned (G := G) (Z := Z) (z := z) p hp
      u.property v.property
  have hu : (⟨(remainIncl Z z u : V), u.property⟩ : {x // x ∈ Zᶜ}) = u :=
    Subtype.ext rfl
  have hv : (⟨(remainIncl Z z v : V), v.property⟩ : {x // x ∈ Zᶜ}) = v :=
    Subtype.ext rfl
  exact hu ▸ hv ▸ h

lemma not_mem_tail_of_isPath_cons {α : Type*} {a : α} {l : List α}
    (h : (a :: l).Nodup) : a ∉ l :=
  (List.nodup_cons.mp h).1

/-- `z` reaches `u` in `G−(Z\{z})` iff `u`'s old component meets `z`. -/
lemma reachable_returned_iff {Z : Set V} {z : V} (hz : z ∈ Z) (u : {x // x ∈ Zᶜ}) :
    (G.induce (Z \ {z})ᶜ).Reachable
        (returnedVert Z z)
        (remainIncl Z z u) ↔
      (G.induce Zᶜ).connectedComponentMk u ∈ neighborComponentSet G Z z := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.exists_isPath
    cases p with
    | nil =>
        exact (remainIncl_ne_returned hz u rfl).elim
    | @cons _ w _ hadj q =>
        have hwz : (w : V) ≠ z := by
          intro hweq
          exact hadj.ne (Subtype.ext hweq).symm
        obtain ⟨hw', hweq⟩ := eq_remainIncl_of_ne_z w hwz
        have hadjG : G.Adj z (w : V) := hadj
        have hnodup : (returnedVert Z z :: q.support).Nodup := by
          simpa [Walk.support_cons] using hp.support_nodup
        have hqsupp : ∀ t ∈ q.support, (t : V) ≠ z := by
          intro t ht htz
          have ht' : t = returnedVert Z z := Subtype.ext htz
          exact not_mem_tail_of_isPath_cons hnodup (ht' ▸ ht)
        refine ⟨⟨w, hw'⟩, hadjG, ConnectedComponent.sound ?_⟩
        exact reachable_of_avoid_remainIncl (G := G) (q.copy hweq rfl) (by
          intro t ht htz
          have : t ∈ q.support := by
            cases hweq
            exact ht
          exact hqsupp t this htz)
  · rintro ⟨w, hadj, hw⟩
    have h1 :
        (G.induce (Z \ {z})ᶜ).Reachable
          (returnedVert Z z)
          (remainIncl Z z w) :=
      (adj_returned_remainIncl (G := G) hadj).reachable
    have h2 := reachable_remainIncl (G := G) (z := z) (ConnectedComponent.exact hw)
    exact h1.trans h2

lemma reachable_returned_of_mem_neighbor {Z : Set V} {z : V} (hz : z ∈ Z)
    {u : {x // x ∈ Zᶜ}}
    (h : (G.induce Zᶜ).connectedComponentMk u ∈ neighborComponentSet G Z z) :
    (G.induce (Z \ {z})ᶜ).Reachable
      (returnedVert Z z)
      (remainIncl Z z u) :=
  (reachable_returned_iff (G := G) hz u).mpr h

/-- Two surviving vertices are joined after returning `z` iff they were
already joined or both meet `z`. -/
lemma reachable_remainIncl_iff {Z : Set V} {z : V} (hz : z ∈ Z) (u v : {x // x ∈ Zᶜ}) :
    (G.induce (Z \ {z})ᶜ).Reachable
        (remainIncl Z z u)
        (remainIncl Z z v) ↔
      (G.induce Zᶜ).Reachable u v ∨
        ((G.induce Zᶜ).connectedComponentMk u ∈ neighborComponentSet G Z z ∧
          (G.induce Zᶜ).connectedComponentMk v ∈ neighborComponentSet G Z z) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.exists_isPath
    by_cases hzmem : returnedVert Z z ∈ p.support
    · refine .inr ⟨?_, ?_⟩
      · exact (reachable_returned_iff (G := G) hz u).mp
          (p.takeUntil (returnedVert Z z) hzmem).reachable.symm
      · exact (reachable_returned_iff (G := G) hz v).mp
          (p.dropUntil (returnedVert Z z) hzmem).reachable
    · refine .inl (reachable_of_avoid_remainIncl (G := G) p ?_)
      intro x hx hxz
      exact hzmem <| by
        have : x = returnedVert Z z := Subtype.ext hxz
        exact this ▸ hx
  · rintro (h | ⟨hu, hv⟩)
    · exact reachable_remainIncl (G := G) h
    · exact (reachable_returned_of_mem_neighbor (G := G) hz hu).symm.trans
        (reachable_returned_of_mem_neighbor (G := G) hz hv)

lemma mapRemainComp_eq_returned_iff {Z : Set V} {z : V} (hz : z ∈ Z)
    (c : (G.induce Zᶜ).ConnectedComponent) :
    mapRemainComp G Z z c = returnedComp G Z z ↔
      c ∈ neighborComponentSet G Z z := by
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hc : (G.induce Zᶜ).connectedComponentMk v = c := hv
  rw [← hc, mapRemainComp_mk, returnedComp, ConnectedComponent.eq, reachable_comm]
  exact reachable_returned_iff G hz v

lemma mapRemainComp_supp_of_not_mem {Z : Set V} {z : V} (hz : z ∈ Z)
    {c : (G.induce Zᶜ).ConnectedComponent}
    (hc : c ∉ neighborComponentSet G Z z) :
    (mapRemainComp G Z z c).supp =
      remainIncl Z z '' c.supp := by
  ext x
  constructor
  · intro hx
    rw [ConnectedComponent.mem_supp_iff] at hx
    by_cases hxz : (x : V) = z
    · have : x = returnedVert Z z := Subtype.ext hxz
      have heq : mapRemainComp G Z z c = returnedComp G Z z := by
        rw [this] at hx
        exact hx.symm
      exact (hc ((mapRemainComp_eq_returned_iff (G := G) hz c).mp heq)).elim
    · obtain ⟨hx', hxe⟩ := eq_remainIncl_of_ne_z (Z := Z) (z := z) x hxz
      refine ⟨⟨x, hx'⟩, ?_, hxe.symm⟩
      obtain ⟨v, hv⟩ := c.nonempty_supp
      have hc' : (G.induce Zᶜ).connectedComponentMk v = c := hv
      have hreach :
          (G.induce (Z \ {z})ᶜ).Reachable
            (remainIncl Z z v)
            (remainIncl Z z ⟨x, hx'⟩) := by
        apply ConnectedComponent.exact
        calc
          (G.induce (Z \ {z})ᶜ).connectedComponentMk (remainIncl Z z v)
              = mapRemainComp G Z z ((G.induce Zᶜ).connectedComponentMk v) :=
            (mapRemainComp_mk G v).symm
          _ = mapRemainComp G Z z c := by rw [hc']
          _ = (G.induce (Z \ {z})ᶜ).connectedComponentMk x := hx.symm
          _ = (G.induce (Z \ {z})ᶜ).connectedComponentMk
                (remainIncl Z z ⟨x, hx'⟩) := congrArg _ hxe
      have hiff := (reachable_remainIncl_iff (G := G) hz v ⟨x, hx'⟩).mp hreach
      rcases hiff with h0 | ⟨hmet, _⟩
      · have : (G.induce Zᶜ).connectedComponentMk ⟨x, hx'⟩ = c :=
          (ConnectedComponent.sound h0).symm.trans hc'
        simpa [ConnectedComponent.mem_supp_iff] using this
      · exact (hc (by simpa [hc'] using hmet)).elim
  · rintro ⟨v, hv, rfl⟩
    have hc' : (G.induce Zᶜ).connectedComponentMk v = c := hv
    rw [ConnectedComponent.mem_supp_iff, ← hc', mapRemainComp_mk]

lemma mapRemainComp_ncard_of_not_mem {Z : Set V} {z : V} (hz : z ∈ Z)
    {c : (G.induce Zᶜ).ConnectedComponent}
    (hc : c ∉ neighborComponentSet G Z z) :
    (mapRemainComp G Z z c).supp.ncard = c.supp.ncard := by
  rw [mapRemainComp_supp_of_not_mem (G := G) hz hc,
      ncard_image_of_injective _ (remainIncl_injective Z z)]

lemma mapRemainComp_injOn_not_mem {Z : Set V} {z : V} (hz : z ∈ Z) :
    InjOn (mapRemainComp G Z z) (neighborComponentSet G Z z)ᶜ := by
  intro c hc d hd hcd
  obtain ⟨v, hv⟩ := c.nonempty_supp
  obtain ⟨w, hw⟩ := d.nonempty_supp
  have hreach :
      (G.induce (Z \ {z})ᶜ).Reachable
        (remainIncl Z z v)
        (remainIncl Z z w) := by
    have hc' : (G.induce Zᶜ).connectedComponentMk v = c := hv
    have hd' : (G.induce Zᶜ).connectedComponentMk w = d := hw
    apply ConnectedComponent.exact
    calc
      (G.induce (Z \ {z})ᶜ).connectedComponentMk (remainIncl Z z v)
          = mapRemainComp G Z z c := by
            rw [← hc', mapRemainComp_mk]
      _ = mapRemainComp G Z z d := hcd
      _ = (G.induce (Z \ {z})ᶜ).connectedComponentMk (remainIncl Z z w) := by
            rw [← hd', mapRemainComp_mk]
  have hiff := (reachable_remainIncl_iff (G := G) hz v w).mp hreach
  rcases hiff with h0 | ⟨hmet, _⟩
  · have hc' : (G.induce Zᶜ).connectedComponentMk v = c := hv
    have hd' : (G.induce Zᶜ).connectedComponentMk w = d := hw
    exact hc'.symm.trans (ConnectedComponent.sound h0 |>.trans hd')
  · have hc' : (G.induce Zᶜ).connectedComponentMk v = c := hv
    exact (hc (by simpa [hc'] using hmet)).elim

lemma returnedComp_supp {Z : Set V} {z : V} (hz : z ∈ Z) :
    (returnedComp G Z z).supp =
      insert (returnedVert Z z)
        (remainIncl Z z ''
          (⋃ c ∈ neighborComponentSet G Z z, c.supp)) := by
  ext x
  constructor
  · intro hx
    rw [ConnectedComponent.mem_supp_iff, returnedComp] at hx
    by_cases hxz : (x : V) = z
    · left
      exact Subtype.ext hxz
    · obtain ⟨hx', hxe⟩ := eq_remainIncl_of_ne_z (Z := Z) (z := z) x hxz
      refine .inr ⟨⟨x, hx'⟩, ?_, hxe.symm⟩
      rw [mem_iUnion₂]
      refine ⟨(G.induce Zᶜ).connectedComponentMk ⟨x, hx'⟩, ?_, ?_⟩
      · exact (reachable_returned_iff (G := G) hz ⟨x, hx'⟩).mp (by
          have hreach : (G.induce (Z \ {z})ᶜ).Reachable
              (returnedVert Z z) x := ConnectedComponent.exact hx.symm
          exact hxe ▸ hreach)
      · simp [ConnectedComponent.mem_supp_iff]
  · intro hx
    rw [mem_insert_iff] at hx
    rcases hx with rfl | ⟨v, hv, rfl⟩
    · simp [ConnectedComponent.mem_supp_iff, returnedComp]
    · rw [mem_iUnion₂] at hv
      obtain ⟨c, hc, hv'⟩ := hv
      have hc' : (G.induce Zᶜ).connectedComponentMk v = c := hv'
      have hmet : (G.induce Zᶜ).connectedComponentMk v ∈
          neighborComponentSet G Z z := by simpa [hc'] using hc
      rw [ConnectedComponent.mem_supp_iff, returnedComp, ConnectedComponent.eq]
      exact (reachable_returned_of_mem_neighbor (G := G) hz hmet).symm

lemma ncard_iUnion_supp {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (s : Finset H.ConnectedComponent) :
    (⋃ c ∈ s, c.supp).ncard = ∑ c ∈ s, c.supp.ncard := by
  classical
  have hunion :
      (⋃ c ∈ s, c.supp).toFinset = s.biUnion fun c => c.supp.toFinset := by
    ext x
    simp
  rw [ncard_eq_toFinset_card', hunion, Finset.card_biUnion]
  · simp [ncard_eq_toFinset_card']
  · intro a _ b _ hab
    exact disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hab)

lemma returnedComp_ncard {Z : Set V} {z : V} (hz : z ∈ Z) :
    (returnedComp G Z z).supp.ncard =
      1 + ∑ c ∈ (neighborComponentSet G Z z).toFinset, c.supp.ncard := by
  have himage :
      remainIncl Z z '' (⋃ c ∈ neighborComponentSet G Z z, c.supp) =
        remainIncl Z z ''
          (⋃ c ∈ (neighborComponentSet G Z z).toFinset, c.supp) := by
    simp
  have hnot :
      returnedVert Z z ∉
        remainIncl Z z '' (⋃ c ∈ neighborComponentSet G Z z, c.supp) := by
    intro h
    obtain ⟨v, _, hv⟩ := (mem_image _ _ _).mp h
    exact v.property (congrArg Subtype.val hv ▸ hz)
  rw [returnedComp_supp (G := G) hz, ncard_insert_of_notMem hnot,
      ncard_image_of_injective _ (remainIncl_injective Z z)]
  have hunion :
      (⋃ c ∈ neighborComponentSet G Z z, c.supp) =
        ⋃ c ∈ (neighborComponentSet G Z z).toFinset, c.supp := by
    simp
  rw [hunion, ncard_iUnion_supp, add_comm]

lemma returnedComp_odd_iff {Z : Set V} {z : V} (hz : z ∈ Z) :
    Odd (returnedComp G Z z).supp.ncard ↔
      Even (neighborComponentSet G Z z ∩ (G.induce Zᶜ).oddComponents).ncard := by
  have hsum := returnedComp_ncard (G := G) hz
  have hodd :
      Odd (∑ c ∈ (neighborComponentSet G Z z).toFinset, c.supp.ncard) ↔
        Odd ((neighborComponentSet G Z z).toFinset.filter
          fun c => Odd c.supp.ncard).card :=
    Finset.odd_sum_iff_odd_card_odd _
  have hcard :
      ((neighborComponentSet G Z z).toFinset.filter
          fun c => Odd c.supp.ncard).card =
        (neighborComponentSet G Z z ∩ (G.induce Zᶜ).oddComponents).ncard := by
    rw [ncard_eq_toFinset_card']
    congr 1
    ext c
    simp [oddComponents, Finset.mem_filter, Set.mem_toFinset]
  have hparity : Odd (1 + ∑ c ∈ (neighborComponentSet G Z z).toFinset, c.supp.ncard) ↔
      Even (∑ c ∈ (neighborComponentSet G Z z).toFinset, c.supp.ncard) := by
    rw [add_comm, Nat.odd_add_one, Nat.not_odd_iff_even]
  rw [hsum, hparity, ← Nat.not_odd_iff_even, hodd, hcard, Nat.not_odd_iff_even]

lemma oddComponentCount_return_eq {Z : Set V} {z : V} (hz : z ∈ Z) :
    oddComponentCount G (Z \ {z}) =
      oddComponentCount G Z -
          (neighborComponentSet G Z z ∩ (G.induce Zᶜ).oddComponents).ncard +
        (if Even (neighborComponentSet G Z z ∩ (G.induce Zᶜ).oddComponents).ncard
          then 1 else 0) := by
  classical
  set G0 := G.induce Zᶜ
  set G1 := G.induce (Z \ {z})ᶜ
  set met := neighborComponentSet G Z z
  set k := (met ∩ G0.oddComponents).ncard
  set untouched := (metᶜ : Set G0.ConnectedComponent)
  have hpart :
      G0.oddComponents =
        (untouched ∩ G0.oddComponents) ∪ (met ∩ G0.oddComponents) := by
    ext c
    constructor
    · intro hc
      by_cases hmet : c ∈ met
      · exact .inr ⟨hmet, hc⟩
      · exact .inl ⟨hmet, hc⟩
    · intro hc
      rcases hc with ⟨_, hodd⟩ | ⟨_, hodd⟩ <;> exact hodd
  have hdisj :
      Disjoint (untouched ∩ G0.oddComponents) (met ∩ G0.oddComponents) := by
    rw [disjoint_iff_inter_eq_empty]
    ext c
    constructor
    · intro h
      exact (h.1.1 h.2.1).elim
    · intro h
      exact h.elim
  have h0 :
      oddComponentCount G Z =
        (untouched ∩ G0.oddComponents).ncard + k := by
    have hn := congrArg ncard hpart
    rw [ncard_union_eq hdisj] at hn
    simpa [oddComponentCount, k] using hn
  have himg_inj : InjOn (mapRemainComp G Z z) (untouched ∩ G0.oddComponents) :=
    (mapRemainComp_injOn_not_mem (G := G) hz).mono inter_subset_left
  have hncard_img :
      (mapRemainComp G Z z '' (untouched ∩ G0.oddComponents)).ncard =
        (untouched ∩ G0.oddComponents).ncard :=
    himg_inj.ncard_image
  have hnot_ret :
      returnedComp G Z z ∉ mapRemainComp G Z z '' (untouched ∩ G0.oddComponents) := by
    intro h
    obtain ⟨c, hc, heq⟩ := h
    have : c ∈ met := (mapRemainComp_eq_returned_iff (G := G) hz c).mp heq
    exact hc.1 this
  have hodd_img :
      mapRemainComp G Z z '' (untouched ∩ G0.oddComponents) ⊆ G1.oddComponents := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := hd
    have : Odd (mapRemainComp G Z z c).supp.ncard := by
      rw [mapRemainComp_ncard_of_not_mem (G := G) hz hc.1]
      exact hc.2
    exact this
  have hcover :
      G1.oddComponents =
        (mapRemainComp G Z z '' (untouched ∩ G0.oddComponents)) ∪
          {c | c = returnedComp G Z z ∧ Odd c.supp.ncard} := by
    ext d
    constructor
    · intro hd
      by_cases hret : d = returnedComp G Z z
      · exact .inr ⟨hret, hret ▸ hd⟩
      · left
        obtain ⟨x, hx⟩ := d.nonempty_supp
        have hxz : (x : V) ≠ z := by
          intro hxz
          have hxret : x = returnedVert Z z := Subtype.ext hxz
          have : d = returnedComp G Z z := by
            rw [hxret, ConnectedComponent.mem_supp_iff] at hx
            exact hx.symm
          exact hret this
        obtain ⟨hx', hxe⟩ := eq_remainIncl_of_ne_z x hxz
        set u : {v // v ∈ Zᶜ} := ⟨x, hx'⟩
        set c := G0.connectedComponentMk u
        have hdc : mapRemainComp G Z z c = d := by
          have hxmk : (G.induce (Z \ {z})ᶜ).connectedComponentMk x = d := hx
          rw [hxe] at hxmk
          exact (mapRemainComp_mk G u).symm.trans hxmk
        have hc_un : c ∉ met := by
          intro hmet
          have : d = returnedComp G Z z := by
            rw [← hdc]
            exact (mapRemainComp_eq_returned_iff (G := G) hz c).mpr hmet
          exact hret this
        have hc_odd : c ∈ G0.oddComponents := by
          have : Odd (mapRemainComp G Z z c).supp.ncard := by
            simpa [hdc] using hd
          rw [mapRemainComp_ncard_of_not_mem (G := G) hz hc_un] at this
          exact this
        exact ⟨c, ⟨hc_un, hc_odd⟩, hdc⟩
    · intro hd
      rcases hd with h | ⟨rfl, hodd⟩
      · exact hodd_img h
      · exact hodd
  have hdisj2 :
      Disjoint (mapRemainComp G Z z '' (untouched ∩ G0.oddComponents))
        {c | c = returnedComp G Z z ∧ Odd c.supp.ncard} := by
    rw [Set.disjoint_left]
    intro d hd hd'
    exact hnot_ret (by
      have : d = returnedComp G Z z := hd'.1
      simpa [this] using hd)
  have hret_ncard :
      {c : G1.ConnectedComponent |
          c = returnedComp G Z z ∧ Odd c.supp.ncard}.ncard =
        if Odd (returnedComp G Z z).supp.ncard then 1 else 0 := by
    by_cases hodd : Odd (returnedComp G Z z).supp.ncard
    · have : {c : G1.ConnectedComponent |
          c = returnedComp G Z z ∧ Odd c.supp.ncard} =
          {returnedComp G Z z} := by
        ext c
        constructor
        · intro h
          exact h.1
        · intro h
          exact ⟨h, h ▸ hodd⟩
      rw [this, ncard_singleton, if_pos hodd]
    · have : {c : G1.ConnectedComponent |
          c = returnedComp G Z z ∧ Odd c.supp.ncard} = ∅ := by
        ext c
        constructor
        · intro h
          exact (hodd (h.1 ▸ h.2)).elim
        · intro h
          exact h.elim
      rw [this, ncard_empty, if_neg hodd]
  have h1 :
      oddComponentCount G (Z \ {z}) =
        (untouched ∩ G0.oddComponents).ncard +
          (if Odd (returnedComp G Z z).supp.ncard then 1 else 0) := by
    simp only [oddComponentCount, G1]
    rw [hcover, ncard_union_eq hdisj2, hncard_img, hret_ncard]
  have hk_le : k ≤ oddComponentCount G Z := by
    simp only [oddComponentCount, k, met, G0]
    exact ncard_le_ncard inter_subset_right
  have hsub : (untouched ∩ G0.oddComponents).ncard = oddComponentCount G Z - k := by
    omega
  have hite : (if Odd (returnedComp G Z z).supp.ncard then 1 else 0) =
      if Even k then 1 else 0 := by
    have hiff := returnedComp_odd_iff (G := G) hz
    by_cases hodd : Odd (returnedComp G Z z).supp.ncard
    · have hkEven : Even k := hiff.mp hodd
      simp [hodd, hkEven]
    · have hkOdd : ¬ Even k := fun hkEven => hodd (hiff.mpr hkEven)
      simp [hodd, hkOdd]
  rw [h1, hsub, hite]

/-- Returning a vertex that meets at most two components of `G−Z` drops
the odd-component count by at most one. -/
theorem oddComponentCount_return_le {Z : Set V} {z : V} (hz : z ∈ Z)
    (hmeet : (neighborComponentSet G Z z).ncard ≤ 2) :
    oddComponentCount G (Z \ {z}) + 1 ≥ oddComponentCount G Z := by
  classical
  set k := (neighborComponentSet G Z z ∩ (G.induce Zᶜ).oddComponents).ncard
    with hkdef
  have hk : (neighborComponentSet G Z z ∩ (G.induce Zᶜ).oddComponents).ncard ≤
      (neighborComponentSet G Z z).ncard := ncard_le_ncard inter_subset_left
  have hk2 : k ≤ 2 := hk.trans hmeet
  have hk_le : (neighborComponentSet G Z z ∩ (G.induce Zᶜ).oddComponents).ncard ≤
      oddComponentCount G Z := ncard_le_ncard inter_subset_right
  have heq := oddComponentCount_return_eq (G := G) hz
  rw [← hkdef] at heq hk_le
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at heq
    simp at heq
    omega
  · rw [h1] at heq hk_le
    have : ¬ Even (1 : ℕ) := by decide
    simp [this] at heq
    omega
  · rw [h2] at heq hk_le
    have : Even (2 : ℕ) := even_two
    simp [this] at heq
    omega

/-- Signed deficiency cannot decrease when returning a vertex that meets
at most two components of the deleted remainder. -/
theorem signedDeficiency_return_mono {Z : Set V} {z : V} (hz : z ∈ Z)
    (hmeet : (neighborComponentSet G Z z).ncard ≤ 2) :
    signedDeficiency G Z ≤ signedDeficiency G (Z \ {z}) := by
  have hodd := oddComponentCount_return_le (G := G) hz hmeet
  have hpos : 1 ≤ Z.ncard :=
    Nat.one_le_iff_ne_zero.mpr (ncard_ne_zero_of_mem hz)
  have hZ : ((Z \ {z}).ncard : ℤ) = (Z.ncard : ℤ) - 1 := by
    rw [ncard_sdiff_singleton_of_mem hz, Nat.cast_sub hpos, Nat.cast_one]
  simp only [signedDeficiency, hZ]
  have hoddZ : (oddComponentCount G (Z \ {z}) : ℤ) + 1 ≥
      (oddComponentCount G Z : ℤ) := by exact_mod_cast hodd
  omega

/-! ## Gadget survivor classification (interface §4) -/

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An original vertex still has a surviving clone outside the gadget cut. -/
def hasSurvivingClone (Z : Set (GadgetVert G)) (v : V) : Prop :=
  ∃ b : Fin 2, GadgetVert.clone v b ∉ Z

/-- An original vertex still has a surviving port outside the gadget cut. -/
def hasSurvivingPort (Z : Set (GadgetVert G)) (v : V) : Prop :=
  ∃ w, ∃ h : G.Adj v w, GadgetVert.port v w h ∉ Z

/-- S-vertices: both clones lie in the cut. -/
def classS (Z : Set (GadgetVert G)) (v : V) : Prop :=
  ¬ hasSurvivingClone Z v

/-- T-vertices: some clone survives, but no port survives. -/
def classT (Z : Set (GadgetVert G)) (v : V) : Prop :=
  hasSurvivingClone Z v ∧ ¬ hasSurvivingPort Z v

/-- U-vertices: some clone and some port survive. -/
def classU (Z : Set (GadgetVert G)) (v : V) : Prop :=
  hasSurvivingClone Z v ∧ hasSurvivingPort Z v

lemma classS_of_not_clone (Z : Set (GadgetVert G)) {v : V}
    (h : ∀ b : Fin 2, GadgetVert.clone v b ∈ Z) : classS Z v := by
  intro ⟨b, hb⟩
  exact hb (h b)

lemma gadget_adj_port_cases {v w : V} {hvw : G.Adj v w} {x : GadgetVert G} :
    (gadget G).Adj (.port v w hvw) x ↔
      (∃ b : Fin 2, x = .clone v b) ∨ ∃ h' : G.Adj w v, x = .port w v h' :=
  port_adj_iff

lemma gadget_adj_clone_cases {v : V} {b : Fin 2} {x : GadgetVert G} :
    (gadget G).Adj (.clone v b) x ↔
      ∃ w, ∃ h : G.Adj v w, x = .port v w h :=
  clone_adj_iff

/-- A clone whose every incident port is deleted has no neighbour in the
remainder, so returning it meets zero components. -/
lemma neighborComponentSet_clone_of_no_port
    {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hZ : GadgetVert.clone v b ∈ Z)
    (hports : ∀ w, ∀ h : G.Adj v w, GadgetVert.port v w h ∈ Z) :
    neighborComponentSet (gadget G) Z (.clone v b) = ∅ := by
  ext c
  constructor
  · intro hc
    rcases (mem_neighborComponentSet_iff (G := gadget G)).mp hc with ⟨x, hx, hadj⟩
    obtain ⟨w, h, hxval⟩ := (clone_adj_iff (G := G)).mp hadj
    exact (x.property (hxval ▸ hports w h)).elim
  · intro h
    exact h.elim

lemma port_eq_of_same_ends {v w : V} {h h' : G.Adj v w} :
    GadgetVert.port v w h = GadgetVert.port v w h' :=
  rfl

/-- Returning a T-clone meets zero remainder components. -/
lemma neighborComponentSet_clone_of_classT
    {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hZ : GadgetVert.clone v b ∈ Z) (hT : classT Z v) :
    neighborComponentSet (gadget G) Z (.clone v b) = ∅ :=
  neighborComponentSet_clone_of_no_port hZ (fun w h => by
    by_contra hop
    exact hT.2 ⟨w, h, hop⟩)

/-- A returned S-port meets at most one remainder component (its opposite port). -/
lemma neighborComponentSet_ncard_port_of_classS
    {Z : Set (GadgetVert G)} {v w : V} {hvw : G.Adj v w}
    (hZ : GadgetVert.port v w hvw ∈ Z)
    (hS : classS Z v) :
    (neighborComponentSet (gadget G) Z (.port v w hvw)).ncard ≤ 1 := by
  classical
  have hclones : ∀ b : Fin 2, GadgetVert.clone v b ∈ Z := by
    intro b
    by_contra hb
    exact hS ⟨b, hb⟩
  by_cases hopp : GadgetVert.port w v hvw.symm ∈ Z
  · have hempty : neighborComponentSet (gadget G) Z (.port v w hvw) = ∅ := by
      ext c
      constructor
      · intro hc
        rcases (mem_neighborComponentSet_iff (G := gadget G)).mp hc with ⟨x, _, hadj⟩
        rcases (port_adj_iff (G := G)).mp hadj with ⟨b, hxval⟩ | ⟨h', hxval⟩
        · exact (x.property (hxval ▸ hclones b)).elim
        · have : (x : GadgetVert G) = .port w v hvw.symm :=
            hxval.trans port_eq_of_same_ends
          exact x.property (this ▸ hopp)
      · intro h
        exact h.elim
    simp [hempty]
  · let opp : {x // x ∈ (Zᶜ : Set (GadgetVert G))} := ⟨.port w v hvw.symm, hopp⟩
    let c0 := ((gadget G).induce Zᶜ).connectedComponentMk opp
    have heq : neighborComponentSet (gadget G) Z (.port v w hvw) = {c0} := by
      ext c
      constructor
      · intro hc
        rcases (mem_neighborComponentSet_iff (G := gadget G)).mp hc with ⟨x, hxsupp, hadj⟩
        rcases (port_adj_iff (G := G)).mp hadj with ⟨b, hxval⟩ | ⟨h', hxval⟩
        · exact (x.property (hxval ▸ hclones b)).elim
        · have hxval' : (x : GadgetVert G) = .port w v hvw.symm :=
            hxval.trans port_eq_of_same_ends
          have hxeq : x = opp := Subtype.ext hxval'
          rw [mem_singleton_iff]
          have hxmk : ((gadget G).induce Zᶜ).connectedComponentMk x = c := hxsupp
          rw [hxeq] at hxmk
          exact hxmk.symm
      · intro hc
        rw [mem_singleton_iff] at hc
        subst c
        refine (mem_neighborComponentSet_iff (G := gadget G)).mpr ⟨opp, ?_, ?_⟩
        · simp [c0, ConnectedComponent.mem_supp_iff]
        · exact gadget_adj_mate hvw
    simpa [heq]

/-- Returning a missing U-clone meets at most one remainder component:
all surviving ports of `v` lie in the component of a surviving clone. -/
lemma neighborComponentSet_ncard_clone_of_classU
    {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hZ : GadgetVert.clone v b ∈ Z) (hU : classU Z v) :
    (neighborComponentSet (gadget G) Z (.clone v b)).ncard ≤ 1 := by
  classical
  obtain ⟨b', hb'⟩ := hU.1
  let cl : {x // x ∈ (Zᶜ : Set (GadgetVert G))} := ⟨.clone v b', hb'⟩
  let c0 := ((gadget G).induce Zᶜ).connectedComponentMk cl
  have hsub : neighborComponentSet (gadget G) Z (.clone v b) ⊆ {c0} := by
    intro c hc
    rcases (mem_neighborComponentSet_iff (G := gadget G)).mp hc with ⟨x, hxsupp, hadj⟩
    obtain ⟨w, h, hxval⟩ := (clone_adj_iff (G := G)).mp hadj
    have hadj' : (gadget G).Adj (.clone v b') (x : GadgetVert G) := by
      rw [hxval]
      exact (rfl : v = v)
    have hadjI : ((gadget G).induce Zᶜ).Adj cl x := hadj'
    have : c0 = c :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hadjI).trans
        (by simpa [ConnectedComponent.mem_supp_iff] using hxsupp)
    exact this ▸ mem_singleton c0
  exact (ncard_le_ncard hsub).trans_eq (ncard_singleton _)

/-! ## U-port returns and finite cut normalization (interface §4) -/

lemma classSTU (Z : Set (GadgetVert G)) (v : V) :
    classS Z v ∨ classT Z v ∨ classU Z v := by
  by_cases hc : hasSurvivingClone Z v
  · by_cases hp : hasSurvivingPort Z v
    · exact .inr (.inr ⟨hc, hp⟩)
    · exact .inr (.inl ⟨hc, hp⟩)
  · exact .inl hc

lemma not_classS_of_TU {Z : Set (GadgetVert G)} {v : V}
    (h : classT Z v ∨ classU Z v) : ¬ classS Z v := by
  intro hS
  rcases h with hT | hU
  · exact hS hT.1
  · exact hS hU.1

lemma not_classT_of_SU {Z : Set (GadgetVert G)} {v : V}
    (h : classS Z v ∨ classU Z v) : ¬ classT Z v := by
  intro hT
  rcases h with hS | hU
  · exact hS hT.1
  · exact hT.2 hU.2

lemma classS_clone_mem {Z : Set (GadgetVert G)} {v : V}
    (hS : classS Z v) (b : Fin 2) : GadgetVert.clone v b ∈ Z := by
  by_contra hb
  exact hS ⟨b, hb⟩

lemma classT_port_mem {Z : Set (GadgetVert G)} {v : V}
    (hT : classT Z v) {w : V} (hvw : G.Adj v w) :
    GadgetVert.port v w hvw ∈ Z := by
  by_contra hp
  exact hT.2 ⟨w, hvw, hp⟩

lemma exists_adj_of_classU {Z : Set (GadgetVert G)} {v : V}
    (hU : classU Z v) : ∃ w, G.Adj v w := by
  obtain ⟨w, h, _⟩ := hU.2
  exact ⟨w, h⟩

lemma disjoint_classS_classT (Z : Set (GadgetVert G)) :
    Disjoint {v | classS Z v} {v | classT Z v} := by
  rw [Set.disjoint_left]
  intro v hS hT
  exact hS hT.1

/-- Surviving clones of a U-vertex lie in one remainder component, via the
two-edge walk through a surviving own port (repeated endpoints allowed). -/
lemma reachable_surviving_clones_of_classU
    {Z : Set (GadgetVert G)} {v : V} (hU : classU Z v)
    {b b' : Fin 2}
    (hb : GadgetVert.clone v b ∉ Z) (hb' : GadgetVert.clone v b' ∉ Z) :
    ((gadget G).induce Zᶜ).Reachable
      ⟨.clone v b, hb⟩ ⟨.clone v b', hb'⟩ := by
  obtain ⟨w0, h0, hp0⟩ := hU.2
  have h1 : ((gadget G).induce Zᶜ).Adj
      ⟨.clone v b, hb⟩ ⟨.port v w0 h0, hp0⟩ := by
    rw [induce_adj]
    simp
  have h2 : ((gadget G).induce Zᶜ).Adj
      ⟨.port v w0 h0, hp0⟩ ⟨.clone v b', hb'⟩ := by
    rw [induce_adj]
    simp
  exact h1.reachable.trans h2.reachable

/-- Returning a missing U-port meets at most two remainder components:
the local surviving-clone gadget, and possibly the opposite port. -/
lemma neighborComponentSet_ncard_port_of_classU
    {Z : Set (GadgetVert G)} {v w : V} {hvw : G.Adj v w}
    (_hZ : GadgetVert.port v w hvw ∈ Z) (hU : classU Z v) :
    (neighborComponentSet (gadget G) Z (.port v w hvw)).ncard ≤ 2 := by
  classical
  obtain ⟨b, hb⟩ := hU.1
  let cl : {x // x ∈ (Zᶜ : Set (GadgetVert G))} := ⟨.clone v b, hb⟩
  let cLoc := ((gadget G).induce Zᶜ).connectedComponentMk cl
  have hclone :
      ∀ b' : Fin 2, ∀ hb' : GadgetVert.clone v b' ∉ Z,
        ((gadget G).induce Zᶜ).connectedComponentMk ⟨.clone v b', hb'⟩ = cLoc := by
    intro b' hb'
    exact ConnectedComponent.sound
      (reachable_surviving_clones_of_classU hU hb' hb)
  by_cases hopp : GadgetVert.port w v hvw.symm ∈ Z
  · have hsub : neighborComponentSet (gadget G) Z (.port v w hvw) ⊆ {cLoc} := by
      intro c hc
      rcases (mem_neighborComponentSet_iff (G := gadget G)).mp hc with ⟨x, hxsupp, hadj⟩
      have hxmk : ((gadget G).induce Zᶜ).connectedComponentMk x = c := by
        simpa [ConnectedComponent.mem_supp_iff] using hxsupp
      rcases (port_adj_iff (G := G)).mp hadj with ⟨b', hxval⟩ | ⟨h', hxval⟩
      · have hb' : GadgetVert.clone v b' ∉ Z := by
          simpa [hxval] using x.property
        have hxeq : x = ⟨.clone v b', hb'⟩ := Subtype.ext hxval
        have : c = cLoc := by
          rw [hxeq] at hxmk
          exact hxmk.symm.trans (hclone b' hb')
        exact this ▸ mem_singleton cLoc
      · have hxval' : (x : GadgetVert G) = .port w v hvw.symm :=
          hxval.trans port_eq_of_same_ends
        exact (x.property (hxval' ▸ hopp)).elim
    exact (ncard_le_ncard hsub).trans (by simp [ncard_singleton])
  · let opp : {x // x ∈ (Zᶜ : Set (GadgetVert G))} := ⟨.port w v hvw.symm, hopp⟩
    let cOpp := ((gadget G).induce Zᶜ).connectedComponentMk opp
    have hsub :
        neighborComponentSet (gadget G) Z (.port v w hvw) ⊆ ({cLoc, cOpp} : Set _) := by
      intro c hc
      rcases (mem_neighborComponentSet_iff (G := gadget G)).mp hc with ⟨x, hxsupp, hadj⟩
      have hxmk : ((gadget G).induce Zᶜ).connectedComponentMk x = c := by
        simpa [ConnectedComponent.mem_supp_iff] using hxsupp
      rcases (port_adj_iff (G := G)).mp hadj with ⟨b', hxval⟩ | ⟨h', hxval⟩
      · have hb' : GadgetVert.clone v b' ∉ Z := by
          simpa [hxval] using x.property
        have hxeq : x = ⟨.clone v b', hb'⟩ := Subtype.ext hxval
        have : c = cLoc := by
          rw [hxeq] at hxmk
          exact hxmk.symm.trans (hclone b' hb')
        simp [this]
      · have hxval' : (x : GadgetVert G) = .port w v hvw.symm :=
          hxval.trans port_eq_of_same_ends
        have hxeq : x = opp := Subtype.ext hxval'
        have : c = cOpp := by
          rw [hxeq] at hxmk
          exact hxmk.symm
        simp [this]
    have hpair : ({cLoc, cOpp} : Set _).ncard ≤ 2 :=
      (ncard_insert_le cLoc {cOpp}).trans (by simp [ncard_singleton])
    exact (ncard_le_ncard hsub).trans hpair

/-- Intermediate-cut invariant: original S-clones and T-ports stay deleted. -/
structure CutInv (Z0 W : Set (GadgetVert G)) : Prop where
  subset : W ⊆ Z0
  keep_S_clones : ∀ v, classS Z0 v → ∀ b : Fin 2, GadgetVert.clone v b ∈ W
  keep_T_ports :
    ∀ v, classT Z0 v → ∀ {w : V} (hvw : G.Adj v w), GadgetVert.port v w hvw ∈ W

lemma CutInv.refl (Z : Set (GadgetVert G)) : CutInv Z Z where
  subset := fun _ hx => hx
  keep_S_clones := fun v hS b => classS_clone_mem hS b
  keep_T_ports := fun v hT _ hvw => classT_port_mem hT hvw

lemma classS_of_inv {Z0 W : Set (GadgetVert G)} {v : V}
    (h : CutInv Z0 W) (hS : classS Z0 v) : classS W v := by
  intro ⟨b, hb⟩
  exact hb (h.keep_S_clones v hS b)

lemma classT_of_inv {Z0 W : Set (GadgetVert G)} {v : V}
    (h : CutInv Z0 W) (hT : classT Z0 v) : classT W v := by
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := hT.1
    exact ⟨b, fun hW => hb (h.subset hW)⟩
  · intro ⟨w, hvw, hp⟩
    exact hp (h.keep_T_ports v hT hvw)

lemma classU_of_inv {Z0 W : Set (GadgetVert G)} {v : V}
    (h : CutInv Z0 W) (hU : classU Z0 v) : classU W v := by
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := hU.1
    exact ⟨b, fun hW => hb (h.subset hW)⟩
  · obtain ⟨w, hvw, hp⟩ := hU.2
    exact ⟨w, hvw, fun hW => hp (h.subset hW)⟩

/-- Missing T/U clones still present in the current cut. -/
def pendingTUClones (Z0 W : Set (GadgetVert G)) : Set (GadgetVert G) :=
  {x | x ∈ W ∧ ∃ v : V, ∃ b : Fin 2,
      x = .clone v b ∧ (classT Z0 v ∨ classU Z0 v)}

/-- Missing S/U ports still present in the current cut. -/
def pendingSUPorts (Z0 W : Set (GadgetVert G)) : Set (GadgetVert G) :=
  {x | x ∈ W ∧ ∃ v w : V, ∃ h : G.Adj v w,
      x = .port v w h ∧ (classS Z0 v ∨ classU Z0 v)}

lemma pendingTUClones_sdiff {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hz : z ∈ pendingTUClones Z0 W) :
    pendingTUClones Z0 (W \ {z}) = pendingTUClones Z0 W \ {z} := by
  ext x
  simp only [pendingTUClones, mem_diff, mem_singleton_iff, mem_setOf]
  constructor
  · intro ⟨⟨hxW, hne⟩, h⟩
    exact ⟨⟨hxW, h⟩, hne⟩
  · intro ⟨⟨hxW, h⟩, hne⟩
    exact ⟨⟨hxW, hne⟩, h⟩

lemma pendingSUPorts_sdiff {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hz : z ∈ pendingSUPorts Z0 W) :
    pendingSUPorts Z0 (W \ {z}) = pendingSUPorts Z0 W \ {z} := by
  ext x
  simp only [pendingSUPorts, mem_diff, mem_singleton_iff, mem_setOf]
  constructor
  · intro ⟨⟨hxW, hne⟩, h⟩
    exact ⟨⟨hxW, h⟩, hne⟩
  · intro ⟨⟨hxW, h⟩, hne⟩
    exact ⟨⟨hxW, hne⟩, h⟩

lemma sdiff_pending_eq {α : Type*} {W P : Set α} {z : α}
    (hzP : z ∈ P) (hPW : P ⊆ W) :
    (W \ {z}) \ (P \ {z}) = W \ P := by
  ext x
  simp only [mem_diff, mem_singleton_iff]
  constructor
  · intro ⟨⟨hxW, hxz⟩, hnot⟩
    exact ⟨hxW, fun hxP => hnot ⟨hxP, hxz⟩⟩
  · intro ⟨hxW, hxP⟩
    have hxz : x ≠ z := fun h => hxP (h ▸ hzP)
    exact ⟨⟨hxW, hxz⟩, fun h => hxP h.1⟩

lemma CutInv.return_TU_clone {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hinv : CutInv Z0 W) (hz : z ∈ pendingTUClones Z0 W) :
    CutInv Z0 (W \ {z}) where
  subset := fun x hx => hinv.subset hx.1
  keep_S_clones := by
    intro v hS b
    have hin : GadgetVert.clone v b ∈ W := hinv.keep_S_clones v hS b
    refine ⟨hin, ?_⟩
    intro h
    rw [mem_singleton_iff] at h
    obtain ⟨_, v', b', rfl, hTU⟩ := hz
    injection h with hv _
    cases hv
    exact not_classS_of_TU hTU hS
  keep_T_ports := by
    intro v hT w hvw
    have hin : GadgetVert.port v w hvw ∈ W := hinv.keep_T_ports v hT hvw
    refine ⟨hin, ?_⟩
    intro h
    rw [mem_singleton_iff] at h
    obtain ⟨_, v', b', rfl, _⟩ := hz
    cases h

lemma CutInv.return_SU_port {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hinv : CutInv Z0 W) (hz : z ∈ pendingSUPorts Z0 W) :
    CutInv Z0 (W \ {z}) where
  subset := fun x hx => hinv.subset hx.1
  keep_S_clones := by
    intro v hS b
    have hin : GadgetVert.clone v b ∈ W := hinv.keep_S_clones v hS b
    refine ⟨hin, ?_⟩
    intro h
    rw [mem_singleton_iff] at h
    obtain ⟨_, v', w', h', rfl, _⟩ := hz
    cases h
  keep_T_ports := by
    intro v hT w hvw
    have hin : GadgetVert.port v w hvw ∈ W := hinv.keep_T_ports v hT hvw
    refine ⟨hin, ?_⟩
    intro h
    rw [mem_singleton_iff] at h
    obtain ⟨_, v', w', h', rfl, hSU⟩ := hz
    injection h with hv hw
    cases hv
    exact not_classT_of_SU hSU hT

lemma neighborComponentSet_ncard_pending_TU_clone
    {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hinv : CutInv Z0 W) (hz : z ∈ pendingTUClones Z0 W) :
    (neighborComponentSet (gadget G) W z).ncard ≤ 2 := by
  obtain ⟨hzW, v, b, rfl, hTU⟩ := hz
  rcases hTU with hT | hU
  · have hempty :=
      neighborComponentSet_clone_of_classT (Z := W) hzW (classT_of_inv hinv hT)
    simp [hempty]
  · exact (neighborComponentSet_ncard_clone_of_classU (Z := W) hzW
      (classU_of_inv hinv hU)).trans (by omega)

lemma neighborComponentSet_ncard_pending_SU_port
    {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hinv : CutInv Z0 W) (hz : z ∈ pendingSUPorts Z0 W) :
    (neighborComponentSet (gadget G) W z).ncard ≤ 2 := by
  obtain ⟨hzW, v, w, hvw, rfl, hSU⟩ := hz
  rcases hSU with hS | hU
  · exact (neighborComponentSet_ncard_port_of_classS (Z := W) hzW
      (classS_of_inv hinv hS)).trans (by omega)
  · exact neighborComponentSet_ncard_port_of_classU (Z := W) hzW
      (classU_of_inv hinv hU)

lemma signedDeficiency_return_pending_TU_clone
    {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hinv : CutInv Z0 W) (hz : z ∈ pendingTUClones Z0 W) :
    signedDeficiency (gadget G) W ≤ signedDeficiency (gadget G) (W \ {z}) :=
  signedDeficiency_return_mono (G := gadget G) hz.1
    (neighborComponentSet_ncard_pending_TU_clone hinv hz)

lemma signedDeficiency_return_pending_SU_port
    {Z0 W : Set (GadgetVert G)} {z : GadgetVert G}
    (hinv : CutInv Z0 W) (hz : z ∈ pendingSUPorts Z0 W) :
    signedDeficiency (gadget G) W ≤ signedDeficiency (gadget G) (W \ {z}) :=
  signedDeficiency_return_mono (G := gadget G) hz.1
    (neighborComponentSet_ncard_pending_SU_port hinv hz)

lemma stage_return_clones (Z0 : Set (GadgetVert G)) :
    ∀ W, CutInv Z0 W →
      signedDeficiency (gadget G) W ≤
        signedDeficiency (gadget G) (W \ pendingTUClones Z0 W) ∧
      CutInv Z0 (W \ pendingTUClones Z0 W) ∧
      pendingTUClones Z0 (W \ pendingTUClones Z0 W) = ∅ := by
  intro W hinv0
  generalize hn : (pendingTUClones Z0 W).ncard = n
  induction n generalizing W with
  | zero =>
      have hempty : pendingTUClones Z0 W = ∅ := by
        exact (ncard_eq_zero (s := pendingTUClones Z0 W)).mp hn
      refine ⟨?_, ?_, ?_⟩
      · simp [hempty]
      · simpa [hempty] using hinv0
      · simp [hempty]
  | succ n ih =>
      have hpos : 0 < (pendingTUClones Z0 W).ncard := by omega
      obtain ⟨z, hz⟩ := (ncard_pos (s := pendingTUClones Z0 W)).mp hpos
      have hinv1 : CutInv Z0 (W \ {z}) := hinv0.return_TU_clone hz
      have hPeq : pendingTUClones Z0 (W \ {z}) = pendingTUClones Z0 W \ {z} :=
        pendingTUClones_sdiff hz
      have hcard : (pendingTUClones Z0 (W \ {z})).ncard = n := by
        rw [hPeq, ncard_sdiff_singleton_of_mem hz]
        omega
      obtain ⟨hdef1, hinv2, hempty⟩ := ih (W \ {z}) hinv1 hcard
      have hset :
          (W \ {z}) \ pendingTUClones Z0 (W \ {z}) =
            W \ pendingTUClones Z0 W := by
        rw [hPeq]
        exact sdiff_pending_eq hz (fun x hx => hx.1)
      refine ⟨?_, ?_, ?_⟩
      · exact (signedDeficiency_return_pending_TU_clone hinv0 hz).trans
          (hset ▸ hdef1)
      · simpa [hset] using hinv2
      · simpa [hset] using hempty

lemma stage_return_ports (Z0 : Set (GadgetVert G)) :
    ∀ W, CutInv Z0 W →
      signedDeficiency (gadget G) W ≤
        signedDeficiency (gadget G) (W \ pendingSUPorts Z0 W) ∧
      CutInv Z0 (W \ pendingSUPorts Z0 W) ∧
      pendingSUPorts Z0 (W \ pendingSUPorts Z0 W) = ∅ := by
  intro W hinv0
  generalize hn : (pendingSUPorts Z0 W).ncard = n
  induction n generalizing W with
  | zero =>
      have hempty : pendingSUPorts Z0 W = ∅ := by
        exact (ncard_eq_zero (s := pendingSUPorts Z0 W)).mp hn
      refine ⟨?_, ?_, ?_⟩
      · simp [hempty]
      · simpa [hempty] using hinv0
      · simp [hempty]
  | succ n ih =>
      have hpos : 0 < (pendingSUPorts Z0 W).ncard := by omega
      obtain ⟨z, hz⟩ := (ncard_pos (s := pendingSUPorts Z0 W)).mp hpos
      have hinv1 : CutInv Z0 (W \ {z}) := hinv0.return_SU_port hz
      have hPeq : pendingSUPorts Z0 (W \ {z}) = pendingSUPorts Z0 W \ {z} :=
        pendingSUPorts_sdiff hz
      have hcard : (pendingSUPorts Z0 (W \ {z})).ncard = n := by
        rw [hPeq, ncard_sdiff_singleton_of_mem hz]
        omega
      obtain ⟨hdef1, hinv2, hempty⟩ := ih (W \ {z}) hinv1 hcard
      have hset :
          (W \ {z}) \ pendingSUPorts Z0 (W \ {z}) =
            W \ pendingSUPorts Z0 W := by
        rw [hPeq]
        exact sdiff_pending_eq hz (fun x hx => hx.1)
      refine ⟨?_, ?_, ?_⟩
      · exact (signedDeficiency_return_pending_SU_port hinv0 hz).trans
          (hset ▸ hdef1)
      · simpa [hset] using hinv2
      · simpa [hset] using hempty

/-- Canonical gadget cut: all clones of original S-vertices together with
all ports of original T-vertices. -/
def canonicalCut (Z : Set (GadgetVert G)) : Set (GadgetVert G) :=
  {x | ∃ v : V, ∃ b : Fin 2, x = .clone v b ∧ classS Z v} ∪
    {x | ∃ v w : V, ∃ h : G.Adj v w, x = .port v w h ∧ classT Z v}

lemma canonicalCut_subset (Z : Set (GadgetVert G)) : canonicalCut Z ⊆ Z := by
  intro x hx
  rcases hx with ⟨v, b, rfl, hS⟩ | ⟨v, w, h, rfl, hT⟩
  · exact classS_clone_mem hS b
  · exact classT_port_mem hT h

lemma pendingTUClones_empty_of_return_port {Z0 W : Set (GadgetVert G)}
    {z : GadgetVert G}
    (hempty : pendingTUClones Z0 W = ∅)
    (hz : z ∈ pendingSUPorts Z0 W) :
    pendingTUClones Z0 (W \ {z}) = ∅ := by
  ext x
  constructor
  · intro hx
    have : x ∈ pendingTUClones Z0 W := by
      refine ⟨hx.1.1, ?_⟩
      obtain ⟨v, b, rfl, hTU⟩ := hx.2
      exact ⟨v, b, rfl, hTU⟩
    exact (hempty ▸ this).elim
  · intro h
    exact h.elim

lemma pendingTUClones_empty_after_ports {Z0 W : Set (GadgetVert G)}
    (hempty : pendingTUClones Z0 W = ∅) :
    pendingTUClones Z0 (W \ pendingSUPorts Z0 W) = ∅ := by
  ext x
  constructor
  · intro hx
    have : x ∈ pendingTUClones Z0 W := ⟨(W.sdiff_subset hx.1), hx.2⟩
    exact (hempty ▸ this).elim
  · intro h
    exact h.elim

lemma eq_canonical_of_pending_empty {Z0 W : Set (GadgetVert G)}
    (hinv : CutInv Z0 W)
    (hcl : pendingTUClones Z0 W = ∅)
    (hpo : pendingSUPorts Z0 W = ∅) :
    W = canonicalCut Z0 := by
  ext x
  constructor
  · intro hx
    cases x with
    | clone v b =>
        have hS : classS Z0 v := by
          by_contra hS
          have hTU : classT Z0 v ∨ classU Z0 v := by
            rcases classSTU Z0 v with hS' | hT | hU
            · exact (hS hS').elim
            · exact .inl hT
            · exact .inr hU
          have : GadgetVert.clone v b ∈ pendingTUClones Z0 W :=
            ⟨hx, v, b, rfl, hTU⟩
          exact (hcl ▸ this).elim
        exact .inl ⟨v, b, rfl, hS⟩
    | port v w h =>
        have hT : classT Z0 v := by
          by_contra hT
          have hSU : classS Z0 v ∨ classU Z0 v := by
            rcases classSTU Z0 v with hS | hT' | hU
            · exact .inl hS
            · exact (hT hT').elim
            · exact .inr hU
          have : GadgetVert.port v w h ∈ pendingSUPorts Z0 W :=
            ⟨hx, v, w, h, rfl, hSU⟩
          exact (hpo ▸ this).elim
        exact .inr ⟨v, w, h, rfl, hT⟩
  · intro hx
    rcases hx with ⟨v, b, rfl, hS⟩ | ⟨v, w, h, rfl, hT⟩
    · exact hinv.keep_S_clones v hS b
    · exact hinv.keep_T_ports v hT h

/-- Returning missing T/U clones then missing S/U ports yields the canonical
cut `Z(S,T)`, and signed Tutte deficiency cannot decrease. -/
theorem gadget_normalize_cut (Z : Set (GadgetVert G)) :
    Disjoint {v | classS Z v} {v | classT Z v} ∧
    (∀ v, classU Z v → ∃ w, G.Adj v w) ∧
    canonicalCut Z ⊆ Z ∧
    signedDeficiency (gadget G) Z ≤
      signedDeficiency (gadget G) (canonicalCut Z) := by
  classical
  refine ⟨disjoint_classS_classT Z, fun v => exists_adj_of_classU, canonicalCut_subset Z, ?_⟩
  obtain ⟨hdefC, hinvC, hemptyC⟩ := stage_return_clones Z Z (CutInv.refl Z)
  obtain ⟨hdefP, hinvP, hemptyP⟩ := stage_return_ports Z
    (Z \ pendingTUClones Z Z) hinvC
  have hemptyC' :
      pendingTUClones Z ((Z \ pendingTUClones Z Z) \ pendingSUPorts Z
        (Z \ pendingTUClones Z Z)) = ∅ :=
    pendingTUClones_empty_after_ports hemptyC
  have hW :
      ((Z \ pendingTUClones Z Z) \ pendingSUPorts Z
        (Z \ pendingTUClones Z Z)) =
        canonicalCut Z :=
    eq_canonical_of_pending_empty hinvP hemptyC' hemptyP
  exact hdefC.trans (hW ▸ hdefP)

/-! ## Canonical remainder: membership and isolated T-clones -/

lemma clone_mem_canonicalCut_iff {Z : Set (GadgetVert G)} {v : V} {b : Fin 2} :
    GadgetVert.clone v b ∈ canonicalCut Z ↔ classS Z v := by
  constructor
  · intro h
    rcases h with ⟨v', b', heq, hS⟩ | ⟨_, _, _, heq, _⟩
    · injection heq with hv _
      cases hv
      exact hS
    · cases heq
  · intro hS
    exact .inl ⟨v, b, rfl, hS⟩

lemma port_mem_canonicalCut_iff {Z : Set (GadgetVert G)} {v w : V}
    {hvw : G.Adj v w} :
    GadgetVert.port v w hvw ∈ canonicalCut Z ↔ classT Z v := by
  constructor
  · intro h
    rcases h with ⟨_, _, heq, _⟩ | ⟨v', w', h', heq, hT⟩
    · cases heq
    · injection heq with hv hw
      cases hv
      exact hT
  · intro hT
    exact .inr ⟨v, w, hvw, rfl, hT⟩

lemma not_adj_remain_T_clone {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hT : classT Z v) {x : GadgetVert G} (hx : x ∉ canonicalCut Z) :
    ¬ (gadget G).Adj (.clone v b) x := by
  intro hadj
  obtain ⟨w, hvw, rfl⟩ := (clone_adj_iff (G := G)).mp hadj
  exact hx ((port_mem_canonicalCut_iff (Z := Z)).mpr hT)

lemma reachable_isolated_eq {W : Type*} [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {s : Set W}
    {x y : {z // z ∈ s}}
    (hiso : ∀ z : {z // z ∈ s}, ¬ H.Adj x z)
    (h : (H.induce s).Reachable x y) : x = y := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact (hiso _ hadj).elim

lemma T_clone_component_singleton {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hT : classT Z v) :
    (((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.clone v b, by
          intro h
          exact ((clone_mem_canonicalCut_iff (Z := Z)).mp h) hT.1⟩).supp =
      {⟨.clone v b, by
          intro h
          exact ((clone_mem_canonicalCut_iff (Z := Z)).mp h) hT.1⟩} := by
  ext y
  constructor
  · intro hy
    have hy' : ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
        ⟨.clone v b, by
          intro h
          exact ((clone_mem_canonicalCut_iff (Z := Z)).mp h) hT.1⟩ y := by
      have hy' : ((gadget G).induce (canonicalCut Z)ᶜ).Reachable y
          ⟨.clone v b, by
            intro h
            exact ((clone_mem_canonicalCut_iff (Z := Z)).mp h) hT.1⟩ := by
        simpa [ConnectedComponent.mem_supp_iff] using hy
      exact hy'.symm
    have hiso :
        ∀ z : {z // z ∈ (canonicalCut Z)ᶜ},
          ¬ (gadget G).Adj (.clone v b) z := by
      intro z hadj
      exact not_adj_remain_T_clone hT z.property hadj
    have : (⟨.clone v b, by
          intro h
          exact ((clone_mem_canonicalCut_iff (Z := Z)).mp h) hT.1⟩ :
            {z // z ∈ (canonicalCut Z)ᶜ}) = y :=
      reachable_isolated_eq (H := gadget G) (s := (canonicalCut Z)ᶜ)
        (x := ⟨.clone v b, by
          intro h
          exact ((clone_mem_canonicalCut_iff (Z := Z)).mp h) hT.1⟩) hiso hy'
    simp [this]
  · intro hy
    simp only [mem_singleton_iff] at hy
    subst y
    simp [ConnectedComponent.mem_supp_iff]

lemma T_clone_component_odd {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hT : classT Z v) :
    Odd ((((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.clone v b, by
          intro h
          exact ((clone_mem_canonicalCut_iff (Z := Z)).mp h) hT.1⟩).supp.ncard) := by
  rw [T_clone_component_singleton hT, ncard_singleton]
  exact odd_one

/-- The two clones of a T-vertex are distinct remainder vertices. -/
lemma T_clones_ne {v : V} {b b' : Fin 2} (h : b ≠ b') :
    GadgetVert.clone (G := G) v b ≠ .clone v b' := by
  intro hxy
  injection hxy with _ hb
  exact h hb

lemma ncard_sClones (Z : Set (GadgetVert G)) :
    ({x : GadgetVert G | ∃ v : V, ∃ b : Fin 2, x = .clone v b ∧ classS Z v}).ncard =
      2 * {v | classS Z v}.ncard := by
  classical
  let f : {v // classS Z v} × Fin 2 → GadgetVert G :=
    fun p => .clone p.1.1 p.2
  have himage :
      f '' (Set.univ : Set ({v // classS Z v} × Fin 2)) =
        {x | ∃ v b, x = .clone v b ∧ classS Z v} := by
    ext x
    constructor
    · rintro ⟨p, -, rfl⟩
      exact ⟨p.1.1, p.2, rfl, p.1.2⟩
    · rintro ⟨v, b, rfl, hS⟩
      exact ⟨⟨⟨v, hS⟩, b⟩, mem_univ _, rfl⟩
  have hinj : Function.Injective f := by
    intro a b h
    injection h with hv hb
    apply Prod.ext
    · exact Subtype.ext hv
    · exact hb
  rw [← himage, ncard_image_of_injective _ hinj, ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, mul_comm]
  congr 1
  rw [ncard_eq_toFinset_card', Fintype.card_subtype]
  simp [Set.toFinset_setOf]

lemma ncard_ports_of_vertex (v : V) :
    ({x : GadgetVert G | ∃ w : V, ∃ h : G.Adj v w, x = .port v w h}).ncard =
      G.degree v := by
  classical
  let f : G.neighborSet v → GadgetVert G :=
    fun w => .port v w.1 w.property
  have himage :
      f '' (Set.univ : Set (G.neighborSet v)) =
        {x | ∃ w h, x = .port v w h} := by
    ext x
    constructor
    · rintro ⟨⟨w, hw⟩, -, rfl⟩
      exact ⟨w, by simpa [mem_neighborSet] using hw, rfl⟩
    · rintro ⟨w, h, rfl⟩
      exact ⟨⟨w, by simpa [mem_neighborSet] using h⟩, mem_univ _, rfl⟩
  have hinj : Function.Injective f := by
    intro a b h
    injection h with _ hw
    exact Subtype.ext hw
  rw [← himage, ncard_image_of_injective _ hinj, ncard_univ,
      Nat.card_eq_fintype_card]
  simp [SimpleGraph.degree, neighborFinset, Fintype.card_coe]

lemma ncard_tPorts (Z : Set (GadgetVert G)) :
    ({x : GadgetVert G | ∃ v w : V, ∃ h : G.Adj v w,
        x = .port v w h ∧ classT Z v}).ncard =
      ∑ v ∈ {v | classT Z v}.toFinset, G.degree v := by
  classical
  let T := {v | classT Z v}
  let P : V → Set (GadgetVert G) :=
    fun v => {x | ∃ w h, x = .port v w h}
  have hunion :
      {x | ∃ v w h, x = .port v w h ∧ classT Z v} =
        ⋃ v ∈ T.toFinset, P v := by
    ext x
    simp only [mem_iUnion, mem_toFinset, T, P, mem_setOf_eq]
    constructor
    · rintro ⟨v, w, h, rfl, hT⟩
      exact ⟨v, hT, ⟨w, h, rfl⟩⟩
    · rintro ⟨v, hT, ⟨w, h, rfl⟩⟩
      exact ⟨v, w, h, rfl, hT⟩
  have hdisj : ∀ a ∈ T.toFinset, ∀ b ∈ T.toFinset, a ≠ b →
      Disjoint (P a) (P b) := by
    intro a _ b _ hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    obtain ⟨w, h, rfl⟩ := hxa
    obtain ⟨w', h', heq⟩ := hxb
    injection heq with hv _
    exact hab hv
  rw [hunion, ncard_eq_toFinset_card']
  have hTF :
      (⋃ v ∈ T.toFinset, P v).toFinset =
        T.toFinset.biUnion fun v => (P v).toFinset := by
    ext x
    simp
  rw [hTF, Finset.card_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro v hv
    have : (P v).toFinset.card = G.degree v := by
      rw [← ncard_eq_toFinset_card', ncard_ports_of_vertex]
    simpa [P] using this
  · intro a ha b hb hab
    exact disjoint_toFinset.mpr (hdisj a ha b hb hab)

lemma disjoint_sClones_tPorts (Z : Set (GadgetVert G)) :
    Disjoint
      {x : GadgetVert G | ∃ v b, x = .clone v b ∧ classS Z v}
      {x : GadgetVert G | ∃ v w h, x = .port v w h ∧ classT Z v} := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨_, _, rfl, _⟩ := hx
  obtain ⟨_, _, _, hport, _⟩ := hx'
  cases hport

lemma ncard_canonicalCut (Z : Set (GadgetVert G)) :
    (canonicalCut Z).ncard =
      2 * {v | classS Z v}.ncard +
        ∑ v ∈ {v | classT Z v}.toFinset, G.degree v := by
  simp only [canonicalCut]
  rw [ncard_union_eq (disjoint_sClones_tPorts Z), ncard_sClones, ncard_tPorts]

lemma ST_port_not_mem_canonical {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) :
    GadgetVert.port s t hst ∉ canonicalCut Z := by
  intro h
  exact not_classT_of_SU (.inl hS) ((port_mem_canonicalCut_iff (Z := Z)).mp h)

lemma not_adj_remain_ST_port {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hT : classT Z t)
    {x : GadgetVert G} (hx : x ∉ canonicalCut Z) :
    ¬ (gadget G).Adj (.port s t hst) x := by
  intro hadj
  rcases (port_adj_iff (G := G)).mp hadj with ⟨b, rfl⟩ | ⟨h', rfl⟩
  · exact hx ((clone_mem_canonicalCut_iff (Z := Z)).mpr hS)
  · have : GadgetVert.port t s h' ∈ canonicalCut Z :=
      (port_mem_canonicalCut_iff (Z := Z)).mpr hT
    exact hx this

lemma ST_port_component_singleton {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hT : classT Z t) :
    (((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.port s t hst, ST_port_not_mem_canonical hS⟩).supp =
      {⟨.port s t hst, ST_port_not_mem_canonical hS⟩} := by
  ext y
  constructor
  · intro hy
    have hy' : ((gadget G).induce (canonicalCut Z)ᶜ).Reachable y
        ⟨.port s t hst, ST_port_not_mem_canonical hS⟩ := by
      simpa [ConnectedComponent.mem_supp_iff] using hy
    have hiso :
        ∀ z : {z // z ∈ (canonicalCut Z)ᶜ},
          ¬ (gadget G).Adj (.port s t hst) z := by
      intro z hadj
      exact not_adj_remain_ST_port hS hT z.property hadj
    have : (⟨.port s t hst, ST_port_not_mem_canonical hS⟩ :
        {z // z ∈ (canonicalCut Z)ᶜ}) = y :=
      reachable_isolated_eq (H := gadget G) (s := (canonicalCut Z)ᶜ)
        (x := ⟨.port s t hst, ST_port_not_mem_canonical hS⟩) hiso hy'.symm
    simp [this]
  · intro hy
    simp only [mem_singleton_iff] at hy
    subst y
    simp [ConnectedComponent.mem_supp_iff]

lemma ST_port_component_odd {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hT : classT Z t) :
    Odd ((((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.port s t hst, ST_port_not_mem_canonical hS⟩).supp.ncard) := by
  rw [ST_port_component_singleton hS hT, ncard_singleton]
  exact odd_one

lemma SS_port_only_remain_nbr {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hS' : classS Z t)
    {y : {z // z ∈ (canonicalCut Z)ᶜ}}
    (hadj : (gadget G).Adj (.port s t hst) y) :
    (y : GadgetVert G) = .port t s hst.symm := by
  rcases (port_adj_iff (G := G)).mp hadj with ⟨b, hy⟩ | ⟨h', hy⟩
  · have : GadgetVert.clone s b ∈ canonicalCut Z :=
      (clone_mem_canonicalCut_iff (Z := Z)).mpr hS
    exact (y.property (hy ▸ this)).elim
  · exact hy.trans port_eq_of_same_ends

lemma SS_ports_remain_adj {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hS' : classS Z t) :
    ((gadget G).induce (canonicalCut Z)ᶜ).Adj
      ⟨.port s t hst, ST_port_not_mem_canonical hS⟩
      ⟨.port t s hst.symm, ST_port_not_mem_canonical hS'⟩ := by
  rw [induce_adj]
  exact gadget_adj_mate hst

lemma SS_port_component_pair {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hS' : classS Z t) :
    (((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.port s t hst, ST_port_not_mem_canonical hS⟩).supp =
      ({⟨.port s t hst, ST_port_not_mem_canonical hS⟩,
        ⟨.port t s hst.symm, ST_port_not_mem_canonical hS'⟩} :
          Set _) := by
  set pst := (⟨.port s t hst, ST_port_not_mem_canonical hS⟩ :
      {z // z ∈ (canonicalCut Z)ᶜ})
  set pts := (⟨.port t s hst.symm, ST_port_not_mem_canonical hS'⟩ :
      {z // z ∈ (canonicalCut Z)ᶜ})
  have hne : pst ≠ pts := by
    intro h
    injection (congrArg Subtype.val h) with hv _
    exact hst.ne hv
  have hadj := SS_ports_remain_adj (hst := hst) hS hS'
  have honly_st : ∀ y, ((gadget G).induce (canonicalCut Z)ᶜ).Adj pst y → y = pts := by
    intro y hy
    exact Subtype.ext (SS_port_only_remain_nbr hS hS' (by simpa [induce_adj] using hy))
  have honly_ts : ∀ y, ((gadget G).induce (canonicalCut Z)ᶜ).Adj pts y → y = pst := by
    intro y hy
    have : (y : GadgetVert G) = .port s t hst :=
      SS_port_only_remain_nbr hS' hS (by
        have : (pts : GadgetVert G) = .port t s hst.symm := rfl
        simpa [induce_adj, this, port_eq_of_same_ends] using hy)
    exact Subtype.ext (this.trans port_eq_of_same_ends.symm)
  ext y
  constructor
  · intro hy
    have hreach : ((gadget G).induce (canonicalCut Z)ᶜ).Reachable y pst := by
      simpa [ConnectedComponent.mem_supp_iff] using hy
    obtain ⟨p, hp⟩ := hreach.symm.exists_isPath
    cases p with
    | nil =>
        simp
    | @cons _ w _ hadj' q =>
        have hw : w = pts := honly_st w hadj'
        have hnodup : (pst :: q.support).Nodup := by
          simpa [Walk.support_cons] using hp.support_nodup
        cases q with
        | nil =>
            simp [hw]
        | @cons _ w2 _ hadj2 q2 =>
            have hw2 : w2 = pst := honly_ts w2 (by
              cases hw
              exact hadj2)
            have hw2mem : w2 ∈ (Walk.cons hadj2 q2).support := by
              simp [Walk.support_cons]
            exact (not_mem_tail_of_isPath_cons hnodup (hw2 ▸ hw2mem)).elim
  · intro hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with h | h
    · subst y
      simp [ConnectedComponent.mem_supp_iff]
    · subst y
      rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
      exact hadj.reachable.symm

lemma SS_port_component_even {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hS' : classS Z t) :
    Even ((((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.port s t hst, ST_port_not_mem_canonical hS⟩).supp.ncard) := by
  rw [SS_port_component_pair hS hS']
  set pst := (⟨.port s t hst, ST_port_not_mem_canonical hS⟩ :
      {z // z ∈ (canonicalCut Z)ᶜ})
  set pts := (⟨.port t s hst.symm, ST_port_not_mem_canonical hS'⟩ :
      {z // z ∈ (canonicalCut Z)ᶜ})
  have hne : pst ≠ pts := by
    intro h
    injection (congrArg Subtype.val h) with hv _
    exact hst.ne hv
  have : ({pst, pts} : Set _).ncard = 2 := by
    rw [ncard_insert_of_notMem, ncard_singleton]
    simpa using hne
  rw [this]
  exact even_two

lemma U_clone_not_mem_canonical {Z : Set (GadgetVert G)} {v : V}
    {b : Fin 2} (hU : classU Z v) :
    GadgetVert.clone v b ∉ canonicalCut Z := by
  intro h
  exact not_classS_of_TU (.inr hU) ((clone_mem_canonicalCut_iff (Z := Z)).mp h)

lemma U_surviving_port_not_mem_canonical {Z : Set (GadgetVert G)} {v : V}
    (hU : classU Z v) :
    ∃ w : V, ∃ h : G.Adj v w, GadgetVert.port v w h ∉ canonicalCut Z := by
  obtain ⟨w, h, hp⟩ := hU.2
  refine ⟨w, h, fun hmem => hp (canonicalCut_subset Z hmem)⟩

lemma U_clones_remain_reachable {Z : Set (GadgetVert G)} {v : V}
    (hU : classU Z v) {b b' : Fin 2} :
    ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
      ⟨.clone v b, U_clone_not_mem_canonical (b := b) hU⟩
      ⟨.clone v b', U_clone_not_mem_canonical (b := b') hU⟩ := by
  obtain ⟨w0, h0, hp0⟩ := U_surviving_port_not_mem_canonical hU
  have h1 : ((gadget G).induce (canonicalCut Z)ᶜ).Adj
      ⟨.clone v b, U_clone_not_mem_canonical (b := b) hU⟩
      ⟨.port v w0 h0, hp0⟩ := by
    rw [induce_adj]
    simp
  have h2 : ((gadget G).induce (canonicalCut Z)ᶜ).Adj
      ⟨.port v w0 h0, hp0⟩
      ⟨.clone v b', U_clone_not_mem_canonical (b := b') hU⟩ := by
    rw [induce_adj]
    simp
  exact h1.reachable.trans h2.reachable

end TwoFactor
end Nikoghosyan
