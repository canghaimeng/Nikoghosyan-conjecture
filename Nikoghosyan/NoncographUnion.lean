/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.TraceableExtension
import Nikoghosyan.FactorAssembly

/-!
Manuscript `lem:noncograph-union`: 1-toughness of the induced union of
pairwise vertex-disjoint original Hamiltonian noncograph blocks, in a
host with no induced `P₄ ∪ P₁`. No ambient `OneTough` hypothesis is used.

A separating original cut of the union must meet every selected cycle:
an intact noncograph cycle support is connected and would lie in one
remainder component, which is a cograph by the forbidden-pattern
component lemma. Cycle deletion then bounds each block remainder, the
actual support partition identifies the union remainder, and the
disjoint intersection sum recovers the cut cardinality.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ### Component-count tools on finite unions -/

lemma OneToughOn.empty : OneToughOn G (∅ : Finset V) := by
  intro S hS h2
  have hSempty : S = ∅ := subset_empty.1 hS
  subst hSempty
  simp [componentCount_empty] at h2

lemma componentCount_eq_one_of_connected {U : Finset V}
    (hU : U.Nonempty) (hc : (G.induce (U : Set V)).Connected) :
    componentCount G U = 1 := by
  have hneU : Nonempty (U : Set V) := hU.to_subtype
  have hne : Nonempty (G.induce (U : Set V)).ConnectedComponent :=
    ⟨(G.induce (U : Set V)).connectedComponentMk ⟨hU.choose, hU.choose_spec⟩⟩
  have hss : Subsingleton (G.induce (U : Set V)).ConnectedComponent :=
    hc.preconnected.subsingleton_connectedComponent
  exact Nat.card_eq_one_iff_unique.2 ⟨hss, hne⟩

lemma not_connected_of_two_le_componentCount {U : Finset V}
    (h : 2 ≤ componentCount G U) :
    ¬ (G.induce (U : Set V)).Connected := by
  intro hc
  have hne : U.Nonempty := by
    by_contra hempty
    have : U = ∅ := not_nonempty_iff_eq_empty.1 hempty
    have h0 : componentCount G U = 0 := by simp [this, componentCount_empty]
    omega
  have h1 := componentCount_eq_one_of_connected (G := G) hne hc
  omega

lemma induceIncl_apply {A B : Finset V} (hAB : A ⊆ B) (x : (A : Set V)) :
    induceIncl G hAB x = ⟨x.1, hAB x.2⟩ :=
  rfl

lemma reachable_of_induce_subset {A B : Finset V} (hAB : A ⊆ B) {x y : V}
    (hx : x ∈ A) (hy : y ∈ A)
    (h : (G.induce (A : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (G.induce (B : Set V)).Reachable ⟨x, hAB hx⟩ ⟨y, hAB hy⟩ := by
  convert h.map (induceIncl G hAB) <;> rw [induceIncl_apply]

lemma reachable_of_componentCount_eq_one {U : Finset V}
    (h : componentCount G U = 1) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    (G.induce (U : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  have hss : Subsingleton (G.induce (U : Set V)).ConnectedComponent :=
    (Nat.card_eq_one_iff_unique.1 h).1
  exact ConnectedComponent.exact (Subsingleton.elim _ _)

lemma mem_componentFinset_iff {U : Finset V} {x : V}
    {C : (G.induce (U : Set V)).ConnectedComponent} :
    x ∈ componentFinset G U C ↔
      ∃ hx : x ∈ U, (G.induce (U : Set V)).connectedComponentMk ⟨x, hx⟩ = C := by
  simp [componentFinset]

/-- A connected original cycle support that sits inside `U` is contained
in a single induced component of `U`. -/
lemma cycle_support_subset_componentFinset (c : GraphCycle G) {U : Finset V}
    (hsub : c.support ⊆ U) {x : V} (hx : x ∈ c.support) :
    c.support ⊆
      componentFinset G U
        ((G.induce (U : Set V)).connectedComponentMk ⟨x, hsub hx⟩) := by
  intro y hy
  refine (mem_componentFinset_iff (G := G)).2 ⟨hsub hy, ?_⟩
  apply ConnectedComponent.sound
  exact (reachable_of_induce_subset hsub hx hy
    (reachable_of_componentCount_eq_one (componentCount_cycle_eq_one c) hx hy)).symm

lemma componentCount_biUnion_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset V) :
    componentCount G (s.biUnion f) ≤ s.sum fun i => componentCount G (f i) := by
  induction s using Finset.induction with
  | empty =>
    simp [componentCount_empty]
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    exact (componentCount_union_le G (f a) (s.biUnion f)).trans
      (Nat.add_le_add_left ih _)

lemma biUnion_sdiff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset V) (S : Finset V) :
    s.biUnion f \ S = s.biUnion fun i => f i \ S := by
  ext x
  simp only [mem_sdiff, mem_biUnion]
  constructor
  · intro ⟨⟨i, hi, hxf⟩, hxS⟩
    exact ⟨i, hi, hxf, hxS⟩
  · intro ⟨i, hi, hxf, hxS⟩
    exact ⟨⟨i, hi, hxf⟩, hxS⟩

lemma sdiff_eq_sdiff_inter_noncograph_union (A S : Finset V) :
    A \ S = A \ (S ∩ A) := by
  ext x
  simp [mem_sdiff]

lemma eq_biUnion_inter {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset V) {S : Finset V}
    (hS : S ⊆ s.biUnion f) :
    S = s.biUnion fun i => S ∩ f i := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxf⟩ := mem_biUnion.1 (hS hx)
    exact mem_biUnion.2 ⟨i, hi, mem_inter.2 ⟨hx, hxf⟩⟩
  · intro hx
    obtain ⟨i, _, hx'⟩ := mem_biUnion.1 hx
    exact (mem_inter.1 hx').1

lemma pairwiseDisjoint_inter_of_pairwise {ι : Type*} [DecidableEq ι]
    {c : ι → GraphCycle G}
    (hdisj : Pairwise fun i j => Disjoint (c i).support (c j).support)
    (I : Finset ι) (S : Finset V) :
    Set.PairwiseDisjoint (I : Set ι) fun i => S ∩ (c i).support := by
  intro i hi j hj hij
  exact (hdisj hij).mono inter_subset_right inter_subset_right

lemma card_sum_inter_cycle_family {ι : Type*} [DecidableEq ι]
    (c : ι → GraphCycle G)
    (hdisj : Pairwise fun i j => Disjoint (c i).support (c j).support)
    (I : Finset ι) {S : Finset V}
    (hS : S ⊆ I.biUnion fun i => (c i).support) :
    (I.sum fun i => (S ∩ (c i).support).card) = S.card := by
  have hunion : S = I.biUnion fun i => S ∩ (c i).support :=
    eq_biUnion_inter I (fun i => (c i).support) hS
  have hd := pairwiseDisjoint_inter_of_pairwise (c := c) hdisj I S
  rw [← card_biUnion hd, ← hunion]

/-! ### Every selected noncograph cycle meets a genuine remainder cut -/

lemma selected_cycle_meets_cut {ι : Type*} [DecidableEq ι]
    (c : ι → GraphCycle G)
    (I : Finset ι) (hcof : NoInducedP4UnionP1 G)
    (hnc : ∀ i ∈ I, ¬ IsCograph G (c i).support)
    {S : Finset V}
    (_hS : S ⊆ I.biUnion fun i => (c i).support)
    (h2 : 2 ≤ componentCount G ((I.biUnion fun i => (c i).support) \ S))
    {i : ι} (hi : i ∈ I) :
    (S ∩ (c i).support).Nonempty := by
  by_contra hdis
  have hmiss : Disjoint S (c i).support :=
    disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 hdis)
  set J := I.biUnion fun j => (c j).support
  set U := J \ S
  have hCsubJ : (c i).support ⊆ J :=
    subset_biUnion_of_mem (fun j => (c j).support) hi
  have hCsubU : (c i).support ⊆ U := by
    intro x hx
    exact mem_sdiff.2 ⟨hCsubJ hx, fun hxS =>
      Finset.disjoint_left.1 hmiss hxS hx⟩
  have hdc : ¬ (G.induce (U : Set V)).Connected :=
    not_connected_of_two_le_componentCount (G := G) h2
  have hx : (c i).start ∈ (c i).support := (c i).start_mem_support
  let C :=
    (G.induce (U : Set V)).connectedComponentMk ⟨(c i).start, hCsubU hx⟩
  have hcog : IsCograph G (componentFinset G U C) :=
    NoInducedP4UnionP1.isCograph_componentFinset (G := G) hcof hdc C
  have hsub :=
    cycle_support_subset_componentFinset (c i) hCsubU hx
  exact hnc i hi (IsCograph.subset (G := G) hcog hsub)

/-! ### Primary toughness theorem -/

/-- Manuscript `lem:noncograph-union` on an arbitrary finite family of
pairwise-disjoint original cycles whose supports are noncographs. Empty
selected index sets are included and give the empty-support case. -/
theorem oneToughOn_of_noncograph_cycle_family
    {ι : Type*} [DecidableEq ι]
    (c : ι → GraphCycle G)
    (hdisj : Pairwise fun i j => Disjoint (c i).support (c j).support)
    (I : Finset ι) (hcof : NoInducedP4UnionP1 G)
    (hnc : ∀ i ∈ I, ¬ IsCograph G (c i).support) :
    OneToughOn G (I.biUnion fun i => (c i).support) := by
  intro S hS h2
  set J := I.biUnion fun i => (c i).support
  have hmeet : ∀ i ∈ I, (S ∩ (c i).support).Nonempty :=
    fun i hi => selected_cycle_meets_cut (c := c) I hcof hnc hS h2 hi
  have hrem : J \ S = I.biUnion fun i => (c i).support \ S :=
    biUnion_sdiff I (fun i => (c i).support) S
  rw [hrem]
  have hblock :
      ∀ i ∈ I,
        componentCount G ((c i).support \ S) ≤ (S ∩ (c i).support).card := by
    intro i hi
    have hSi : S ∩ (c i).support ⊆ (c i).support := inter_subset_right
    have hne := hmeet i hi
    have hrew : (c i).support \ S = (c i).support \ (S ∩ (c i).support) :=
      sdiff_eq_sdiff_inter_noncograph_union _ _
    rw [hrew]
    exact componentCount_cycle_sdiff_le (c i) hSi hne
  have hunion :=
    componentCount_biUnion_le (G := G) I fun i => (c i).support \ S
  have hsum :=
    Finset.sum_le_sum hblock
  have hcard := card_sum_inter_cycle_family (c := c) hdisj I hS
  omega

/-- Support-level form used by a genuine original cycle factor: the
selected noncograph blocks induce a 1-tough original union. -/
theorem oneToughOn_selectedSupport_of_noncograph
    (F : CycleFactor G) (I : Finset (Fin F.card))
    (hcof : NoInducedP4UnionP1 G)
    (hnc : ∀ i ∈ I, ¬ IsCograph G (F.getCycle i).support) :
    OneToughOn G (F.selectedSupport I) := by
  simpa [CycleFactor.selectedSupport] using
    oneToughOn_of_noncograph_cycle_family (c := F.getCycle)
      (fun i j hij => F.disjoint_getCycle hij) I hcof hnc

/-- `OneTough` of the actual induced selected union. -/
theorem oneTough_induce_of_selected_noncograph
    (F : CycleFactor G) (I : Finset (Fin F.card))
    (hcof : NoInducedP4UnionP1 G)
    (hnc : ∀ i ∈ I, ¬ IsCograph G (F.getCycle i).support) :
    OneTough (G.induce ((F.selectedSupport I : Finset V) : Set V)) :=
  (OneToughOn_iff_OneTough_induce (F.selectedSupport I)).1
    (oneToughOn_selectedSupport_of_noncograph F I hcof hnc)

/-! ### Two-cycle specialization -/

noncomputable def twoCycleBlocks (cH cD : GraphCycle G) : Bool → GraphCycle G
  | true => cH
  | false => cD

lemma twoCycleBlocks_pairwise
    {cH cD : GraphCycle G} (hdisj : Disjoint cH.support cD.support) :
    Pairwise fun i j =>
      Disjoint (twoCycleBlocks cH cD i).support
        (twoCycleBlocks cH cD j).support := by
  intro i j hij
  cases i <;> cases j <;> simp [twoCycleBlocks] at hij ⊢
  · exact hdisj.symm
  · exact hdisj

lemma twoCycleBlocks_support (cH cD : GraphCycle G) :
    (univ : Finset Bool).biUnion (fun b => (twoCycleBlocks cH cD b).support) =
      cH.support ∪ cD.support := by
  ext x
  simp [twoCycleBlocks, mem_union]

lemma twoCycleBlocks_noncograph {cH cD : GraphCycle G}
    (hH : ¬ IsCograph G cH.support) (hD : ¬ IsCograph G cD.support) :
    ∀ b : Bool, ¬ IsCograph G (twoCycleBlocks cH cD b).support := by
  intro b
  cases b
  · simpa [twoCycleBlocks] using hD
  · simpa [twoCycleBlocks] using hH

/-- Two actual pairwise-disjoint original noncograph cycles induce a
1-tough union. This does not produce a Hamilton cycle of that union. -/
theorem oneToughOn_of_two_noncograph_cycles
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hcof : NoInducedP4UnionP1 G)
    (hH : ¬ IsCograph G cH.support)
    (hD : ¬ IsCograph G cD.support) :
    OneToughOn G (cH.support ∪ cD.support) := by
  have hnc : ∀ b ∈ (univ : Finset Bool),
      ¬ IsCograph G (twoCycleBlocks cH cD b).support :=
    fun b _ => twoCycleBlocks_noncograph hH hD b
  convert oneToughOn_of_noncograph_cycle_family (twoCycleBlocks cH cD)
      (twoCycleBlocks_pairwise hdisj) (univ : Finset Bool) hcof hnc using 1
  exact (twoCycleBlocks_support cH cD).symm

theorem oneTough_induce_of_two_noncograph_cycles
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hcof : NoInducedP4UnionP1 G)
    (hH : ¬ IsCograph G cH.support)
    (hD : ¬ IsCograph G cD.support) :
    OneTough (G.induce ((cH.support ∪ cD.support : Finset V) : Set V)) :=
  (OneToughOn_iff_OneTough_induce (cH.support ∪ cD.support)).1
    (oneToughOn_of_two_noncograph_cycles cH cD hdisj hcof hH hD)

end Nikoghosyan
