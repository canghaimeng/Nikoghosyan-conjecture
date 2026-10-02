import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
Foundational graph predicates for the Nikoghosyan formalization.

These definitions follow `FORMALIZATION_PLAN.md`. They do not encode any
manuscript theorem as a field of a structure. All edges are edges of the
input `SimpleGraph`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Number of connected components of the subgraph induced by `U`.
The empty vertex set has count zero. -/
noncomputable def componentCount (U : Finset V) : ℕ :=
  Nat.card (G.induce (U : Set V)).ConnectedComponent

/-- Conditional 1-toughness: the cut bound is required only when the
deleted remainder has at least two components. -/
def OneTough : Prop :=
  ∀ S : Finset V,
    2 ≤ componentCount G (univ \ S) →
      componentCount G (univ \ S) ≤ S.card

/-- An induced copy of `P₄` on four distinct original vertices. -/
def InducedP4 (a b c d : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧
    ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b d

/-- Exclusion of an induced `P₄ ∪ P₁`. -/
def NoInducedP4UnionP1 : Prop :=
  ∀ ⦃a b c d x : V⦄,
    InducedP4 G a b c d →
      x ≠ a → x ≠ b → x ≠ c → x ≠ d →
        G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d

/-- Induced-`P₄`-free predicate on a specified original vertex set. -/
def IsCograph (U : Finset V) : Prop :=
  ∀ ⦃a b c d : V⦄, a ∈ U → b ∈ U → c ∈ U → d ∈ U → ¬ InducedP4 G a b c d

/-- Open antineighborhood of `v` in `G`. -/
noncomputable def antineighbors (v : V) : Finset V :=
  univ.filter fun x => x ≠ v ∧ ¬ G.Adj v x

/-- Vertices of one induced connected component, as original vertices. -/
noncomputable def componentFinset (U : Finset V)
    (C : (G.induce (U : Set V)).ConnectedComponent) : Finset V :=
  U.filter fun x =>
    ∃ hx : x ∈ U, (G.induce (U : Set V)).connectedComponentMk ⟨x, hx⟩ = C

lemma componentCount_empty : componentCount G ∅ = 0 := by
  simp [componentCount]

lemma componentCount_singleton (v : V) : componentCount G {v} = 1 := by
  let s : Set V := ({v} : Finset V)
  haveI : Unique s :=
    { default := ⟨v, mem_singleton_self v⟩
      uniq := by
        intro y
        apply Subtype.ext
        simpa [s] using y.property }
  haveI : Unique (G.induce s).ConnectedComponent := inferInstance
  simp [componentCount, s]

lemma componentCount_univ :
    componentCount G univ = Nat.card G.ConnectedComponent := by
  rw [componentCount, Finset.coe_univ]
  exact Nat.card_congr G.induceUnivIso.connectedComponentEquiv

/-- Inclusion of induced vertex sets yields a homomorphism of induced graphs. -/
def induceIncl {A B : Finset V} (hAB : A ⊆ B) :
    G.induce (A : Set V) →g G.induce (B : Set V) :=
  (G.induceHomOfLE (fun _ hx => hAB hx)).toHom

lemma componentCount_union_le (A B : Finset V) :
    componentCount G (A ∪ B) ≤ componentCount G A + componentCount G B := by
  let f : (G.induce (A : Set V)).ConnectedComponent ⊕
        (G.induce (B : Set V)).ConnectedComponent →
      (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent
    | .inl C => C.map (induceIncl G (subset_union_left (s₁ := A)))
    | .inr C => C.map (induceIncl G (subset_union_right (s₁ := A)))
  have hf : Surjective f := by
    intro C
    refine C.ind fun x => ?_
    rcases mem_union.mp x.property with hA | hB
    · refine ⟨.inl ((G.induce (A : Set V)).connectedComponentMk ⟨x.val, hA⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
    · refine ⟨.inr ((G.induce (B : Set V)).connectedComponentMk ⟨x.val, hB⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
  haveI : Fintype (A : Set V) := inferInstance
  haveI : Fintype (B : Set V) := inferInstance
  haveI : Fintype ((A ∪ B : Finset V) : Set V) := inferInstance
  haveI : DecidableRel (G.induce (A : Set V)).Adj := inferInstance
  haveI : DecidableRel (G.induce (B : Set V)).Adj := inferInstance
  haveI : Fintype (G.induce (A : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce (B : Set V)).ConnectedComponent := inferInstance
  simpa [componentCount, Nat.card_sum, Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_surjective f hf

lemma componentCount_insert_le (U : Finset V) (u : V) :
    componentCount G (insert u U) ≤ componentCount G U + 1 := by
  rw [insert_eq]
  have h := componentCount_union_le G {u} U
  have hs := componentCount_singleton G u
  omega

lemma componentCount_insert_of_adj {U : Finset V} {u w : V}
    (hw : w ∈ U) (hadj : G.Adj u w) :
    componentCount G (insert u U) ≤ componentCount G U := by
  let f : (G.induce (U : Set V)).ConnectedComponent →
      (G.induce ((insert u U : Finset V) : Set V)).ConnectedComponent :=
    fun C => C.map (induceIncl G (Finset.subset_insert u U))
  have hf : Surjective f := by
    intro C
    refine C.ind fun x => ?_
    by_cases hx : x.val = u
    · refine ⟨(G.induce (U : Set V)).connectedComponentMk ⟨w, hw⟩, ?_⟩
      apply ConnectedComponent.sound
      change (G.induce ((insert u U : Finset V) : Set V)).Reachable
          (induceIncl G (Finset.subset_insert u U) ⟨w, hw⟩) x
      have hw' :
          induceIncl G (Finset.subset_insert u U) ⟨w, hw⟩ =
            ⟨w, mem_insert_of_mem hw⟩ := rfl
      rw [hw']
      have hx' : (⟨u, mem_insert_self u U⟩ : ((insert u U : Finset V) : Set V)) = x :=
        Subtype.ext hx.symm
      rw [← hx']
      exact Adj.reachable <| by simpa [induce_adj] using hadj.symm
    · have hxU : x.val ∈ U := (mem_insert.mp x.property).resolve_left hx
      refine ⟨(G.induce (U : Set V)).connectedComponentMk ⟨x.val, hxU⟩, ?_⟩
      apply ConnectedComponent.sound
      have : induceIncl G (Finset.subset_insert u U) ⟨x.val, hxU⟩ = x :=
        Subtype.ext rfl
      simpa [this] using Reachable.rfl
  exact Nat.card_le_card_of_surjective f hf

lemma IsCograph.subset {U W : Finset V} (hW : IsCograph G W) (hUW : U ⊆ W) :
    IsCograph G U := by
  intro a b c d ha hb hc hd
  exact hW (hUW ha) (hUW hb) (hUW hc) (hUW hd)

lemma IsCograph.empty : IsCograph G ∅ := by
  intro a _ _ _ ha
  exact (notMem_empty a ha).elim

lemma NoInducedP4UnionP1.isCograph_antineighbors
    (h : NoInducedP4UnionP1 G) (v : V) :
    IsCograph G (antineighbors G v) := by
  intro a b c d ha hb hc hd hp
  have ha' := mem_filter.mp ha
  have hb' := mem_filter.mp hb
  have hc' := mem_filter.mp hc
  have hd' := mem_filter.mp hd
  have hx :
      ¬ (G.Adj v a ∨ G.Adj v b ∨ G.Adj v c ∨ G.Adj v d) := by
    simp [ha'.2.2, hb'.2.2, hc'.2.2, hd'.2.2]
  exact hx <| h hp ha'.2.1.symm hb'.2.1.symm hc'.2.1.symm hd'.2.1.symm

lemma NoInducedP4UnionP1.isCograph_componentFinset
    (h : NoInducedP4UnionP1 G) {U : Finset V}
    (hdc : ¬ (G.induce (U : Set V)).Connected)
    (C : (G.induce (U : Set V)).ConnectedComponent) :
    IsCograph G (componentFinset G U C) := by
  have hVne : Nonempty (U : Set V) := C.ind fun x => ⟨x⟩
  have hpre : ¬ (G.induce (U : Set V)).Preconnected := by
    intro hp
    exact hdc ((connected_iff _).2 ⟨hp, hVne⟩)
  have hnt : Nontrivial (G.induce (U : Set V)).ConnectedComponent := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hpre fun x y => ConnectedComponent.exact (Subsingleton.elim _ _)
  obtain ⟨D, hD⟩ := exists_ne C
  obtain ⟨x, hxU, hxD⟩ :
      ∃ (x : V) (hxU : x ∈ U),
        (G.induce (U : Set V)).connectedComponentMk ⟨x, hxU⟩ = D := by
    refine D.ind fun z => ?_
    exact ⟨z.1, z.2, rfl⟩
  intro a b c d ha hb hc hd hp
  have haU : a ∈ U := (mem_filter.mp ha).1
  have hbU : b ∈ U := (mem_filter.mp hb).1
  have hcU : c ∈ U := (mem_filter.mp hc).1
  have hdU : d ∈ U := (mem_filter.mp hd).1
  have haC : (G.induce (U : Set V)).connectedComponentMk ⟨a, haU⟩ = C := by
    obtain ⟨_, hC⟩ := (mem_filter.mp ha).2
    exact hC
  have hbC : (G.induce (U : Set V)).connectedComponentMk ⟨b, hbU⟩ = C := by
    obtain ⟨_, hC⟩ := (mem_filter.mp hb).2
    exact hC
  have hcC : (G.induce (U : Set V)).connectedComponentMk ⟨c, hcU⟩ = C := by
    obtain ⟨_, hC⟩ := (mem_filter.mp hc).2
    exact hC
  have hdC : (G.induce (U : Set V)).connectedComponentMk ⟨d, hdU⟩ = C := by
    obtain ⟨_, hC⟩ := (mem_filter.mp hd).2
    exact hC
  have hxne {y : V} {hyU : y ∈ U}
      (hyC : (G.induce (U : Set V)).connectedComponentMk ⟨y, hyU⟩ = C) : x ≠ y := by
    intro hxy
    apply hD
    subst hxy
    exact hxD.symm.trans hyC
  have nAdj {y : V} {hyU : y ∈ U}
      (hyC : (G.induce (U : Set V)).connectedComponentMk ⟨y, hyU⟩ = C) :
      ¬ G.Adj x y := by
    intro hadj
    have hmk :
        (G.induce (U : Set V)).connectedComponentMk ⟨x, hxU⟩ =
          (G.induce (U : Set V)).connectedComponentMk ⟨y, hyU⟩ :=
      ConnectedComponent.connectedComponentMk_eq_of_adj (by
        simpa [induce_adj] using hadj)
    exact hD (hxD.symm.trans (hmk.trans hyC))
  have : ¬ (G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d) := by
    simp [nAdj haC, nAdj hbC, nAdj hcC, nAdj hdC]
  exact this <| h hp (hxne haC) (hxne hbC) (hxne hcC) (hxne hdC)

lemma OneTough.connected [Nonempty V] (h : OneTough G) : G.Connected := by
  have hle : componentCount G univ ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ componentCount G univ := Nat.succ_le_of_lt (lt_of_not_ge hlt)
    have hbound := h ∅ (by simpa using h2)
    have : componentCount G univ ≤ 0 := by simpa using hbound
    omega
  haveI : Nonempty (G.induce ((univ : Finset V) : Set V)).ConnectedComponent :=
    ⟨(G.induce _).connectedComponentMk ⟨Classical.choice ‹Nonempty V›, mem_univ _⟩⟩
  have hpos : 0 < componentCount G univ := Nat.card_pos
  have heq : componentCount G univ = 1 := le_antisymm hle (Nat.succ_le_of_lt hpos)
  have hsub : Subsingleton (G.induce ((univ : Finset V) : Set V)).ConnectedComponent :=
    (Nat.card_eq_one_iff_unique.1 heq).1
  have heqG : Nat.card G.ConnectedComponent = 1 := by
    rwa [← componentCount_univ]
  haveI : Subsingleton G.ConnectedComponent :=
    (Nat.card_eq_one_iff_unique.1 heqG).1
  refine (connected_iff G).2 ⟨?_, ‹Nonempty V›⟩
  intro u v
  exact ConnectedComponent.exact
    (Subsingleton.elim (G.connectedComponentMk u) (G.connectedComponentMk v))

lemma OneTough.not_ncard_neighborSet_eq_one
    (h : OneTough G) (hord : 3 ≤ Fintype.card V) (v : V) :
    (G.neighborSet v).ncard ≠ 1 := by
  intro hdeg
  obtain ⟨w, hwN⟩ := (Set.ncard_eq_one).1 hdeg
  have hadj : G.Adj v w := by
    have : w ∈ G.neighborSet v := by simp [hwN]
    simpa [mem_neighborSet] using this
  have hvw : v ≠ w := hadj.ne
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (univ \ ({v, w} : Finset V)) := by
    have hpair : ({v, w} : Finset V).card = 2 := card_pair hvw
    have : (univ \ {v, w} : Finset V).Nonempty := by
      rw [sdiff_nonempty]
      intro hsub
      have : Fintype.card V ≤ 2 := by
        simpa [hpair] using card_le_card hsub
      omega
    exact this
  have hzv : z ≠ v := by
    have := (mem_sdiff.1 hz).2
    simp at this
    exact this.1
  have hzw : z ≠ w := by
    have := (mem_sdiff.1 hz).2
    simp at this
    exact this.2
  let S : Finset V := {w}
  let U : Finset V := univ \ S
  have hvU : v ∈ U := by simp [U, S, hvw]
  have hzU : z ∈ U := by simp [U, S, hzw]
  have hnr : ¬ (G.induce (U : Set V)).Reachable ⟨v, hvU⟩ ⟨z, hzU⟩ := by
    rintro ⟨p⟩
    have hne : (⟨v, hvU⟩ : (U : Set V)) ≠ ⟨z, hzU⟩ := by
      intro hEq
      exact hzv ((congrArg Subtype.val hEq).symm)
    have hnn : ¬ p.Nil := Walk.not_nil_of_ne hne
    obtain ⟨y, -, hyadj⟩ := adj_of_mem_walk_support p hnn p.start_mem_support
    have : G.Adj v y.1 := by simpa [induce_adj] using hyadj
    have hyw : y.1 = w := by
      have : y.1 ∈ G.neighborSet v := this
      simpa [hwN] using this
    have : y.1 ∈ U := y.property
    simp [U, S, hyw] at this
  have hnt : Nontrivial (G.induce (U : Set V)).ConnectedComponent :=
    ⟨⟨(G.induce (U : Set V)).connectedComponentMk ⟨v, hvU⟩,
      (G.induce (U : Set V)).connectedComponentMk ⟨z, hzU⟩,
      fun hC => hnr (ConnectedComponent.exact hC)⟩⟩
  have h2 : 2 ≤ componentCount G U := by
    haveI : Nonempty (G.induce (U : Set V)).ConnectedComponent := inferInstance
    haveI : Finite (G.induce (U : Set V)).ConnectedComponent := inferInstance
    have hpos : 0 < componentCount G U := Nat.card_pos
    have hne1 : componentCount G U ≠ 1 := by
      intro h1
      have : Subsingleton (G.induce (U : Set V)).ConnectedComponent :=
        (Nat.card_eq_one_iff_unique.1 h1).1
      exact (not_subsingleton_iff_nontrivial).2 hnt this
    omega
  have hbound := h S (by simpa [U, S] using h2)
  have : componentCount G U ≤ 1 := by simpa [S] using hbound
  omega

lemma OneTough.two_le_ncard_neighborSet
    (h : OneTough G) (hord : 3 ≤ Fintype.card V) (v : V) :
    2 ≤ (G.neighborSet v).ncard := by
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hord)
  have hc := h.connected
  have hne : (G.neighborSet v).ncard ≠ 0 := by
    intro h0
    have hempty : G.neighborSet v = ∅ := (Set.ncard_eq_zero).1 h0
    obtain ⟨w, hvw⟩ := exists_ne v
    have : G.Reachable v w := hc.preconnected v w
    obtain ⟨p⟩ := this
    cases p with
    | nil => exact hvw rfl
    | cons hx _ =>
      have : _ ∈ G.neighborSet v := hx
      simp [hempty] at this
  have hnot1 := OneTough.not_ncard_neighborSet_eq_one (G := G) h hord v
  omega

end Nikoghosyan
