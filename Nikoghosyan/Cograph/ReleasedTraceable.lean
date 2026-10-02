/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ReleasedDistinct
import Nikoghosyan.Prerequisites.TerminalPieces

/-!
# Traceable released endpoints of a Hamiltonian attachment

Manuscript `abs:lem:traceable-release`. Under the same partition hypotheses
as `distinct_release`, both carrier and union are traceable (`p = 1`) and a
vertex released from `F(L)` into `E(J)` is realised as an actual original
spanning `J`-path from that vertex to one old end of a given spanning
`L`-path. The argument follows the paper: the `q = 1` meets-nondominant
calculation, then the critical child via `distinct_release` inside that
child, then the balanced complete-multipartite class argument.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma three_le_card_of_mem_ineligible {U : Finset V} {x : V}
    (hx : x ∈ ineligibleSet G U) (hp : pathCoverNumber G U = 1) :
    3 ≤ U.card := by
  have hxU : x ∈ U := ineligibleSet_subset (G := G) U hx
  have hpos : 1 ≤ U.card := card_pos.2 ⟨x, hxU⟩
  by_contra hlt
  have hle : U.card ≤ 2 := by omega
  have h12 : U.card = 1 ∨ U.card = 2 := by omega
  rcases h12 with h1 | h2
  · obtain ⟨y, hy⟩ := card_eq_one.1 h1
    have hxy : x = y := mem_singleton.1 (hy ▸ hxU)
    subst hxy
    have hxF : x ∈ ineligibleSet G ({x} : Finset V) := by simpa [hy] using hx
    exact (notMem_empty x
      ((ineligibleSet_singleton (G := G) x) ▸ hxF)).elim
  · obtain ⟨p, hpU⟩ := exists_spanning_path_of_pathCoverNumber_eq_one (G := G) hp
    have hE := Eligible_of_support_ends p hpU
    have hneSF : p.start ≠ p.finish := by
      intro heq
      have hnil : p.walk.Nil := (GraphPath.nil_iff_start_eq_finish p).2 heq
      have hsing : p.support = {p.start} :=
        GraphPath.support_eq_singleton_of_nil p hnil
      have : U.card = 1 := by
        calc
          U.card = p.support.card := by rw [hpU]
          _ = ({p.start} : Finset V).card := by rw [hsing]
          _ = 1 := Finset.card_singleton _
      omega
    have hpair : p.support = {p.start, p.finish} :=
      support_eq_pair_of_card_two p hpU (by simpa [hpU] using h2) hneSF
    have hy : x = p.start ∨ x = p.finish := by
      have : x ∈ ({p.start, p.finish} : Finset V) := by
        have : x ∈ p.support := by simpa [hpU] using hxU
        simpa [hpair] using this
      simpa [mem_insert, mem_singleton] using this
    have hEx : Eligible G U x := by
      rcases hy with rfl | rfl
      · simpa [hpU] using hE.1
      · simpa [hpU] using hE.2
    exact (mem_ineligibleSet_iff (G := G)).1 hx |>.2 hEx

lemma exists_oriented_spanning {U : Finset V} {x y : V}
    (hR : SpanningPathCompatible (G := G) U x y) :
    ∃ q : GraphPath G, q.support = U ∧ q.start = x ∧ q.finish = y := by
  obtain ⟨hne, p, hp, hends⟩ := hR
  rcases hends with ⟨hs, hf⟩ | ⟨hs, hf⟩
  · exact ⟨p, hp, hs, hf⟩
  · refine ⟨p.reverse, ?_, ?_, ?_⟩
    · simpa [GraphPath.support_reverse] using hp
    · simpa [GraphPath.reverse] using hf
    · simpa [GraphPath.reverse] using hs

lemma connected_of_pathCoverNumber_eq_one {U : Finset V}
    (hp : pathCoverNumber G U = 1) :
    (G.induce (U : Set V)).Connected := by
  obtain ⟨p, hpU⟩ := exists_spanning_path_of_pathCoverNumber_eq_one (G := G) hp
  exact connected_of_spanning_path p hpU

lemma two_le_card_of_union_cycle {L D : Finset V}
    (c : GraphCycle G) (hc : c.support = D) :
    2 ≤ (L ∪ D).card := by
  have h3 : 3 ≤ D.card := by simpa [hc] using c.three_le_card_support
  have : D ⊆ L ∪ D := subset_union_right
  exact le_trans (by decide : (2 : ℕ) ≤ 3)
    (h3.trans (card_le_card this))

lemma one_le_pathCoverNumber_iff_nonempty (U : Finset V) :
    1 ≤ pathCoverNumber G U ↔ U.Nonempty := by
  constructor
  · intro h
    by_contra hempty
    have : U = ∅ := not_nonempty_iff_eq_empty.1 hempty
    have : pathCoverNumber G U = 0 := by
      simpa [this] using pathCoverNumber_empty (G := G)
    omega
  · exact one_le_pathCoverNumber_of_nonempty (G := G)

/-- The `q = 1` form of the meets-nondominant calculation from
`distinct_release`. The original helper demanded `2 ≤ p(J)` only because
that lemma's ambient pair was a distinct-path pair; the equalities never
used that lower bound. -/
lemma false_of_cycle_meets_nondominant_of_eq_one {L D X Y : Finset V} {h : V}
    (c : GraphCycle G)
    (hLD : Disjoint L D) (hc : c.support = D)
    (hcover : X ∪ Y = L ∪ D)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hdom : Y.card < pathCoverNumber G X)
    (hXcog : Nikoghosyan.IsCograph G X)
    (hp : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hp1 : pathCoverNumber G (L ∪ D) = 1)
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hDY : (D ∩ Y).Nonempty) : False := by
  have hdisjXY := disjoint_of_completeBetween hXY
  have hpX : pathCoverNumber G X =
      pathCoverNumber G (L ∪ D) + Y.card := by
    have := pathCoverNumber_add_card_of_dominant hXne hYne hXY hdom
    have hJ : pathCoverNumber G (X ∪ Y) = pathCoverNumber G (L ∪ D) := by
      rw [hcover]
    omega
  let LX := L ∩ X
  let LY := L ∩ Y
  let DX := D ∩ X
  let DY := D ∩ Y
  have hXsplit : LX ∪ DX = X := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzL | hzD
      · exact (mem_inter.1 hzL).2
      · exact (mem_inter.1 hzD).2
    · intro hzX
      have hzJ : z ∈ L ∪ D := by
        rw [← hcover]
        exact mem_union.2 (Or.inl hzX)
      rcases mem_union.1 hzJ with hzL | hzD
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzD, hzX⟩))
  have hYsplit : LY ∪ DY = Y := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzL | hzD
      · exact (mem_inter.1 hzL).2
      · exact (mem_inter.1 hzD).2
    · intro hzY
      have hzJ : z ∈ L ∪ D := by
        rw [← hcover]
        exact mem_union.2 (Or.inr hzY)
      rcases mem_union.1 hzJ with hzL | hzD
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzY⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzD, hzY⟩))
  have hdisjLXDX : Disjoint LX DX :=
    disjoint_of_subset_left (inter_subset_left (s₂ := X))
      (disjoint_of_subset_right (inter_subset_left (s₂ := X)) hLD)
  have hdisjLYDY : Disjoint LY DY :=
    disjoint_of_subset_left (inter_subset_left (s₂ := Y))
      (disjoint_of_subset_right (inter_subset_left (s₂ := Y)) hLD)
  have hLXsdiff : LX = L \ LY := by
    ext z
    constructor
    · intro hz
      exact mem_sdiff.2 ⟨(mem_inter.1 hz).1, fun hzLY =>
        Finset.disjoint_left.1 hdisjXY (mem_inter.1 hz).2 (mem_inter.1 hzLY).2⟩
    · intro hz
      have hzL : z ∈ L := (mem_sdiff.1 hz).1
      have hznotLY : z ∉ LY := (mem_sdiff.1 hz).2
      have hzX : z ∈ X := by
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inl hzL)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact hzX
        · exact (hznotLY (mem_inter.2 ⟨hzL, hzY⟩)).elim
      exact mem_inter.2 ⟨hzL, hzX⟩
  have hDXsdiff : DX = D \ DY := by
    ext z
    constructor
    · intro hz
      exact mem_sdiff.2 ⟨(mem_inter.1 hz).1, fun hzDY =>
        Finset.disjoint_left.1 hdisjXY (mem_inter.1 hz).2 (mem_inter.1 hzDY).2⟩
    · intro hz
      have hzD : z ∈ D := (mem_sdiff.1 hz).1
      have hznotDY : z ∉ DY := (mem_sdiff.1 hz).2
      have hzX : z ∈ X := by
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inr hzD)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact hzX
        · exact (hznotDY (mem_inter.2 ⟨hzD, hzY⟩)).elim
      exact mem_inter.2 ⟨hzD, hzX⟩
  have hpXle :=
    pathCoverNumber_union_le_of_disjoint (G := G) (A := LX) (B := DX) hdisjLXDX
  have hpXle' : pathCoverNumber G X ≤ pathCoverNumber G LX + pathCoverNumber G DX := by
    simpa [hXsplit] using hpXle
  have hLYsub : LY ⊆ L := inter_subset_left
  have hpLX : pathCoverNumber G LX ≤ pathCoverNumber G L + LY.card := by
    simpa [hLXsdiff] using pathCoverNumber_sdiff_le (G := G) L LY hLYsub
  have hDYsub : DY ⊆ D := inter_subset_left
  have hpDX : pathCoverNumber G DX ≤ DY.card := by
    have hdel :=
      pathCoverNumber_sdiff_le_card_of_cycle (U := D) (A := DY) c hc hDYsub hDY
    simpa [hDXsdiff] using hdel
  have hYcard : Y.card = LY.card + DY.card := by
    have := card_union_of_disjoint hdisjLYDY
    simpa [hYsplit] using this
  have hpLXeq : pathCoverNumber G LX = pathCoverNumber G L + LY.card := by
    omega
  have hEjoin := eligibleSet_complete_join_dominant hXne hYne hXY hdom
  have hEJ : eligibleSet G (L ∪ D) = eligibleSet G X := by
    simpa [hcover] using hEjoin
  have hhX : h ∈ X := (eligibleSet_subset (G := G) X) (by
    have : h ∈ eligibleSet G X := by simpa [hEJ] using hhE
    exact this)
  have hhL : h ∈ L := (ineligibleSet_subset (G := G) L) hhF
  have hhLX : h ∈ LX := mem_inter.2 ⟨hhL, hhX⟩
  obtain ⟨pcLX, hpcLX⟩ := exists_min_pathCover (G := G) LX
  obtain ⟨pcDX, hpcDX⟩ := exists_min_pathCover (G := G) DX
  let pcX := PathCover.unionDisjoint hdisjLXDX pcLX pcDX
  have hminX : pcX.card = pathCoverNumber G X := by
    have hsum := PathCover.unionDisjoint_card (G := G) hdisjLXDX pcLX pcDX
    have hpcX : pcX.card = pcLX.card + pcDX.card := hsum
    have heq : pathCoverNumber G LX + pathCoverNumber G DX = pathCoverNumber G X := by
      have hle := hpXle'
      omega
    omega
  have hErest :=
    eligibleSet_unionDisjoint_left hdisjLXDX (by simpa [hXsplit] using hXcog)
      pcLX pcDX (by simpa [hXsplit] using hminX)
  have hhELX : h ∈ eligibleSet G LX := by
    have hhEX : h ∈ eligibleSet G X := by simpa [hEJ] using hhE
    have hErest' : eligibleSet G LX = eligibleSet G X ∩ LX := by
      simpa [hXsplit] using hErest
    have : h ∈ eligibleSet G X ∩ LX := mem_inter.2 ⟨hhEX, hhLX⟩
    simpa [hErest'] using this
  by_cases hLYne : LY.Nonempty
  · have hLXne : LX.Nonempty := ⟨h, hhLX⟩
    have hLXY : G.IsCompleteBetween (LX : Set V) (LY : Set V) :=
      isCompleteBetween_mono hXY inter_subset_right inter_subset_right
    have hLXdom : LY.card < pathCoverNumber G LX := by omega
    have hEL := eligibleSet_complete_join_dominant hLXne hLYne hLXY hLXdom
    have hLsplit : LX ∪ LY = L := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with hzX | hzY
        · exact (mem_inter.1 hzX).1
        · exact (mem_inter.1 hzY).1
      · intro hzL
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inl hzL)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
        · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzL, hzY⟩))
    have : h ∈ eligibleSet G L := by
      have : eligibleSet G L = eligibleSet G LX := by simpa [hLsplit] using hEL
      simpa [this] using hhELX
    exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2
      ((mem_eligibleSet_iff (G := G)).1 this).2
  · have hLYempty : LY = ∅ := not_nonempty_iff_eq_empty.1 hLYne
    have hLeq : LX = L := by
      have : L ∩ Y = ∅ := hLYempty
      ext z
      constructor
      · intro hz
        exact (mem_inter.1 hz).1
      · intro hzL
        refine mem_inter.2 ⟨hzL, ?_⟩
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inl hzL)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact hzX
        · have hzLY : z ∈ LY := mem_inter.2 ⟨hzL, hzY⟩
          have : z ∈ (∅ : Finset V) := by simpa [hLYempty] using hzLY
          exact (notMem_empty z this).elim
    have : h ∈ eligibleSet G L := by simpa [hLeq] using hhELX
    exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2
      ((mem_eligibleSet_iff (G := G)).1 this).2

lemma connectedComponent_map_induceIncl_left {A B : Finset V} {a : V}
    (ha : a ∈ A) :
    ((G.induce (A : Set V)).connectedComponentMk ⟨a, ha⟩).map
      (induceIncl G (subset_union_left (s₁ := A) (s₂ := B))) =
      (G.induce ((A ∪ B : Finset V) : Set V)).connectedComponentMk
        ⟨a, mem_union.2 (Or.inl ha)⟩ :=
  rfl

lemma connectedComponent_map_induceIncl_right {A B : Finset V} {b : V}
    (hb : b ∈ B) :
    ((G.induce (B : Set V)).connectedComponentMk ⟨b, hb⟩).map
      (induceIncl G (subset_union_right (s₁ := A) (s₂ := B))) =
      (G.induce ((A ∪ B : Finset V) : Set V)).connectedComponentMk
        ⟨b, mem_union.2 (Or.inr hb)⟩ :=
  rfl

lemma componentCount_union_le_sub_one_of_adj {A B : Finset V}
    (hdisj : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) (hadj : G.Adj a b) :
    componentCount G (A ∪ B) ≤ componentCount G A + componentCount G B - 1 := by
  have hle := componentCount_union_le (G := G) A B
  let f : (G.induce (A : Set V)).ConnectedComponent ⊕
        (G.induce (B : Set V)).ConnectedComponent →
      (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent
    | .inl C => C.map (induceIncl G (subset_union_left (s₁ := A)))
    | .inr C => C.map (induceIncl G (subset_union_right (s₁ := A)))
  have hf : Function.Surjective f := by
    intro C
    refine C.ind fun x => ?_
    rcases mem_union.mp x.property with hA | hB
    · refine ⟨.inl ((G.induce (A : Set V)).connectedComponentMk ⟨x.val, hA⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
    · refine ⟨.inr ((G.induce (B : Set V)).connectedComponentMk ⟨x.val, hB⟩), ?_⟩
      exact ConnectedComponent.sound Reachable.rfl
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    let hCa := (G.induce (A : Set V)).connectedComponentMk ⟨a, ha⟩
    let hCb := (G.induce (B : Set V)).connectedComponentMk ⟨b, hb⟩
    have hmap : f (.inl hCa) = f (.inr hCb) := by
      change hCa.map (induceIncl G (subset_union_left (s₁ := A))) =
        hCb.map (induceIncl G (subset_union_right (s₁ := A)))
      rw [connectedComponent_map_induceIncl_left ha,
        connectedComponent_map_induceIncl_right hb]
      exact ConnectedComponent.sound
        (Adj.reachable (by simpa [induce_adj] using hadj))
    have hsum : (Sum.inl hCa :
        (G.induce (A : Set V)).ConnectedComponent ⊕
          (G.induce (B : Set V)).ConnectedComponent) =
      Sum.inr hCb := hinj hmap
    exact Sum.inl_ne_inr hsum
  haveI : Fintype (A : Set V) := inferInstance
  haveI : Fintype (B : Set V) := inferInstance
  haveI : Fintype ((A ∪ B : Finset V) : Set V) := inferInstance
  haveI : DecidableRel (G.induce (A : Set V)).Adj := inferInstance
  haveI : DecidableRel (G.induce (B : Set V)).Adj := inferInstance
  haveI : Fintype (G.induce (A : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce (B : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  have hlt :
      Fintype.card (G.induce ((A ∪ B : Finset V) : Set V)).ConnectedComponent <
        Fintype.card
          ((G.induce (A : Set V)).ConnectedComponent ⊕
            (G.induce (B : Set V)).ConnectedComponent) :=
    Fintype.card_lt_of_surjective_not_injective f hf hnotinj
  have hposA : 0 < componentCount G A := by
    simpa [componentCount, Nat.card_eq_fintype_card] using
      Fintype.card_pos_iff.2
        ⟨(G.induce (A : Set V)).connectedComponentMk ⟨a, ha⟩⟩
  have hposB : 0 < componentCount G B := by
    simpa [componentCount, Nat.card_eq_fintype_card] using
      Fintype.card_pos_iff.2
        ⟨(G.induce (B : Set V)).connectedComponentMk ⟨b, hb⟩⟩
  have hsum :
      Fintype.card
        ((G.induce (A : Set V)).ConnectedComponent ⊕
          (G.induce (B : Set V)).ConnectedComponent) =
        componentCount G A + componentCount G B := by
    simp [componentCount, Nat.card_eq_fintype_card, Fintype.card_sum]
  have hlt' :
      componentCount G (A ∪ B) <
        Fintype.card
          ((G.induce (A : Set V)).ConnectedComponent ⊕
            (G.induce (B : Set V)).ConnectedComponent) := by
    simpa [componentCount, Nat.card_eq_fintype_card] using hlt
  have hlt'' :
      componentCount G (A ∪ B) < componentCount G A + componentCount G B := by
    simpa [hsum] using hlt'
  have hpos : 1 ≤ componentCount G A + componentCount G B := by omega
  omega

lemma no_cross_of_componentCount_add {A B : Finset V}
    (hdisj : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (heq : componentCount G (A ∪ B) = componentCount G A + componentCount G B) :
    ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
  intro a ha b hb hadj
  have hle' :=
    componentCount_union_le_sub_one_of_adj hdisj hAne hBne ha hb hadj
  have hpos : 0 < componentCount G A := by
    simpa [componentCount, Nat.card_eq_fintype_card] using
      Fintype.card_pos_iff.2
        ⟨(G.induce (A : Set V)).connectedComponentMk ⟨a, ha⟩⟩
  omega

/-- Critical-join case of traceable release: `X` is the unique dominant child. -/
lemma traceable_release_of_critical {L D X Y : Finset V} {h u v : V}
    (c : GraphCycle G)
    (P : GraphPath G)
    (hLD : Disjoint L D) (hc : c.support = D)
    (hcover : X ∪ Y = L ∪ D)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hcrit : pathCoverNumber G X = Y.card + 1)
    (hJcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hLcog : Nikoghosyan.IsCograph G L)
    (hXcog : Nikoghosyan.IsCograph G X)
    (hp : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hpL : pathCoverNumber G L = 1)
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hP : P.support = L) (hs : P.start = u) (hf : P.finish = v) :
    (∃ Q : GraphPath G, Q.support = L ∪ D ∧ Q.start = h ∧ Q.finish = u) ∨
      (∃ Q : GraphPath G, Q.support = L ∪ D ∧ Q.start = h ∧ Q.finish = v) := by
  have hpJ : pathCoverNumber G (L ∪ D) = 1 := by omega
  have hdom : Y.card < pathCoverNumber G X := by omega
  have hdisjXY := disjoint_of_completeBetween hXY
  by_cases hDY : (D ∩ Y).Nonempty
  · exact (false_of_cycle_meets_nondominant_of_eq_one c hLD hc hcover
      hXne hYne hXY hdom hXcog hp hpJ hhF hhE hDY).elim
  · have hDYempty : D ∩ Y = ∅ := not_nonempty_iff_eq_empty.1 hDY
    have hDX : D ⊆ X := by
      intro z hz
      have hzJ : z ∈ X ∪ Y := by
        rw [hcover]
        exact mem_union.2 (Or.inr hz)
      rcases mem_union.1 hzJ with hzX | hzY
      · exact hzX
      · have : z ∈ D ∩ Y := mem_inter.2 ⟨hz, hzY⟩
        exact (notMem_empty z (by simpa [hDYempty] using this)).elim
    obtain ⟨hXeq, hYsub, hdisjLXY⟩ :=
      union_inter_eq_of_cycle_subset_left hcover hLD hdisjXY hDX
    let LX := L ∩ X
    have hXeq' : LX ∪ D = X := by
      simpa [LX] using hXeq
    have hdisjLXD : Disjoint LX D :=
      disjoint_of_subset_left inter_subset_left hLD
    have hLXcan : Nikoghosyan.IsCograph G LX :=
      isCograph_canonical_subset hLcog inter_subset_left
    have hpD : pathCoverNumber G D = 1 := pathCoverNumber_eq_one_of_cycle c hc
    have hpXadd : pathCoverNumber G X = 1 + Y.card := by
      have hadd := pathCoverNumber_add_card_of_dominant hXne hYne hXY hdom
      have hJeq : pathCoverNumber G (X ∪ Y) = 1 := by simpa [hcover] using hpJ
      omega
    have hpXle : pathCoverNumber G X ≤ pathCoverNumber G LX + 1 := by
      have hle : pathCoverNumber G (LX ∪ D) ≤
          pathCoverNumber G LX + pathCoverNumber G D :=
        pathCoverNumber_union_le_of_disjoint hdisjLXD
      have hle' : pathCoverNumber G (LX ∪ D) ≤ pathCoverNumber G LX + 1 := by
        simpa [hpD] using hle
      simpa [hXeq'] using hle'
    have hpLXge : Y.card ≤ pathCoverNumber G LX := by omega
    have hpLXle : pathCoverNumber G LX ≤ Y.card + 1 := by
      have hLsplit : LX ∪ Y = L := by
        ext z
        constructor
        · intro hz
          rcases mem_union.1 hz with hzX | hzY
          · exact (mem_inter.1 hzX).1
          · exact hYsub hzY
        · intro hzL
          have hzJ : z ∈ X ∪ Y := by
            rw [hcover]
            exact mem_union.2 (Or.inl hzL)
          rcases mem_union.1 hzJ with hzX | hzY
          · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
          · exact mem_union.2 (Or.inr hzY)
      have hLXY : G.IsCompleteBetween (LX : Set V) (Y : Set V) :=
        isCompleteBetween_mono (A := X) (A' := LX) (B := Y) (B' := Y)
          hXY inter_subset_right (fun _ hy => hy)
      have hge := pathCoverNumber_complete_join_ge_sub (A := LX) (B := Y) hLXY
      have : pathCoverNumber G (LX ∪ Y) = 1 := by simpa [hLsplit] using hpL
      omega
    have hpLXeq : pathCoverNumber G LX = Y.card + 1 := by
      by_contra hne
      have hpLXr : pathCoverNumber G LX = Y.card := by omega
      have hLXne : LX.Nonempty := by
        by_contra hempty
        have hLXempty : LX = ∅ := not_nonempty_iff_eq_empty.1 hempty
        have hpempty : pathCoverNumber G (∅ : Finset V) = 0 :=
          pathCoverNumber_empty (G := G)
        have hY0 : Y.card = 0 := by
          have this := hpLXr
          rw [hLXempty, hpempty] at this
          exact this.symm
        exact hYne.ne_empty (card_eq_zero.1 hY0)
      have hLsplit : LX ∪ Y = L := by
        ext z
        constructor
        · intro hz
          rcases mem_union.1 hz with hzX | hzY
          · exact (mem_inter.1 hzX).1
          · exact hYsub hzY
        · intro hzL
          have hzJ : z ∈ X ∪ Y := by
            rw [hcover]
            exact mem_union.2 (Or.inl hzL)
          rcases mem_union.1 hzJ with hzX | hzY
          · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
          · exact mem_union.2 (Or.inr hzY)
      have hLXY : G.IsCompleteBetween (LX : Set V) (Y : Set V) :=
        isCompleteBetween_mono (A := X) (A' := LX) (B := Y) (B' := Y)
          hXY inter_subset_right (fun _ hy => hy)
      have hpYle : pathCoverNumber G Y ≤ LX.card := by
        have hpYcard := pathCoverNumber_le_card (G := G) Y
        have hpLXcard := pathCoverNumber_le_card (G := G) LX
        have : Y.card ≤ LX.card := by
          have : pathCoverNumber G LX ≤ LX.card := hpLXcard
          omega
        exact hpYcard.trans this
      have hEL :=
        eligibleSet_complete_join_balanced hLXne hYne hLXY
          (by omega : pathCoverNumber G LX ≤ Y.card) hpYle
      have : h ∈ eligibleSet G L := by
        have hhL : h ∈ L := ineligibleSet_subset (G := G) L hhF
        have : eligibleSet G L = L := by simpa [hLsplit] using hEL
        simpa [this] using hhL
      exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2
        ((mem_eligibleSet_iff (G := G)).1 this).2
    have hLXne : LX.Nonempty :=
      (one_le_pathCoverNumber_iff_nonempty (G := G) LX).1 (by omega)
    have hLsplit : LX ∪ Y = L := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with hzX | hzY
        · exact (mem_inter.1 hzX).1
        · exact hYsub hzY
      · intro hzL
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inl hzL)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
        · exact mem_union.2 (Or.inr hzY)
    have hLXY : G.IsCompleteBetween (LX : Set V) (Y : Set V) :=
      isCompleteBetween_mono (A := X) (A' := LX) (B := Y) (B' := Y)
        hXY inter_subset_right (fun _ hy => hy)
    have hune : u ≠ v := by
      intro heq
      have hnil : P.walk.Nil :=
        (GraphPath.nil_iff_start_eq_finish P).2 (by simp [hs, hf, heq])
      have hsing : P.support = {P.start} :=
        GraphPath.support_eq_singleton_of_nil P hnil
      have hLcard : L.card = 1 := by
        calc
          L.card = P.support.card := by rw [hP]
          _ = ({P.start} : Finset V).card := by rw [hsing]
          _ = 1 := by rw [hs, Finset.card_singleton]
      have : 3 ≤ L.card := three_le_card_of_mem_ineligible hhF hpL
      omega
    have hRL : SpanningPathCompatible (G := G) L u v :=
      ⟨hune, P, hP, Or.inl ⟨hs, hf⟩⟩
    have hDuv : DistinctPathCompatible (G := G) LX u v :=
      (SpanningPathCompatible_critical_iff hLXne hYne hLXY hpLXeq).1
        (by simpa [hLsplit] using hRL)
    have hFjoin := ineligibleSet_complete_join_critical hLXne hYne hLXY hpLXeq
    have hEjoinL := eligibleSet_complete_join_critical hLXne hYne hLXY hpLXeq
    have hhFLX : h ∈ ineligibleSet G LX := by
      have hhL : h ∈ L := ineligibleSet_subset (G := G) L hhF
      have : h ∈ Y ∪ ineligibleSet G LX := by
        have : ineligibleSet G L = Y ∪ ineligibleSet G LX := by
          simpa [hLsplit] using hFjoin
        simpa [this] using hhF
      rcases mem_union.1 this with hhY | hhX
      · have hEJ := eligibleSet_complete_join_critical hXne hYne hXY hcrit
        have hhX' : h ∈ X := by
          have : eligibleSet G (L ∪ D) = eligibleSet G X := by
            simpa [hcover] using hEJ
          exact eligibleSet_subset (G := G) X (by simpa [this] using hhE)
        exact (Finset.disjoint_left.1 hdisjXY hhX' hhY).elim
      · exact hhX
    have hhEX : h ∈ eligibleSet G X := by
      have hEJ := eligibleSet_complete_join_critical hXne hYne hXY hcrit
      have : eligibleSet G (L ∪ D) = eligibleSet G X := by
        simpa [hcover] using hEJ
      simpa [this] using hhE
    have hpLXpX : pathCoverNumber G LX = pathCoverNumber G (LX ∪ D) := by
      rw [hXeq']; omega
    have hXcan' : Nikoghosyan.IsCograph G (LX ∪ D) := by
      rw [hXeq']; exact hXcog
    have hhEX' : h ∈ eligibleSet G (LX ∪ D) := by
      rw [hXeq']; exact hhEX
    have hrel :=
      distinct_release (L := LX) (D := D) (h := h) (u := u) (v := v)
        c hdisjLXD hc hXcan' hLXcan hpLXpX hhFLX hhEX' hDuv
    have hiff_hu :=
      SpanningPathCompatible_critical_iff (x := h) (y := u) hXne hYne hXY hcrit
    have hiff_hv :=
      SpanningPathCompatible_critical_iff (x := h) (y := v) hXne hYne hXY hcrit
    rcases hrel with hhu | hhv
    · have hhuX : DistinctPathCompatible (G := G) X h u := by
        simpa [hXeq'] using hhu
      have hR : SpanningPathCompatible (G := G) (X ∪ Y) h u := hiff_hu.2 hhuX
      obtain ⟨Q, hQ, hsQ, hfQ⟩ := exists_oriented_spanning hR
      refine Or.inl ⟨Q, ?_, hsQ, hfQ⟩
      simpa [hcover] using hQ
    · have hhvX : DistinctPathCompatible (G := G) X h v := by
        simpa [hXeq'] using hhv
      have hR : SpanningPathCompatible (G := G) (X ∪ Y) h v := hiff_hv.2 hhvX
      obtain ⟨Q, hQ, hsQ, hfQ⟩ := exists_oriented_spanning hR
      refine Or.inr ⟨Q, ?_, hsQ, hfQ⟩
      simpa [hcover] using hQ


lemma mem_union_sdiff_eq {L D P : Finset V} :
    (L ∪ D) \ P = (L \ P) ∪ (D \ P) := by
  ext z
  simp only [mem_sdiff, mem_union]
  tauto

lemma ineligibleSet_eq_empty_of_eligibleSet_eq {U : Finset V}
    (h : eligibleSet G U = U) : ineligibleSet G U = ∅ := by
  ext z
  constructor
  · intro hz
    have hzU : z ∈ U := ineligibleSet_subset (G := G) U hz
    have hzE : z ∈ eligibleSet G U := by simpa [h] using hzU
    exact (disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) U)
      hzE hz).elim
  · intro hz
    exact (notMem_empty z hz).elim

lemma card_supportUnion_eq_sum {l : List (GraphPath G)}
    (h : l.Pairwise fun p q => Disjoint p.support q.support) :
    (supportUnion l).card = (l.map (fun p => p.support.card)).sum := by
  induction l with
  | nil => simp [supportUnion]
  | cons p ps ih =>
    have hpw := List.pairwise_cons.1 h
    have hfold : supportUnion (p :: ps) = p.support ∪ supportUnion ps := by
      simp [supportUnion]
    have hd : Disjoint p.support (supportUnion ps) := by
      rw [disjoint_iff_inter_eq_empty]
      ext x
      constructor
      · intro hx
        obtain ⟨q, hq, hxq⟩ :=
          (mem_supportUnion_iff (l := ps) (x := x)).1 (mem_inter.1 hx).2
        exact (Finset.disjoint_left.1 (hpw.1 q hq) (mem_inter.1 hx).1 hxq).elim
      · intro hx
        exact (notMem_empty x hx).elim
    rw [hfold, card_union_of_disjoint hd, ih hpw.2, List.map_cons]
    simp [List.sum_cons]

lemma eligibleSet_eq_of_pathCoverNumber_eq_card {U : Finset V}
    (h : pathCoverNumber G U = U.card) : eligibleSet G U = U := by
  ext x
  constructor
  · intro hx
    exact eligibleSet_subset (G := G) U hx
  · intro hxU
    obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
    have hlen : pc.card = U.card := by simpa [h] using hpc
    have hnodStarts : (pc.paths.map (fun q => q.start)).Nodup := by
      rw [List.nodup_map_iff_inj_on pc.nodup_paths]
      intro q hq r hr hqr
      by_contra hne
      exact Finset.disjoint_left.1
        (PathCover.pairwise_disjoint_of_mem pc.disjoint hq hr hne)
        q.start_mem_support (by simpa [hqr] using r.start_mem_support)
    let starts := (pc.paths.map (fun q => q.start)).toFinset
    have hcard_starts : starts.card = pc.card := by
      simpa [starts, PathCover.card, List.toFinset_card_of_nodup hnodStarts]
    have hsub : starts ⊆ U := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hz)
      exact pc.support_subset hq q.start_mem_support
    have heq : starts = U :=
      eq_of_subset_of_card_le hsub (by omega)
    have hxS : x ∈ starts := by simpa [heq] using hxU
    obtain ⟨p, hp, hs⟩ := List.mem_map.1 (List.mem_toFinset.1 hxS)
    exact (mem_eligibleSet_iff (G := G)).2
      ⟨hxU, ⟨pc, (by simpa [h] using hpc), p, hp, Or.inl hs.symm⟩⟩

lemma not_IsEndpoint_of_mem_ineligible {U : Finset V} {x : V}
    (pc : PathCover G U) (hmin : pc.card = pathCoverNumber G U)
    (hx : x ∈ ineligibleSet G U) : ¬ pc.IsEndpoint x := by
  intro h
  obtain ⟨p, hp, hend⟩ := h
  have hE : Eligible G U x := ⟨pc, hmin, p, hp, hend⟩
  exact (mem_ineligibleSet_iff (G := G)).1 hx |>.2 hE

lemma exists_pathCover_sdiff_ineligible_keepEndpoint
    {U C : Finset V} {x : V}
    (hU : Nikoghosyan.IsCograph G U)
    (pc : PathCover G U) (hmin : pc.card = pathCoverNumber G U)
    (hC : C ⊆ ineligibleSet G U)
    (hx : pc.IsEndpoint x) (hxC : x ∉ C) :
    ∃ pc' : PathCover G (U \ C),
      pc'.card = pc.card + C.card ∧ pc'.IsEndpoint x := by
  induction C using Finset.induction generalizing U pc with
  | empty =>
    refine ⟨pc.cast (by simp), ?_, ?_⟩
    · simp [PathCover.cast_card]
    · exact (PathCover.cast_IsEndpoint pc (by simp)).2 hx
  | insert f C hfC ih =>
    have hf : f ∈ ineligibleSet G U := hC (mem_insert_self f C)
    have hfU : f ∈ U := ineligibleSet_subset (G := G) U hf
    have hCsub : C ⊆ ineligibleSet G U := fun z hz =>
      hC (mem_insert_of_mem hz)
    have hnotEnd : ¬ pc.IsEndpoint f :=
      not_IsEndpoint_of_mem_ineligible pc hmin hf
    have hinternal : ∀ p ∈ pc.paths, f ≠ p.start ∧ f ≠ p.finish := by
      intro p hp
      constructor
      · intro hfs
        exact hnotEnd ⟨p, hp, Or.inl hfs⟩
      · intro hff
        exact hnotEnd ⟨p, hp, Or.inr hff⟩
    have hcard1 : (pc.deleteVertex f).card = pc.card + 1 :=
      PathCover.card_deleteVertex_eq_add_one_of_internal pc hfU hinternal
    have hdel := ineligible_deletion_erase_of_canonical hU hf
    have hmin1 : (pc.deleteVertex f).card =
        pathCoverNumber G (U.erase f) := by
      rw [hcard1, hmin, hdel.1]
    have hCnew : C ⊆ ineligibleSet G (U.erase f) := by
      intro z hz
      have hzF : z ∈ ineligibleSet G U := hCsub hz
      have hzne : z ≠ f := fun h => hfC (h ▸ hz)
      rw [hdel.2.2]
      exact mem_erase.2 ⟨hzne, hzF⟩
    have hxne : x ≠ f := fun h => hxC (by simp [h])
    have hx' : (pc.deleteVertex f).IsEndpoint x :=
      PathCover.IsEndpoint_deleteVertex pc hx hxne
    have hxS' : x ∉ C := fun h => hxC (mem_insert_of_mem h)
    have hU' : Nikoghosyan.IsCograph G (U.erase f) :=
      isCograph_canonical_subset hU (erase_subset f U)
    obtain ⟨pc1, hcard1', hend1⟩ :=
      ih (U := U.erase f) hU' (pc.deleteVertex f) hmin1 hCnew hx' hxS'
    have hEq : U.erase f \ C = U \ insert f C := by
      rw [sdiff_insert, erase_sdiff_distrib, erase_eq_of_notMem hfC]
    refine ⟨pc1.cast hEq, ?_, ?_⟩
    · have hcard := card_insert_of_notMem (s := C) hfC
      rw [PathCover.cast_card, hcard1', hcard1]
      omega
    · exact (PathCover.cast_IsEndpoint pc1 hEq).2 hend1

lemma exists_edge_from_meet_to_miss {D : Finset V} (p : GraphPath G)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxD : x ∈ D) (hyD : y ∉ D) :
    ∃ a b, a ∈ p.support ∧ b ∈ p.support ∧ a ∈ D ∧ b ∉ D ∧ G.Adj a b := by
  have hconn : (G.induce (p.support : Set V)).Connected :=
    connected_of_spanning_path p rfl
  have hreach :
      (G.induce (p.support : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
    hconn ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨wReach⟩ := hreach
  have : ∀ {u v : (p.support : Set V)}
      (q : (G.induce (p.support : Set V)).Walk u v),
      u.val ∈ D → v.val ∉ D →
        ∃ a b, a ∈ p.support ∧ b ∈ p.support ∧ a ∈ D ∧ b ∉ D ∧ G.Adj a b := by
    intro u v q
    induction q with
    | nil =>
      intro huD hvD
      exact (hvD huD).elim
    | cons hadj q ih =>
      intro huD hvD
      rename_i u0 v0 w0
      have hadjG : G.Adj u0.val v0.val := by simpa [induce_adj] using hadj
      by_cases hv0D : v0.val ∈ D
      · exact ih hv0D hvD
      · exact ⟨u0.val, v0.val, u0.property, v0.property, huD, hv0D, hadjG⟩
  exact this wReach hxD hyD

lemma path_support_subset_of_component {U D : Finset V}
    (hnocross : ∀ a ∈ D, ∀ b ∈ U \ D, ¬ G.Adj a b)
    (p : GraphPath G) (hsupp : p.support ⊆ U)
    {x : V} (hxD : x ∈ D) (hxp : x ∈ p.support) :
    p.support ⊆ D := by
  intro z hz
  by_contra hzD
  have hzU : z ∈ U := hsupp hz
  have hzUD : z ∈ U \ D := mem_sdiff.2 ⟨hzU, hzD⟩
  obtain ⟨a, b, haP, hbP, haD, hbD, hadj⟩ :=
    exists_edge_from_meet_to_miss (D := D) p hxp hz hxD hzD
  have hbU : b ∈ U \ D := mem_sdiff.2 ⟨hsupp hbP, hbD⟩
  exact hnocross a haD b hbU hadj

lemma path_support_eq_of_component {U D : Finset V}
    (pc : PathCover G U)
    (hcard : pc.card = componentCount G U)
    (hD : D ⊆ U) (hDne : D.Nonempty)
    (hconn : (G.induce (D : Set V)).Connected)
    (hnocross : ∀ a ∈ D, ∀ b ∈ U \ D, ¬ G.Adj a b)
    {p : GraphPath G} (hp : p ∈ pc.paths) {x : V}
    (hxD : x ∈ D) (hxp : x ∈ p.support) :
    p.support = D := by
  have hsub : p.support ⊆ D :=
    path_support_subset_of_component (U := U) (D := D) hnocross p
      (pc.support_subset hp) hxD hxp
  refine Finset.Subset.antisymm hsub ?_
  intro y hyD
  by_contra hyP
  obtain ⟨q, hq, hyq⟩ := (pc.mem_iff y).1 (hD hyD)
  have hne : p ≠ q := fun heq => hyP (heq ▸ hyq)
  have hDcomp : componentCount G D = 1 :=
    componentCount_eq_one_of_connected hDne hconn
  have hcoverUD : D ∪ (U \ D) = U := union_sdiff_of_subset hD
  have hadd : componentCount G U =
      componentCount G D + componentCount G (U \ D) := by
    simpa [hcoverUD] using
      componentCount_union_of_no_cross (A := D) (B := U \ D)
        disjoint_sdiff (fun a ha b hb => hnocross a ha b hb)
  by_cases hW : (U \ D).Nonempty
  · let l := pc.paths.filter fun r => decide (∀ z ∈ r.support, z ∉ D)
    have hdisj : l.Pairwise fun r s => Disjoint r.support s.support :=
      List.Pairwise.filter _ pc.disjoint
    have hmem : ∀ z, z ∈ U \ D ↔ ∃ r ∈ l, z ∈ r.support := by
      intro z
      constructor
      · intro hz
        have hzU : z ∈ U := (mem_sdiff.1 hz).1
        obtain ⟨r, hr, hzr⟩ := (pc.mem_iff z).1 hzU
        have hzD : z ∉ D := (mem_sdiff.1 hz).2
        have hnotD : ∀ t ∈ r.support, t ∉ D := by
          intro t ht htD
          have hrD : r.support ⊆ D :=
            path_support_subset_of_component (U := U) (D := D) hnocross r
              (pc.support_subset hr) htD ht
          exact hzD (hrD hzr)
        exact ⟨r, List.mem_filter.2 ⟨hr, decide_eq_true hnotD⟩, hzr⟩
      · intro ⟨r, hr, hzr⟩
        have hr' := List.mem_filter.1 hr
        have hnotD : ∀ t ∈ r.support, t ∉ D := of_decide_eq_true hr'.2
        exact mem_sdiff.2 ⟨pc.support_subset hr'.1 hzr, hnotD z hzr⟩
    let pcW : PathCover G (U \ D) := ofPathList l hdisj hmem
    have hleW := pathCoverNumber_le (G := G) pcW
    have hcW := componentCount_le_pathCoverNumber (G := G) (U \ D)
    have hpN : ¬ ∀ z ∈ p.support, z ∉ D := fun hpN => hpN x hxp hxD
    have hqN : ¬ ∀ z ∈ q.support, z ∉ D := fun hqN => hqN y hyq hyD
    have hp' : p ∈ pc.paths.filter fun r =>
        !decide (∀ z ∈ r.support, z ∉ D) :=
      List.mem_filter.2 ⟨hp, by simp [hpN]⟩
    have hq' : q ∈ pc.paths.filter fun r =>
        !decide (∀ z ∈ r.support, z ∉ D) :=
      List.mem_filter.2 ⟨hq, by simp [hqN]⟩
    have hdrop :
        2 ≤ (pc.paths.filter fun r =>
          !decide (∀ z ∈ r.support, z ∉ D)).length := by
      have : ({p, q} : Finset (GraphPath G)).card = 2 := by
        rw [card_insert_of_notMem (by simp [hne])]
        simp
      have hsub' : ({p, q} : Finset (GraphPath G)) ⊆
          (pc.paths.filter fun r =>
            !decide (∀ z ∈ r.support, z ∉ D)).toFinset := by
        intro r hr
        rcases mem_insert.1 hr with rfl | hr'
        · exact List.mem_toFinset.2 hp'
        · simpa [mem_singleton.1 hr'] using List.mem_toFinset.2 hq'
      have hnod := List.Nodup.filter
        (fun r => !decide (∀ z ∈ r.support, z ∉ D)) pc.nodup_paths
      have hcard' := List.toFinset_card_of_nodup hnod
      have hle := card_le_card hsub'
      omega
    have hadd :=
      length_filter_add_not (fun r : GraphPath G =>
        decide (∀ z ∈ r.support, z ∉ D)) pc.paths
    have hl : l.length =
        (pc.paths.filter fun r =>
          decide (∀ z ∈ r.support, z ∉ D)).length := rfl
    have hlenW : pcW.card + 2 ≤ pc.card := by
      have hpcW : pcW.card = l.length := ofPathList_card l hdisj hmem
      have hpc : pc.card = pc.paths.length := rfl
      omega
    have hposW : 1 ≤ componentCount G (U \ D) := by
      obtain ⟨z, hz⟩ := hW
      have hpos : 0 < Fintype.card
          (G.induce ((U \ D : Finset V) : Set V)).ConnectedComponent :=
        Fintype.card_pos_iff.2
          ⟨(G.induce ((U \ D : Finset V) : Set V)).connectedComponentMk ⟨z, hz⟩⟩
      simpa [componentCount, Nat.card_eq_fintype_card] using
        Nat.succ_le_of_lt hpos
    omega
  · have hUeq : U = D := by
      ext z
      constructor
      · intro hz
        by_contra hzD
        exact hW ⟨z, mem_sdiff.2 ⟨hz, hzD⟩⟩
      · exact fun hz => hD hz
    have h1 : pc.card = 1 := by
      rw [hcard, hUeq, hDcomp]
    obtain ⟨r, hr⟩ := PathCover.exists_singleton_of_card_one pc h1
    have : p = q := by
      have hp' : p ∈ ([r] : List (GraphPath G)) := by simpa [hr] using hp
      have hq' : q ∈ ([r] : List (GraphPath G)) := by simpa [hr] using hq
      simp only [List.mem_singleton] at hp' hq'
      exact hp'.trans hq'.symm
    exact hne this

lemma exists_surviving_distinct_paths
    {U S : Finset V} {a b : V}
    (pc : PathCover G U) (hS : S ⊆ U)
    (haS : a ∉ S) (hbS : b ∉ S)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hap : a ∈ p.support) (hbq : b ∈ q.support) :
    ∃ (pc' : PathCover G (U \ S)) (p' q' : GraphPath G),
      p' ∈ pc'.paths ∧ q' ∈ pc'.paths ∧ p' ≠ q' ∧
        a ∈ p'.support ∧ b ∈ q'.support := by
  induction S using Finset.induction generalizing U pc p q with
  | empty =>
    refine ⟨pc.cast (by simp), p, q, ?_, ?_, hne, hap, hbq⟩
    · simpa [PathCover.cast_paths] using hp
    · simpa [PathCover.cast_paths] using hq
  | insert f S hf ih =>
    have ha : a ≠ f := fun h => haS (by simp [h])
    have hb : b ≠ f := fun h => hbS (by simp [h])
    have haU : a ∈ U := pc.support_subset hp hap
    have hbU : b ∈ U := pc.support_subset hq hbq
    have hap' : a ∈ p.support.erase f := mem_erase.2 ⟨ha, hap⟩
    have hbq' : b ∈ q.support.erase f := mem_erase.2 ⟨hb, hbq⟩
    obtain ⟨p1, hp1, hap1⟩ :=
      (GraphPath.mem_deleteVertex_support_iff p f a).2 hap'
    obtain ⟨q1, hq1, hbq1⟩ :=
      (GraphPath.mem_deleteVertex_support_iff q f b).2 hbq'
    have hp1' : p1 ∈ (pc.deleteVertex f).paths :=
      List.mem_flatMap.2 ⟨p, hp, hp1⟩
    have hq1' : q1 ∈ (pc.deleteVertex f).paths :=
      List.mem_flatMap.2 ⟨q, hq, hq1⟩
    have hne1 : p1 ≠ q1 := by
      intro heq
      have haq : a ∈ q.support := by
        have : a ∈ q1.support := by simpa [heq] using hap1
        exact GraphPath.support_subset_of_mem_deleteVertex hq1 this
      exact Finset.disjoint_left.1
        (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne) hap haq
    have hSsub : S ⊆ U.erase f := by
      intro z hz
      exact mem_erase.2 ⟨fun hfz => hf (hfz ▸ hz), hS (mem_insert_of_mem hz)⟩
    have haS' : a ∉ S := fun h => haS (mem_insert_of_mem h)
    have hbS' : b ∉ S := fun h => hbS (mem_insert_of_mem h)
    obtain ⟨pc1, p2, q2, hp2, hq2, hne2, hap2, hbq2⟩ :=
      ih (U := U.erase f) (pc.deleteVertex f) hSsub haS' hbS'
        hp1' hq1' hne1 hap1 hbq1
    have hEq : U.erase f \ S = U \ insert f S := by
      rw [sdiff_insert, erase_sdiff_distrib, erase_eq_of_notMem hf]
    refine ⟨pc1.cast hEq, p2, q2, ?_, ?_, hne2, hap2, hbq2⟩
    · simpa [PathCover.cast_paths] using hp2
    · simpa [PathCover.cast_paths] using hq2

lemma erase_union_eq_of_mem_right {X Y : Finset V} {y : V}
    (hdisj : Disjoint X Y) (hy : y ∈ Y) :
    (X ∪ Y).erase y = X ∪ Y.erase y := by
  ext z
  constructor
  · intro hz
    have hzJ : z ∈ X ∪ Y := (mem_erase.1 hz).2
    have hzne : z ≠ y := (mem_erase.1 hz).1
    rcases mem_union.1 hzJ with hzX | hzY
    · exact mem_union.2 (Or.inl hzX)
    · exact mem_union.2 (Or.inr (mem_erase.2 ⟨hzne, hzY⟩))
  · intro hz
    rcases mem_union.1 hz with hzX | hzY
    · exact mem_erase.2 ⟨fun hzy =>
        Finset.disjoint_left.1 hdisj hzX (by simpa [hzy] using hy),
        mem_union.2 (Or.inl hzX)⟩
    · exact mem_erase.2 ⟨(mem_erase.1 hzY).1,
        mem_union.2 (Or.inr (mem_erase.1 hzY).2)⟩

lemma erase_union_eq_left_of_singleton {X : Finset V} {y : V}
    (hdisj : Disjoint X {y}) :
    (X ∪ ({y} : Finset V)).erase y = X := by
  have hy : y ∈ ({y} : Finset V) := mem_singleton_self y
  have h := erase_union_eq_of_mem_right hdisj hy
  simpa [erase_singleton, union_empty] using h

lemma rNonadjClass_eq_side_union_ineligible
    {X Y : Finset V} {y : V}
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hpX : pathCoverNumber G X = Y.card)
    (hpJ : pathCoverNumber G (X ∪ Y) = 1)
    (hE : eligibleSet G (X ∪ Y) = X ∪ Y)
    (hJcog : Nikoghosyan.IsCograph G (X ∪ Y))
    (hy : y ∈ Y) (hX2 : 2 ≤ X.card) :
    rNonadjClass (G := G) (X ∪ Y) y = Y ∪ ineligibleSet G X := by
  have hdisj := disjoint_of_completeBetween hXY
  have hyJ : y ∈ X ∪ Y := mem_union.2 (Or.inr hy)
  have hXcog : Nikoghosyan.IsCograph G X :=
    isCograph_canonical_subset hJcog subset_union_left
  have hAcog : IsCograph G X := isCograph_iff.2 hXcog
  have hKdata : HamiltonEndpointsData (G := G) ((X ∪ Y).erase y) ∧
      pathCoverNumber G ((X ∪ Y).erase y) = 1 ∧
        insert y (ineligibleSet G ((X ∪ Y).erase y)) =
          Y ∪ ineligibleSet G X := by
    by_cases hY1 : Y.card = 1
    · have hYeq : Y = {y} := by
        obtain ⟨z, hz⟩ := card_eq_one.1 hY1
        have : y = z := mem_singleton.1 (hz ▸ hy)
        simpa [this] using hz
      have hK : (X ∪ Y).erase y = X := by
        simpa [hYeq] using
          erase_union_eq_left_of_singleton (X := X) (y := y)
            (by simpa [hYeq] using hdisj)
      have hpK : pathCoverNumber G ((X ∪ Y).erase y) = 1 := by
        simpa [hK, hpX, hY1]
      have hconn := connected_of_pathCoverNumber_eq_one (G := G) hpK
      have hKcog : Nikoghosyan.IsCograph G ((X ∪ Y).erase y) := by
        simpa [hK] using hXcog
      refine ⟨?_, hpK, ?_⟩
      · have hconnX : (G.induce (X : Set V)).Connected := hK ▸ hconn
        have hpKX : pathCoverNumber G X = 1 := hK ▸ hpK
        exact hK.symm ▸
          hamilton_endpoints_of_traceable_cograph_canonical hX2 hXcog hconnX hpKX
      · rw [hK, hYeq]
        ext z
        simp [mem_insert, mem_union, mem_singleton]
    · have hYer_card : (Y.erase y).card = Y.card - 1 := card_erase_of_mem hy
      have hYge : 2 ≤ Y.card := by
        have : 1 ≤ Y.card := card_pos.2 hYne
        omega
      have hYer : (Y.erase y).Nonempty := by
        have : 1 ≤ (Y.erase y).card := by omega
        exact card_pos.1 this
      have hK := erase_union_eq_of_mem_right hdisj hy
      have hYerXY : G.IsCompleteBetween (X : Set V) ((Y.erase y) : Set V) :=
        isCompleteBetween_mono hXY (fun _ hx => hx) (erase_subset y Y)
      have hcrit : pathCoverNumber G X = (Y.erase y).card + 1 := by omega
      have hpK : pathCoverNumber G ((X ∪ Y).erase y) = 1 := by
        simpa [hK] using
          pathCoverNumber_eq_one_of_critical hXne hYer hYerXY hcrit
      refine ⟨?_, hpK, ?_⟩
      · rw [hK]
        exact Or.inl (critical_endpoints_of_join hXne hYer hYerXY hcrit hAcog)
      · have hFeq :=
          ineligibleSet_complete_join_critical hXne hYer hYerXY hcrit
        have hF : ineligibleSet G ((X ∪ Y).erase y) =
            Y.erase y ∪ ineligibleSet G X := by simpa [hK] using hFeq
        ext z
        constructor
        · intro hz
          rcases mem_insert.1 hz with rfl | hz'
          · exact mem_union.2 (Or.inl hy)
          · have : z ∈ Y.erase y ∪ ineligibleSet G X := by simpa [hF] using hz'
            rcases mem_union.1 this with hzY | hzX
            · exact mem_union.2 (Or.inl (mem_erase.1 hzY).2)
            · exact mem_union.2 (Or.inr hzX)
        · intro hz
          rcases mem_union.1 hz with hzY | hzX
          · by_cases hzy : z = y
            · subst hzy
              exact mem_insert_self _ _
            · have : z ∈ Y.erase y ∪ ineligibleSet G X :=
                mem_union.2 (Or.inl (mem_erase.2 ⟨hzy, hzY⟩))
              exact mem_insert_of_mem (by simpa [hF] using this)
          · have : z ∈ Y.erase y ∪ ineligibleSet G X := mem_union.2 (Or.inr hzX)
            exact mem_insert_of_mem (by simpa [hF] using this)
  obtain ⟨hKdata, hpK, hins⟩ := hKdata
  have hiff : ∀ z ∈ (X ∪ Y).erase y,
      SpanningPathCompatible (G := G) (X ∪ Y) y z ↔
        Eligible G ((X ∪ Y).erase y) z :=
    fun z hz =>
      extension_iff_of_IH (U := X ∪ Y) (x := y) (y := z)
        hyJ hz hKdata hpK hE hpJ
  have hQ : rNonadjClass (G := G) (X ∪ Y) y = qxSet (G := G) (X ∪ Y) y :=
    rNonadjClass_eq_qxSet_of_extension hyJ hiff
  simpa [hQ, qxSet] using hins

lemma exists_surviving_distinct_paths_ineligible
    {U S : Finset V} {a b : V}
    (hU : Nikoghosyan.IsCograph G U)
    (pc : PathCover G U) (hmin : pc.card = pathCoverNumber G U)
    (hS : S ⊆ ineligibleSet G U)
    (haS : a ∉ S) (hbS : b ∉ S)
    {p q : GraphPath G} (hp : p ∈ pc.paths) (hq : q ∈ pc.paths) (hne : p ≠ q)
    (hap : a ∈ p.support) (hbq : b ∈ q.support) :
    ∃ (pc' : PathCover G (U \ S)) (p' q' : GraphPath G),
      pc'.card = pc.card + S.card ∧
        p' ∈ pc'.paths ∧ q' ∈ pc'.paths ∧ p' ≠ q' ∧
          a ∈ p'.support ∧ b ∈ q'.support := by
  induction S using Finset.induction generalizing U pc p q with
  | empty =>
    refine ⟨pc.cast (by simp), p, q, ?_, ?_, ?_, hne, hap, hbq⟩
    · simp [PathCover.cast_card]
    · simpa [PathCover.cast_paths] using hp
    · simpa [PathCover.cast_paths] using hq
  | insert f S hfC ih =>
    have hf : f ∈ ineligibleSet G U := hS (mem_insert_self f S)
    have hfU : f ∈ U := ineligibleSet_subset (G := G) U hf
    have hSsub : S ⊆ ineligibleSet G U := fun z hz =>
      hS (mem_insert_of_mem hz)
    have hnotEnd : ¬ pc.IsEndpoint f :=
      not_IsEndpoint_of_mem_ineligible pc hmin hf
    have hinternal : ∀ t ∈ pc.paths, f ≠ t.start ∧ f ≠ t.finish := by
      intro t ht
      constructor
      · intro hfs
        exact hnotEnd ⟨t, ht, Or.inl hfs⟩
      · intro hff
        exact hnotEnd ⟨t, ht, Or.inr hff⟩
    have hcard1 : (pc.deleteVertex f).card = pc.card + 1 :=
      PathCover.card_deleteVertex_eq_add_one_of_internal pc hfU hinternal
    have hdel := ineligible_deletion_erase_of_canonical hU hf
    have hmin1 : (pc.deleteVertex f).card =
        pathCoverNumber G (U.erase f) := by
      rw [hcard1, hmin, hdel.1]
    have hSnew : S ⊆ ineligibleSet G (U.erase f) := by
      intro z hz
      have hzF : z ∈ ineligibleSet G U := hSsub hz
      have hzne : z ≠ f := fun h => hfC (h ▸ hz)
      rw [hdel.2.2]
      exact mem_erase.2 ⟨hzne, hzF⟩
    have ha : a ≠ f := fun h => haS (by simp [h])
    have hb : b ≠ f := fun h => hbS (by simp [h])
    have hap' : a ∈ p.support.erase f := mem_erase.2 ⟨ha, hap⟩
    have hbq' : b ∈ q.support.erase f := mem_erase.2 ⟨hb, hbq⟩
    obtain ⟨p1, hp1, hap1⟩ :=
      (GraphPath.mem_deleteVertex_support_iff p f a).2 hap'
    obtain ⟨q1, hq1, hbq1⟩ :=
      (GraphPath.mem_deleteVertex_support_iff q f b).2 hbq'
    have hp1' : p1 ∈ (pc.deleteVertex f).paths :=
      List.mem_flatMap.2 ⟨p, hp, hp1⟩
    have hq1' : q1 ∈ (pc.deleteVertex f).paths :=
      List.mem_flatMap.2 ⟨q, hq, hq1⟩
    have hne1 : p1 ≠ q1 := by
      intro heq
      have haq : a ∈ q.support := by
        have : a ∈ q1.support := by simpa [heq] using hap1
        exact GraphPath.support_subset_of_mem_deleteVertex hq1 this
      exact Finset.disjoint_left.1
        (PathCover.pairwise_disjoint_of_mem pc.disjoint hp hq hne) hap haq
    have haS' : a ∉ S := fun h => haS (mem_insert_of_mem h)
    have hbS' : b ∉ S := fun h => hbS (mem_insert_of_mem h)
    have hU' : Nikoghosyan.IsCograph G (U.erase f) :=
      isCograph_canonical_subset hU (erase_subset f U)
    obtain ⟨pc1, p2, q2, hcard1', hp2, hq2, hne2, hap2, hbq2⟩ :=
      ih (U := U.erase f) hU' (pc.deleteVertex f) hmin1 hSnew haS' hbS'
        hp1' hq1' hne1 hap1 hbq1
    have hEq : U.erase f \ S = U \ insert f S := by
      rw [sdiff_insert, erase_sdiff_distrib, erase_eq_of_notMem hfC]
    refine ⟨pc1.cast hEq, p2, q2, ?_, ?_, ?_, hne2, hap2, hbq2⟩
    · have hcard := card_insert_of_notMem (s := S) hfC
      rw [PathCover.cast_card, hcard1', hcard1]
      omega
    · simpa [PathCover.cast_paths] using hp2
    · simpa [PathCover.cast_paths] using hq2

lemma find?_none_support_subset_D {p : GraphPath G} {D : Finset V}
    (h : p.walk.support.find? (fun x => decide (x ∉ D)) = none) :
    p.support ⊆ D := by
  intro z hz
  have hzW : z ∈ p.walk.support := GraphPath.mem_walk_support.1 hz
  have hnot : ¬ decide (z ∉ D) :=
    (List.find?_eq_none (p := fun x : V => decide (x ∉ D))).1 h z hzW
  simpa using hnot

lemma takeUntil_prefix_mem_D {p : GraphPath G} {D : Finset V} {z y : V}
    (h : p.walk.support.find? (fun x => decide (x ∉ D)) = some z)
    (hz : z ∈ p.support) (hy : y ∈ (p.takeUntil hz).support) (hne : y ≠ z) :
    y ∈ D := by
  have hB :
      p.walk.support.find? (fun x => decide (x ∈ (univ : Finset V) \ D)) =
        some z := by
    simpa [mem_sdiff, mem_univ] using h
  have hnot :
      y ∉ (univ : Finset V) \ D :=
    GraphPath.takeUntil_ne_first_not_mem_B (B := (univ : Finset V) \ D)
      hB hz hy hne
  simpa [mem_sdiff, mem_univ] using hnot

lemma pathCoverNumber_sdiff_of_traceable_component
    {X D : Finset V}
    (hXcog : Nikoghosyan.IsCograph G X)
    (hD : D ⊆ X \ ineligibleSet G X)
    (hDne : D.Nonempty)
    (hconn : (G.induce (D : Set V)).Connected)
    (hnocross : ∀ a ∈ D, ∀ b ∈ (X \ ineligibleSet G X) \ D, ¬ G.Adj a b)
    {d : V} (hdD : d ∈ D) :
    pathCoverNumber G (X \ D) ≤ pathCoverNumber G X := by
  let F := ineligibleSet G X
  have hdXF : d ∈ X \ F := hD hdD
  have hdX : d ∈ X := (mem_sdiff.1 hdXF).1
  have hdF : d ∉ F := (mem_sdiff.1 hdXF).2
  have hdE : Eligible G X d :=
    (mem_eligibleSet_iff (G := G)).1
      (mem_eligibleSet_of_mem_not_ineligible hdX hdF) |>.2
  obtain ⟨pc0, hmin0, p0, hp0, hdend⟩ := hdE
  have horient :
      ∃ (pc : PathCover G X) (p : GraphPath G),
        pc.card = pathCoverNumber G X ∧ p ∈ pc.paths ∧ p.start = d := by
    rcases hdend with h | h
    · exact ⟨pc0, p0, hmin0, hp0, h.symm⟩
    · refine ⟨pc0.replacePath_sat hp0 p0.reverse (GraphPath.support_reverse p0),
        p0.reverse, ?_, ?_, ?_⟩
      · simpa [pc0.replacePath_sat_card hp0 p0.reverse
          (GraphPath.support_reverse p0)] using hmin0
      · exact pc0.replacePath_sat_self_mem hp0 p0.reverse
          (GraphPath.support_reverse p0)
      · simpa [GraphPath.reverse] using h.symm
  obtain ⟨pc, p, hmin, hp, hs⟩ := horient
  have hend : pc.IsEndpoint d := ⟨p, hp, Or.inl hs.symm⟩
  obtain ⟨pcF, hcardF, hendF⟩ :=
    exists_pathCover_sdiff_ineligible_keepEndpoint (U := X) (C := F) (x := d)
      hXcog pc hmin (fun _ hx => hx) hend hdF
  have hid := componentCount_sdiff_ineligibleSet_eq_of_canonical hXcog
  have hcardEq : pcF.card = componentCount G (X \ F) := by
    have hsum : pcF.card = pathCoverNumber G X + F.card := by
      simpa [hmin] using hcardF
    have hid' : componentCount G (X \ F) = F.card + pathCoverNumber G X := by
      simpa [F] using hid
    omega
  obtain ⟨q, hq, hdq⟩ := hendF
  have hdq' : d ∈ q.support := by
    rcases hdq with h | h
    · simpa [h] using q.start_mem_support
    · simpa [h] using q.finish_mem_support
  have hUeq : X \ F = D ∪ ((X \ F) \ D) :=
    (union_sdiff_of_subset hD).symm
  have hqD : q.support = D :=
    path_support_eq_of_component (U := X \ F) (D := D) pcF hcardEq
      (fun z hz => hD hz) hDne hconn
      (fun a ha b hb => hnocross a ha b hb) hq hdD hdq'
  have hDp : D ⊆ p.support := by
    intro y hyD
    by_contra hyP
    have hyX : y ∈ X := (mem_sdiff.1 (hD hyD)).1
    obtain ⟨r, hr, hyr⟩ := (pc.mem_iff y).1 hyX
    have hne : p ≠ r := fun heq => hyP (heq ▸ hyr)
    have hyF : y ∉ F := (mem_sdiff.1 (hD hyD)).2
    obtain ⟨pc', p', r', hcard', hp', hr', hne', hdp', hyr'⟩ :=
      exists_surviving_distinct_paths_ineligible (U := X) (S := F)
        hXcog pc hmin (fun _ hx => hx) hdF hyF hp hr hne
        (by simpa [hs] using p.start_mem_support) hyr
    have hcard'c : pc'.card = componentCount G (X \ F) := by
      have : pc'.card = pathCoverNumber G X + F.card := by
        simpa [hmin] using hcard'
      omega
    have hp'D : p'.support = D :=
      path_support_eq_of_component (U := X \ F) (D := D) pc' hcard'c
        (fun z hz => hD hz) hDne hconn
        (fun a ha b hb => hnocross a ha b hb) hp' hdD hdp'
    have hr'D : r'.support = D :=
      path_support_eq_of_component (U := X \ F) (D := D) (p := r') (x := y)
        pc' hcard'c (fun z hz => hD hz) hDne hconn
        (fun a ha b hb => hnocross a ha b hb) hr' hyD hyr'
    have hdisj := PathCover.pairwise_disjoint_of_mem pc'.disjoint hp' hr' hne'
    exact Finset.disjoint_left.1 hdisj
      (by simpa [hp'D] using hdD) (by simpa [hr'D] using hdD)
  cases hfind : p.walk.support.find? (fun x => decide (x ∉ D)) with
  | none =>
    have hpD : p.support = D :=
      Subset.antisymm (find?_none_support_subset_D hfind) hDp
    have hEq : X \ p.support = X \ D := by simpa [hpD]
    exact (pathCoverNumber_le (G := G) ((pc.erasePath hp).cast hEq)).trans
      (by
        have hcard := PathCover.erasePath_card pc hp
        have : ((pc.erasePath hp).cast hEq).card = pc.card - 1 := by
          simpa [PathCover.cast_card] using hcard
        omega)
  | some z =>
    have hzW : z ∈ p.walk.support := List.mem_of_find?_eq_some hfind
    have hz : z ∈ p.support := GraphPath.mem_walk_support.2 hzW
    have hzD : z ∉ D :=
      of_decide_eq_true (List.find?_some (p := fun x : V => decide (x ∉ D)) hfind)
    have hzX : z ∈ X := pc.support_subset hp hz
    have hzne : z ≠ d := fun hzd => hzD (by simpa [hzd] using hdD)
    have hzneS : z ≠ p.start := fun hzs => hzne (hzs.trans hs)
    have hnnTake : ¬ (p.takeUntil hz).walk.Nil := fun hn =>
      hzneS ((GraphPath.takeUntil_nil_iff p hz).1 hn)
    have hadjPen : G.Adj (p.takeUntil hz).walk.penultimate z :=
      (p.takeUntil hz).walk.adj_penultimate hnnTake
    have hpenW :
        (p.takeUntil hz).walk.penultimate ∈ (p.takeUntil hz).walk.support := by
      simp only [Walk.penultimate]
      exact Walk.getVert_mem_support _ _
    have hpen : (p.takeUntil hz).walk.penultimate ∈ (p.takeUntil hz).support :=
      GraphPath.mem_walk_support.2 hpenW
    have hpenNe : (p.takeUntil hz).walk.penultimate ≠ z := hadjPen.ne
    have hpenD : (p.takeUntil hz).walk.penultimate ∈ D :=
      takeUntil_prefix_mem_D hfind hz hpen hpenNe
    have hzF : z ∈ F := by
      by_contra hznotF
      exact hnocross _ hpenD z
        (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hzX, hznotF⟩, hzD⟩) hadjPen
    have hdropD : ∀ y, y ∈ (p.dropUntil hz).support → y ∉ D := by
      intro y hyDrop hyD
      have hyz : y ≠ z := fun h => hzD (h ▸ hyD)
      have hzNeF : z ≠ p.finish := by
        intro hzFsh
        have hnil : (p.dropUntil hz).walk.Nil :=
          (GraphPath.dropUntil_nil_iff p hz).2 hzFsh
        have hsing : (p.dropUntil hz).support = {(p.dropUntil hz).start} :=
          GraphPath.support_eq_singleton_of_nil (p.dropUntil hz) hnil
        have : y = z := by
          have hy' : y ∈ ({(p.dropUntil hz).start} : Finset V) := by
            simpa [hsing] using hyDrop
          simpa [GraphPath.dropUntil] using mem_singleton.1 hy'
        exact hyz this
      have hnilP : ¬ p.walk.Nil := GraphPath.not_nil_of_internal hz hzneS
      have hnnDrop : ¬ (p.dropUntil hz).walk.Nil := fun hn =>
        hzNeF ((GraphPath.dropUntil_nil_iff p hz).1 hn)
      let pL := (p.takeUntil hz).trimFinish hnnTake
      let pR := (p.dropUntil hz).trimStart hnnDrop
      have hdv :
          p.deleteVertex z =
            [(p.takeUntil hz).trimFinish hnnTake,
              (p.dropUntil hz).trimStart hnnDrop] := by
        simp [GraphPath.deleteVertex, hz, hnilP, hzneS, hzNeF]
      have hpLmem : pL ∈ (pc.deleteVertex z).paths := by
        refine List.mem_flatMap.2 ⟨p, hp, ?_⟩
        simpa [hdv, pL]
      have hpRmem : pR ∈ (pc.deleteVertex z).paths := by
        refine List.mem_flatMap.2 ⟨p, hp, ?_⟩
        simpa [hdv, pR]
      have hsTake : d ∈ (p.takeUntil hz).support := by
        simpa [hs] using GraphPath.start_mem_takeUntil p hz
      have hdpL : d ∈ pL.support := by
        have hfTake : (p.takeUntil hz).finish = z := rfl
        simpa [pL, GraphPath.support_trimFinish (p.takeUntil hz) hnnTake, hfTake]
          using mem_erase.2 ⟨Ne.symm hzne, hsTake⟩
      have hyr : y ∈ pR.support := by
        have hsDrop : (p.dropUntil hz).start = z := rfl
        simpa [pR, GraphPath.support_trimStart (p.dropUntil hz) hnnDrop, hsDrop]
          using mem_erase.2 ⟨hyz, hyDrop⟩
      have hneLR : pL ≠ pR := by
        intro heq
        have hdR : d ∈ pR.support := by simpa [heq] using hdpL
        have : pR.support ⊆ (p.dropUntil hz).support := by
          have hsDrop : (p.dropUntil hz).start = z := rfl
          simpa [pR, GraphPath.support_trimStart (p.dropUntil hz) hnnDrop, hsDrop]
            using erase_subset z (p.dropUntil hz).support
        exact GraphPath.start_not_mem_dropUntil p hz hzneS
          (by simpa [hs] using this hdR)
      have hinternal : ∀ t ∈ pc.paths, z ≠ t.start ∧ z ≠ t.finish := by
        intro t ht
        have hnotEnd : ¬ pc.IsEndpoint z :=
          not_IsEndpoint_of_mem_ineligible pc hmin hzF
        constructor
        · intro hfs
          exact hnotEnd ⟨t, ht, Or.inl hfs⟩
        · intro hff
          exact hnotEnd ⟨t, ht, Or.inr hff⟩
      have hcard1 : (pc.deleteVertex z).card = pc.card + 1 :=
        PathCover.card_deleteVertex_eq_add_one_of_internal pc hzX hinternal
      have hdel := ineligible_deletion_erase_of_canonical hXcog hzF
      have hmin1 : (pc.deleteVertex z).card =
          pathCoverNumber G (X.erase z) := by
        rw [hcard1, hmin, hdel.1]
      have hSnew : F.erase z ⊆ ineligibleSet G (X.erase z) := by
        intro t ht
        have htF : t ∈ F := (mem_erase.1 ht).2
        have htne : t ≠ z := (mem_erase.1 ht).1
        rw [hdel.2.2]
        exact mem_erase.2 ⟨htne, htF⟩
      have hdSe : d ∉ F.erase z := fun h => hdF (mem_of_mem_erase h)
      have hySe : y ∉ F.erase z := fun hyF =>
        (mem_sdiff.1 (hD hyD)).2 (mem_of_mem_erase hyF)
      have hU' : Nikoghosyan.IsCograph G (X.erase z) :=
        isCograph_canonical_subset hXcog (erase_subset z X)
      obtain ⟨pc', p', r', hcard', hp', hr', hne', hdp', hyr'⟩ :=
        exists_surviving_distinct_paths_ineligible
          (U := X.erase z) (S := F.erase z)
          hU' (pc.deleteVertex z) hmin1 hSnew hdSe hySe
          hpLmem hpRmem hneLR hdpL hyr
      have hEqF : X.erase z \ F.erase z = X \ F := by
        ext t
        constructor
        · intro ht
          have ht1 := mem_sdiff.1 ht
          have htE := mem_erase.1 ht1.1
          refine mem_sdiff.2 ⟨htE.2, ?_⟩
          intro hF
          exact ht1.2 (mem_erase.2 ⟨htE.1, hF⟩)
        · intro ht
          have htX := (mem_sdiff.1 ht).1
          have htF := (mem_sdiff.1 ht).2
          have htz : t ≠ z := fun heq => htF (heq ▸ hzF)
          exact mem_sdiff.2 ⟨mem_erase.2 ⟨htz, htX⟩,
            fun hEr => htF (mem_erase.1 hEr).2⟩
      let pcF' : PathCover G (X \ F) := pc'.cast hEqF
      have hcard'c : pcF'.card = componentCount G (X \ F) := by
        have hcardz : (F.erase z).card = F.card - 1 := card_erase_of_mem hzF
        have hpos : 1 ≤ F.card := Nat.succ_le_of_lt (card_pos.2 ⟨z, hzF⟩)
        have : pcF'.card = pc.card + F.card := by
          rw [PathCover.cast_card, hcard', hcard1]
          omega
        simpa [hmin] using (by
          have : pcF'.card = pathCoverNumber G X + F.card := by
            simpa [hmin] using this
          omega)
      have hpF' : p' ∈ pcF'.paths := by simpa [pcF', PathCover.cast_paths] using hp'
      have hrF' : r' ∈ pcF'.paths := by simpa [pcF', PathCover.cast_paths] using hr'
      have hp'D : p'.support = D :=
        path_support_eq_of_component (U := X \ F) (D := D) (p := p') (x := d)
          pcF' hcard'c (fun t ht => hD ht) hDne hconn
          (fun a ha b hb => hnocross a ha b hb) hpF' hdD hdp'
      have hr'D : r'.support = D :=
        path_support_eq_of_component (U := X \ F) (D := D) (p := r') (x := y)
          pcF' hcard'c (fun t ht => hD ht) hDne hconn
          (fun a ha b hb => hnocross a ha b hb) hrF' hyD hyr'
      have hdisj :=
        PathCover.pairwise_disjoint_of_mem pcF'.disjoint hpF' hrF' hne'
      exact Finset.disjoint_left.1 hdisj
        (by simpa [hp'D] using hdD) (by simpa [hr'D] using hdD)
    have htakeD : (p.takeUntil hz).support.erase z = D := by
      refine Subset.antisymm ?_ ?_
      · intro y hy
        have hyT := (mem_erase.1 hy).2
        have hyz := (mem_erase.1 hy).1
        exact takeUntil_prefix_mem_D hfind hz hyT hyz
      · intro y hyD
        have hyP : y ∈ p.support := hDp hyD
        have hyDrop : y ∉ (p.dropUntil hz).support := fun h => hdropD y h hyD
        have hyTake : y ∈ (p.takeUntil hz).support := by
          have hunion := GraphPath.support_takeUntil_union_dropUntil p hz
          have : y ∈ (p.takeUntil hz).support ∪ (p.dropUntil hz).support := by
            simpa [hunion] using hyP
          exact (mem_union.1 this).resolve_right hyDrop
        exact mem_erase.2 ⟨fun hyz => hzD (hyz ▸ hyD), hyTake⟩
    have hdropEq : (p.dropUntil hz).support = p.support \ D := by
      have hunion := GraphPath.support_takeUntil_union_dropUntil p hz
      ext y
      constructor
      · intro hy
        exact mem_sdiff.2 ⟨(GraphPath.dropUntil_support_subset p hz) hy, hdropD y hy⟩
      · intro hy
        have hyP := (mem_sdiff.1 hy).1
        have hyD := (mem_sdiff.1 hy).2
        have : y ∈ (p.takeUntil hz).support ∪ (p.dropUntil hz).support := by
          simpa [hunion] using hyP
        rcases mem_union.1 this with hyT | hyR
        · have hyz : y = z := by
            have : y ∈ (p.takeUntil hz).support.erase z ∨ y = z := by
              by_cases h : y = z
              · exact Or.inr h
              · exact Or.inl (mem_erase.2 ⟨h, hyT⟩)
            rcases this with hEr | rfl
            · exact (hyD ((htakeD ▸ hEr))).elim
            · rfl
          simpa [hyz, GraphPath.dropUntil] using
            (p.dropUntil hz).start_mem_support
        · exact hyR
    have hdisjDrop : Disjoint (X \ p.support) (p.dropUntil hz).support := by
      rw [disjoint_iff_inter_eq_empty]
      ext y
      constructor
      · intro hy
        exact ((mem_sdiff.1 (mem_inter.1 hy).1).2
          (GraphPath.dropUntil_support_subset p hz (mem_inter.1 hy).2)).elim
      · intro hy
        exact (notMem_empty y hy).elim
    have hEq : (X \ p.support) ∪ (p.dropUntil hz).support = X \ D := by
      rw [hdropEq]
      ext y
      constructor
      · intro hy
        rcases mem_union.1 hy with hL | hR
        · exact mem_sdiff.2 ⟨(mem_sdiff.1 hL).1,
            fun hyD => (mem_sdiff.1 hL).2 (hDp hyD)⟩
        · exact mem_sdiff.2 ⟨pc.support_subset hp (mem_sdiff.1 hR).1,
            (mem_sdiff.1 hR).2⟩
      · intro hy
        have hyX := (mem_sdiff.1 hy).1
        have hyD := (mem_sdiff.1 hy).2
        by_cases hyP : y ∈ p.support
        · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hyP, hyD⟩))
        · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hyX, hyP⟩))
    let pcRem := PathCover.unionDisjoint hdisjDrop
      (pc.erasePath hp) (PathCover.ofPath (p.dropUntil hz))
    have hle := pathCoverNumber_le (G := G) (pcRem.cast hEq)
    have hcardRem : (pcRem.cast hEq).card = pc.card := by
      rw [PathCover.cast_card, PathCover.unionDisjoint_card, PathCover.erasePath_card,
        PathCover.ofPath_card]
      have hpos : 1 ≤ pc.card := Nat.succ_le_of_lt (List.length_pos_of_mem hp)
      omega
    exact hle.trans (by omega)

/-- A disconnected induced block of a complete join lies in one side. -/
lemma subset_join_side_of_disconnected {A B W : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hW : W ⊆ A ∪ B)
    (h2 : 2 ≤ componentCount G W) :
    W ⊆ A ∨ W ⊆ B := by
  by_cases hA : (W ∩ A).Nonempty
  · by_cases hB : (W ∩ B).Nonempty
    · have hjoin :=
        isCompleteBetween_mono (A := A) (A' := W ∩ A) (B := B) (B' := W ∩ B)
          hAB inter_subset_right inter_subset_right
      have hconn := induce_connected_of_completeJoin hA hB hjoin
      have hcoverW : (W ∩ A) ∪ (W ∩ B) = W := by
        ext z
        constructor
        · intro hz
          rcases mem_union.1 hz with hzA | hzB
          · exact (mem_inter.1 hzA).1
          · exact (mem_inter.1 hzB).1
        · intro hzW
          have hzAB := hW hzW
          rcases mem_union.1 hzAB with hzA | hzB
          · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzW, hzA⟩))
          · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzW, hzB⟩))
      have h1 : componentCount G W = 1 := by
        have hne : W.Nonempty :=
          hA.mono (by simpa [hcoverW] using subset_union_left (s₁ := W ∩ A))
        have hconnW : (G.induce (W : Set V)).Connected := hcoverW ▸ hconn
        exact componentCount_eq_one_of_connected hne hconnW
      omega
    · have hBempty : W ∩ B = ∅ := not_nonempty_iff_eq_empty.1 hB
      refine Or.inl ?_
      intro z hz
      have hzAB := hW hz
      rcases mem_union.1 hzAB with hzA | hzB
      · exact hzA
      · exact (notMem_empty z (by simpa [hBempty] using mem_inter.2 ⟨hz, hzB⟩)).elim
  · have hAempty : W ∩ A = ∅ := not_nonempty_iff_eq_empty.1 hA
    refine Or.inr ?_
    intro z hz
    have hzAB := hW hz
    rcases mem_union.1 hzAB with hzA | hzB
    ·       exact (notMem_empty z (by simpa [hAempty] using mem_inter.2 ⟨hz, hzA⟩)).elim
    · exact hzB

lemma three_le_card_of_three_mem {s : Finset V} {a b c : V}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset V) ⊆ s := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [hbc]
    · simp [mem_insert, mem_singleton, hab, hac]
  exact (by omega : 3 ≤ ({a, b, c} : Finset V).card).trans (card_le_card hsub)

lemma sdiff_union_eq_sdiff_left_union {L D Px : Finset V}
    (hLD : Disjoint L D) (hP : Px ⊆ L) :
    (L ∪ D) \ Px = (L \ Px) ∪ D := by
  rw [mem_union_sdiff_eq]
  have hD : D \ Px = D := by
    ext z
    constructor
    · intro hz
      exact (mem_sdiff.1 hz).1
    · intro hzD
      exact mem_sdiff.2 ⟨hzD, fun hzP =>
        (Finset.disjoint_left.1 hLD (hP hzP) hzD).elim⟩
  rw [hD]

lemma componentCount_sdiff_le_sub_one_of_path_cycle
    {L D Px : Finset V} {u v : V}
    (hLD : Disjoint L D)
    (c : GraphCycle G) (hc : c.support = D)
    (pL : GraphPath G) (hpLsup : pL.support = L)
    (hs : pL.start = u) (hf : pL.finish = v) (huv : u ≠ v)
    (huP : u ∈ Px) (hvP : v ∈ Px) (hPx : Px ⊆ L ∪ D)
    (hPD : (Px ∩ D).Nonempty) :
    componentCount G ((L ∪ D) \ Px) ≤ Px.card - 1 := by
  let PL := Px ∩ L
  let PD := Px ∩ D
  have hdecomp : (L ∪ D) \ Px = (L \ PL) ∪ (D \ PD) := by
    ext z
    constructor
    · intro hz
      have hzLD := (mem_sdiff.1 hz).1
      have hzP := (mem_sdiff.1 hz).2
      rcases mem_union.1 hzLD with hzL | hzD
      · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzL, fun h =>
          hzP (mem_inter.1 h).1⟩))
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hzD, fun h =>
          hzP (mem_inter.1 h).1⟩))
    · intro hz
      rcases mem_union.1 hz with hzL | hzD
      · exact mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hzL).1),
          fun hP => (mem_sdiff.1 hzL).2 (mem_inter.2 ⟨hP, (mem_sdiff.1 hzL).1⟩)⟩
      · exact mem_sdiff.2 ⟨mem_union.2 (Or.inr (mem_sdiff.1 hzD).1),
          fun hP => (mem_sdiff.1 hzD).2 (mem_inter.2 ⟨hP, (mem_sdiff.1 hzD).1⟩)⟩
  have hdisjPLPD : Disjoint PL PD :=
    Disjoint.mono inter_subset_right inter_subset_right hLD
  have hPeq : Px = PL ∪ PD := by
    ext z
    constructor
    · intro hz
      have hzJ := hPx hz
      rcases mem_union.1 hzJ with hzL | hzD
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hz, hzL⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hz, hzD⟩))
    · intro hz
      rcases mem_union.1 hz with hPL | hPD'
      · exact (mem_inter.1 hPL).1
      · exact (mem_inter.1 hPD').1
  have huL : u ∈ L := by simpa [hpLsup, hs] using pL.start_mem_support
  have hvL : v ∈ L := by simpa [hpLsup, hf] using pL.finish_mem_support
  have huPL : u ∈ PL := mem_inter.2 ⟨huP, huL⟩
  have hvPL : v ∈ PL := mem_inter.2 ⟨hvP, hvL⟩
  have hRL : SpanningPathCompatible (G := G) L u v :=
    ⟨huv, pL, hpLsup, Or.inl ⟨hs, hf⟩⟩
  have hleL :=
    componentCount_sdiff_le_of_both_endpoints (U := L) (S := PL)
      inter_subset_right huPL hvPL huv hRL
  have hleD :=
    pathCoverNumber_sdiff_le_card_of_cycle (U := D) (A := PD) c hc
      inter_subset_right hPD
  have hleDc :=
    (componentCount_le_pathCoverNumber (G := G) (D \ PD)).trans hleD
  have hle := componentCount_union_le (G := G) (L \ PL) (D \ PD)
  have hcard : Px.card = PL.card + PD.card := by
    rw [hPeq, card_union_of_disjoint hdisjPLPD]
  have hPLge : 2 ≤ PL.card := by
    have hsub : ({u, v} : Finset V) ⊆ PL := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact huPL
      · exact hvPL
    have h2 : ({u, v} : Finset V).card = 2 := by
      rw [card_insert_of_notMem, card_singleton]
      simp [huv]
    exact (by omega : 2 ≤ ({u, v} : Finset V).card).trans (card_le_card hsub)
  have hpos : 1 ≤ PL.card := by omega
  have : componentCount G ((L ∪ D) \ Px) ≤ PL.card - 1 + PD.card := by
    simpa [hdecomp] using hle.trans (Nat.add_le_add hleL hleDc)
  omega

lemma Px_subset_L_of_partCut
    {L D Px : Finset V} {u v : V}
    (hLD : Disjoint L D)
    (c : GraphCycle G) (hc : c.support = D)
    (pL : GraphPath G) (hpLsup : pL.support = L)
    (hs : pL.start = u) (hf : pL.finish = v) (huv : u ≠ v)
    (huP : u ∈ Px) (hvP : v ∈ Px) (hPx : Px ⊆ L ∪ D)
    (hcut : componentCount G ((L ∪ D) \ Px) = Px.card) :
    Px ⊆ L := by
  by_contra hnot
  have hPD : (Px ∩ D).Nonempty := by
    rw [not_subset] at hnot
    obtain ⟨z, hzP, hzL⟩ := hnot
    have hzJ := hPx hzP
    rcases mem_union.1 hzJ with hzL' | hzD
    · exact (hzL hzL').elim
    · exact ⟨z, mem_inter.2 ⟨hzP, hzD⟩⟩
  have hle :=
    componentCount_sdiff_le_sub_one_of_path_cycle hLD c hc pL hpLsup hs hf huv
      huP hvP hPx hPD
  have hpos : 1 ≤ Px.card := Nat.succ_le_of_lt (card_pos.2 ⟨u, huP⟩)
  omega

lemma D_component_of_Px_subset_L
    {L D Px : Finset V} {u v : V}
    (hLD : Disjoint L D)
    (c : GraphCycle G) (hc : c.support = D)
    (pL : GraphPath G) (hpLsup : pL.support = L)
    (hs : pL.start = u) (hf : pL.finish = v) (huv : u ≠ v)
    (huP : u ∈ Px) (hvP : v ∈ Px) (hP : Px ⊆ L)
    (hPge : 2 ≤ Px.card)
    (hcut : componentCount G ((L ∪ D) \ Px) = Px.card) :
    componentCount G (L \ Px) = Px.card - 1 ∧
      (∀ a ∈ D, ∀ b ∈ L \ Px, ¬ G.Adj a b) ∧
        (L ∪ D) \ Px = (L \ Px) ∪ D := by
  have hdecomp := sdiff_union_eq_sdiff_left_union hLD hP
  have hDne : D.Nonempty := by
    have h3 : 3 ≤ D.card := by simpa [hc] using c.three_le_card_support
    exact card_pos.1 (le_trans (by decide : (1 : ℕ) ≤ 3) h3)
  have hconnD : (G.induce (D : Set V)).Connected := by
    obtain ⟨q, hq, _⟩ := GraphCycle.exists_spanning_path c
    exact connected_of_spanning_path q (hq.trans hc)
  have hcD : componentCount G D = 1 :=
    componentCount_eq_one_of_connected hDne hconnD
  have huL : u ∈ L := by simpa [hpLsup, hs] using pL.start_mem_support
  have hvL : v ∈ L := by simpa [hpLsup, hf] using pL.finish_mem_support
  have hRL : SpanningPathCompatible (G := G) L u v :=
    ⟨huv, pL, hpLsup, Or.inl ⟨hs, hf⟩⟩
  have hleL :=
    componentCount_sdiff_le_of_both_endpoints (U := L) (S := Px)
      hP huP hvP huv hRL
  have hLPne : (L \ Px).Nonempty := by
    by_contra hempty
    have hempty : L \ Px = ∅ := not_nonempty_iff_eq_empty.1 hempty
    have hJD : (L ∪ D) \ Px = D := by
      simpa [hempty, empty_union] using hdecomp
    have : Px.card = 1 := by
      have := hcut
      simpa [hJD, hcD] using this.symm
    omega
  have hle := componentCount_union_le (G := G) (L \ Px) D
  have hcut' : componentCount G ((L \ Px) ∪ D) = Px.card := by
    simpa [hdecomp] using hcut
  have hpos : 1 ≤ Px.card := by omega
  have hcLP : componentCount G (L \ Px) = Px.card - 1 := by omega
  have heq : componentCount G ((L \ Px) ∪ D) =
      componentCount G (L \ Px) + componentCount G D := by omega
  have hdisj : Disjoint (L \ Px) D :=
    Disjoint.mono sdiff_subset (fun _ hx => hx) hLD
  have hnocross :=
    no_cross_of_componentCount_add hdisj hLPne hDne (by simpa using heq)
  exact ⟨hcLP, fun a ha b hb hadj => hnocross b hb a ha hadj.symm, hdecomp⟩

lemma false_of_balanced_join_child
    {L D X Y Px : Finset V} {h u v : V}
    (c : GraphCycle G) (pL : GraphPath G)
    (hLD : Disjoint L D) (hc : c.support = D)
    (hcover : X ∪ Y = L ∪ D)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hJcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hpL : pathCoverNumber G L = 1)
    (hpJ : pathCoverNumber G (L ∪ D) = 1)
    (hE : eligibleSet G (L ∪ D) = L ∪ D)
    (hhF : h ∈ ineligibleSet G L)
    (hpLsup : pL.support = L) (hs : pL.start = u) (hf : pL.finish = v)
    (huv : u ≠ v)
    (hbal : IsBalancedEndpoints (G := G) (L ∪ D))
    (hPxeq : Px = rNonadjClass (G := G) (L ∪ D) h)
    (hhP : h ∈ Px) (huP : u ∈ Px) (hvP : v ∈ Px)
    (hPL : Px ⊆ L) (hPge : 2 ≤ Px.card)
    (hcut : componentCount G ((L ∪ D) \ Px) = Px.card)
    (hWP : (L ∪ D) \ Px ⊆ X) :
    False := by
  have hdisjXY := disjoint_of_completeBetween hXY
  have hhL : h ∈ L := ineligibleSet_subset (G := G) L hhF
  have hhJ : h ∈ L ∪ D := mem_union.2 (Or.inl hhL)
  have hYP : Y ⊆ Px := by
    intro y hy
    have hyJ : y ∈ L ∪ D := by
      have : y ∈ X ∪ Y := mem_union.2 (Or.inr hy)
      simpa [hcover] using this
    by_contra hyP
    have hyW : y ∈ (L ∪ D) \ Px := mem_sdiff.2 ⟨hyJ, hyP⟩
    exact (Finset.disjoint_left.1 hdisjXY (hWP hyW) hy).elim
  have hPeq : Px = Y ∪ (Px ∩ X) := by
    ext z
    constructor
    · intro hzP
      have hzJ : z ∈ X ∪ Y := by
        have : z ∈ L ∪ D := mem_union.2 (Or.inl (hPL hzP))
        simpa [hcover] using this
      rcases mem_union.1 hzJ with hzX | hzY
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzP, hzX⟩))
      · exact mem_union.2 (Or.inl hzY)
    · intro hz
      rcases mem_union.1 hz with hzY | hzZ
      · exact hYP hzY
      · exact (mem_inter.1 hzZ).1
  have hdisjYZ : Disjoint Y (Px ∩ X) :=
    Disjoint.mono (fun _ hy => hy) inter_subset_right hdisjXY.symm
  have hcardP : Px.card = Y.card + (Px ∩ X).card :=
    (congrArg Finset.card hPeq).trans (card_union_of_disjoint hdisjYZ)
  have hJP : (L ∪ D) \ Px = X \ (Px ∩ X) := by
    ext z
    constructor
    · intro hz
      have hzX : z ∈ X := hWP hz
      exact mem_sdiff.2 ⟨hzX, fun hZ => (mem_sdiff.1 hz).2 (mem_inter.1 hZ).1⟩
    · intro hz
      have hzX := (mem_sdiff.1 hz).1
      have hzJ : z ∈ L ∪ D := by
        have : z ∈ X ∪ Y := mem_union.2 (Or.inl hzX)
        simpa [hcover] using this
      exact mem_sdiff.2 ⟨hzJ, fun hzP =>
        (mem_sdiff.1 hz).2 (mem_inter.2 ⟨hzP, hzX⟩)⟩
  have hXsub : X ⊆ L ∪ D := by
    intro z hz
    have : z ∈ X ∪ Y := mem_union.2 (Or.inl hz)
    simpa [hcover] using this
  have hXcog : Nikoghosyan.IsCograph G X :=
    isCograph_canonical_subset hJcog hXsub
  have hpXle : pathCoverNumber G X ≤ Y.card := by
    by_contra hgt
    have hle := pathCoverNumber_child_le_succ hXY (by simpa [hcover] using hpJ)
    have hpX : pathCoverNumber G X = Y.card + 1 := by omega
    have hF := ineligibleSet_complete_join_critical hXne hYne hXY hpX
    have hFne : (ineligibleSet G (X ∪ Y)).Nonempty :=
      hYne.mono fun z hz => by simpa [hF] using mem_union.2 (Or.inl hz)
    have hFempty : ineligibleSet G (L ∪ D) = ∅ :=
      ineligibleSet_eq_empty_of_eligibleSet_eq hE
    have : ineligibleSet G (X ∪ Y) = ∅ := by simpa [hcover] using hFempty
    exact hFne.ne_empty this
  have hgen := componentCount_sdiff_le (G := G) X (Px ∩ X) inter_subset_right
  have hcXZ : componentCount G (X \ (Px ∩ X)) = Px.card := by
    simpa [hJP] using hcut
  have hpX : pathCoverNumber G X = Y.card := by omega
  have hatt : componentCount G (X \ (Px ∩ X)) =
      pathCoverNumber G X + (Px ∩ X).card := by omega
  have hZinF : Px ∩ X ⊆ ineligibleSet G X :=
    (ineligibleSet_is_largest_attaining_cut_of_canonical hXcog).2.1
      (Px ∩ X) inter_subset_right hatt
  have hX2 : 2 ≤ X.card := by
    have hle := card_le_card hWP
    have hge :=
      (componentCount_le_pathCoverNumber (G := G) ((L ∪ D) \ Px)).trans
        (pathCoverNumber_le_card (G := G) ((L ∪ D) \ Px))
    omega
  have ⟨y, hy⟩ := hYne
  have hQ :
      rNonadjClass (G := G) (X ∪ Y) y = Y ∪ ineligibleSet G X :=
    rNonadjClass_eq_side_union_ineligible hXne hYne hXY hpX
      (by simpa [hcover] using hpJ) (by simpa [hcover] using hE)
      (by simpa [hcover] using hJcog) hy hX2
  have hyJ : y ∈ L ∪ D := by
    have : y ∈ X ∪ Y := mem_union.2 (Or.inr hy)
    simpa [hcover] using this
  have hyP : y ∈ Px := hYP hy
  have hcl : rNonadjClass (G := G) (L ∪ D) h =
      rNonadjClass (G := G) (L ∪ D) y :=
    (hbal.2.2 hhJ hyJ).2 (by simpa [hPxeq] using hyP)
  have hPxF : Px = Y ∪ ineligibleSet G X := by
    calc
      Px = rNonadjClass (G := G) (L ∪ D) h := hPxeq
      _ = rNonadjClass (G := G) (L ∪ D) y := hcl
      _ = rNonadjClass (G := G) (X ∪ Y) y := by simpa [hcover]
      _ = Y ∪ ineligibleSet G X := hQ
  have hPXF : Px ∩ X = ineligibleSet G X := by
    ext z
    constructor
    · intro hz
      have hzP := (mem_inter.1 hz).1
      have hzX := (mem_inter.1 hz).2
      have : z ∈ Y ∪ ineligibleSet G X := by simpa [hPxF] using hzP
      rcases mem_union.1 this with hzY | hzF
      · exact (Finset.disjoint_left.1 hdisjXY hzX hzY).elim
      · exact hzF
    · intro hzF
      have hzP : z ∈ Px := by
        have : z ∈ Y ∪ ineligibleSet G X := mem_union.2 (Or.inr hzF)
        simpa [hPxF] using this
      exact mem_inter.2 ⟨hzP, ineligibleSet_subset (G := G) X hzF⟩
  obtain ⟨hcLP, hnocrossDL, hdecomp⟩ :=
    D_component_of_Px_subset_L hLD c hc pL hpLsup hs hf huv huP hvP hPL hPge hcut
  have hDne : D.Nonempty := by
    have h3 : 3 ≤ D.card := by simpa [hc] using c.three_le_card_support
    exact card_pos.1 (le_trans (by decide : (1 : ℕ) ≤ 3) h3)
  have hconnD : (G.induce (D : Set V)).Connected := by
    obtain ⟨q, hq, _⟩ := GraphCycle.exists_spanning_path c
    exact connected_of_spanning_path q (hq.trans hc)
  have hDX : D ⊆ X := by
    intro z hzD
    have hzW : z ∈ (L ∪ D) \ Px :=
      mem_sdiff.2 ⟨mem_union.2 (Or.inr hzD), fun hzP =>
        (Finset.disjoint_left.1 hLD (hPL hzP) hzD).elim⟩
    exact hWP hzW
  have hDF : D ⊆ X \ ineligibleSet G X := by
    intro z hzD
    have hzJP : z ∈ (L ∪ D) \ Px :=
      mem_sdiff.2 ⟨mem_union.2 (Or.inr hzD), fun hzP =>
        (Finset.disjoint_left.1 hLD (hPL hzP) hzD).elim⟩
    have : z ∈ X \ (Px ∩ X) := by simpa [hJP] using hzJP
    simpa [hPXF] using this
  have hrest : (X \ ineligibleSet G X) \ D = L \ Px := by
    have hXF : X \ ineligibleSet G X = (L ∪ D) \ Px := by
      simpa [hPXF] using hJP.symm
    rw [hXF, hdecomp]
    ext z
    constructor
    · intro hz
      have hzU := (mem_sdiff.1 hz).1
      have hzD := (mem_sdiff.1 hz).2
      rcases mem_union.1 hzU with hzL | hzD'
      · exact hzL
      · exact (hzD hzD').elim
    · intro hz
      exact mem_sdiff.2 ⟨mem_union.2 (Or.inl hz), fun hzD =>
        (Finset.disjoint_left.1 hLD (mem_sdiff.1 hz).1 hzD).elim⟩
  have ⟨d, hdD⟩ := hDne
  have hpXD :=
    pathCoverNumber_sdiff_of_traceable_component (X := X) (D := D)
      hXcog hDF hDne hconnD (by simpa [hrest] using hnocrossDL) hdD
  have hid :=
    (ineligibleSet_is_largest_attaining_cut_of_canonical hXcog).1
  have hXDsplit : X \ D =
      ((X \ ineligibleSet G X) \ D) ∪ ineligibleSet G X := by
    ext z
    constructor
    · intro hz
      have hzX := (mem_sdiff.1 hz).1
      have hzD := (mem_sdiff.1 hz).2
      by_cases hzF : z ∈ ineligibleSet G X
      · exact mem_union.2 (Or.inr hzF)
      · exact mem_union.2
          (Or.inl (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hzX, hzF⟩, hzD⟩))
    · intro hz
      rcases mem_union.1 hz with hXF | hF
      · exact mem_sdiff.2 ⟨(mem_sdiff.1 (mem_sdiff.1 hXF).1).1,
          (mem_sdiff.1 hXF).2⟩
      · exact mem_sdiff.2 ⟨ineligibleSet_subset (G := G) X hF, fun hzD =>
          (mem_sdiff.1 (hDF hzD)).2 hF⟩
  have hdisjRestF :
      Disjoint ((X \ ineligibleSet G X) \ D) (ineligibleSet G X) := by
    refine Finset.disjoint_left.2 ?_
    intro z hzRest hzF
    exact (mem_sdiff.1 (mem_sdiff.1 hzRest).1).2 hzF
  have hcardXD : (X \ D).card =
      ((X \ ineligibleSet G X) \ D).card + (ineligibleSet G X).card := by
    rw [hXDsplit, card_union_of_disjoint hdisjRestF]
  have hcRest : componentCount G ((X \ ineligibleSet G X) \ D) =
      Px.card - 1 := by simpa [hrest] using hcLP
  have hgeRest :=
    (componentCount_le_pathCoverNumber (G := G)
      ((X \ ineligibleSet G X) \ D)).trans
      (pathCoverNumber_le_card (G := G) ((X \ ineligibleSet G X) \ D))
  have hcardP' : Px.card = Y.card + (ineligibleSet G X).card := by
    simpa [hPXF] using hcardP
  have hXDge : Y.card + 2 * (ineligibleSet G X).card - 1 ≤ (X \ D).card := by
    have hpos : 1 ≤ Px.card := by omega
    omega
  have hLsplit : (X \ D) ∪ Y = L := by
    have hLD' : L = (L ∪ D) \ D := by
      ext z
      constructor
      · intro hzL
        exact mem_sdiff.2 ⟨mem_union.2 (Or.inl hzL), fun hzD =>
          (Finset.disjoint_left.1 hLD hzL hzD).elim⟩
      · intro hz
        have hzJ := (mem_sdiff.1 hz).1
        have hzD := (mem_sdiff.1 hz).2
        rcases mem_union.1 hzJ with hzL | hzD'
        · exact hzL
        · exact (hzD hzD').elim
    have hXYD : (X ∪ Y) \ D = (X \ D) ∪ Y := by
      ext z
      constructor
      · intro hz
        have hzXY := (mem_sdiff.1 hz).1
        have hzD := (mem_sdiff.1 hz).2
        rcases mem_union.1 hzXY with hzX | hzY
        · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzX, hzD⟩))
        · exact mem_union.2 (Or.inr hzY)
      · intro hz
        rcases mem_union.1 hz with hzX | hzY
        · exact mem_sdiff.2 ⟨mem_union.2 (Or.inl (mem_sdiff.1 hzX).1),
            (mem_sdiff.1 hzX).2⟩
        · have hzD : z ∉ D := fun h =>
            (Finset.disjoint_left.1 hdisjXY (hDX h) hzY).elim
          exact mem_sdiff.2 ⟨mem_union.2 (Or.inr hzY), hzD⟩
    calc
      (X \ D) ∪ Y = (X ∪ Y) \ D := hXYD.symm
      _ = (L ∪ D) \ D := by rw [hcover]
      _ = L := hLD'.symm
  have hXDY :
      G.IsCompleteBetween ((X \ D : Finset V) : Set V) (Y : Set V) :=
    isCompleteBetween_mono (A := X) (A' := X \ D) (B := Y) (B' := Y)
      hXY sdiff_subset (fun _ hy => hy)
  have hXDne : (X \ D).Nonempty := by
    have : 1 ≤ (X \ D).card := by
      have hposP : 1 ≤ Px.card := by omega
      omega
    exact card_pos.1 this
  have hpXDle : pathCoverNumber G (X \ D) ≤ Y.card := by omega
  have hunionY : Y ∪ (X \ D) = L := by rw [union_comm, hLsplit]
  have hhEL : h ∈ eligibleSet G L := by
    by_cases hfpos : 1 ≤ (ineligibleSet G X).card
    · have hpY : pathCoverNumber G Y ≤ (X \ D).card :=
        (pathCoverNumber_le_card (G := G) Y).trans (by
          have hn : Y.card + 2 * (ineligibleSet G X).card ≤
              (X \ D).card + 1 := by
            have hpos : 1 ≤ Y.card + 2 * (ineligibleSet G X).card := by omega
            omega
          omega)
      have hEL :=
        eligibleSet_complete_join_balanced hXDne hYne hXDY hpXDle hpY
      have hEeq : eligibleSet G L = L := by simpa [hLsplit] using hEL
      simpa [hEeq] using hhL
    · have hf0 : ineligibleSet G X = ∅ :=
        card_eq_zero.1 (by omega)
      have hPeqY : Px = Y := by simpa [hf0, union_empty] using hPxF
      by_cases hYcrit : pathCoverNumber G Y = (X \ D).card + 1
      · have hpYle := pathCoverNumber_le_card (G := G) Y
        have hpYeq : pathCoverNumber G Y = Y.card := by
          have hF0 : (ineligibleSet G X).card = 0 := by simp [hf0]
          omega
        have hEY : eligibleSet G Y = Y :=
          eligibleSet_eq_of_pathCoverNumber_eq_card hpYeq
        have hEjoin :=
          eligibleSet_complete_join_critical hYne hXDne
            (isCompleteBetween_symm hXDY) hYcrit
        have hEeq : eligibleSet G L = Y := by
          simpa [hunionY, hEY] using hEjoin
        have hhY : h ∈ Y := by simpa [hPeqY] using hhP
        simpa [hEeq] using hhY
      · have hpY :=
          pathCoverNumber_child_le_of_not_crit
            (A := Y) (B := X \ D) (isCompleteBetween_symm hXDY)
            (by simpa [hunionY] using hpL) hYcrit
        have hEL :=
          eligibleSet_complete_join_balanced hXDne hYne hXDY hpXDle hpY
        have hEeq : eligibleSet G L = L := by simpa [hLsplit] using hEL
        simpa [hEeq] using hhL
  exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2
    ((mem_eligibleSet_iff (G := G)).1 hhEL).2

lemma false_of_balanced_common_class
    {L D : Finset V} {h u v : V}
    (c : GraphCycle G) (pL : GraphPath G)
    (hLD : Disjoint L D) (hc : c.support = D)
    (hJcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hpL : pathCoverNumber G L = 1)
    (hpJ : pathCoverNumber G (L ∪ D) = 1)
    (hhF : h ∈ ineligibleSet G L)
    (hpLsup : pL.support = L) (hs : pL.start = u) (hf : pL.finish = v)
    (hbal : IsBalancedEndpoints (G := G) (L ∪ D))
    (hclass_u : rNonadjClass (G := G) (L ∪ D) h =
        rNonadjClass (G := G) (L ∪ D) u)
    (hclass_v : rNonadjClass (G := G) (L ∪ D) h =
        rNonadjClass (G := G) (L ∪ D) v) :
    False := by
  have hE : eligibleSet G (L ∪ D) = L ∪ D := hbal.1
  have hL3 : 3 ≤ L.card := three_le_card_of_mem_ineligible hhF hpL
  have hhL : h ∈ L := ineligibleSet_subset (G := G) L hhF
  have huL : u ∈ L := by simpa [hpLsup, hs] using pL.start_mem_support
  have hvL : v ∈ L := by simpa [hpLsup, hf] using pL.finish_mem_support
  have hhJ : h ∈ L ∪ D := mem_union.2 (Or.inl hhL)
  have huJ : u ∈ L ∪ D := mem_union.2 (Or.inl huL)
  have hvJ : v ∈ L ∪ D := mem_union.2 (Or.inl hvL)
  have huv : u ≠ v := by
    intro heq
    have hnil : pL.walk.Nil :=
      (GraphPath.nil_iff_start_eq_finish pL).2 (by simp [hs, hf, heq])
    have hsing : pL.support = {pL.start} :=
      GraphPath.support_eq_singleton_of_nil pL hnil
    have hLcard : L.card = 1 := by
      calc
        L.card = pL.support.card := by rw [hpLsup]
        _ = ({pL.start} : Finset V).card := by rw [hsing]
        _ = 1 := Finset.card_singleton _
    omega
  have hhu : h ≠ u := by
    intro heq
    have hEend := Eligible_of_support_ends pL hpLsup
    have hEu : Eligible G L u := by simpa [hs] using hEend.1
    exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2 (heq ▸ hEu)
  have hhv : h ≠ v := by
    intro heq
    have hEend := Eligible_of_support_ends pL hpLsup
    have hEv : Eligible G L v := by simpa [hf] using hEend.2
    exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2 (heq ▸ hEv)
  let Px := rNonadjClass (G := G) (L ∪ D) h
  have hhP : h ∈ Px := mem_rNonadjClass_self hhJ
  have huP : u ∈ Px := (hbal.2.2 hhJ huJ).1 hclass_u
  have hvP : v ∈ Px := (hbal.2.2 hhJ hvJ).1 hclass_v
  have hPx : Px ⊆ L ∪ D := rNonadjClass_subset (G := G) (L ∪ D) h
  have hcut : componentCount G ((L ∪ D) \ Px) = Px.card :=
    partCut_of_balanced hbal hhJ
  have hPge3 : 3 ≤ Px.card :=
    three_le_card_of_three_mem hhP huP hvP hhu hhv huv
  have hPge : 2 ≤ Px.card := le_trans (by decide : (2 : ℕ) ≤ 3) hPge3
  have hPL : Px ⊆ L :=
    Px_subset_L_of_partCut hLD c hc pL hpLsup hs hf huv huP hvP hPx hcut
  have hJ2 : 2 ≤ (L ∪ D).card := two_le_card_of_union_cycle (L := L) c hc
  have hconnJ := connected_of_pathCoverNumber_eq_one (G := G) hpJ
  have hJst : IsCograph G (L ∪ D) := isCograph_iff.2 hJcog
  obtain ⟨A0, B0, _, _, hA0ne, hB0ne, _, hcover0, hAB0, _, _⟩ :=
    exists_complete_join_on hJst hconnJ hJ2
  have hW : (L ∪ D) \ Px ⊆ A0 ∪ B0 := by
    intro z hz
    have hzJ := (mem_sdiff.1 hz).1
    simpa [hcover0] using hzJ
  have hW2 : 2 ≤ componentCount G ((L ∪ D) \ Px) := by
    simpa [hcut] using hPge
  have hside := subset_join_side_of_disconnected hAB0 hW hW2
  rcases hside with hWA | hWB
  · exact false_of_balanced_join_child c pL hLD hc hcover0 hA0ne hB0ne hAB0
      hJcog hpL hpJ hE hhF hpLsup hs hf huv hbal rfl hhP huP hvP hPL hPge
      hcut hWA
  · exact false_of_balanced_join_child c pL hLD hc
      (by simpa [union_comm] using hcover0) hB0ne hA0ne
      (isCompleteBetween_symm hAB0) hJcog hpL hpJ hE hhF hpLsup hs hf huv
      hbal rfl hhP huP hvP hPL hPge hcut hWB

theorem traceable_release {L D : Finset V} {h u v : V}
    (c : GraphCycle G)
    (pL : GraphPath G)
    (hLD : Disjoint L D)
    (hc : c.support = D)
    (hJcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hLcog : Nikoghosyan.IsCograph G L)
    (hp : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hpL : pathCoverNumber G L = 1)
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hpLsup : pL.support = L) (hs : pL.start = u) (hf : pL.finish = v) :
    ((∃ Q : GraphPath G, Q.support = L ∪ D ∧ Q.start = h ∧ Q.finish = u) ∨
      (∃ Q : GraphPath G, Q.support = L ∪ D ∧ Q.start = h ∧ Q.finish = v)) ∧
      3 ≤ L.card := by
  have hL3 : 3 ≤ L.card := three_le_card_of_mem_ineligible hhF hpL
  refine ⟨?_, hL3⟩
  have hpJ : pathCoverNumber G (L ∪ D) = 1 := by omega
  have hJ2 : 2 ≤ (L ∪ D).card := two_le_card_of_union_cycle (L := L) c hc
  have hconnJ := connected_of_pathCoverNumber_eq_one (G := G) hpJ
  have hdata :=
    hamilton_endpoints_of_traceable_cograph_canonical hJ2 hJcog hconnJ hpJ
  have hhL : h ∈ L := ineligibleSet_subset (G := G) L hhF
  have huL : u ∈ L := by simpa [hpLsup, hs] using pL.start_mem_support
  have hvL : v ∈ L := by simpa [hpLsup, hf] using pL.finish_mem_support
  have hhJ : h ∈ L ∪ D := mem_union.2 (Or.inl hhL)
  have huJ : u ∈ L ∪ D := mem_union.2 (Or.inl huL)
  have hvJ : v ∈ L ∪ D := mem_union.2 (Or.inl hvL)
  rcases hdata with hcrit | hbal
  · obtain ⟨X, Y, hXne, hYne, hcover, hXY, hcritXY, hXst, _, _, _, _⟩ := hcrit
    have hXcog : Nikoghosyan.IsCograph G X := isCograph_iff.1 hXst
    have hcover' : X ∪ Y = L ∪ D := hcover
    exact traceable_release_of_critical c pL hLD hc hcover' hXne hYne hXY
      hcritXY hJcog hLcog hXcog hp hpL hhF hhE hpLsup hs hf
  · by_cases hhu : rNonadjClass (G := G) (L ∪ D) h =
        rNonadjClass (G := G) (L ∪ D) u
    · by_cases hhv : rNonadjClass (G := G) (L ∪ D) h =
          rNonadjClass (G := G) (L ∪ D) v
      · exact (false_of_balanced_common_class c pL hLD hc hJcog hpL hpJ hhF
          hpLsup hs hf hbal hhu hhv).elim
      · have hR : SpanningPathCompatible (G := G) (L ∪ D) h v :=
          spanningPath_of_distinct_classes hbal hhJ hvJ hhv
        obtain ⟨Q, hQ, hsQ, hfQ⟩ := exists_oriented_spanning hR
        exact Or.inr ⟨Q, hQ, hsQ, hfQ⟩
    · have hR : SpanningPathCompatible (G := G) (L ∪ D) h u :=
        spanningPath_of_distinct_classes hbal hhJ huJ hhu
      obtain ⟨Q, hQ, hsQ, hfQ⟩ := exists_oriented_spanning hR
      exact Or.inl ⟨Q, hQ, hsQ, hfQ⟩

end Cograph
end Nikoghosyan
