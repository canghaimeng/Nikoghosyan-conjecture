/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.HamiltonBalanced
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Large-port classification of Hamiltonian cograph blocks

Manuscript `all:thm:all-cograph`, first classification: if two distinct
actual R-classes of a Hamiltonian cograph block have size at least two,
the block is an original `K_{m,m}` whose sides are exactly the R-classes.
Equivalently, outside that case at most one actual class is nonsingleton.

Root children are the connected components of the complement of the
induced block. The bound `p(X) ≤ r` uses the checked binary join
recurrence together with the critical identity `E(U) = E(X)`, not a
new cycle-segment count. The identity `rNonadjClass = Q_x` is exported
for every Hamiltonian cograph of order at least three.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Original-edge path on a single edge `a b`. -/
def edgePath {a b : V} (h : G.Adj a b) : GraphPath G :=
  let p := GraphPath.singleton (G := G) b
  have hs : p.start = b := rfl
  have hadj : G.Adj a p.start := by simpa [hs] using h
  have hmem : a ∉ p.support := by
    simp [p, GraphPath.support_singleton, h.ne]
  p.consAdj hadj hmem

lemma support_edgePath {a b : V} (h : G.Adj a b) :
    (edgePath h).support = {a, b} := by
  simp [edgePath, GraphPath.support_consAdj, GraphPath.support_singleton]

/-- Cover of `U` by the original edge `ab` together with singletons of the
remaining vertices. Cardinality is `|U| - 1`. -/
noncomputable def edgeSingletonsCover {U : Finset V} {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) (hadj : G.Adj a b) : PathCover G U where
  paths := edgePath hadj ::
    ((U.erase a).erase b).toList.map GraphPath.singleton
  disjoint := by
    rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro q hq
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
      have hzU : z ∈ (U.erase a).erase b := mem_toList.1 hz
      have hza : z ≠ a := (mem_erase.1 (mem_of_mem_erase hzU)).1
      have hzb : z ≠ b := (mem_erase.1 hzU).1
      refine Finset.disjoint_left.2 ?_
      intro w hw1 hw2
      have hwz : w = z := by simpa [GraphPath.support_singleton] using hw2
      have hwa : w = a ∨ w = b := by
        simpa [support_edgePath] using hw1
      rcases hwa with rfl | rfl
      · exact hza hwz.symm
      · exact hzb hwz.symm
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ ((U.erase a).erase b).nodup_toList
      intro u v hne
      change Disjoint {u} {v}
      rw [disjoint_iff_inter_eq_empty]
      simp [hne]
  mem_iff := by
    intro w
    constructor
    · intro hw
      by_cases hwa : w = a
      · refine ⟨edgePath hadj, List.mem_cons.2 (Or.inl rfl), ?_⟩
        simp [support_edgePath, hwa]
      · by_cases hwb : w = b
        · refine ⟨edgePath hadj, List.mem_cons.2 (Or.inl rfl), ?_⟩
          simp [support_edgePath, hwb]
        · refine ⟨GraphPath.singleton w,
            List.mem_cons.2 (Or.inr (List.mem_map.2
              ⟨w, mem_toList.2 (mem_erase.2 ⟨hwb, mem_erase.2 ⟨hwa, hw⟩⟩), rfl⟩)),
            by simp⟩
    · intro ⟨p, hp, hwp⟩
      rcases List.mem_cons.1 hp with rfl | hp'
      · have hwab : w ∈ ({a, b} : Finset V) := by
          simpa [support_edgePath] using hwp
        rcases mem_insert.1 hwab with rfl | hw'
        · exact ha
        · simpa using (mem_singleton.1 hw').symm ▸ hb
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp'
        have hw' : w = z := by simpa using hwp
        subst hw'
        exact mem_of_mem_erase (mem_of_mem_erase (mem_toList.1 hz))

lemma edgeSingletonsCover_card {U : Finset V} {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) (hadj : G.Adj a b) :
    (edgeSingletonsCover (G := G) ha hb hadj).card = U.card - 1 := by
  have hne : a ≠ b := hadj.ne
  have hb' : b ∈ U.erase a := mem_erase.2 ⟨hne.symm, hb⟩
  have h2 : 2 ≤ U.card := by
    have hsub : ({a, b} : Finset V) ⊆ U :=
      insert_subset_iff.2 ⟨ha, singleton_subset_iff.2 hb⟩
    have hcard : ({a, b} : Finset V).card = 2 := by
      rw [card_insert_of_notMem (by simp [hne])]
      simp
    have := card_le_card hsub
    omega
  simp [edgeSingletonsCover, PathCover.card, card_erase_of_mem hb',
    card_erase_of_mem ha]
  omega

lemma pathCoverNumber_le_card_sub_one_of_adj {U : Finset V} {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) (hadj : G.Adj a b) :
    pathCoverNumber G U ≤ U.card - 1 :=
  (pathCoverNumber_le (G := G)
    (edgeSingletonsCover (G := G) ha hb hadj)).trans_eq
    (edgeSingletonsCover_card (G := G) ha hb hadj)

lemma not_adj_of_pathCoverNumber_eq_card {U : Finset V}
    (h : pathCoverNumber G U = U.card) {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) : ¬ G.Adj a b := by
  intro hadj
  have hle := pathCoverNumber_le_card_sub_one_of_adj (G := G) ha hb hadj
  have hpos : 1 ≤ U.card := Nat.succ_le_of_lt (card_pos.2 ⟨a, ha⟩)
  omega

lemma eligible_of_singletons_min {U : Finset V} {x : V} (hx : x ∈ U)
    (hmin : (PathCover.singletons (G := G) U).card = pathCoverNumber G U) :
    Eligible G U x := by
  refine ⟨PathCover.singletons (G := G) U, hmin, GraphPath.singleton x, ?_, Or.inl rfl⟩
  exact List.mem_map.2 ⟨x, mem_toList.2 hx, rfl⟩

lemma ineligibleSet_eq_empty_of_pathCoverNumber_eq_card {U : Finset V}
    (h : pathCoverNumber G U = U.card) :
    ineligibleSet G U = ∅ := by
  have hmin : (PathCover.singletons (G := G) U).card = pathCoverNumber G U := by
    simpa [PathCover.singletons_card] using h.symm
  ext z
  constructor
  · intro hz
    have hzU : z ∈ U := ineligibleSet_subset (G := G) U hz
    have hE : Eligible G U z := eligible_of_singletons_min hzU hmin
    exact (Finset.disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) U)
      ((mem_eligibleSet_iff (G := G)).2 ⟨hzU, hE⟩) hz).elim
  · intro hz
    exact (notMem_empty z hz).elim

lemma nonempty_of_two_le_componentCount {U : Finset V}
    (h : 2 ≤ componentCount G U) : U.Nonempty := by
  by_contra hne
  have : U = ∅ := not_nonempty_iff_eq_empty.1 hne
  subst this
  simp [componentCount_empty] at h

/-! ## Root children: components of the induced complement -/

/-- Complement of the induced block graph on `U`. -/
abbrev complInduce (U : Finset V) : SimpleGraph (U : Set V) :=
  (G.induce (U : Set V))ᶜ

/-- Component of `x` in the complement of `G[U]`. -/
noncomputable def rootComp (U : Finset V) {x : V} (hx : x ∈ U) :
    (complInduce (G := G) U).ConnectedComponent :=
  (complInduce (G := G) U).connectedComponentMk ⟨x, hx⟩

lemma rootComp_eq {U : Finset V} {x : V} (hx hy : x ∈ U) :
    rootComp (G := G) U hx = rootComp (G := G) U hy := by
  simp [rootComp]

/-- Original-vertex set of one complement-component of `G[U]`. -/
noncomputable def rootChild (U : Finset V)
    (C : (complInduce (G := G) U).ConnectedComponent) : Finset V :=
  U.filter fun x => ∃ hx : x ∈ U, rootComp (G := G) U hx = C

lemma mem_rootChild_iff {U : Finset V} {x : V}
    {C : (complInduce (G := G) U).ConnectedComponent} :
    x ∈ rootChild (G := G) U C ↔ ∃ hx : x ∈ U, rootComp (G := G) U hx = C := by
  constructor
  · intro hx
    exact (mem_filter.1 hx).2
  · intro ⟨hx, hC⟩
    exact mem_filter.2 ⟨hx, ⟨hx, hC⟩⟩

lemma rootChild_subset (U : Finset V)
    (C : (complInduce (G := G) U).ConnectedComponent) :
    rootChild (G := G) U C ⊆ U :=
  filter_subset _ _

lemma mem_rootChild_self {U : Finset V} {x : V} (hx : x ∈ U) :
    x ∈ rootChild (G := G) U (rootComp (G := G) U hx) :=
  mem_rootChild_iff.2 ⟨hx, rfl⟩

lemma rootChild_nonempty (U : Finset V)
    (C : (complInduce (G := G) U).ConnectedComponent) :
    (rootChild (G := G) U C).Nonempty := by
  refine ⟨C.out.val, mem_rootChild_iff.2 ⟨C.out.property, ?_⟩⟩
  simp [rootComp]
  exact Quot.out_eq C

lemma disjoint_rootChild {U : Finset V}
    {C D : (complInduce (G := G) U).ConnectedComponent} (hCD : C ≠ D) :
    Disjoint (rootChild (G := G) U C) (rootChild (G := G) U D) := by
  rw [Finset.disjoint_left]
  intro x hxC hxD
  obtain ⟨hx, hC⟩ := mem_rootChild_iff.1 hxC
  obtain ⟨hx', hD⟩ := mem_rootChild_iff.1 hxD
  have : C = D := hC.symm.trans ((rootComp_eq (G := G) hx hx').trans hD)
  exact hCD this

lemma adj_of_mem_distinct_rootChild {U : Finset V}
    {C D : (complInduce (G := G) U).ConnectedComponent} (hCD : C ≠ D)
    {x y : V}
    (hx : x ∈ rootChild (G := G) U C)
    (hy : y ∈ rootChild (G := G) U D) :
    G.Adj x y := by
  obtain ⟨hxU, hC⟩ := mem_rootChild_iff.1 hx
  obtain ⟨hyU, hD⟩ := mem_rootChild_iff.1 hy
  have hne : x ≠ y := by
    intro hxy
    subst hxy
    exact hCD (hC.symm.trans ((rootComp_eq (G := G) hxU hyU).trans hD))
  by_contra hna
  have hadj : (complInduce (G := G) U).Adj ⟨x, hxU⟩ ⟨y, hyU⟩ := by
    simp [complInduce, compl_adj, induce_adj, hne, hna]
  have heq : rootComp (G := G) U hxU = rootComp (G := G) U hyU :=
    ConnectedComponent.sound (Adj.reachable hadj)
  exact hCD (hC.symm.trans (heq.trans hD))

lemma adj_mem_rootChild_not_mem {U : Finset V}
    {C : (complInduce (G := G) U).ConnectedComponent} {x y : V}
    (hx : x ∈ rootChild (G := G) U C) (hy : y ∈ U)
    (hyC : y ∉ rootChild (G := G) U C) : G.Adj x y := by
  have hCy := mem_rootChild_self (G := G) hy
  have hCD : C ≠ rootComp (G := G) U hy := by
    intro heq
    exact hyC (by simpa [heq] using hCy)
  exact adj_of_mem_distinct_rootChild (G := G)
    (C := C) (D := rootComp (G := G) U hy) hCD hx hCy

lemma isCompleteBetween_rootChildren {U : Finset V}
    {C D : (complInduce (G := G) U).ConnectedComponent} (hCD : C ≠ D) :
    G.IsCompleteBetween
      (rootChild (G := G) U C : Set V)
      (rootChild (G := G) U D : Set V) :=
  fun {_} hx {_} hy => adj_of_mem_distinct_rootChild (G := G) hCD hx hy

/-- A complement-walk that starts in a complete-join side stays in that side. -/
lemma mem_left_of_compl_walk {U A B : Finset V}
    (hunion : A ∪ B = U)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    {x y : (U : Set V)} (hx : x.val ∈ A) :
    (complInduce (G := G) U).Walk x y → y.val ∈ A
  | .nil => hx
  | .cons (v := mid) hadj p => by
      have hcompl : x.val ≠ mid.val ∧ ¬ G.Adj x.val mid.val := by
        simpa [complInduce, compl_adj, induce_adj] using hadj
      have hmidU : mid.val ∈ U := mid.property
      have hmidA : mid.val ∈ A := by
        have : mid.val ∈ A ∪ B := by simpa [hunion] using hmidU
        rcases mem_union.1 this with hA | hB
        · exact hA
        · exact (hcompl.2 (hAB hx hB)).elim
      exact mem_left_of_compl_walk hunion hAB hmidA p

lemma mem_left_of_compl_reachable {U A B : Finset V}
    (hunion : A ∪ B = U)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    {x y : (U : Set V)} (hx : x.val ∈ A)
    (hreach : (complInduce (G := G) U).Reachable x y) :
    y.val ∈ A :=
  mem_left_of_compl_walk hunion hAB hx (Classical.choice hreach)

lemma exists_two_rootChildren {U : Finset V}
    (hcog : IsCograph G U)
    (hconn : (G.induce (U : Set V)).Connected)
    (h2 : 2 ≤ U.card) :
    ∃ (C D : (complInduce (G := G) U).ConnectedComponent), C ≠ D := by
  obtain ⟨A, B, hAU, hBU, hAne, hBne, hdisj, hcover, hAB, _, _⟩ :=
    exists_complete_join_on hcog hconn h2
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  have haU : a ∈ U := hAU ha
  have hbU : b ∈ U := hBU hb
  refine ⟨rootComp (G := G) U haU, rootComp (G := G) U hbU, ?_⟩
  intro heq
  have hreach :
      (complInduce (G := G) U).Reachable ⟨a, haU⟩ ⟨b, hbU⟩ :=
    ConnectedComponent.exact heq
  have hbA : b ∈ A :=
    mem_left_of_compl_reachable (G := G) hcover hAB ha hreach
  exact (Finset.disjoint_left.1 hdisj) hbA hb

lemma induce_connected_of_meets_two_rootChildren {U W : Finset V}
    (hW : W ⊆ U) (hWne : W.Nonempty)
    {C D : (complInduce (G := G) U).ConnectedComponent} (hCD : C ≠ D)
    {a b : V} (ha : a ∈ W) (hb : b ∈ W)
    (haC : a ∈ rootChild (G := G) U C)
    (hbD : b ∈ rootChild (G := G) U D) :
    (G.induce (W : Set V)).Connected := by
  haveI : Nonempty (W : Set V) := hWne.to_subtype
  refine (connected_iff _).2 ⟨?_, inferInstance⟩
  intro x y
  have hxU : x.val ∈ U := hW x.property
  have hyU : y.val ∈ U := hW y.property
  let Cx := rootComp (G := G) U hxU
  let Cy := rootComp (G := G) U hyU
  have hxC : x.val ∈ rootChild (G := G) U Cx := mem_rootChild_self hxU
  have hyC : y.val ∈ rootChild (G := G) U Cy := mem_rootChild_self hyU
  by_cases hxy : Cx = Cy
  · have hbridge :
        ∃ w : V, w ∈ W ∧ w ∉ rootChild (G := G) U Cx := by
      by_cases hCa : Cx = C
      · refine ⟨b, hb, ?_⟩
        intro hbC
        exact (Finset.disjoint_left.1 (disjoint_rootChild (G := G) hCD))
          (by simpa [hCa] using hbC) hbD
      · refine ⟨a, ha, ?_⟩
        intro haCx
        have : Cx = C := by
          obtain ⟨ha1, hC'⟩ := mem_rootChild_iff.1 haC
          obtain ⟨ha2, hCx⟩ := mem_rootChild_iff.1 haCx
          exact hCx.symm.trans ((rootComp_eq (G := G) ha2 ha1).trans hC')
        exact hCa this
    obtain ⟨w, hwW, hwnot⟩ := hbridge
    have hwU : w ∈ U := hW hwW
    have hwC : w ∈ rootChild (G := G) U (rootComp (G := G) U hwU) :=
      mem_rootChild_self hwU
    have hneC : rootComp (G := G) U hwU ≠ Cx := by
      intro heq
      exact hwnot (by simpa [heq] using hwC)
    have hadj_xw : G.Adj x.val w :=
      adj_mem_rootChild_not_mem hxC hwU hwnot
    have hadj_yw : G.Adj y.val w := by
      have hyCx : y.val ∈ rootChild (G := G) U Cx := by
        simpa [hxy] using hyC
      exact adj_mem_rootChild_not_mem hyCx hwU hwnot
    let w' : (W : Set V) := ⟨w, hwW⟩
    have hxw : (G.induce (W : Set V)).Adj x w' := by
      simpa [induce_adj] using hadj_xw
    have hyw : (G.induce (W : Set V)).Adj y w' := by
      simpa [induce_adj] using hadj_yw
    exact (Adj.reachable hxw).trans hyw.reachable.symm
  · have hadj : G.Adj x.val y.val :=
      adj_of_mem_distinct_rootChild (G := G) hxy hxC hyC
    exact Adj.reachable (by simpa [induce_adj] using hadj)

lemma exists_rootChild_superset {U W : Finset V}
    (hW : W ⊆ U) (hWne : W.Nonempty)
    (hcut : 2 ≤ componentCount G W) :
    ∃ C : (complInduce (G := G) U).ConnectedComponent,
      W ⊆ rootChild (G := G) U C := by
  let a := hWne.choose
  have ha : a ∈ W := hWne.choose_spec
  have haU : a ∈ U := hW ha
  refine ⟨rootComp (G := G) U haU, ?_⟩
  intro b hb
  have hbU : b ∈ U := hW hb
  have hsame : rootComp (G := G) U hbU = rootComp (G := G) U haU := by
    by_contra hne
    have hconn :
        (G.induce (W : Set V)).Connected :=
      induce_connected_of_meets_two_rootChildren hW hWne hne hb ha
        (mem_rootChild_self hbU) (mem_rootChild_self haU)
    have hone := componentCount_eq_one_of_connected hWne hconn
    omega
  simpa [hsame] using mem_rootChild_self (G := G) hbU

/-- For a large balanced part, survivors of `U \ P` lie in one root child `X`.
The second root child of the connected block makes `Y = U \ X` nonempty. -/
lemma exists_assigned_rootChild {U P : Finset V}
    (hPsub : P ⊆ U)
    (hcut : 2 ≤ componentCount G (U \ P))
    {C0 D0 : (complInduce (G := G) U).ConnectedComponent} (hCD : C0 ≠ D0) :
    ∃ (X : Finset V)
      (C : (complInduce (G := G) U).ConnectedComponent),
      X = rootChild (G := G) U C ∧
        (U \ P) ⊆ X ∧
          X ⊆ U ∧ X.Nonempty ∧
            (U \ X).Nonempty ∧
              (U \ X) ⊆ P ∧
                  U \ P = X \ (P ∩ X) ∧
                    P = (U \ X) ∪ (P ∩ X) ∧
                      Disjoint (U \ X) (P ∩ X) := by
  have hWne := nonempty_of_two_le_componentCount (G := G) hcut
  obtain ⟨C, hsup⟩ :=
    exists_rootChild_superset (G := G) (sdiff_subset (s := U) (t := P)) hWne hcut
  set X := rootChild (G := G) U C
  have hXU : X ⊆ U := rootChild_subset (G := G) U C
  have hXne : X.Nonempty := rootChild_nonempty (G := G) U C
  have hYne : (U \ X).Nonempty := by
    obtain ⟨u0, hu0⟩ := rootChild_nonempty (G := G) U C0
    obtain ⟨v0, hv0⟩ := rootChild_nonempty (G := G) U D0
    by_cases hC0 : C0 = C
    · refine ⟨v0, mem_sdiff.2 ⟨rootChild_subset (G := G) U D0 hv0, ?_⟩⟩
      intro hvX
      have hCD' : C ≠ D0 := by simpa [hC0] using hCD
      exact (Finset.disjoint_left.1 (disjoint_rootChild (G := G) hCD'))
        (by simpa [X] using hvX) hv0
    · refine ⟨u0, mem_sdiff.2 ⟨rootChild_subset (G := G) U C0 hu0, ?_⟩⟩
      intro huX
      exact (Finset.disjoint_left.1 (disjoint_rootChild (G := G) hC0))
        hu0 (by simpa [X] using huX)
  have hYsub : U \ X ⊆ P := by
    intro y hy
    have hyU : y ∈ U := (mem_sdiff.1 hy).1
    have hyX : y ∉ X := (mem_sdiff.1 hy).2
    by_contra hyP
    have : y ∈ U \ P := mem_sdiff.2 ⟨hyU, hyP⟩
    exact hyX (hsup this)
  have hdisj : Disjoint (U \ X) (P ∩ X) := by
    rw [Finset.disjoint_left]
    intro z hzY hzZ
    exact (mem_sdiff.1 hzY).2 (mem_of_mem_inter_right hzZ)
  have hPeq : P = (U \ X) ∪ (P ∩ X) := by
    ext z
    constructor
    · intro hzP
      have hzU : z ∈ U := hPsub hzP
      by_cases hzX : z ∈ X
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzP, hzX⟩))
      · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzU, hzX⟩))
    · intro hz
      rcases mem_union.1 hz with hzY | hzZ
      · exact hYsub hzY
      · exact mem_of_mem_inter_left hzZ
  have hWeq : U \ P = X \ (P ∩ X) := by
    ext z
    constructor
    · intro hz
      have hzP : z ∉ P := (mem_sdiff.1 hz).2
      have hzX : z ∈ X := hsup hz
      refine mem_sdiff.2 ⟨hzX, ?_⟩
      intro hzPX
      exact hzP (mem_of_mem_inter_left hzPX)
    · intro hz
      have hzX : z ∈ X := (mem_sdiff.1 hz).1
      have hzPX : z ∉ P ∩ X := (mem_sdiff.1 hz).2
      have hzU : z ∈ U := hXU hzX
      refine mem_sdiff.2 ⟨hzU, ?_⟩
      intro hzP
      exact hzPX (mem_inter.2 ⟨hzP, hzX⟩)
  exact ⟨X, C, rfl, hsup, hXU, hXne, hYne, hYsub, hWeq, hPeq, hdisj⟩

/-- Hamiltonian cograph: `rNonadjClass U x = Q_x`. Extension is used only
under full eligibility of the Hamiltonian parent together with an actual
smaller critical-or-balanced certificate. -/
lemma rNonadjClass_eq_qxSet_of_hamiltonian {U : Finset V} {x : V}
    (hcog : IsCograph G U) (cyc : GraphCycle G) (hc : cyc.support = U)
    (hx : x ∈ U) :
    rNonadjClass (G := G) U x = qxSet (G := G) U x := by
  have hport := hamiltonian_cograph_port hcog cyc hc
  have hEall := hport.1
  have h3 : 3 ≤ U.card := by simpa [hc] using cyc.three_le_card_support
  obtain ⟨p, hp, _⟩ := GraphCycle.exists_spanning_path cyc
  have hpU : pathCoverNumber G U = 1 :=
    pathCoverNumber_eq_one_of_support p (hp.trans hc)
  set K := U.erase x
  have hxE : Eligible G U x := by
    have : x ∈ eligibleSet G U := by simpa [hEall] using hx
    exact (mem_eligibleSet_iff (G := G)).1 this |>.2
  have hK2 : 2 ≤ K.card := by
    have : K.card = U.card - 1 := card_erase_of_mem hx
    omega
  have hKcog : IsCograph G K := hcog.subset (erase_subset x U)
  have hpKle : pathCoverNumber G K ≤ pathCoverNumber G U := by
    simpa [K] using pathCoverNumber_erase_le_of_eligible (G := G) hxE
  have hKne : K.Nonempty :=
    card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hK2)
  have hpKge := one_le_pathCoverNumber_of_nonempty (G := G) hKne
  have hpK : pathCoverNumber G K = 1 := by omega
  obtain ⟨pK, hpKsup⟩ :=
    exists_spanning_path_of_pathCoverNumber_eq_one (G := G) hpK
  have hKconn := connected_of_spanning_path pK hpKsup
  have hKdata :=
    hamilton_endpoints_of_traceable_cograph hK2 hKcog hKconn hpK
  exact rNonadjClass_eq_qxSet_of_extension hx fun y hy =>
    extension_iff_of_IH hx hy hKdata hpK hEall hpU

lemma pathCoverNumber_eq_of_assigned {U P : Finset V}
    (hcog : IsCograph G U) (cyc : GraphCycle G) (hc : cyc.support = U)
    (hPsub : P ⊆ U)
    (hPcut : componentCount G (U \ P) = P.card)
    (hP2 : 2 ≤ P.card)
    {C0 D0 : (complInduce (G := G) U).ConnectedComponent} (hCD : C0 ≠ D0)
    {X : Finset V} {C : (complInduce (G := G) U).ConnectedComponent}
    (hX : X = rootChild (G := G) U C)
    (hWP : U \ P ⊆ X)
    (hXU : X ⊆ U) (hXne : X.Nonempty)
    (hYne : (U \ X).Nonempty)
    (hYsub : U \ X ⊆ P)
    (hWeq : U \ P = X \ (P ∩ X))
    (hPeq : P = (U \ X) ∪ (P ∩ X))
    (hdisj : Disjoint (U \ X) (P ∩ X)) :
    pathCoverNumber G X = (U \ X).card := by
  set Y := U \ X
  set Z := P ∩ X
  have hunion : X ∪ Y = U := union_sdiff_of_subset hXU
  have hAB : G.IsCompleteBetween (X : Set V) (Y : Set V) := by
    intro x hx y hy
    have hxC : x ∈ rootChild (G := G) U C := by simpa [hX] using hx
    have hyU : y ∈ U := (mem_sdiff.1 hy).1
    have hyX : y ∉ X := (mem_sdiff.1 hy).2
    have hyC : y ∉ rootChild (G := G) U C := by
      intro hyC
      have : y ∈ X := by simpa [hX] using hyC
      exact hyX this
    exact adj_mem_rootChild_not_mem hxC hyU hyC
  have hr : Y.card = (U \ X).card := rfl
  have hge : Y.card ≤ pathCoverNumber G X := by
    have hZsub : Z ⊆ X := inter_subset_right
    have hcutZ : componentCount G (X \ Z) = Y.card + Z.card := by
      have hPc : P.card = Y.card + Z.card := by
        rw [hPeq, card_union_of_disjoint hdisj]
      have : componentCount G (U \ P) = P.card := hPcut
      simpa [hWeq, hPc] using this
    have hle := componentCount_sdiff_le (G := G) X Z hZsub
    have : Y.card + Z.card ≤ pathCoverNumber G X + Z.card := by
      simpa [hcutZ] using hle
    omega
  have hpU : pathCoverNumber G U = 1 := by
    obtain ⟨p, hp, _⟩ := GraphCycle.exists_spanning_path cyc
    exact pathCoverNumber_eq_one_of_support p (hp.trans hc)
  have hpU' : pathCoverNumber G (X ∪ Y) = 1 := by simpa [hunion] using hpU
  have hle := pathCoverNumber_child_le_succ (G := G) hAB hpU'
  have hnotcrit : pathCoverNumber G X ≠ Y.card + 1 := by
    intro hcrit
    have hE :=
      eligibleSet_complete_join_critical hXne hYne hAB hcrit
    have hEall : eligibleSet G U = U :=
      (hamiltonian_cograph_port hcog cyc hc).1
    obtain ⟨y, hyY⟩ := hYne
    have hyU : y ∈ U := (mem_sdiff.1 hyY).1
    have hyX : y ∉ X := (mem_sdiff.1 hyY).2
    have hyE : y ∈ eligibleSet G U := by simpa [hEall] using hyU
    have hyEX : y ∈ eligibleSet G X := by
      have hyU' : y ∈ eligibleSet G (X ∪ Y) := by simpa [hunion] using hyE
      simpa [hE] using hyU'
    exact hyX (eligibleSet_subset (G := G) X hyEX)
  have hle' : pathCoverNumber G X ≤ Y.card := by omega
  exact le_antisymm hle' hge

lemma union_erase_eq_erase {U A B : Finset V} {x : V}
    (hunion : A ∪ B = U) (hxA : x ∈ A) (hxB : x ∉ B) :
    B ∪ A.erase x = U.erase x := by
  ext z
  constructor
  · intro hz
    rcases mem_union.1 hz with hzB | hzA
    · exact mem_erase.2 ⟨fun hzx => hxB (hzx ▸ hzB), by
        have : z ∈ A ∪ B := mem_union.2 (Or.inr hzB)
        simpa [hunion] using this⟩
    · exact mem_erase.2 ⟨(mem_erase.1 hzA).1, by
        have : z ∈ A ∪ B := mem_union.2 (Or.inl (mem_erase.1 hzA).2)
        simpa [hunion] using this⟩
  · intro hz
    have hzx : z ≠ x := (mem_erase.1 hz).1
    have hzU : z ∈ U := (mem_erase.1 hz).2
    have hzAB : z ∈ A ∪ B := by simpa [hunion] using hzU
    rcases mem_union.1 hzAB with hzA | hzB
    · exact mem_union.2 (Or.inr (mem_erase.2 ⟨hzx, hzA⟩))
    · exact mem_union.2 (Or.inl hzB)

lemma eq_of_same_assigned_child {U : Finset V} {x y : V}
    (hbal : IsBalancedEndpoints (G := G) U)
    (hx : x ∈ U) (hy : y ∈ U)
    {Xx Xy : Finset V}
    (hYx : U \ Xx ⊆ rNonadjClass (G := G) U x)
    (hYy : U \ Xy ⊆ rNonadjClass (G := G) U y)
    (hYxne : (U \ Xx).Nonempty)
    (hEq : Xx = Xy) :
    rNonadjClass (G := G) U x = rNonadjClass (G := G) U y := by
  obtain ⟨z, hz⟩ := hYxne
  have hzPx : z ∈ rNonadjClass (G := G) U x := hYx hz
  have hzPy : z ∈ rNonadjClass (G := G) U y := by
    have : z ∈ U \ Xy := by simpa [hEq] using hz
    exact hYy this
  have hzU : z ∈ U := rNonadjClass_subset (G := G) U x hzPx
  have heqx : rNonadjClass (G := G) U x = rNonadjClass (G := G) U z :=
    (hbal.2.2 (x := x) (y := z) hx hzU).2 hzPx
  have heqy : rNonadjClass (G := G) U y = rNonadjClass (G := G) U z :=
    (hbal.2.2 (x := y) (y := z) hy hzU).2 hzPy
  exact heqx.trans heqy.symm

lemma large_port_classification {U : Finset V}
    (hcog : IsCograph G U) (cyc : GraphCycle G) (hc : cyc.support = U)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (hPx : 2 ≤ (rNonadjClass (G := G) U x).card)
    (hPy : 2 ≤ (rNonadjClass (G := G) U y).card)
    (hne : rNonadjClass (G := G) U x ≠ rNonadjClass (G := G) U y) :
    ∃ (A B : Finset V),
      A ∪ B = U ∧ Disjoint A B ∧
        A.card = B.card ∧ 2 ≤ A.card ∧
          (∀ a ∈ A, ∀ a' ∈ A, ¬ G.Adj a a') ∧
            (∀ b ∈ B, ∀ b' ∈ B, ¬ G.Adj b b') ∧
              G.IsCompleteBetween (A : Set V) (B : Set V) ∧
                rNonadjClass (G := G) U x = A ∧
                  rNonadjClass (G := G) U y = B ∧
                    (∀ z ∈ U,
                      rNonadjClass (G := G) U z = A ∨
                        rNonadjClass (G := G) U z = B) := by
  have hport := hamiltonian_cograph_port hcog cyc hc
  have hbal := hport.2.1
  have hEall := hport.1
  have h3 : 3 ≤ U.card := by simpa [hc] using cyc.three_le_card_support
  have h2 : 2 ≤ U.card := le_trans (by decide : (2 : ℕ) ≤ 3) h3
  obtain ⟨p0, hp0, _⟩ := GraphCycle.exists_spanning_path cyc
  have hpU : pathCoverNumber G U = 1 :=
    pathCoverNumber_eq_one_of_support p0 (hp0.trans hc)
  have hconn := connected_of_spanning_path p0 (hp0.trans hc)
  obtain ⟨C0, D0, hCD⟩ := exists_two_rootChildren hcog hconn h2
  set Px := rNonadjClass (G := G) U x
  set Py := rNonadjClass (G := G) U y
  have hPxsub : Px ⊆ U := rNonadjClass_subset (G := G) U x
  have hPysub : Py ⊆ U := rNonadjClass_subset (G := G) U y
  have hPxcut : componentCount G (U \ Px) = Px.card :=
    partCut_of_balanced hbal hx
  have hPycut : componentCount G (U \ Py) = Py.card :=
    partCut_of_balanced hbal hy
  have hPx2 : 2 ≤ componentCount G (U \ Px) := by simpa [hPxcut] using hPx
  have hPy2 : 2 ≤ componentCount G (U \ Py) := by simpa [hPycut] using hPy
  obtain ⟨Xx, Cx, hXx, hWPx, hXxU, hXxne, hYxne, hYxsub, hWeqx, hPeqx, hdisjx⟩ :=
    exists_assigned_rootChild (P := Px) hPxsub hPx2 hCD
  obtain ⟨Xy, Cy, hXy, hWPy, hXyU, hXyne, hYyne, hYysub, hWeqy, hPeqy, hdisjy⟩ :=
    exists_assigned_rootChild (P := Py) hPysub hPy2 hCD
  have hpXx :=
    pathCoverNumber_eq_of_assigned hcog cyc hc hPxsub hPxcut hPx hCD
      hXx hWPx hXxU hXxne hYxne hYxsub hWeqx hPeqx hdisjx
  have hpXy :=
    pathCoverNumber_eq_of_assigned hcog cyc hc hPysub hPycut hPy hCD
      hXy hWPy hXyU hXyne hYyne hYysub hWeqy hPeqy hdisjy
  have hXne : Xx ≠ Xy := by
    intro hEq
    exact hne (eq_of_same_assigned_child hbal hx hy hYxsub hYysub hYxne hEq)
  have hXxcard : (U \ Xx).card = pathCoverNumber G Xx := hpXx.symm
  have hXycard : (U \ Xy).card = pathCoverNumber G Xy := hpXy.symm
  have hleX : pathCoverNumber G Xx ≤ Xx.card := pathCoverNumber_le_card (G := G) Xx
  have hleY : pathCoverNumber G Xy ≤ Xy.card := pathCoverNumber_le_card (G := G) Xy
  have hnX : (U \ Xx).card + Xx.card = U.card := by
    have : Xx ⊆ U := hXxU
    exact (card_sdiff_add_card_eq_card this)
  have hnY : (U \ Xy).card + Xy.card = U.card :=
    card_sdiff_add_card_eq_card hXyU
  have hhalfX : U.card ≤ 2 * Xx.card := by omega
  have hhalfY : U.card ≤ 2 * Xy.card := by omega
  have hdisjXY : Disjoint Xx Xy := by
    have hCxy : Cx ≠ Cy := by
      intro hCeq
      apply hXne
      simp [hXx, hXy, hCeq]
    simpa [hXx, hXy] using disjoint_rootChild (G := G) hCxy
  have hsum : Xx.card + Xy.card ≤ U.card := by
    have hsub : Xx ∪ Xy ⊆ U := union_subset hXxU hXyU
    have := card_union_of_disjoint hdisjXY
    have hle := card_le_card hsub
    omega
  have hXeq : Xx.card = Xy.card := by omega
  have hpart : Xx ∪ Xy = U := by
    have hle' : U.card ≤ (Xx ∪ Xy).card := by
      have : (Xx ∪ Xy).card = Xx.card + Xy.card := card_union_of_disjoint hdisjXY
      omega
    have hsub : Xx ∪ Xy ⊆ U := union_subset hXxU hXyU
    exact eq_of_subset_of_card_le hsub (by omega)
  have hYy0 : U \ Xy = Xx := by
    have h1 : U \ Xy = (Xx ∪ Xy) \ Xy := by rw [hpart]
    have h2 : (Xx ∪ Xy) \ Xy = Xx \ Xy := union_sdiff_right Xx Xy
    have h3 : Xx \ Xy = Xx := sdiff_eq_self_iff_disjoint.2 hdisjXY
    exact h1.trans (h2.trans h3)
  have hm : 2 ≤ Xx.card := by
    have : (U \ Xy).card = Xx.card := by simpa [hYy0] using hpXy.symm
    omega
  have hnoX : ∀ a ∈ Xx, ∀ a' ∈ Xx, ¬ G.Adj a a' :=
    fun a ha a' ha' => not_adj_of_pathCoverNumber_eq_card (by omega) ha ha'
  have hnoY : ∀ b ∈ Xy, ∀ b' ∈ Xy, ¬ G.Adj b b' :=
    fun b hb b' hb' => not_adj_of_pathCoverNumber_eq_card (by omega) hb hb'
  have hCxy : Cx ≠ Cy := by
    intro hCeq
    apply hXne
    simp [hXx, hXy, hCeq]
  have hABxy : G.IsCompleteBetween (Xy : Set V) (Xx : Set V) := by
    simpa [hXy, hXx] using
      isCompleteBetween_rootChildren (G := G) hCxy.symm
  -- Identify classes with sides via Q_x.
  have hYx : U \ Xx = Xy := by
    have h1 : U \ Xx = (Xx ∪ Xy) \ Xx := by rw [hpart]
    have h2 : (Xx ∪ Xy) \ Xx = Xy \ Xx := union_sdiff_left Xx Xy
    have h3 : Xy \ Xx = Xy := sdiff_eq_self_iff_disjoint.2 hdisjXY.symm
    exact h1.trans (h2.trans h3)
  have hYy : U \ Xy = Xx := hYy0
  have hpXx' : pathCoverNumber G Xx = Xx.card := by omega
  have hpXy' : pathCoverNumber G Xy = Xy.card := by omega
  have hxSide : x ∈ Xy := by
    have hxPx : x ∈ Px := mem_rNonadjClass_self hx
    have hYsub' : Xy ⊆ Px := by simpa [hYx] using hYxsub
    -- If x ∈ Xx then Q_x = Xx after the side identity, contradicting Xy ⊆ Px.
    by_contra hxX
    have hxA : x ∈ Xx := by
      have : x ∈ Xx ∪ Xy := by simpa [hpart] using hx
      exact (mem_union.1 this).resolve_right hxX
    have hQx :
        rNonadjClass (G := G) U x = Xx := by
      -- dominant join of Xy over Xx.erase x
      have hAex : (Xx.erase x).Nonempty := by
        have : (Xx.erase x).card = Xx.card - 1 := card_erase_of_mem hxA
        have : 1 ≤ (Xx.erase x).card := by omega
        exact card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) this)
      have hK : Xy ∪ Xx.erase x = U.erase x :=
        union_erase_eq_erase (U := U) (A := Xx) (B := Xy)
          (by simpa [union_comm] using hpart) hxA hxX
      have hAB' : G.IsCompleteBetween (Xy : Set V) ((Xx.erase x) : Set V) :=
        fun {_} hb {_} ha => hABxy hb (mem_of_mem_erase ha)
      have hdom : (Xx.erase x).card < pathCoverNumber G Xy := by
        have : (Xx.erase x).card = Xx.card - 1 := card_erase_of_mem hxA
        omega
      have hQ := rNonadjClass_eq_qxSet_of_hamiltonian hcog cyc hc hx
      have hF :
          ineligibleSet G (U.erase x) = Xx.erase x := by
        have hFdom :=
          ineligibleSet_complete_join_dominant hXyne hAex hAB' hdom
        have hFB : ineligibleSet G Xy = ∅ :=
          ineligibleSet_eq_empty_of_pathCoverNumber_eq_card hpXy'
        have : ineligibleSet G (Xy ∪ Xx.erase x) = Xx.erase x ∪ ineligibleSet G Xy :=
          hFdom
        simpa [hK, hFB] using this
      have hqx : qxSet (G := G) U x = Xx := by
        simp [qxSet, hF, insert_erase hxA]
      exact hQ.trans hqx
    have : Xy ⊆ Xx := by
      simpa [hQx, Px] using hYsub'
    have hYne' : Xy.Nonempty := hXyne
    obtain ⟨z, hz⟩ := hYne'
    exact (Finset.disjoint_left.1 hdisjXY) (this hz) hz
  have hPxA : Px = Xy := by
    have hQ := rNonadjClass_eq_qxSet_of_hamiltonian hcog cyc hc hx
    have hAex : (Xy.erase x).Nonempty := by
      have : (Xy.erase x).card = Xy.card - 1 := card_erase_of_mem hxSide
      have : 1 ≤ (Xy.erase x).card := by omega
      exact card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) this)
    have hK : Xx ∪ Xy.erase x = U.erase x :=
      union_erase_eq_erase (U := U) (A := Xy) (B := Xx)
        (by rw [union_comm]; exact hpart) hxSide
        (Finset.disjoint_left.1 hdisjXY.symm hxSide)
    have hAB' : G.IsCompleteBetween (Xx : Set V) ((Xy.erase x) : Set V) :=
      fun {_} ha {_} hb =>
        (hABxy (mem_of_mem_erase hb) ha).symm
    have hdom : (Xy.erase x).card < pathCoverNumber G Xx := by
      have : (Xy.erase x).card = Xy.card - 1 := card_erase_of_mem hxSide
      omega
    have hF :
        ineligibleSet G (U.erase x) = Xy.erase x := by
      have hFdom :=
        ineligibleSet_complete_join_dominant hXxne hAex hAB' hdom
      have hFA : ineligibleSet G Xx = ∅ :=
        ineligibleSet_eq_empty_of_pathCoverNumber_eq_card hpXx'
      have : ineligibleSet G (Xx ∪ Xy.erase x) =
          Xy.erase x ∪ ineligibleSet G Xx := hFdom
      simpa [hK, hFA] using this
    have hqx : qxSet (G := G) U x = Xy := by
      simp [qxSet, hF, insert_erase hxSide]
    simpa [Px] using hQ.trans hqx
  have hySide : y ∈ Xx := by
    have hyPy : y ∈ Py := mem_rNonadjClass_self hy
    have hYsub' : Xx ⊆ Py := by simpa [hYy] using hYysub
    by_contra hyY
    have hyB : y ∈ Xy := by
      have : y ∈ Xx ∪ Xy := by simpa [hpart] using hy
      exact (mem_union.1 this).resolve_left hyY
    have hQy :
        rNonadjClass (G := G) U y = Xy := by
      have hAex : (Xy.erase y).Nonempty := by
        have : (Xy.erase y).card = Xy.card - 1 := card_erase_of_mem hyB
        have : 1 ≤ (Xy.erase y).card := by omega
        exact card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) this)
      have hK : Xx ∪ Xy.erase y = U.erase y :=
        union_erase_eq_erase (U := U) (A := Xy) (B := Xx)
          (by rw [union_comm]; exact hpart) hyB hyY
      have hAB' : G.IsCompleteBetween (Xx : Set V) ((Xy.erase y) : Set V) :=
        fun {_} ha {_} hb =>
          (hABxy (mem_of_mem_erase hb) ha).symm
      have hdom : (Xy.erase y).card < pathCoverNumber G Xx := by
        have : (Xy.erase y).card = Xy.card - 1 := card_erase_of_mem hyB
        omega
      have hQ := rNonadjClass_eq_qxSet_of_hamiltonian hcog cyc hc hy
      have hF :
          ineligibleSet G (U.erase y) = Xy.erase y := by
        have hFdom :=
          ineligibleSet_complete_join_dominant hXxne hAex hAB' hdom
        have hFA : ineligibleSet G Xx = ∅ :=
          ineligibleSet_eq_empty_of_pathCoverNumber_eq_card hpXx'
        have : ineligibleSet G (Xx ∪ Xy.erase y) =
            Xy.erase y ∪ ineligibleSet G Xx := hFdom
        simpa [hK, hFA] using this
      have hqx : qxSet (G := G) U y = Xy := by
        simp [qxSet, hF, insert_erase hyB]
      exact hQ.trans hqx
    have : Xx ⊆ Xy := by simpa [hQy, Py] using hYsub'
    obtain ⟨z, hz⟩ := hXxne
    exact (Finset.disjoint_left.1 hdisjXY) hz (this hz)
  have hPyB : Py = Xx := by
    have hQ := rNonadjClass_eq_qxSet_of_hamiltonian hcog cyc hc hy
    have hAex : (Xx.erase y).Nonempty := by
      have : (Xx.erase y).card = Xx.card - 1 := card_erase_of_mem hySide
      have : 1 ≤ (Xx.erase y).card := by omega
      exact card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) this)
    have hK : Xy ∪ Xx.erase y = U.erase y :=
      union_erase_eq_erase (U := U) (A := Xx) (B := Xy)
        (by simpa [union_comm] using hpart) hySide
        (Finset.disjoint_left.1 hdisjXY hySide)
    have hAB' : G.IsCompleteBetween (Xy : Set V) ((Xx.erase y) : Set V) :=
      fun {_} hb {_} ha => hABxy hb (mem_of_mem_erase ha)
    have hdom : (Xx.erase y).card < pathCoverNumber G Xy := by
      have : (Xx.erase y).card = Xx.card - 1 := card_erase_of_mem hySide
      omega
    have hF :
        ineligibleSet G (U.erase y) = Xx.erase y := by
      have hFdom :=
        ineligibleSet_complete_join_dominant hXyne hAex hAB' hdom
      have hFB : ineligibleSet G Xy = ∅ :=
        ineligibleSet_eq_empty_of_pathCoverNumber_eq_card hpXy'
      have : ineligibleSet G (Xy ∪ Xx.erase y) =
          Xx.erase y ∪ ineligibleSet G Xy := hFdom
      simpa [hK, hFB] using this
    have hqx : qxSet (G := G) U y = Xx := by
      simp [qxSet, hF, insert_erase hySide]
    simpa [Py] using hQ.trans hqx
  refine ⟨Xy, Xx, by simpa [union_comm] using hpart, hdisjXY.symm, hXeq.symm, ?_,
    hnoY, hnoX, hABxy, hPxA, hPyB, ?_⟩
  · simpa [hXeq] using hm
  · intro z hz
    have : z ∈ Xy ∪ Xx := by simpa [hpart, union_comm] using hz
    rcases mem_union.1 this with hzA | hzB
    · have hzPx : z ∈ Px := hPxA.symm.subset hzA
      exact Or.inl
        (((hbal.2.2 (x := x) (y := z) hx hz).2 hzPx).symm.trans hPxA)
    · have hzPy : z ∈ Py := hPyB.symm.subset hzB
      exact Or.inr
        (((hbal.2.2 (x := y) (y := z) hy hz).2 hzPy).symm.trans hPyB)

lemma at_most_one_nonsingleton_class {U : Finset V}
    (hcog : IsCograph G U) (cyc : GraphCycle G) (hc : cyc.support = U)
    (hnotK : ∀ (A B : Finset V),
      ¬ (A ∪ B = U ∧ Disjoint A B ∧ A.card = B.card ∧ 2 ≤ A.card ∧
          (∀ a ∈ A, ∀ a' ∈ A, ¬ G.Adj a a') ∧
            (∀ b ∈ B, ∀ b' ∈ B, ¬ G.Adj b b') ∧
              G.IsCompleteBetween (A : Set V) (B : Set V) ∧
                (∀ z ∈ U,
                  rNonadjClass (G := G) U z = A ∨
                    rNonadjClass (G := G) U z = B)))
    {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (hPx : 2 ≤ (rNonadjClass (G := G) U x).card)
    (hPy : 2 ≤ (rNonadjClass (G := G) U y).card) :
    rNonadjClass (G := G) U x = rNonadjClass (G := G) U y := by
  by_contra hne
  obtain ⟨A, B, hunion, hdisj, hcard, hm, hnoA, hnoB, hAB, hA, hB, hall⟩ :=
    large_port_classification hcog cyc hc hx hy hPx hPy hne
  exact hnotK A B ⟨hunion, hdisj, hcard, hm, hnoA, hnoB, hAB, hall⟩

end Cograph
end Nikoghosyan

