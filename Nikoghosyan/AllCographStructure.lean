/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.FactorPCExtraction
import Nikoghosyan.FactorColoredCycle
import Nikoghosyan.Cograph.LargePorts
import Nikoghosyan.Prerequisites.TerminalCover

/-!
Phase 12: actual original-edge side partition of a non-Hamiltonian
minimum ALL-cograph factor.

From the internally discharged Yeo block splitter, each outside
component of `G-H` has a real `H`-attachment, all of those attachments
share one R-class, singleton used classes are excluded by the
per-component cut, and a common used class is excluded by the original
port cut. Two distinct used classes of size at least two force original
`H = K_{m,m}` via `large_port_classification`. The unions `U,W` of
outside components using the two sides, together with an original
`A–U` or `B–W` completeness argument from `NoInducedP4UnionP1`,
assemble an actual `AllCographSides`. No interface edge is added.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ### Card-one Hamiltonicity and outside nonemptiness -/

lemma hamiltonian_cycle_of_card_one (F : CycleFactor G) (hF : F.card = 1) :
    ∃ c : GraphCycle G, c.support = univ := by
  cases hcs : F.cycles with
  | nil =>
    simp [CycleFactor.card, hcs] at hF
  | cons c rest =>
    have hrest : rest = [] := by
      simp [CycleFactor.card, hcs] at hF
      cases rest with
      | nil => rfl
      | cons _ _ => simp at hF
    subst hrest
    refine ⟨c, eq_univ_of_forall ?_⟩
    intro x
    obtain ⟨d, hd, hx⟩ := F.mem_iff x
    have : d = c := by
      have : d ∈ ([c] : List (GraphCycle G)) := by simpa [hcs] using hd
      simpa using this
    simpa [this] using hx

lemma mem_support_iff_index (F : CycleFactor G) {i : Fin F.card} {x : V} :
    x ∈ (F.getCycle i).support ↔ F.partition.index x = i := by
  constructor
  · intro hx
    exact F.partition.index_eq (by simpa [CycleFactor.partition] using hx)
  · intro hx
    have hmem := F.partition.mem_index x
    rw [hx] at hmem
    simpa [CycleFactor.partition] using hmem

def otherIndex {n : ℕ} (i : Fin n) (h2 : 2 ≤ n) : Fin n :=
  if h : i.1 = 0 then ⟨1, Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) h2⟩
  else ⟨0, Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) h2⟩

lemma otherIndex_ne {n : ℕ} (i : Fin n) (h2 : 2 ≤ n) : i ≠ otherIndex i h2 := by
  intro h
  have hval : i.1 = (otherIndex i h2).1 := congrArg Fin.val h
  by_cases hi0 : i.1 = 0 <;> simp [otherIndex, hi0] at hval

lemma outside_nonempty_of_two_le_card (F : CycleFactor G) {i : Fin F.card}
    (h2 : 2 ≤ F.card) : (univ \ (F.getCycle i).support).Nonempty := by
  let j := otherIndex i h2
  have hij : i ≠ j := otherIndex_ne i h2
  obtain ⟨x, hx⟩ := (F.getCycle j).support_nonempty
  have hxj : F.partition.index x = j := (mem_support_iff_index F).1 hx
  refine ⟨x, mem_sdiff.2 ⟨mem_univ x, ?_⟩⟩
  intro hxH
  have hxi : F.partition.index x = i := (mem_support_iff_index F).1 hxH
  exact hij (hxi.symm.trans hxj)

/-! ### First original attachment of an outside walk -/

lemma exists_boundary_of_walk (F : CycleFactor G) {i : Fin F.card} :
    ∀ {x a : V} (hx : F.partition.index x ≠ i) (ha : F.partition.index a = i)
      (w : G.Walk x a),
      ∃ y b, ∃ hy : F.partition.index y ≠ i,
        F.partition.index b = i ∧ G.Adj y b ∧
          (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, hx, ha, Walk.nil => (hx ha).elim
  | x, a, hx, ha, Walk.cons (v := v) hadj p => by
    by_cases hv : F.partition.index v = i
    · exact ⟨x, v, hx, hv, hadj, Reachable.rfl⟩
    · obtain ⟨y, b, hy, hb, hadjyb, hreach⟩ :=
        exists_boundary_of_walk (F := F) (i := i) hv ha p
      refine ⟨y, b, hy, hb, hadjyb, ?_⟩
      have hadjI :
          (G.induce {z | F.partition.index z ≠ i}).Adj ⟨x, hx⟩ ⟨v, hv⟩ := by
        simpa [SimpleGraph.induce_adj] using hadj
      exact hadjI.reachable.trans hreach

lemma exists_attachment_of_connected (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {i : Fin F.card} {x : V} (hx : F.partition.index x ≠ i) :
    ∃ y a, ∃ hy : F.partition.index y ≠ i,
      a ∈ (F.getCycle i).support ∧ G.Adj y a ∧
        (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  have hconn : G.Connected := hT.connected
  obtain ⟨a, ha⟩ := (F.getCycle i).support_nonempty
  have hai : F.partition.index a = i := (mem_support_iff_index F).1 ha
  have hR : G.Reachable x a := hconn.1 x a
  obtain ⟨w⟩ := hR
  obtain ⟨y, b, hy, hb, hadj, hreach⟩ := exists_boundary_of_walk F hx hai w
  exact ⟨y, b, hy, (mem_support_iff_index F).2 hb, hadj, hreach⟩

/-! ### Component attachments share one R-class -/

def CompAttaches (F : CycleFactor G) (i : Fin F.card) (x : V)
    (hx : F.partition.index x ≠ i) (a : V) : Prop :=
  a ∈ (F.getCycle i).support ∧
    ∃ y, ∃ hy : F.partition.index y ≠ i,
      G.Adj y a ∧
        (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩

lemma exists_comp_attachment (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {i : Fin F.card} {x : V} (hx : F.partition.index x ≠ i) :
    ∃ a, CompAttaches F i x hx a := by
  obtain ⟨y, a, hy, ha, hadj, hreach⟩ :=
    exists_attachment_of_connected (F := F) hT hord hx
  exact ⟨a, ha, y, hy, hadj, hreach⟩

lemma comp_attachment_port_eq (F : CycleFactor G)
    {i : Fin F.card}
    (hsplit : Yeo.SplittingVertex
      (auxColoring (G := G) F.partition (factorPort F)) (.inl i))
    {x : V} (hx : F.partition.index x ≠ i) {a b : V}
    (ha : CompAttaches F i x hx a) (hb : CompAttaches F i x hx b) :
    factorPort F a = factorPort F b := by
  obtain ⟨haH, y, hy, hya, hxy⟩ := ha
  obtain ⟨hbH, z, hz, hzb, hxz⟩ := hb
  have hai : F.partition.index a = i := (mem_support_iff_index F).1 haH
  have hbi : F.partition.index b = i := (mem_support_iff_index F).1 hbH
  have hyz :
      (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨y, hy⟩ ⟨z, hz⟩ :=
    hxy.symm.trans hxz
  exact attachment_factorPort_eq (F := F) hsplit hy hz hai hbi hya hzb hyz

noncomputable def usedPort_aux (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {i : Fin F.card} {x : V} (hx : F.partition.index x ≠ i) :
    { a : V // CompAttaches F i x hx a } :=
  ⟨Classical.choose (exists_comp_attachment (F := F) hT hord hx),
    Classical.choose_spec (exists_comp_attachment (F := F) hT hord hx)⟩

noncomputable def usedPort (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {i : Fin F.card} {x : V} (hx : F.partition.index x ≠ i) : Finset V :=
  factorPort F (usedPort_aux (F := F) hT hord hx).1

lemma usedPort_eq_of_attachment (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {i : Fin F.card}
    (hsplit : Yeo.SplittingVertex
      (auxColoring (G := G) F.partition (factorPort F)) (.inl i))
    {x : V} (hx : F.partition.index x ≠ i) {a : V}
    (ha : CompAttaches F i x hx a) :
    usedPort (F := F) hT hord hx = factorPort F a :=
  comp_attachment_port_eq (F := F) hsplit hx
    (usedPort_aux (F := F) hT hord hx).2 ha

lemma usedPort_eq_of_reachable (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {i : Fin F.card}
    (hsplit : Yeo.SplittingVertex
      (auxColoring (G := G) F.partition (factorPort F)) (.inl i))
    {x y : V} (hx : F.partition.index x ≠ i) (hy : F.partition.index y ≠ i)
    (hR : (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    usedPort (F := F) hT hord hx = usedPort (F := F) hT hord hy := by
  let a := (usedPort_aux (F := F) hT hord hy).1
  have ha : CompAttaches F i y hy a := (usedPort_aux (F := F) hT hord hy).2
  have ha' : CompAttaches F i x hx a := by
    obtain ⟨haH, z, hz, hadj, hzy⟩ := ha
    exact ⟨haH, z, hz, hadj, hR.trans hzy⟩
  have h1 := usedPort_eq_of_attachment (F := F) hT hord hsplit hx ha'
  have h2 := usedPort_eq_of_attachment (F := F) hT hord hsplit hy ha
  exact h1.trans h2.symm

/-! ### Singleton and common-class exclusions -/

lemma two_le_usedPort (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {i : Fin F.card}
    (hsplit : Yeo.SplittingVertex
      (auxColoring (G := G) F.partition (factorPort F)) (.inl i))
    {x : V} (hx : F.partition.index x ≠ i) :
    2 ≤ (usedPort (F := F) hT hord hx).card := by
  by_contra hlt
  have hcard : (usedPort (F := F) hT hord hx).card ≤ 1 := Nat.not_lt.1 (mt Nat.succ_le_iff.mpr hlt)
  let a := (usedPort_aux (F := F) hT hord hx).1
  have ha : CompAttaches F i x hx a := (usedPort_aux (F := F) hT hord hx).2
  have haP : a ∈ usedPort (F := F) hT hord hx := by
    have : usedPort (F := F) hT hord hx = factorPort F a := rfl
    simpa [this] using factorPort_mem_self (F := F) (x := a)
  have hpos : 1 ≤ (usedPort (F := F) hT hord hx).card :=
    Nat.succ_le_iff.mpr (card_pos.mpr ⟨a, haP⟩)
  have h1 : (usedPort (F := F) hT hord hx).card = 1 := le_antisymm hcard hpos
  obtain ⟨p, hpEq⟩ := card_eq_one.1 h1
  have hp : p ∈ (F.getCycle i).support := by
    have hpP : p ∈ usedPort (F := F) hT hord hx := by simp [hpEq]
    have hsub : usedPort (F := F) hT hord hx ⊆ (F.getCycle i).support := by
      have : usedPort (F := F) hT hord hx = factorPort F a := rfl
      simpa [this] using factorPort_subset_block F ha.1
    exact hsub hpP
  refine not_component_singleton_attachment (F := F) hT hp hx ?_
  intro y b hy hbH hadj hreach
  have hbAtt : CompAttaches F i x hx b := ⟨hbH, y, hy, hadj, hreach⟩
  have hport := usedPort_eq_of_attachment (F := F) hT hord hsplit hx hbAtt
  have hbP : b ∈ usedPort (F := F) hT hord hx := by
    have : b ∈ factorPort F b := factorPort_mem_self (F := F) (x := b)
    simpa [hport] using this
  have : b ∈ ({p} : Finset V) := by simpa [hpEq] using hbP
  exact mem_singleton.1 this

lemma not_all_usedPorts_eq (F : CycleFactor G)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    {i : Fin F.card}
    (hsplit : Yeo.SplittingVertex
      (auxColoring (G := G) F.partition (factorPort F)) (.inl i))
    (h2 : 2 ≤ F.card) :
    ∃ (x y : V) (hx : F.partition.index x ≠ i) (hy : F.partition.index y ≠ i),
      usedPort (F := F) hT hord hx ≠ usedPort (F := F) hT hord hy := by
  obtain ⟨x0, hx0s⟩ := outside_nonempty_of_two_le_card F (i := i) h2
  have hOutside : (univ \ (F.getCycle i).support).Nonempty := ⟨x0, hx0s⟩
  have hx0 : F.partition.index x0 ≠ i := by
    intro h
    exact (mem_sdiff.1 hx0s).2 ((mem_support_iff_index F).2 h)
  by_contra hsame
  have hsame' :
      ∀ (x y : V) (hx : F.partition.index x ≠ i) (hy : F.partition.index y ≠ i),
        usedPort (F := F) hT hord hx = usedPort (F := F) hT hord hy := by
    intro x y hx hy
    by_contra hne
    exact hsame ⟨x, y, hx, hy, hne⟩
  let a := (usedPort_aux (F := F) hT hord hx0).1
  have ha : CompAttaches F i x0 hx0 a := (usedPort_aux (F := F) hT hord hx0).2
  have haH : a ∈ (F.getCycle i).support := ha.1
  refine original_common_port_cut (F := F) hT hcog haH hOutside ?_
  intro z b hbH hzW hadj
  have hz : F.partition.index z ≠ i := by
    intro h
    exact (mem_sdiff.1 hzW).2 ((mem_support_iff_index F).2 h)
  have hbAtt : CompAttaches F i z hz b := ⟨hbH, z, hz, hadj, Reachable.rfl⟩
  have hportz := usedPort_eq_of_attachment (F := F) hT hord hsplit hz hbAtt
  have hports := hsame' z x0 hz hx0
  have hport0 : usedPort (F := F) hT hord hx0 = factorPort F a := rfl
  have : factorPort F b = factorPort F a :=
    hportz.symm.trans (hports.trans hport0)
  have hbP : b ∈ factorPort F b := factorPort_mem_self (F := F) (x := b)
  simpa [this] using hbP

/-! ### Adjacent complete/anticomplete transition along an outside walk -/

lemma exists_adjacent_pred {S : Set V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (P : V → Prop)
    (hPx : P x) (hnPy : ¬ P y)
    (w : (G.induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ u v, ∃ hu : u ∈ S, ∃ hv : v ∈ S,
      P u ∧ ¬ P v ∧ G.Adj u v ∧
        (G.induce S).Reachable ⟨x, hx⟩ ⟨u, hu⟩ ∧
          (G.induce S).Reachable ⟨x, hx⟩ ⟨v, hv⟩ := by
  classical
  let Q : ℕ → Prop := fun n => n ≤ w.length ∧ ¬ P (w.getVert n).1
  have hQ : ∃ n, Q n :=
    ⟨w.length, le_rfl, by simpa [Walk.getVert_length] using hnPy⟩
  let n := Nat.find hQ
  have hn : Q n := Nat.find_spec hQ
  have npos : 0 < n := by
    by_contra hle
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hle
    have : ¬ P (w.getVert 0).1 := by
      simpa [hn0, Walk.getVert_zero] using hn.2
    exact this (by simpa [Walk.getVert_zero] using hPx)
  have hn1_lt : n - 1 < n := Nat.sub_lt npos (by decide)
  have hnot : ¬ Q (n - 1) := Nat.find_min hQ hn1_lt
  have hn1_le : n - 1 ≤ w.length :=
    le_trans (Nat.sub_le n 1) hn.1
  have hPn1 : P (w.getVert (n - 1)).1 := by
    have : ¬ ((n - 1) ≤ w.length ∧ ¬ P (w.getVert (n - 1)).1) := hnot
    have : n - 1 ≤ w.length → P (w.getVert (n - 1)).1 := by
      intro hle
      by_contra hnP
      exact this ⟨hle, hnP⟩
    exact this hn1_le
  have hn1_len : n - 1 < w.length := by omega
  have hadj := w.adj_getVert_succ hn1_len
  have hsucc : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos npos
  have hadjG : G.Adj (w.getVert (n - 1)).1 (w.getVert (n - 1 + 1)).1 := by
    simpa [SimpleGraph.induce_adj] using hadj
  refine ⟨(w.getVert (n - 1)).1, (w.getVert n).1,
    (w.getVert (n - 1)).property, (w.getVert n).property,
    hPn1, hn.2, ?_, ⟨w.take (n - 1)⟩, ⟨w.take n⟩⟩
  simpa [hsucc] using hadjG

lemma isCograph_of_isolated (hpat : NoInducedP4UnionP1 G)
    {U : Finset V} {w : V} (hw : w ∉ U)
    (hanti : ∀ x ∈ U, ¬ G.Adj w x) : IsCograph G U := by
  intro a b c d ha hb hc hd hp
  have hwa : w ≠ a := fun h => hw (h ▸ ha)
  have hwb : w ≠ b := fun h => hw (h ▸ hb)
  have hwc : w ≠ c := fun h => hw (h ▸ hc)
  have hwd : w ≠ d := fun h => hw (h ▸ hd)
  have hmeet := hpat hp hwa hwb hwc hwd
  rcases hmeet with h1 | h2 | h3 | h4
  · exact hanti a ha h1
  · exact hanti b hb h2
  · exact hanti c hc h3
  · exact hanti d hd h4

/-! ### Completeness of one original interface -/

lemma inducedP4_a0_b_a1_u
    {A B U : Finset V} {a0 b a1 u : V}
    (hdisjAU : Disjoint A U) (hdisjBU : Disjoint B U)
    (hAind : Independent (G := G) A)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hUantiB : ∀ u ∈ U, ∀ b ∈ B, ¬ G.Adj u b)
    (ha0 : a0 ∈ A) (ha1 : a1 ∈ A) (hb : b ∈ B) (hu : u ∈ U)
    (h0 : ¬ G.Adj u a0) (h1 : G.Adj u a1) :
    InducedP4 G a0 b a1 u := by
  have hABdisj : Disjoint A B := disjoint_of_completeBetween (G := G) hAB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hAB ha0 hb, (hAB ha1 hb).symm, h1.symm,
    hAind ha0 ha1, fun h => h0 h.symm, fun h => hUantiB u hu b hb h.symm⟩
  · exact fun h => (disjoint_left.1 hABdisj ha0 (h ▸ hb)).elim
  · exact fun h => h0 (by simpa [h] using h1)
  · exact fun h => (disjoint_left.1 hdisjAU ha0 (h ▸ hu)).elim
  · exact fun h => (disjoint_left.1 hABdisj ha1 (h.symm ▸ hb)).elim
  · exact fun h => (disjoint_left.1 hdisjBU hb (h ▸ hu)).elim
  · exact fun h => (disjoint_left.1 hdisjAU ha1 (h ▸ hu)).elim

lemma inducedP4_b_a_u1_u0
    {A B U : Finset V} {b a u1 u0 : V}
    (hdisjAU : Disjoint A U) (hdisjBU : Disjoint B U)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hUantiB : ∀ u ∈ U, ∀ b ∈ B, ¬ G.Adj u b)
    (ha : a ∈ A) (hb : b ∈ B) (hu1 : u1 ∈ U) (hu0 : u0 ∈ U)
    (hcomplete : G.Adj u1 a) (hanti : ¬ G.Adj u0 a) (hadj : G.Adj u1 u0) :
    InducedP4 G b a u1 u0 := by
  have hABdisj : Disjoint A B := disjoint_of_completeBetween (G := G) hAB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (hAB ha hb).symm, hcomplete.symm, hadj,
    fun h => hUantiB u1 hu1 b hb h.symm, fun h => hUantiB u0 hu0 b hb h.symm,
    fun h => hanti h.symm⟩
  · exact fun h => (disjoint_left.1 hABdisj ha (h.symm ▸ hb)).elim
  · exact fun h => (disjoint_left.1 hdisjBU hb (h ▸ hu1)).elim
  · exact fun h => (disjoint_left.1 hdisjBU hb (h ▸ hu0)).elim
  · exact fun h => (disjoint_left.1 hdisjAU ha (h ▸ hu1)).elim
  · exact fun h => (disjoint_left.1 hdisjAU ha (h ▸ hu0)).elim
  · exact fun h => hanti (by simpa [h] using hcomplete)

lemma adj_b_of_isolated_W
    (hpat : NoInducedP4UnionP1 G)
    {A B U W : Finset V} {a0 b a1 u w : V}
    (hdisjAW : Disjoint A W) (hdisjBW : Disjoint B W) (hdisjUW : Disjoint U W)
    (hWantiA : ∀ w ∈ W, ∀ a ∈ A, ¬ G.Adj w a)
    (hUantiW : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w)
    (ha0 : a0 ∈ A) (ha1 : a1 ∈ A) (hb : b ∈ B) (hu : u ∈ U) (hw : w ∈ W)
    (hp4 : InducedP4 G a0 b a1 u) : G.Adj w b := by
  have hwA0 : w ≠ a0 := fun h => (disjoint_left.1 hdisjAW ha0 (h ▸ hw)).elim
  have hwB : w ≠ b := fun h => (disjoint_left.1 hdisjBW hb (h ▸ hw)).elim
  have hwA1 : w ≠ a1 := fun h => (disjoint_left.1 hdisjAW ha1 (h ▸ hw)).elim
  have hwU : w ≠ u := fun h => (disjoint_left.1 hdisjUW hu (h ▸ hw)).elim
  have hmeet := hpat hp4 hwA0 hwB hwA1 hwU
  have nA0 : ¬ G.Adj w a0 := hWantiA w hw a0 ha0
  have nA1 : ¬ G.Adj w a1 := hWantiA w hw a1 ha1
  have nU : ¬ G.Adj w u := fun h => hUantiW u hu w hw h.symm
  rcases hmeet with h1 | h2 | h3 | h4
  · exact (nA0 h1).elim
  · exact h2
  · exact (nA1 h3).elim
  · exact (nU h4).elim

lemma adj_b_of_isolated_W_path
    (hpat : NoInducedP4UnionP1 G)
    {A B U W : Finset V} {b a u1 u0 w : V}
    (hdisjAW : Disjoint A W) (hdisjBW : Disjoint B W) (hdisjUW : Disjoint U W)
    (hWantiA : ∀ w ∈ W, ∀ a ∈ A, ¬ G.Adj w a)
    (hUantiW : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w)
    (ha : a ∈ A) (hb : b ∈ B) (hu1 : u1 ∈ U) (hu0 : u0 ∈ U) (hw : w ∈ W)
    (hp4 : InducedP4 G b a u1 u0) : G.Adj w b := by
  have hwB : w ≠ b := fun h => (disjoint_left.1 hdisjBW hb (h ▸ hw)).elim
  have hwA : w ≠ a := fun h => (disjoint_left.1 hdisjAW ha (h ▸ hw)).elim
  have hw1 : w ≠ u1 := fun h => (disjoint_left.1 hdisjUW hu1 (h ▸ hw)).elim
  have hw0 : w ≠ u0 := fun h => (disjoint_left.1 hdisjUW hu0 (h ▸ hw)).elim
  have hmeet := hpat hp4 hwB hwA hw1 hw0
  have nA : ¬ G.Adj w a := hWantiA w hw a ha
  have n1 : ¬ G.Adj w u1 := fun h => hUantiW u1 hu1 w hw h.symm
  have n0 : ¬ G.Adj w u0 := fun h => hUantiW u0 hu0 w hw h.symm
  rcases hmeet with h1 | h2 | h3 | h4
  · exact h1
  · exact (nA h2).elim
  · exact (n1 h3).elim
  · exact (n0 h4).elim

/-! ### Assembly of an actual `AllCographSides` -/

lemma exists_allCographSides_of_two_le_card
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G) (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    (h2 : 2 ≤ F.card) : Nonempty (AllCographSides G) := by
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  obtain ⟨i, hsplit⟩ := exists_block_splitter_of_min_cograph (F := F) hmin hcog hT hord
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    not_all_usedPorts_eq (F := F) hT hord hcog hsplit h2
  have hx2 := two_le_usedPort (F := F) hT hord hsplit hx
  have hy2 := two_le_usedPort (F := F) hT hord hsplit hy
  let ax := (usedPort_aux (F := F) hT hord hx).1
  let ay := (usedPort_aux (F := F) hT hord hy).1
  have hax : CompAttaches F i x hx ax := (usedPort_aux (F := F) hT hord hx).2
  have hay : CompAttaches F i y hy ay := (usedPort_aux (F := F) hT hord hy).2
  have haxH : ax ∈ (F.getCycle i).support := hax.1
  have hayH : ay ∈ (F.getCycle i).support := hay.1
  have hportx : usedPort (F := F) hT hord hx = factorPort F ax := rfl
  have hporty : usedPort (F := F) hT hord hy = factorPort F ay := rfl
  have hPx : factorPort F ax =
      Cograph.rNonadjClass (G := G) (F.getCycle i).support ax :=
    factorPort_eq_of_mem F haxH
  have hPy : factorPort F ay =
      Cograph.rNonadjClass (G := G) (F.getCycle i).support ay :=
    factorPort_eq_of_mem F hayH
  have hneClass :
      Cograph.rNonadjClass (G := G) (F.getCycle i).support ax ≠
        Cograph.rNonadjClass (G := G) (F.getCycle i).support ay := by
    intro h
    apply hxy
    simp [hportx, hporty, hPx, hPy, h]
  have hPx2 : 2 ≤ (Cograph.rNonadjClass (G := G) (F.getCycle i).support ax).card := by
    simpa [hportx, hPx] using hx2
  have hPy2 : 2 ≤ (Cograph.rNonadjClass (G := G) (F.getCycle i).support ay).card := by
    simpa [hporty, hPy] using hy2
  obtain ⟨A, B, hunion, hdisjAB, hcardAB, hm, hnoA, hnoB, hAB, hAeq, hBeq, hall⟩ :=
    Cograph.large_port_classification (Cograph.isCograph_iff.2 (hcog i))
      (F.getCycle i) rfl haxH hayH
      hPx2 hPy2 hneClass
  have hAH : A ⊆ (F.getCycle i).support := by
    intro z hz
    have : z ∈ A ∪ B := mem_union.2 (Or.inl hz)
    simpa [hunion] using this
  have hBH : B ⊆ (F.getCycle i).support := by
    intro z hz
    have : z ∈ A ∪ B := mem_union.2 (Or.inr hz)
    simpa [hunion] using this
  have husedx : usedPort (F := F) hT hord hx = A := by
    simp [hportx, hPx, hAeq]
  have husedy : usedPort (F := F) hT hord hy = B := by
    simp [hporty, hPy, hBeq]
  have hport_or (z : V) (hz : F.partition.index z ≠ i) :
      usedPort (F := F) hT hord hz = A ∨ usedPort (F := F) hT hord hz = B := by
    let az := (usedPort_aux (F := F) hT hord hz).1
    have haz : CompAttaches F i z hz az := (usedPort_aux (F := F) hT hord hz).2
    have hazH : az ∈ (F.getCycle i).support := haz.1
    have hPaz : usedPort (F := F) hT hord hz =
        Cograph.rNonadjClass (G := G) (F.getCycle i).support az := by
      have : usedPort (F := F) hT hord hz = factorPort F az := rfl
      simpa [this] using factorPort_eq_of_mem F hazH
    rcases hall az hazH with hA | hB
    · exact Or.inl (hPaz.trans hA)
    · exact Or.inr (hPaz.trans hB)
  let U : Finset V := univ.filter fun z =>
    ∃ hz : F.partition.index z ≠ i, usedPort (F := F) hT hord hz = A
  let W : Finset V := univ.filter fun z =>
    ∃ hz : F.partition.index z ≠ i, usedPort (F := F) hT hord hz = B
  have hxU : x ∈ U := mem_filter.2 ⟨mem_univ x, ⟨hx, husedx⟩⟩
  have hyW : y ∈ W := mem_filter.2 ⟨mem_univ y, ⟨hy, husedy⟩⟩
  have hUne : U.Nonempty := ⟨x, hxU⟩
  have hWne : W.Nonempty := ⟨y, hyW⟩
  have hAne : A.Nonempty := card_pos.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm)
  have hBne : B.Nonempty := by
    have : 2 ≤ B.card := by simpa [hcardAB] using hm
    exact card_pos.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) this)
  have hUout : U ⊆ univ \ (F.getCycle i).support := by
    intro z hz
    obtain ⟨hzidx, _⟩ := (mem_filter.1 hz).2
    exact mem_sdiff.2 ⟨mem_univ z, fun hH => hzidx ((mem_support_iff_index F).1 hH)⟩
  have hWout : W ⊆ univ \ (F.getCycle i).support := by
    intro z hz
    obtain ⟨hzidx, _⟩ := (mem_filter.1 hz).2
    exact mem_sdiff.2 ⟨mem_univ z, fun hH => hzidx ((mem_support_iff_index F).1 hH)⟩
  have hdisjAU : Disjoint A U := by
    rw [Finset.disjoint_left]
    intro z hzA hzU
    exact (mem_sdiff.1 (hUout hzU)).2 (hAH hzA)
  have hdisjBU : Disjoint B U := by
    rw [Finset.disjoint_left]
    intro z hzB hzU
    exact (mem_sdiff.1 (hUout hzU)).2 (hBH hzB)
  have hdisjAW : Disjoint A W := by
    rw [Finset.disjoint_left]
    intro z hzA hzW
    exact (mem_sdiff.1 (hWout hzW)).2 (hAH hzA)
  have hdisjBW : Disjoint B W := by
    rw [Finset.disjoint_left]
    intro z hzB hzW
    exact (mem_sdiff.1 (hWout hzW)).2 (hBH hzB)
  have hdisjUW : Disjoint U W := by
    rw [Finset.disjoint_left]
    intro z hzU hzW
    obtain ⟨hzi, hzA⟩ := (mem_filter.1 hzU).2
    obtain ⟨hzi', hzB⟩ := (mem_filter.1 hzW).2
    have hAB : A = B := by
      have hirr := Subsingleton.elim hzi hzi'
      subst hirr
      exact hzA.symm.trans hzB
    have : usedPort (F := F) hT hord hx = usedPort (F := F) hT hord hy := by
      simp [husedx, husedy, hAB]
    exact hxy this
  have hUantiB : ∀ u ∈ U, ∀ b ∈ B, ¬ G.Adj u b := by
    intro u hu b hb hadj
    obtain ⟨hui, huA⟩ := (mem_filter.1 hu).2
    have hbH : b ∈ (F.getCycle i).support := hBH hb
    have hbAtt : CompAttaches F i u hui b := ⟨hbH, u, hui, hadj, Reachable.rfl⟩
    have hport := usedPort_eq_of_attachment (F := F) hT hord hsplit hui hbAtt
    have hbB : Cograph.rNonadjClass (G := G) (F.getCycle i).support b = B := by
      have hbBmem : b ∈ Cograph.rNonadjClass (G := G) (F.getCycle i).support ay := by
        simpa [hBeq] using hb
      exact ((factor_block_balanced F hcog i).2.2 hayH hbH).2 hbBmem |>.symm.trans hBeq
    have : A = B := by
      have hPb : factorPort F b =
          Cograph.rNonadjClass (G := G) (F.getCycle i).support b :=
        factorPort_eq_of_mem F hbH
      calc
        A = usedPort (F := F) hT hord hui := huA.symm
        _ = factorPort F b := hport
        _ = Cograph.rNonadjClass (G := G) (F.getCycle i).support b := hPb
        _ = B := hbB
    have : usedPort (F := F) hT hord hx = usedPort (F := F) hT hord hy := by
      simp [husedx, husedy, this]
    exact hxy this
  have hWantiA : ∀ w ∈ W, ∀ a ∈ A, ¬ G.Adj w a := by
    intro w hw a ha hadj
    obtain ⟨hwi, hwB⟩ := (mem_filter.1 hw).2
    have haH : a ∈ (F.getCycle i).support := hAH ha
    have haAtt : CompAttaches F i w hwi a := ⟨haH, w, hwi, hadj, Reachable.rfl⟩
    have hport := usedPort_eq_of_attachment (F := F) hT hord hsplit hwi haAtt
    have haA : Cograph.rNonadjClass (G := G) (F.getCycle i).support a = A := by
      have hamem : a ∈ Cograph.rNonadjClass (G := G) (F.getCycle i).support ax := by
        simpa [hAeq] using ha
      exact ((factor_block_balanced F hcog i).2.2 haxH haH).2 hamem |>.symm.trans hAeq
    have hEq : B = A := by
      have hPa : factorPort F a =
          Cograph.rNonadjClass (G := G) (F.getCycle i).support a :=
        factorPort_eq_of_mem F haH
      calc
        B = usedPort (F := F) hT hord hwi := hwB.symm
        _ = factorPort F a := hport
        _ = Cograph.rNonadjClass (G := G) (F.getCycle i).support a := hPa
        _ = A := haA
    have : usedPort (F := F) hT hord hx = usedPort (F := F) hT hord hy := by
      simp [husedx, husedy, hEq.symm]
    exact hxy this
  have hUantiW : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w := by
    intro u hu w hw hadj
    obtain ⟨hui, huA⟩ := (mem_filter.1 hu).2
    obtain ⟨hwi, hwB⟩ := (mem_filter.1 hw).2
    have hadjI :
        (G.induce {z | F.partition.index z ≠ i}).Adj ⟨u, hui⟩ ⟨w, hwi⟩ := by
      simpa [SimpleGraph.induce_adj] using hadj
    have hports :=
      usedPort_eq_of_reachable (F := F) hT hord hsplit hui hwi hadjI.reachable
    have : A = B := huA.symm.trans (hports.trans hwB)
    have : usedPort (F := F) hT hord hx = usedPort (F := F) hT hord hy := by
      simp [husedx, husedy, this]
    exact hxy this
  have hAind : Independent (G := G) A := fun x y hx hy => hnoA x hx y hy
  have hBind : Independent (G := G) B := fun x y hx hy => hnoB x hx y hy
  have hcover : A ∪ B ∪ U ∪ W = univ := by
    ext z
    constructor
    · intro _hz
      exact mem_univ z
    · intro _hz
      by_cases hzi : F.partition.index z = i
      · have hzH : z ∈ (F.getCycle i).support := (mem_support_iff_index F).2 hzi
        have : z ∈ A ∪ B := by simpa [hunion] using hzH
        rcases mem_union.1 this with hA | hB
        · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_union.2 (Or.inl hA)))))
        · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_union.2 (Or.inr hB)))))
      · rcases hport_or z hzi with hA | hB
        · have : z ∈ U := mem_filter.2 ⟨mem_univ z, ⟨hzi, hA⟩⟩
          exact mem_union.2 (Or.inl (mem_union.2 (Or.inr this)))
        · have : z ∈ W := mem_filter.2 ⟨mem_univ z, ⟨hzi, hB⟩⟩
          exact mem_union.2 (Or.inr this)
  have hy_not_AU : y ∉ A ∪ U := by
    intro hy'
    rcases mem_union.1 hy' with hA | hU
    · exact (mem_sdiff.1 (hWout hyW)).2 (hAH hA)
    · exact disjoint_left.1 hdisjUW hU hyW
  have hAUcog : IsCograph G (A ∪ U) :=
    isCograph_of_isolated hpat hy_not_AU (by
      intro t ht
      rcases mem_union.1 ht with hA | hU
      · exact hWantiA y hyW t hA
      · exact fun hadj => hUantiW t hU y hyW hadj.symm)
  have hx_not_BW : x ∉ B ∪ W := by
    intro hx'
    rcases mem_union.1 hx' with hB | hW
    · exact (mem_sdiff.1 (hUout hxU)).2 (hBH hB)
    · exact disjoint_left.1 hdisjUW hxU hW
  have hBWcog : IsCograph G (B ∪ W) :=
    isCograph_of_isolated hpat hx_not_BW (by
      intro t ht
      rcases mem_union.1 ht with hB | hW
      · exact hUantiB x hxU t hB
      · exact fun hadj => hUantiW x hxU t hW hadj)
  have hUcog : IsCograph G U :=
    IsCograph.subset (G := G) hAUcog subset_union_right
  have hWcog : IsCograph G W :=
    IsCograph.subset (G := G) hBWcog subset_union_right
  have hcomplete :
      G.IsCompleteBetween (A : Set V) (U : Set V) ∨
        G.IsCompleteBetween (B : Set V) (W : Set V) := by
    by_cases hAU : G.IsCompleteBetween (A : Set V) (U : Set V)
    · exact Or.inl hAU
    · right
      intro b hb w hw
      have hex : ∃ u ∈ U, ∃ a0 ∈ A, ¬ G.Adj u a0 := by
        by_contra hnone
        apply hAU
        intro a ha u hu
        by_contra hn
        exact hnone ⟨u, hu, a, ha, fun h => hn h.symm⟩
      obtain ⟨u0, hu0, a0, ha0, h0⟩ := hex
      by_cases hmix : ∃ u ∈ U, ∃ a1 ∈ A, G.Adj u a1 ∧ ∃ a0' ∈ A, ¬ G.Adj u a0'
      · obtain ⟨u, hu, a1, ha1, h1, a0', ha0', h0'⟩ := hmix
        have hp4 :=
          inducedP4_a0_b_a1_u hdisjAU hdisjBU hAind hAB hUantiB
            ha0' ha1 hb hu h0' h1
        exact (adj_b_of_isolated_W hpat hdisjAW hdisjBW hdisjUW hWantiA hUantiW
          ha0' ha1 hb hu hw hp4).symm
      · have hdich : ∀ u ∈ U, (∀ a ∈ A, G.Adj u a) ∨ (∀ a ∈ A, ¬ G.Adj u a) := by
          intro u hu
          by_cases hc : ∀ a ∈ A, G.Adj u a
          · exact Or.inl hc
          · right
            intro a ha hadj
            apply hmix
            refine ⟨u, hu, a, ha, hadj, ?_⟩
            by_contra hall
            exact hc fun a' ha' => by
              by_contra hn
              exact hall ⟨a', ha', hn⟩
        have hanti0 : ∀ a ∈ A, ¬ G.Adj u0 a := by
          rcases hdich u0 hu0 with hc | ha
          · exact (h0 (hc a0 ha0)).elim
          · exact ha
        obtain ⟨hui0, hu0A⟩ := (mem_filter.1 hu0).2
        obtain ⟨a1, haAtt⟩ := exists_comp_attachment (F := F) hT hord hui0
        have hport := usedPort_eq_of_attachment (F := F) hT hord hsplit hui0 haAtt
        obtain ⟨ha1H, u1, hu1i, hadj1, hreach1⟩ := haAtt
        have hfa : factorPort F a1 = A := hport.symm.trans hu0A
        have ha1A : a1 ∈ A := by
          have : a1 ∈ factorPort F a1 := factorPort_mem_self (F := F) (x := a1)
          simpa [hfa] using this
        have hu1U : u1 ∈ U :=
          mem_filter.2 ⟨mem_univ u1,
            ⟨hu1i, (usedPort_eq_of_reachable (F := F) hT hord hsplit hui0 hu1i
              hreach1).symm.trans hu0A⟩⟩
        have hu1comp : ∀ a ∈ A, G.Adj u1 a := by
          rcases hdich u1 hu1U with hc | ha
          · exact hc
          · exact (ha a1 ha1A hadj1).elim
        obtain ⟨wInd⟩ := hreach1.symm
        have hncomp0 : ¬ ∀ a ∈ A, G.Adj u0 a := fun hc => h0 (hc a0 ha0)
        obtain ⟨p, q, hpS, hqS, hP, hnP, hadjpq, hRp, hRq⟩ :=
          exists_adjacent_pred (S := {z | F.partition.index z ≠ i})
            hu1i hui0 (fun z => ∀ a ∈ A, G.Adj z a) hu1comp hncomp0 wInd
        have hpU : p ∈ U :=
          mem_filter.2 ⟨mem_univ p, ⟨hpS,
            (usedPort_eq_of_reachable (F := F) hT hord hsplit hu1i hpS hRp).symm.trans
              (mem_filter.1 hu1U).2.2⟩⟩
        have hqU : q ∈ U :=
          mem_filter.2 ⟨mem_univ q, ⟨hqS,
            (usedPort_eq_of_reachable (F := F) hT hord hsplit hu1i hqS hRq).symm.trans
              (mem_filter.1 hu1U).2.2⟩⟩
        have hantiq : ¬ G.Adj q a1 := by
          have : ¬ ∀ a ∈ A, G.Adj q a := hnP
          rcases hdich q hqU with hc | ha
          · exact (this hc).elim
          · exact ha a1 ha1A
        have hp4 :=
          inducedP4_b_a_u1_u0 hdisjAU hdisjBU hAB hUantiB ha1A hb hpU hqU
            (hP a1 ha1A) hantiq hadjpq
        exact (adj_b_of_isolated_W_path hpat hdisjAW hdisjBW hdisjUW hWantiA
          hUantiW ha1A hb hpU hqU hw hp4).symm
  rcases hcomplete with hAU | hBW
  · exact ⟨{
      A := A, B := B, U := U, W := W, m := A.card
      hAind := hAind, hBind := hBind
      hAcard := rfl, hBcard := hcardAB.symm, hm := hm
      hAB := hAB, hAU := hAU
      hUantiB := hUantiB, hUantiW := hUantiW, hWantiA := hWantiA
      hUne := hUne, hWne := hWne
      hUcog := hUcog, hKcog := hBWcog
      hdisjAU := hdisjAU, hdisjAW := hdisjAW
      hdisjBU := hdisjBU, hdisjBW := hdisjBW, hdisjUW := hdisjUW
      hcover := hcover }⟩
  · exact ⟨{
      A := B, B := A, U := W, W := U, m := B.card
      hAind := hBind, hBind := hAind
      hAcard := rfl
      hBcard := by simpa [hcardAB]
      hm := by simpa [hcardAB] using hm
      hAB := fun {b} hb {a} ha => (hAB ha hb).symm
      hAU := hBW
      hUantiB := fun w hw a ha => hWantiA w hw a ha
      hUantiW := fun w hw u hu => fun h => hUantiW u hu w hw h.symm
      hWantiA := fun u hu b hb => hUantiB u hu b hb
      hUne := hWne, hWne := hUne
      hUcog := hWcog, hKcog := hAUcog
      hdisjAU := hdisjBW, hdisjAW := hdisjBU
      hdisjBU := hdisjAW, hdisjBW := hdisjAU
      hdisjUW := hdisjUW.symm
      hcover := by
        simpa [union_comm, union_left_comm, union_assoc] using hcover }⟩

lemma min_all_cograph_hamiltonian_or_sides
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G) (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support) :
    (∃ c : GraphCycle G, c.support = univ) ∨ Nonempty (AllCographSides G) := by
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  by_cases h1 : F.card = 1
  · exact Or.inl (hamiltonian_cycle_of_card_one F h1)
  · have h2 : 2 ≤ F.card := by
      haveI : Nonempty (Fin F.card) := BlockPartition.nonempty_index F.partition
      have hpos : 0 < F.card := Fin.pos_iff_nonempty.mpr ‹Nonempty (Fin F.card)›
      omega
    exact Or.inr
      (exists_allCographSides_of_two_le_card hT hord hpat F hmin hcog h2)

end Nikoghosyan




