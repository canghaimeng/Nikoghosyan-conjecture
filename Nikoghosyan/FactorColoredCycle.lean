/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.CographFactorPorts
import Nikoghosyan.Cograph.EndpointCuts

/-!
Phase 10: actual cograph-factor ports, two-block four-edge obstruction,
outside-component attachments in one R-class, per-component singleton
exclusion, and the common used-port original cut.

General `k ≥ 2` extraction from an arbitrary properly coloured auxiliary
walk is not closed in this module. The two-block four-edge case uses the
actual global port `factorPort` derived in `CographFactorPorts`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
variable {F : CycleFactor G}

/-- Two distinct cograph factor blocks, each with opposite actual R-classes
realised by the derived global port, joined by two physical original cross
edges, cannot occur in a globally minimum original-edge factor. -/
lemma minFactor_not_twoBlock_fourEdge_cograph
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    {i j : Fin F.card} (hij : i ≠ j)
    {xi yi xj yj : V}
    (hxi : xi ∈ (F.getCycle i).support) (hyi : yi ∈ (F.getCycle i).support)
    (hxj : xj ∈ (F.getCycle j).support) (hyj : yj ∈ (F.getCycle j).support)
    (hpi : factorPort F xi ≠ factorPort F yi)
    (hpj : factorPort F xj ≠ factorPort F yj)
    (hxy : G.Adj yi xj) (hyx : G.Adj yj xi) : False := by
  let Di : PortData (G := G) (F.getCycle i).support (Finset V) :=
    { port := factorPort F
      realize := fun hx hy hp =>
        exists_spanning_of_factor_ports F hcog hx hy hp }
  let Dj : PortData (G := G) (F.getCycle j).support (Finset V) :=
    { port := factorPort F
      realize := fun hx hy hp =>
        exists_spanning_of_factor_ports F hcog hx hy hp }
  exact minFactor_not_twoBlock_portData (G := G) (Port := Finset V) F hmin hij
    Di Dj hxi hyi hxj hyj hpi hpj hxy hyx

lemma attachment_factorPort_eq
    {i : Fin F.card}
    (hsplit : Yeo.SplittingVertex
      (auxColoring (G := G) F.partition (factorPort F)) (.inl i))
    {x y a b : V}
    (hx : F.partition.index x ≠ i) (hy : F.partition.index y ≠ i)
    (ha : F.partition.index a = i) (hb : F.partition.index b = i)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (hW : (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    factorPort F a = factorPort F b :=
  attachment_port_eq (G := G) (P := F.partition) (factorPort F)
    hsplit hx hy ha hb hxa hyb hW

lemma attachment_same_rClass
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    {i : Fin F.card}
    (hsplit : Yeo.SplittingVertex
      (auxColoring (G := G) F.partition (factorPort F)) (.inl i))
    {x y a b : V}
    (hx : F.partition.index x ≠ i) (hy : F.partition.index y ≠ i)
    (ha : a ∈ (F.getCycle i).support) (hb : b ∈ (F.getCycle i).support)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (hW : (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    factorPort F a = factorPort F b ∧
      b ∈ Cograph.rNonadjClass (G := G) (F.getCycle i).support a := by
  have hai : F.partition.index a = i := F.partition.index_eq
    (by simpa [CycleFactor.partition] using ha)
  have hbi : F.partition.index b = i := F.partition.index_eq
    (by simpa [CycleFactor.partition] using hb)
  have heq :=
    attachment_factorPort_eq (F := F) hsplit hx hy hai hbi hxa hyb hW
  have hbal := factor_block_balanced F hcog i
  have hclass := hbal.2.2 ha hb
  have hEq :
      Cograph.rNonadjClass (G := G) (F.getCycle i).support a =
        Cograph.rNonadjClass (G := G) (F.getCycle i).support b := by
    simpa [factorPort_eq_of_mem F ha, factorPort_eq_of_mem F hb] using heq
  exact ⟨heq, hclass.mp hEq⟩

/-- Per-outside-component singleton exclusion. If one component of `G-H`
attaches only through `p ∈ H`, then after deleting `p` that component has
no edge to its complement, `H.erase p` is nonempty, and `c(G-p) ≥ 2`
contradicts 1-toughness. -/
lemma not_component_singleton_attachment
    (hT : OneTough G)
    {i : Fin F.card} {p : V}
    (hp : p ∈ (F.getCycle i).support)
    {x : V} (hx : F.partition.index x ≠ i)
    (hatt : ∀ {y a : V} (hy : F.partition.index y ≠ i)
      (ha : a ∈ (F.getCycle i).support),
      G.Adj y a →
        (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ →
          a = p) : False := by
  let H := (F.getCycle i).support
  let W : Finset V := univ.filter fun z => F.partition.index z ≠ i
  have hxW : x ∈ W := mem_filter.2 ⟨mem_univ x, hx⟩
  let D : Finset V := W.filter fun y =>
    ∃ hy : F.partition.index y ≠ i,
      (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  have hxD : x ∈ D := mem_filter.2 ⟨hxW, ⟨hx, Reachable.rfl⟩⟩
  have hDne : D.Nonempty := ⟨x, hxD⟩
  have hH3 : 3 ≤ (F.getCycle i).support.card :=
    (F.getCycle i).three_le_card_support
  have hAHne : ((F.getCycle i).support.erase p).Nonempty := by
    have hcard : ((F.getCycle i).support.erase p).card =
        (F.getCycle i).support.card - 1 := card_erase_of_mem hp
    have : 0 < ((F.getCycle i).support.erase p).card := by omega
    exact card_pos.mp this
  let A := D
  let B := univ.erase p \ A
  have hAne : A.Nonempty := hDne
  have hBne : B.Nonempty := by
    refine hAHne.mono ?_
    intro z hz
    have hzH : z ∈ H := mem_of_mem_erase hz
    have hzp : z ≠ p := ne_of_mem_erase hz
    have hzidx : F.partition.index z = i := F.partition.index_eq
      (by simpa [CycleFactor.partition] using hzH)
    have hzW : z ∉ W := by
      intro hW
      exact (mem_filter.1 hW).2 hzidx
    have hzA : z ∉ A := by
      intro hA
      exact hzW (mem_filter.1 hA).1
    exact mem_sdiff.2 ⟨mem_erase.2 ⟨hzp, mem_univ z⟩, hzA⟩
  have hU : A ∪ B = univ.erase p := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hA | hB
      · have hai : F.partition.index z ≠ i := (mem_filter.1 (mem_filter.1 hA).1).2
        have hzp : z ≠ p := by
          intro heq
          have : F.partition.index z = i := F.partition.index_eq
            (by simpa [heq, CycleFactor.partition] using hp)
          exact hai this
        exact mem_erase.2 ⟨hzp, mem_univ z⟩
      · exact (mem_sdiff.1 hB).1
    · intro hz
      by_cases hA : z ∈ A
      · exact mem_union.2 (Or.inl hA)
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hz, hA⟩))
  have hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a ha b hb hadj
    have hai : F.partition.index a ≠ i :=
      (mem_filter.1 (mem_filter.1 ha).1).2
    have hbp : b ≠ p := (mem_erase.1 (mem_sdiff.1 hb).1).1
    have hbA : b ∉ A := (mem_sdiff.1 hb).2
    have hreachA :
        (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨a, hai⟩ :=
      (mem_filter.1 ha).2.2
    by_cases hbH : b ∈ H
    · have := hatt (y := a) (a := b) hai hbH hadj hreachA
      exact hbp this
    · have hbi : F.partition.index b ≠ i := by
        intro hbi
        have : b ∈ H := by
          have hbmem := F.partition.mem_index b
          rw [hbi] at hbmem
          simpa [H, CycleFactor.partition] using hbmem
        exact hbH this
      have hbW : b ∈ W := mem_filter.2 ⟨mem_univ b, hbi⟩
      have hadjI :
          (G.induce {z | F.partition.index z ≠ i}).Adj ⟨a, hai⟩ ⟨b, hbi⟩ := by
        simpa [SimpleGraph.induce_adj] using hadj
      have hreachB :
          (G.induce {z | F.partition.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨b, hbi⟩ :=
        hreachA.trans hadjI.reachable
      have : b ∈ A := mem_filter.2 ⟨hbW, ⟨hbi, hreachB⟩⟩
      exact hbA this
  have hxA : hAne.choose ∈ A ∪ B := mem_union_left _ hAne.choose_spec
  have hyB : hBne.choose ∈ A ∪ B := mem_union_right _ hBne.choose_spec
  have hnr :
      ¬ (G.induce ((A ∪ B : Finset V) : Set V)).Reachable
        ⟨hAne.choose, hxA⟩ ⟨hBne.choose, hyB⟩ := by
    intro hR
    obtain ⟨w⟩ := hR
    have hyA : hBne.choose ∈ A :=
      induce_walk_stays_left (G := G) hno hAne.choose_spec hxA hyB w
    exact (mem_sdiff.1 hBne.choose_spec).2 hyA
  have h2 := two_le_componentCount_of_not_reachable (G := G) hxA hyB hnr
  have hEq : univ \ ({p} : Finset V) = A ∪ B := by
    simp [hU, sdiff_singleton_eq_erase]
  have h2' : 2 ≤ componentCount G (univ \ ({p} : Finset V)) := by
    simpa [hEq] using h2
  have hle := hT {p} h2'
  have : ({p} : Finset V).card = 1 := by simp
  omega

lemma original_common_port_cut
    (hT : OneTough G)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    {i : Fin F.card} {p : V}
    (hp : p ∈ (F.getCycle i).support)
    (hW : (univ \ (F.getCycle i).support).Nonempty)
    (hatt : ∀ {x a : V},
      a ∈ (F.getCycle i).support →
      x ∈ univ \ (F.getCycle i).support →
      G.Adj x a → a ∈ factorPort F p) : False := by
  let H := (F.getCycle i).support
  let W := univ \ H
  let P := factorPort F p
  have hPsub : P ⊆ H := factorPort_subset_block F hp
  have hpP : p ∈ P := by
    simpa [P, factorPort_eq_of_mem F hp] using
      Cograph.mem_rNonadjClass_self (G := G) hp
  have hcut := factor_block_partCut F hcog hp
  have hdisj : Disjoint (H \ P) W := by
    rw [Finset.disjoint_left]
    intro z hzHP hzW
    exact (mem_sdiff.1 hzW).2 (mem_sdiff.1 hzHP).1
  have hnocross : ∀ a ∈ H \ P, ∀ b ∈ W, ¬ G.Adj a b := by
    intro a ha b hb hadj
    have haH : a ∈ H := (mem_sdiff.1 ha).1
    have haP : a ∉ P := (mem_sdiff.1 ha).2
    have : a ∈ P := hatt haH hb hadj.symm
    exact haP this
  have hunion : (H \ P) ∪ W = univ \ P := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hHP | hWz
      · exact mem_sdiff.2 ⟨mem_univ z, (mem_sdiff.1 hHP).2⟩
      · have hzH : z ∉ H := (mem_sdiff.1 hWz).2
        exact mem_sdiff.2 ⟨mem_univ z, fun hP => hzH (hPsub hP)⟩
    · intro hz
      obtain ⟨_, hzP⟩ := mem_sdiff.1 hz
      by_cases hzH : z ∈ H
      · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hzH, hzP⟩))
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨mem_univ z, hzH⟩))
  have hadd :=
    Cograph.componentCount_union_of_no_cross (G := G) hdisj hnocross
  have hWpos : 1 ≤ componentCount G W := by
    obtain ⟨z, hz⟩ := hW
    haveI : Nonempty (W : Set V) := ⟨⟨z, by simpa [W] using hz⟩⟩
    have : 0 < Nat.card (G.induce (W : Set V)).ConnectedComponent := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos
    exact Nat.succ_le_iff.mpr this
  have hcount :
      componentCount G (univ \ factorPort F p) =
        (factorPort F p).card + componentCount G W := by
    have h1 : univ \ factorPort F p = (H \ P) ∪ W := hunion.symm
    have h2 : componentCount G ((H \ P) ∪ W) =
        componentCount G (H \ P) + componentCount G W := hadd
    have h3 : componentCount G (H \ P) = (factorPort F p).card := hcut
    simp [h1, h2, h3]
  have hPpos : 1 ≤ (factorPort F p).card :=
    Nat.succ_le_iff.mpr (card_pos.mpr ⟨p, hpP⟩)
  have hsum : 2 ≤ componentCount G (univ \ factorPort F p) := by
    rw [hcount]
    omega
  have hle := hT (factorPort F p) hsum
  have hcontr :
      (factorPort F p).card + componentCount G W ≤ (factorPort F p).card := by
    rw [← hcount]
    exact hle
  omega

end Nikoghosyan
