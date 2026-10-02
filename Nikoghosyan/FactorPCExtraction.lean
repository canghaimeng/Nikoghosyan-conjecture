/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.FactorCycleIndex
import Nikoghosyan.CographFactorPorts

/-!
Phase 11, items 2–4: extract an actual properly coloured auxiliary cycle
into `k ≥ 2` DISTINCT factor blocks with opposite-port spanning original
paths, assemble via `assembleCycle` / `replaceGroup`, and contradict a
globally minimum original-edge factor.

No extraction theorem takes a supplied certificate in place of an actual
`Yeo.IsProperlyColored` walk. Start type is split explicitly: block-start
uses even indices; physical-start uses odd block indices and outgoing
seams at `2,4,…,length`, with `getVert 0 = getVert length` as a vertex
equality. The wraparound identity `2 * pred 0 + 2 = 0` is never used.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
variable {Port : Type*} [DecidableEq Port]

/-! ### Internal original certificate -/

structure ExtractedPC (F : CycleFactor G)
    (R : GlobalPortData (G := G) F.partition Port) where
  k : ℕ
  hk : 2 ≤ k
  blocks : Fin k → Fin F.card
  seams : Fin k → PhysEdge (G := G) F.partition
  blocks_inj : Function.Injective blocks
  xs : Fin k → V
  ys : Fin k → V
  hxs : ∀ t, xs t ∈ (F.getCycle (blocks t)).support
  hys : ∀ t, ys t ∈ (F.getCycle (blocks t)).support
  hport : ∀ t, R.port (xs t) ≠ R.port (ys t)
  hseams : ∀ t, G.Adj (ys t)
    (xs (pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) t))

namespace ExtractedPC

variable {F : CycleFactor G}
variable {R : GlobalPortData (G := G) F.partition Port}

noncomputable def pathOf (E : ExtractedPC F R) (t : Fin E.k) : GraphPath G :=
  R.realizedPath (E.blocks t)
    (by simpa [CycleFactor.partition] using E.hxs t)
    (by simpa [CycleFactor.partition] using E.hys t)
    (E.hport t)

lemma pathOf_start (E : ExtractedPC F R) (t : Fin E.k) :
    (E.pathOf t).start = E.xs t :=
  (R.realizedPath_spec (E.blocks t)
    (by simpa [CycleFactor.partition] using E.hxs t)
    (by simpa [CycleFactor.partition] using E.hys t)
    (E.hport t)).1

lemma pathOf_finish (E : ExtractedPC F R) (t : Fin E.k) :
    (E.pathOf t).finish = E.ys t :=
  (R.realizedPath_spec (E.blocks t)
    (by simpa [CycleFactor.partition] using E.hxs t)
    (by simpa [CycleFactor.partition] using E.hys t)
    (E.hport t)).2.1

lemma pathOf_support (E : ExtractedPC F R) (t : Fin E.k) :
    (E.pathOf t).support = (F.getCycle (E.blocks t)).support := by
  unfold pathOf
  simpa [CycleFactor.partition] using
    (R.realizedPath_spec (E.blocks t)
      (by simpa [CycleFactor.partition] using E.hxs t)
      (by simpa [CycleFactor.partition] using E.hys t)
      (E.hport t)).2.2

noncomputable def pathList (E : ExtractedPC F R) : List (GraphPath G) :=
  List.ofFn E.pathOf

lemma length_pathList (E : ExtractedPC F R) : E.pathList.length = E.k := by
  simp [pathList]

lemma pathList_get (E : ExtractedPC F R) {i : ℕ} (hi : i < E.pathList.length) :
    E.pathList.get ⟨i, hi⟩ =
      E.pathOf ⟨i, by simpa [length_pathList] using hi⟩ := by
  simp [pathList, List.get_ofFn]

lemma pairwise_pathList (E : ExtractedPC F R) :
    E.pathList.Pairwise fun p q => Disjoint p.support q.support := by
  rw [List.pairwise_iff_get]
  intro a b hab
  have ha : a.1 < E.k := by simpa [length_pathList] using a.2
  have hb : b.1 < E.k := by simpa [length_pathList] using b.2
  have hne : (⟨a.1, ha⟩ : Fin E.k) ≠ ⟨b.1, hb⟩ := by
    intro h
    exact Nat.ne_of_lt hab (Fin.mk.inj_iff.mp h)
  have hblocks : E.blocks ⟨a.1, ha⟩ ≠ E.blocks ⟨b.1, hb⟩ := fun h =>
    hne (E.blocks_inj h)
  have hd := F.disjoint_getCycle hblocks
  have ha' : a.1 < E.pathList.length := a.2
  have hb' : b.1 < E.pathList.length := b.2
  rw [E.pathList_get ha', E.pathList_get hb', E.pathOf_support, E.pathOf_support]
  exact hd

lemma hedges_pathList (E : ExtractedPC F R) :
    ∀ i (hi : i + 1 < E.pathList.length),
      G.Adj (E.pathList.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (E.pathList.get ⟨i + 1, hi⟩).start := by
  intro i hi
  have hi' : i + 1 < E.k := by simpa [length_pathList] using hi
  have hi0 : i < E.k := Nat.lt_of_succ_lt hi'
  have hsucc :
      pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) E.hk) ⟨i, hi0⟩ =
        ⟨i + 1, hi'⟩ := by
    ext
    exact Nat.mod_eq_of_lt hi'
  have hadj := E.hseams ⟨i, hi0⟩
  rw [hsucc] at hadj
  rw [E.pathList_get, E.pathList_get, E.pathOf_finish, E.pathOf_start]
  exact hadj

lemma pathList_ne_nil (E : ExtractedPC F R) : E.pathList ≠ [] := by
  intro h
  have hlen := E.length_pathList
  have hk := E.hk
  have hz : E.pathList.length = 0 := by simp [h]
  omega

lemma hclose_pathList (E : ExtractedPC F R) :
    G.Adj (E.pathList.getLast E.pathList_ne_nil).finish
      (E.pathList.head E.pathList_ne_nil).start := by
  have hlen := E.length_pathList
  have hk := E.hk
  have hne := E.pathList_ne_nil
  have hlastIdx : E.k - 1 < E.k := by omega
  have hlast : E.pathList.getLast hne = E.pathOf ⟨E.k - 1, hlastIdx⟩ := by
    rw [List.getLast_eq_getElem hne]
    have : E.pathList.length - 1 = E.k - 1 := by omega
    simp [pathList, this]
  have hhead : E.pathList.head hne = E.pathOf ⟨0, by omega⟩ := by
    rw [List.head_eq_getElem_zero hne]
    simp [pathList]
  have hsucc :
      pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) E.hk) ⟨E.k - 1, hlastIdx⟩ =
        ⟨0, by omega⟩ :=
    pcSucc_last E.hk
  have hadj := E.hseams ⟨E.k - 1, hlastIdx⟩
  rw [hsucc] at hadj
  rw [hlast, hhead, E.pathOf_finish, E.pathOf_start]
  exact hadj

lemma three_le_supportUnion (E : ExtractedPC F R) :
    3 ≤ (GraphPath.supportUnion E.pathList).card := by
  have ht0 : (0 : ℕ) < E.k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) E.hk
  let t0 : Fin E.k := ⟨0, ht0⟩
  have h3 := (F.getCycle (E.blocks t0)).three_le_card_support
  have hmem : E.pathOf t0 ∈ E.pathList := List.mem_ofFn.2 ⟨t0, rfl⟩
  have hle : (E.pathOf t0).support.card ≤ (GraphPath.supportUnion E.pathList).card := by
    refine card_le_card ?_
    intro x hx
    exact GraphPath.mem_supportUnion.2 ⟨E.pathOf t0, hmem, hx⟩
  have hcard :
      (E.pathOf t0).support.card = (F.getCycle (E.blocks t0)).support.card :=
    congrArg Finset.card (E.pathOf_support t0)
  omega

noncomputable def assembled (E : ExtractedPC F R) : GraphCycle G :=
  GraphPath.assembleCycle E.pathList
    (by simpa [length_pathList] using E.hk)
    E.pairwise_pathList E.hedges_pathList E.hclose_pathList
    E.three_le_supportUnion

lemma support_assembled (E : ExtractedPC F R) :
    E.assembled.support = GraphPath.supportUnion E.pathList :=
  GraphPath.support_assembleCycle E.pathList
    (by simpa [length_pathList] using E.hk)
    E.pairwise_pathList E.hedges_pathList E.hclose_pathList
    E.three_le_supportUnion

noncomputable def selected (E : ExtractedPC F R) : Finset (Fin F.card) :=
  Finset.univ.image E.blocks

lemma selected_card (E : ExtractedPC F R) : E.selected.card = E.k := by
  simp [selected, card_image_of_injective _ E.blocks_inj, Fintype.card_fin]

lemma two_le_selected (E : ExtractedPC F R) : 2 ≤ E.selected.card := by
  simpa [selected_card] using E.hk

lemma supportUnion_eq_selectedSupport (E : ExtractedPC F R) :
    GraphPath.supportUnion E.pathList = F.selectedSupport E.selected := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := GraphPath.mem_supportUnion.1 hx
    obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hp
    have hxB : x ∈ (F.getCycle (E.blocks t)).support := by
      simpa [pathOf_support] using hxp
    exact (CycleFactor.mem_selectedSupport (F := F)).2
      ⟨E.blocks t, by simp [selected], hxB⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hx
    obtain ⟨t, -, rfl⟩ := mem_image.1 hi
    refine GraphPath.mem_supportUnion.2 ⟨E.pathOf t, List.mem_ofFn.2 ⟨t, rfl⟩, ?_⟩
    simpa [pathOf_support] using hxi

lemma assembled_selectedSupport (E : ExtractedPC F R) :
    E.assembled.support = F.selectedSupport E.selected :=
  E.support_assembled.trans E.supportUnion_eq_selectedSupport

lemma not_of_min (E : ExtractedPC F R)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card) : False :=
  F.not_exists_merge_of_min hmin E.selected E.two_le_selected
    E.assembled E.assembled_selectedSupport

end ExtractedPC

/-! ### Extraction from an actual PC walk -/

section Extraction

variable {F : CycleFactor G}
variable {R : GlobalPortData (G := G) F.partition Port}

lemma exists_extracted_of_blockStart {i : Fin F.card}
    (w : (aux (G := G) F.partition).Walk (.inl i) (.inl i))
    (hpc : Yeo.IsProperlyColored w (auxColoring (G := G) F.partition R.port)) :
    Nonempty (ExtractedPC F R) := by
  classical
  have hc : w.IsCycle := hpc.1
  have hEven : Even w.length := aux_cycle_even_length hc
  have h4 : 4 ≤ w.length := aux_cycle_four_le hc
  let k := w.length / 2
  have hk : 2 ≤ k := two_le_half hEven h4
  have hLk : 2 * k = w.length := two_mul_half hEven
  have hpos : 0 < k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk
  let blocks : Fin k → Fin F.card := fun t =>
    Classical.choose
      (aux_getVert_even_inl (w := w)
        (hn := Nat.le_of_lt (two_mul_lt_of_div hEven t.2))
        (he := even_two_mul t.1))
  let seams : Fin k → PhysEdge (G := G) F.partition := fun t =>
    Classical.choose
      (aux_getVert_odd_inr (w := w)
        (hn := Nat.le_of_lt (two_mul_add_one_lt_of_div hEven t.2))
        (ho := odd_two_mul_add_one t.1))
  have hBspec (t : Fin k) :
      w.getVert (2 * t.1) = .inl (blocks t) :=
    Classical.choose_spec
      (aux_getVert_even_inl (w := w)
        (hn := Nat.le_of_lt (two_mul_lt_of_div hEven t.2))
        (he := even_two_mul t.1))
  have hSspec (t : Fin k) :
      w.getVert (2 * t.1 + 1) = .inr (seams t) :=
    Classical.choose_spec
      (aux_getVert_odd_inr (w := w)
        (hn := Nat.le_of_lt (two_mul_add_one_lt_of_div hEven t.2))
        (ho := odd_two_mul_add_one t.1))
  have hBinj : Function.Injective blocks := by
    intro a b hab
    have : w.getVert (2 * a.1) = w.getVert (2 * b.1) := by
      rw [hBspec a, hBspec b, hab]
    exact Fin.ext (by
      have := cycle_getVert_inj hc (two_mul_lt_of_div hEven a.2)
        (two_mul_lt_of_div hEven b.2) this
      omega)
  have hinc_out (t : Fin k) :
      (aux (G := G) F.partition).Adj (.inl (blocks t)) (.inr (seams t)) := by
    have hadj := w.adj_getVert_succ (two_mul_lt_of_div hEven t.2)
    simpa [hBspec t, hSspec t] using hadj
  have hsuccB (t : Fin k) :
      w.getVert (2 * t.1 + 2) = .inl (blocks (pcSucc hpos t)) := by
    have hle := two_mul_add_two_le_of_div hEven t.2
    rcases eq_or_lt_of_le hle with hEq | hlt
    · have ht : t.1 = k - 1 := by omega
      have htF : t = ⟨k - 1, by omega⟩ := Fin.ext ht
      have h0 : pcSucc hpos t = ⟨0, hpos⟩ := by
        rw [htF]
        exact pcSucc_last hk
      have : w.getVert (2 * t.1 + 2) = w.getVert 0 := by
        have : 2 * t.1 + 2 = w.length := by omega
        rw [this, closed_getVert_zero_eq_length]
      have hstart : w.getVert 0 = .inl (blocks ⟨0, hpos⟩) :=
        hBspec ⟨0, hpos⟩
      simpa [h0] using this.trans hstart
    · have ht' : t.1 + 1 < k := by omega
      have hts : pcSucc hpos t = ⟨t.1 + 1, ht'⟩ := pcSucc_of_lt hpos ht'
      have hB := hBspec ⟨t.1 + 1, ht'⟩
      have : 2 * (t.1 + 1) = 2 * t.1 + 2 := by omega
      simpa [hts, this] using hB
  have hinc_in (t : Fin k) :
      (aux (G := G) F.partition).Adj (.inr (seams t))
        (.inl (blocks (pcSucc hpos t))) := by
    have hadj := w.adj_getVert_succ (two_mul_add_one_lt_of_div hEven t.2)
    simpa [hSspec t, hsuccB t] using hadj
  have hinc_in_pred (t : Fin k) :
      (aux (G := G) F.partition).Adj (.inr (seams (pcPred hpos t)))
        (.inl (blocks t)) := by
    have := hinc_in (pcPred hpos t)
    simpa [pcPred_succ hpos t] using this
  let ys : Fin k → V := fun t =>
    endpointOf (G := G) F.partition (blocks t) (seams t)
      (incident_of_adj_inl_inr (hinc_out t))
  let xs : Fin k → V := fun t =>
    endpointOf (G := G) F.partition (blocks t) (seams (pcPred hpos t))
      (incident_of_adj_inr_inl (hinc_in_pred t))
  have hxs : ∀ t, xs t ∈ (F.getCycle (blocks t)).support := by
    intro t
    change endpointOf (G := G) F.partition (blocks t) (seams (pcPred hpos t))
        (hinc_in_pred t) ∈ (F.getCycle (blocks t)).support
    simpa [CycleFactor.partition] using
      endpointOf_mem_block (G := G) F.partition (blocks t)
        (seams (pcPred hpos t)) (incident_of_adj_inr_inl (hinc_in_pred t))
  have hys : ∀ t, ys t ∈ (F.getCycle (blocks t)).support := by
    intro t
    change endpointOf (G := G) F.partition (blocks t) (seams t) (hinc_out t) ∈
      (F.getCycle (blocks t)).support
    simpa [CycleFactor.partition] using
      endpointOf_mem_block (G := G) F.partition (blocks t) (seams t)
        (incident_of_adj_inl_inr (hinc_out t))
  have hport : ∀ t, R.port (xs t) ≠ R.port (ys t) := by
    intro t
    by_cases ht0 : t.1 = 0
    · have hnil : ¬ w.Nil := hc.not_nil
      have hlenpos : 0 < w.length := (Walk.not_nil_iff_lt_length).1 hnil
      have ht : t = ⟨0, hpos⟩ := Fin.ext ht0
      subst ht
      have hL0 : w.getVert 0 = .inl (blocks ⟨0, hpos⟩) := hBspec ⟨0, hpos⟩
      have hL1 : w.getVert 1 = .inr (seams ⟨0, hpos⟩) := hSspec ⟨0, hpos⟩
      have hLm : w.getVert (w.length - 1) = .inr (seams ⟨k - 1, by omega⟩) := by
        have : 2 * (k - 1) + 1 = w.length - 1 := by omega
        simpa [this] using hSspec ⟨k - 1, by omega⟩
      have hLL : w.getVert w.length = .inl (blocks ⟨0, hpos⟩) := by
        simpa [Walk.getVert_length] using hL0
      have cfirst :=
        dartColor_getVert (P := F.partition) R.port w (n := 0) hlenpos
      have clast :=
        dartColor_getVert (P := F.partition) R.port w (n := w.length - 1)
          (by omega)
      have hf := Walk.firstDart_eq (p := w) hnil
        (by simpa [Walk.length_darts] using hlenpos)
      have hl := Walk.lastDart_eq (p := w) hnil
        (by simpa [Walk.length_darts] using hlenpos)
      have hne := hpc.2.2 hnil
      have hpred : pcPred hpos ⟨0, hpos⟩ = ⟨k - 1, by omega⟩ := pcPred_zero hk
      obtain ⟨hincF, hfirst⟩ :=
        auxColor_of_inl_inr (P := F.partition) R.port
          (w.adj_getVert_succ hlenpos) hL0 hL1
      obtain ⟨hincL, hlastC⟩ :=
        auxColor_of_inr_inl (P := F.partition) R.port
          (w.adj_getVert_succ (by omega : w.length - 1 < w.length))
          hLm (by
            have : (w.length - 1) + 1 = w.length := by omega
            simpa [this] using hLL)
      have hyseq :
          endpointOf (G := G) F.partition (blocks ⟨0, hpos⟩) (seams ⟨0, hpos⟩)
              hincF = ys ⟨0, hpos⟩ :=
        endpointOf_proof_irrel hincF (incident_of_adj_inl_inr (hinc_out ⟨0, hpos⟩))
      have hxseq :
          endpointOf (G := G) F.partition (blocks ⟨0, hpos⟩)
              (seams ⟨k - 1, by omega⟩) hincL = xs ⟨0, hpos⟩ := by
        have hincP :
            incident (G := G) F.partition (blocks ⟨0, hpos⟩)
              (seams ⟨k - 1, by omega⟩) := by
          convert incident_of_adj_inr_inl (hinc_in_pred ⟨0, hpos⟩)
          exact congrArg Fin.val hpred.symm
        apply Eq.trans (endpointOf_proof_irrel hincL hincP)
        simp [xs, hpred]
      have hneProd :
          ((blocks ⟨0, hpos⟩, R.port (ys ⟨0, hpos⟩)) :
              Fin F.card × Port) ≠
            (blocks ⟨0, hpos⟩, R.port (xs ⟨0, hpos⟩)) := by
        have hne' := hne
        have hdl : w.darts.length = w.length := Walk.length_darts w
        rw [hf] at hne'
        rw [hl] at hne'
        simp only [hdl] at hne'
        rw [cfirst, clast, hfirst, hlastC, hyseq, hxseq] at hne'
        exact hne'
      intro hp
      exact ports_ne_of_prod (Ne.symm hneProd) hp
    · have htpos : 0 < t.1 := Nat.pos_of_ne_zero ht0
      have hn : 2 * t.1 < w.length := two_mul_lt_of_div hEven t.2
      have halt := hpc.2.1 (i := 2 * t.1 - 1)
        (by simpa [Walk.length_darts] using
          (by omega : 2 * t.1 - 1 + 1 < w.length))
      have hL : w.getVert (2 * t.1) = .inl (blocks t) := hBspec t
      have hR : w.getVert (2 * t.1 + 1) = .inr (seams t) := hSspec t
      have hLm : w.getVert (2 * t.1 - 1) = .inr (seams (pcPred hpos t)) := by
        have hv : (pcPred hpos t).1 = t.1 - 1 := pcPred_val_pos hpos htpos
        have : 2 * (pcPred hpos t).1 + 1 = 2 * t.1 - 1 := by omega
        simpa [this] using hSspec (pcPred hpos t)
      have cin :=
        dartColor_getVert (P := F.partition) R.port w
          (n := 2 * t.1 - 1) (by omega)
      have cout :=
        dartColor_getVert (P := F.partition) R.port w hn
      obtain ⟨hincIn, hcin⟩ :=
        auxColor_of_inr_inl (P := F.partition) R.port
          (w.adj_getVert_succ (by omega : 2 * t.1 - 1 < w.length))
          hLm (by
            have : 2 * t.1 - 1 + 1 = 2 * t.1 := by omega
            simpa [this] using hL)
      obtain ⟨hincOut, hcout⟩ :=
        auxColor_of_inl_inr (P := F.partition) R.port
          (w.adj_getVert_succ hn) hL hR
      have hxseq :
          endpointOf (G := G) F.partition (blocks t) (seams (pcPred hpos t))
              hincIn = xs t :=
        endpointOf_proof_irrel hincIn (incident_of_adj_inr_inl (hinc_in_pred t))
      have hyseq :
          endpointOf (G := G) F.partition (blocks t) (seams t) hincOut =
            ys t :=
        endpointOf_proof_irrel hincOut (incident_of_adj_inl_inr (hinc_out t))
      have hneProd :
          ((blocks t, R.port (xs t)) : Fin F.card × Port) ≠
            (blocks t, R.port (ys t)) := by
        have halt' := halt
        have hidx : (2 * t.1 - 1 + 1 : ℕ) = 2 * t.1 := by omega
        simp only [hidx] at halt'
        rw [cin, hcin, hxseq, cout, hcout, hyseq] at halt'
        exact halt'
      exact ports_ne_of_prod hneProd
  have hseams : ∀ t, G.Adj (ys t)
      (xs (pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) t)) := by
    intro t
    have hsucc :
        pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) t = pcSucc hpos t :=
      rfl
    have hadj :=
      adj_of_endpoints (G := G) F.partition
        (incident_of_adj_inl_inr (hinc_out t))
        (incident_of_adj_inr_inl (hinc_in t)) (fun h =>
          (pcSucc_ne hk t) (hBinj h))
    have hxsucc :
        xs (pcSucc hpos t) =
          endpointOf (G := G) F.partition (blocks (pcSucc hpos t)) (seams t)
            (incident_of_adj_inr_inl (hinc_in t)) := by
      change endpointOf (G := G) F.partition (blocks (pcSucc hpos t))
          (seams (pcPred hpos (pcSucc hpos t)))
          (incident_of_adj_inr_inl (hinc_in_pred (pcSucc hpos t))) = _
      refine (endpointOf_congr (congrArg seams (pcSucc_pred hpos t)) _).trans ?_
      exact endpointOf_proof_irrel _ (incident_of_adj_inr_inl (hinc_in t))
    rw [hsucc, hxsucc]
    exact hadj
  exact ⟨{
    k := k
    hk := hk
    blocks := blocks
    seams := seams
    blocks_inj := hBinj
    xs := xs
    ys := ys
    hxs := hxs
    hys := hys
    hport := hport
    hseams := hseams
  }⟩

lemma exists_extracted_of_physStart {e : PhysEdge (G := G) F.partition}
    (w : (aux (G := G) F.partition).Walk (.inr e) (.inr e))
    (hpc : Yeo.IsProperlyColored w (auxColoring (G := G) F.partition R.port)) :
    Nonempty (ExtractedPC F R) := by
  classical
  have hc : w.IsCycle := hpc.1
  have hEven : Even w.length := aux_cycle_even_length_any hc
  have h4 : 4 ≤ w.length := aux_cycle_four_le_any hc
  let k := w.length / 2
  have hk : 2 ≤ k := two_le_half hEven h4
  have hLk : 2 * k = w.length := two_mul_half hEven
  have hpos : 0 < k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk
  let blocks : Fin k → Fin F.card := fun t =>
    Classical.choose
      (aux_getVert_odd_inl_of_phys (w := w)
        (hn := Nat.le_of_lt (two_mul_add_one_lt_of_div hEven t.2))
        (ho := odd_two_mul_add_one t.1))
  let seams : Fin k → PhysEdge (G := G) F.partition := fun t =>
    Classical.choose
      (aux_getVert_even_inr_of_phys (w := w)
        (hn := two_mul_add_two_le_of_div hEven t.2)
        (he := even_two_mul_add_two t.1))
  have hBspec (t : Fin k) :
      w.getVert (2 * t.1 + 1) = .inl (blocks t) :=
    Classical.choose_spec
      (aux_getVert_odd_inl_of_phys (w := w)
        (hn := Nat.le_of_lt (two_mul_add_one_lt_of_div hEven t.2))
        (ho := odd_two_mul_add_one t.1))
  have hSspec (t : Fin k) :
      w.getVert (2 * t.1 + 2) = .inr (seams t) :=
    Classical.choose_spec
      (aux_getVert_even_inr_of_phys (w := w)
        (hn := two_mul_add_two_le_of_div hEven t.2)
        (he := even_two_mul_add_two t.1))
  have hBinj : Function.Injective blocks := by
    intro a b hab
    have : w.getVert (2 * a.1 + 1) = w.getVert (2 * b.1 + 1) := by
      rw [hBspec a, hBspec b, hab]
    exact Fin.ext (by
      have := cycle_getVert_inj hc (two_mul_add_one_lt_of_div hEven a.2)
        (two_mul_add_one_lt_of_div hEven b.2) this
      omega)
  have hinc_out (t : Fin k) :
      (aux (G := G) F.partition).Adj (.inl (blocks t)) (.inr (seams t)) := by
    have hadj := w.adj_getVert_succ (two_mul_add_one_lt_of_div hEven t.2)
    simpa [hBspec t, hSspec t] using hadj
  have hpredS (t : Fin k) :
      w.getVert (2 * t.1) = .inr (seams (pcPred hpos t)) := by
    by_cases ht0 : t.1 = 0
    · have ht : t = ⟨0, hpos⟩ := Fin.ext ht0
      subst ht
      have hpred : pcPred hpos ⟨0, hpos⟩ = ⟨k - 1, by omega⟩ := pcPred_zero hk
      have hS : w.getVert (2 * (k - 1) + 2) = .inr (seams ⟨k - 1, by omega⟩) :=
        hSspec ⟨k - 1, by omega⟩
      have hidx : 2 * (k - 1) + 2 = w.length := by omega
      have hstart : w.getVert 0 = w.getVert w.length :=
        closed_getVert_zero_eq_length w
      have : w.getVert 0 = .inr (seams ⟨k - 1, by omega⟩) :=
        hstart.trans (by simpa [hidx] using hS)
      simpa [hpred] using this
    · have htpos : 0 < t.1 := Nat.pos_of_ne_zero ht0
      have hv : (pcPred hpos t).1 = t.1 - 1 := pcPred_val_pos hpos htpos
      have : 2 * (pcPred hpos t).1 + 2 = 2 * t.1 := by omega
      simpa [this] using hSspec (pcPred hpos t)
  have hinc_in_pred (t : Fin k) :
      (aux (G := G) F.partition).Adj (.inr (seams (pcPred hpos t)))
        (.inl (blocks t)) := by
    have hn : 2 * t.1 < w.length := two_mul_lt_of_div hEven t.2
    have hadj := w.adj_getVert_succ hn
    simpa [hpredS t, hBspec t] using hadj
  have hinc_in (t : Fin k) :
      (aux (G := G) F.partition).Adj (.inr (seams t))
        (.inl (blocks (pcSucc hpos t))) := by
    simpa [pcPred_succ hpos (pcSucc hpos t), pcSucc_pred hpos t] using
      hinc_in_pred (pcSucc hpos t)
  let ys : Fin k → V := fun t =>
    endpointOf (G := G) F.partition (blocks t) (seams t)
      (incident_of_adj_inl_inr (hinc_out t))
  let xs : Fin k → V := fun t =>
    endpointOf (G := G) F.partition (blocks t) (seams (pcPred hpos t))
      (incident_of_adj_inr_inl (hinc_in_pred t))
  have hxs : ∀ t, xs t ∈ (F.getCycle (blocks t)).support := by
    intro t
    change endpointOf (G := G) F.partition (blocks t) (seams (pcPred hpos t))
        (hinc_in_pred t) ∈ (F.getCycle (blocks t)).support
    simpa [CycleFactor.partition] using
      endpointOf_mem_block (G := G) F.partition (blocks t)
        (seams (pcPred hpos t)) (incident_of_adj_inr_inl (hinc_in_pred t))
  have hys : ∀ t, ys t ∈ (F.getCycle (blocks t)).support := by
    intro t
    change endpointOf (G := G) F.partition (blocks t) (seams t) (hinc_out t) ∈
      (F.getCycle (blocks t)).support
    simpa [CycleFactor.partition] using
      endpointOf_mem_block (G := G) F.partition (blocks t) (seams t)
        (incident_of_adj_inl_inr (hinc_out t))
  have hport : ∀ t, R.port (xs t) ≠ R.port (ys t) := by
    intro t
    have hn : 2 * t.1 + 1 < w.length := two_mul_add_one_lt_of_div hEven t.2
    have halt := hpc.2.1 (i := 2 * t.1)
      (by simpa [Walk.length_darts] using hn)
    have hL : w.getVert (2 * t.1) = .inr (seams (pcPred hpos t)) := hpredS t
    have hM : w.getVert (2 * t.1 + 1) = .inl (blocks t) := hBspec t
    have hR : w.getVert (2 * t.1 + 2) = .inr (seams t) := hSspec t
    have cin :=
      dartColor_getVert (P := F.partition) R.port w
        (two_mul_lt_of_div hEven t.2)
    have cout :=
      dartColor_getVert (P := F.partition) R.port w hn
    obtain ⟨hincIn, hcin⟩ :=
      auxColor_of_inr_inl (P := F.partition) R.port
        (w.adj_getVert_succ (two_mul_lt_of_div hEven t.2)) hL hM
    obtain ⟨hincOut, hcout⟩ :=
      auxColor_of_inl_inr (P := F.partition) R.port
        (w.adj_getVert_succ hn) hM hR
    have hxseq :
        endpointOf (G := G) F.partition (blocks t) (seams (pcPred hpos t))
            hincIn = xs t :=
      endpointOf_proof_irrel hincIn (incident_of_adj_inr_inl (hinc_in_pred t))
    have hyseq :
        endpointOf (G := G) F.partition (blocks t) (seams t) hincOut = ys t :=
      endpointOf_proof_irrel hincOut (incident_of_adj_inl_inr (hinc_out t))
    have hneProd :
        ((blocks t, R.port (xs t)) : Fin F.card × Port) ≠
          (blocks t, R.port (ys t)) := by
      have halt' := halt
      rw [cin, hcin, hxseq, cout, hcout, hyseq] at halt'
      exact halt'
    exact ports_ne_of_prod hneProd
  have hseams : ∀ t, G.Adj (ys t)
      (xs (pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) t)) := by
    intro t
    have hsucc :
        pcSucc (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk) t = pcSucc hpos t :=
      rfl
    have hadj :=
      adj_of_endpoints (G := G) F.partition
        (incident_of_adj_inl_inr (hinc_out t))
        (incident_of_adj_inr_inl (hinc_in t)) (fun h =>
          (pcSucc_ne hk t) (hBinj h))
    have hxsucc :
        xs (pcSucc hpos t) =
          endpointOf (G := G) F.partition (blocks (pcSucc hpos t)) (seams t)
            (incident_of_adj_inr_inl (hinc_in t)) := by
      change endpointOf (G := G) F.partition (blocks (pcSucc hpos t))
          (seams (pcPred hpos (pcSucc hpos t)))
          (incident_of_adj_inr_inl (hinc_in_pred (pcSucc hpos t))) = _
      refine (endpointOf_congr (congrArg seams (pcSucc_pred hpos t)) _).trans ?_
      exact endpointOf_proof_irrel _ (incident_of_adj_inr_inl (hinc_in t))
    rw [hsucc, hxsucc]
    exact hadj
  exact ⟨{
    k := k
    hk := hk
    blocks := blocks
    seams := seams
    blocks_inj := hBinj
    xs := xs
    ys := ys
    hxs := hxs
    hys := hys
    hport := hport
    hseams := hseams
  }⟩

lemma exists_extracted_of_pc
    {u : Fin F.card ⊕ PhysEdge (G := G) F.partition}
    (w : (aux (G := G) F.partition).Walk u u)
    (hpc : Yeo.IsProperlyColored w (auxColoring (G := G) F.partition R.port)) :
    Nonempty (ExtractedPC F R) := by
  cases u with
  | inl i => exact exists_extracted_of_blockStart w hpc
  | inr e => exact exists_extracted_of_physStart w hpc

lemma exists_extracted_of_hasPC
    (h : Yeo.HasProperlyColoredCycle
      (auxColoring (G := G) F.partition R.port)) :
    Nonempty (ExtractedPC F R) := by
  obtain ⟨u, w, hw⟩ := h
  exact exists_extracted_of_pc w hw

/-- A globally minimum original-edge factor, equipped with one global port
map that realises opposite ports on every block, admits no properly
coloured auxiliary cycle. Includes the two-block four-edge case. -/
lemma minFactor_not_hasProperlyColoredCycle
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (R : GlobalPortData (G := G) F.partition Port) :
    ¬ Yeo.HasProperlyColoredCycle
        (auxColoring (G := G) F.partition R.port) := by
  intro h
  obtain ⟨E⟩ := exists_extracted_of_hasPC (R := R) h
  exact E.not_of_min hmin

lemma minFactor_not_hasProperlyColoredCycle_cograph
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support) :
    ¬ Yeo.HasProperlyColoredCycle
        (auxColoring (G := G) F.partition (factorPort F)) :=
  minFactor_not_hasProperlyColoredCycle hmin
    (globalPortData_of_cograph_factor F hcog)

/-- Yeo block splitter with the no-PC hypothesis discharged from a
globally minimum cograph-block factor. -/
lemma exists_block_splitter_of_min_cograph
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V) :
    ∃ i : Fin F.card,
      Yeo.SplittingVertex
        (auxColoring (G := G) F.partition (factorPort F)) (.inl i) := by
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  haveI : Nonempty (Fin F.card) := BlockPartition.nonempty_index F.partition
  exact exists_block_splitter (P := F.partition) (factorPort F) hT hord
    (minFactor_not_hasProperlyColoredCycle_cograph hmin hcog)

end Extraction

end Nikoghosyan
