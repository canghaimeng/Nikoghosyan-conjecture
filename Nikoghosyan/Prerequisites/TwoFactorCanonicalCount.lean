/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Equiv.Set
import Nikoghosyan.Prerequisites.TwoFactorCutNormalization
import Nikoghosyan.Prerequisites.TwoFactorDefs

/-!
# Canonical remainder components and `def(Z(S,T)) = −Δ(S,T)`

Interface §5 of `reports/TWO_FACTOR_GADGET_INTERFACE.md`.

Finite original carriers `originalS/T/U` are the Finset versions of
`classS/classT/classU`. After deleting `canonicalCut Z`, remainder
components are labelled by T-clones, S–T ports, S–S physical edges, or
original `G[U]` components. The signed Tutte deficiency of the canonical
cut equals `-delta G (originalS Z) (originalT Z)`.
-/

universe u

namespace Nikoghosyan
namespace TwoFactor

open Classical
open scoped BigOperators Sym2
open SimpleGraph Set

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ## Finite original carriers -/

/-- Original S-vertices of the initial gadget cut, as a `Finset`. -/
noncomputable def originalS (Z : Set (GadgetVert G)) : Finset V :=
  {v | classS Z v}.toFinset

/-- Original T-vertices of the initial gadget cut, as a `Finset`. -/
noncomputable def originalT (Z : Set (GadgetVert G)) : Finset V :=
  {v | classT Z v}.toFinset

/-- Original U-vertices of the initial gadget cut, as a `Finset`. -/
noncomputable def originalU (Z : Set (GadgetVert G)) : Finset V :=
  {v | classU Z v}.toFinset

lemma mem_originalS_iff {Z : Set (GadgetVert G)} {v : V} :
    v ∈ originalS Z ↔ classS Z v := by
  simp [originalS]

lemma mem_originalT_iff {Z : Set (GadgetVert G)} {v : V} :
    v ∈ originalT Z ↔ classT Z v := by
  simp [originalT]

lemma mem_originalU_iff {Z : Set (GadgetVert G)} {v : V} :
    v ∈ originalU Z ↔ classU Z v := by
  simp [originalU]

lemma classU_of_not_ST {Z : Set (GadgetVert G)} {v : V}
    (hS : ¬ classS Z v) (hT : ¬ classT Z v) : classU Z v := by
  rcases classSTU Z v with h | h | h
  · exact (hS h).elim
  · exact (hT h).elim
  · exact h

lemma disjoint_classS_classU (Z : Set (GadgetVert G)) :
    Disjoint {v | classS Z v} {v | classU Z v} := by
  rw [Set.disjoint_left]
  intro v hS hU
  exact not_classS_of_TU (.inr hU) hS

lemma disjoint_classT_classU (Z : Set (GadgetVert G)) :
    Disjoint {v | classT Z v} {v | classU Z v} := by
  rw [Set.disjoint_left]
  intro v hT hU
  exact not_classT_of_SU (.inr hU) hT

lemma disjoint_originalS_originalT (Z : Set (GadgetVert G)) :
    Disjoint (originalS Z) (originalT Z) := by
  rw [Finset.disjoint_left]
  intro v hS hT
  exact (disjoint_classS_classT Z).le_bot
    ⟨mem_originalS_iff.mp hS, mem_originalT_iff.mp hT⟩

lemma disjoint_originalS_originalU (Z : Set (GadgetVert G)) :
    Disjoint (originalS Z) (originalU Z) := by
  rw [Finset.disjoint_left]
  intro v hS hU
  exact (disjoint_classS_classU Z).le_bot
    ⟨mem_originalS_iff.mp hS, mem_originalU_iff.mp hU⟩

lemma disjoint_originalT_originalU (Z : Set (GadgetVert G)) :
    Disjoint (originalT Z) (originalU Z) := by
  rw [Finset.disjoint_left]
  intro v hT hU
  exact (disjoint_classT_classU Z).le_bot
    ⟨mem_originalT_iff.mp hT, mem_originalU_iff.mp hU⟩

lemma originalSTU_union (Z : Set (GadgetVert G)) :
    originalS Z ∪ originalT Z ∪ originalU Z = (Finset.univ : Finset V) := by
  ext v
  refine ⟨fun _ => Finset.mem_univ v, fun _ => ?_⟩
  simp only [Finset.mem_union, mem_originalS_iff, mem_originalT_iff, mem_originalU_iff]
  rcases classSTU Z v with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

lemma classUSet_eq_remainder (Z : Set (GadgetVert G)) :
    ({v | classU Z v} : Set V) =
      ((originalS Z ∪ originalT Z : Finset V) : Set V)ᶜ := by
  ext v
  simp [mem_originalS_iff, mem_originalT_iff]
  constructor
  · intro hU
    exact ⟨fun hS => not_classS_of_TU (.inr hU) hS,
      fun hT => not_classT_of_SU (.inr hU) hT⟩
  · intro ⟨hS, hT⟩
    exact classU_of_not_ST hS hT

lemma originalU_eq_remainder (Z : Set (GadgetVert G)) :
    originalU Z = remainderVerts G (originalS Z) (originalT Z) := by
  ext v
  simp [originalU, remainderVerts, classUSet_eq_remainder (Z := Z)]

/-- Canonical cut as the pair deleting all S-clones and all T-ports. -/
lemma canonicalCut_eq_pair (Z : Set (GadgetVert G)) :
    canonicalCut Z =
      {x | ∃ v ∈ originalS Z, ∃ b : Fin 2, x = .clone v b} ∪
        {x | ∃ v ∈ originalT Z, ∃ w, ∃ h : G.Adj v w, x = .port v w h} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨v, b, rfl, hS⟩ | ⟨v, w, h, rfl, hT⟩
    · exact .inl ⟨v, mem_originalS_iff.mpr hS, b, rfl⟩
    · exact .inr ⟨v, mem_originalT_iff.mpr hT, w, h, rfl⟩
  · intro hx
    rcases hx with ⟨v, hv, b, rfl⟩ | ⟨v, hv, w, h, rfl⟩
    · exact .inl ⟨v, b, rfl, mem_originalS_iff.mp hv⟩
    · exact .inr ⟨v, w, h, rfl, mem_originalT_iff.mp hv⟩

/-- U-nonisolation from the surviving-port witness, not a degree hypothesis. -/
lemma originalU_nonisolated {Z : Set (GadgetVert G)} {v : V}
    (hv : v ∈ originalU Z) : ∃ w, G.Adj v w :=
  exists_adj_of_classU (mem_originalU_iff.mp hv)

lemma ncard_canonicalCut_original (Z : Set (GadgetVert G)) :
    (canonicalCut Z).ncard =
      2 * (originalS Z).card + ∑ t ∈ originalT Z, G.degree t := by
  rw [ncard_canonicalCut]
  simp [originalS, originalT, ncard_eq_toFinset_card']

/-! ## Remainder labels -/

/-- Connected component of an original U-vertex in `G[U]`. -/
def uComponent (Z : Set (GadgetVert G)) (v : V) (hU : classU Z v) :
    (G.induce {w | classU Z w}).ConnectedComponent :=
  (G.induce {w | classU Z w}).connectedComponentMk ⟨v, hU⟩

/-- Labels of remainder vertices after the canonical cut. -/
inductive CanonicalLabel (Z : Set (GadgetVert G)) where
  | tClone (v : V) (b : Fin 2)
  | stPort (s t : V)
  | ssEdge (e : Sym2 V)
  | uComp (c : (G.induce {w | classU Z w}).ConnectedComponent)

lemma classTU_of_clone_remain {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hx : GadgetVert.clone v b ∉ canonicalCut Z) :
    classT Z v ∨ classU Z v := by
  have hS : ¬ classS Z v := fun hS =>
    hx ((clone_mem_canonicalCut_iff (Z := Z)).mpr hS)
  rcases classSTU Z v with h | h | h
  · exact (hS h).elim
  · exact .inl h
  · exact .inr h

lemma classSU_of_port_remain {Z : Set (GadgetVert G)} {v w : V} {h : G.Adj v w}
    (hx : GadgetVert.port v w h ∉ canonicalCut Z) :
    classS Z v ∨ classU Z v := by
  have hT : ¬ classT Z v := fun hT =>
    hx ((port_mem_canonicalCut_iff (Z := Z)).mpr hT)
  rcases classSTU Z v with hS | hT' | hU
  · exact .inl hS
  · exact (hT hT').elim
  · exact .inr hU

lemma classU_of_clone_remain_not_T {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hx : GadgetVert.clone v b ∉ canonicalCut Z) (hT : ¬ classT Z v) :
    classU Z v :=
  (classTU_of_clone_remain hx).elim (fun h => (hT h).elim) id

lemma classU_of_port_remain_not_S {Z : Set (GadgetVert G)} {v w : V} {h : G.Adj v w}
    (hx : GadgetVert.port v w h ∉ canonicalCut Z) (hS : ¬ classS Z v) :
    classU Z v :=
  (classSU_of_port_remain hx).elim (fun h => (hS h).elim) id

/-- Unique remainder label of a surviving gadget vertex. -/
noncomputable def remainLabel (Z : Set (GadgetVert G)) :
    (x : GadgetVert G) → x ∉ canonicalCut Z → CanonicalLabel Z
  | .clone v b, hx =>
      if hT : classT Z v then
        .tClone v b
      else
        .uComp (uComponent Z v (classU_of_clone_remain_not_T hx hT))
  | .port v w h, hx =>
      if hS : classS Z v then
        if hTt : classT Z w then
          .stPort v w
        else if hSt : classS Z w then
          .ssEdge s(v, w)
        else
          .uComp (uComponent Z w (classU_of_not_ST hSt hTt))
      else
        .uComp (uComponent Z v (classU_of_port_remain_not_S hx hS))

lemma remainLabel_clone_of_T {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hT : classT Z v) (hx : GadgetVert.clone v b ∉ canonicalCut Z) :
    remainLabel Z (.clone v b) hx = .tClone v b :=
  dif_pos hT

lemma remainLabel_clone_of_U {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hU : classU Z v) (hx : GadgetVert.clone v b ∉ canonicalCut Z) :
    remainLabel Z (.clone v b) hx = .uComp (uComponent Z v hU) := by
  have hT : ¬ classT Z v := not_classT_of_SU (.inr hU)
  simp [remainLabel, hT]

lemma remainLabel_port_of_U {Z : Set (GadgetVert G)} {v w : V} {h : G.Adj v w}
    (hU : classU Z v) (hx : GadgetVert.port v w h ∉ canonicalCut Z) :
    remainLabel Z (.port v w h) hx = .uComp (uComponent Z v hU) := by
  have hS : ¬ classS Z v := not_classS_of_TU (.inr hU)
  simp [remainLabel, hS]

lemma remainLabel_port_of_ST {Z : Set (GadgetVert G)} {s t : V} {h : G.Adj s t}
    (hS : classS Z s) (hT : classT Z t)
    (hx : GadgetVert.port s t h ∉ canonicalCut Z) :
    remainLabel Z (.port s t h) hx = .stPort s t := by
  simp [remainLabel, hS, hT]

lemma remainLabel_port_of_SS {Z : Set (GadgetVert G)} {s t : V} {h : G.Adj s t}
    (hS : classS Z s) (hS' : classS Z t)
    (hx : GadgetVert.port s t h ∉ canonicalCut Z) :
    remainLabel Z (.port s t h) hx = .ssEdge s(s, t) := by
  have hT : ¬ classT Z t := not_classT_of_SU (.inl hS')
  simp [remainLabel, hS, hT, hS']

lemma remainLabel_port_of_SU {Z : Set (GadgetVert G)} {s u : V} {h : G.Adj s u}
    (hS : classS Z s) (hU : classU Z u)
    (hx : GadgetVert.port s u h ∉ canonicalCut Z) :
    remainLabel Z (.port s u h) hx = .uComp (uComponent Z u hU) := by
  have hTt : ¬ classT Z u := not_classT_of_SU (.inr hU)
  have hSt : ¬ classS Z u := not_classS_of_TU (.inr hU)
  simp [remainLabel, hS, hTt, hSt]

lemma remain_port_of_not_T {Z : Set (GadgetVert G)} {v w : V} {h : G.Adj v w}
    (hT : ¬ classT Z v) : GadgetVert.port v w h ∉ canonicalCut Z :=
  fun hx => hT ((port_mem_canonicalCut_iff (Z := Z)).mp hx)

lemma remain_port_of_U {Z : Set (GadgetVert G)} {v w : V} {h : G.Adj v w}
    (hU : classU Z v) : GadgetVert.port v w h ∉ canonicalCut Z :=
  remain_port_of_not_T (not_classT_of_SU (.inr hU))

lemma uComponent_eq_of_adj {Z : Set (GadgetVert G)} {v w : V}
    (hUv : classU Z v) (hUw : classU Z w) (h : G.Adj v w) :
    uComponent Z v hUv = uComponent Z w hUw :=
  ConnectedComponent.connectedComponentMk_eq_of_adj
    (show (G.induce {x | classU Z x}).Adj ⟨v, hUv⟩ ⟨w, hUw⟩ from h)

/-! ## Label preservation along remainder edges -/

lemma remainLabel_eq_of_gadget_adj {Z : Set (GadgetVert G)}
    {x y : GadgetVert G}
    (hx : x ∉ canonicalCut Z) (hy : y ∉ canonicalCut Z)
    (hadj : (gadget G).Adj x y) :
    remainLabel Z x hx = remainLabel Z y hy := by
  cases x with
  | clone v b =>
      cases y with
      | clone =>
          exact (not_gadget_adj_clone_clone hadj).elim
      | port v' w h =>
          have hv : v = v' := gadget_adj_clone_port.mp hadj
          cases hv
          rcases classTU_of_clone_remain hx with hT | hU
          · exact (hy ((port_mem_canonicalCut_iff (Z := Z)).mpr hT)).elim
          · rw [remainLabel_clone_of_U hU hx, remainLabel_port_of_U hU hy]
  | port v w h =>
      cases y with
      | clone v' b =>
          have hv : v' = v := by simpa using hadj
          cases hv
          rcases classSU_of_port_remain hx with hS | hU
          · exact (hy ((clone_mem_canonicalCut_iff (Z := Z)).mpr hS)).elim
          · rw [remainLabel_port_of_U hU hx, remainLabel_clone_of_U hU hy]
      | port v' w' h' =>
          have hvw : v = w' ∧ w = v' := gadget_adj_port_port.mp hadj
          rcases hvw with ⟨rfl, rfl⟩
          rcases classSU_of_port_remain hx with hSv | hUv
          · rcases classSTU Z w with hSw | hTw | hUw
            · rw [remainLabel_port_of_SS hSv hSw hx,
                remainLabel_port_of_SS hSw hSv hy]
              exact congrArg CanonicalLabel.ssEdge (Sym2.eq_swap)
            · exact (hy ((port_mem_canonicalCut_iff (Z := Z)).mpr hTw)).elim
            · rw [remainLabel_port_of_SU hSv hUw hx,
                remainLabel_port_of_U hUw hy]
          · rcases classSU_of_port_remain hy with hSw | hUw
            · rw [remainLabel_port_of_U hUv hx,
                remainLabel_port_of_SU hSw hUv hy]
            · rw [remainLabel_port_of_U hUv hx, remainLabel_port_of_U hUw hy]
              exact congrArg CanonicalLabel.uComp (uComponent_eq_of_adj hUv hUw h)

lemma remainLabel_eq_of_reachable {Z : Set (GadgetVert G)}
    {x y : {z // z ∈ (canonicalCut Z)ᶜ}}
    (h : ((gadget G).induce (canonicalCut Z)ᶜ).Reachable x y) :
    remainLabel Z x x.property = remainLabel Z y y.property := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons u v w hadj q ih =>
      have hadj' : (gadget G).Adj u v := hadj
      exact (remainLabel_eq_of_gadget_adj u.property v.property hadj').trans ih

/-! ## U-gadget connectivity -/

lemma UU_three_step {Z : Set (GadgetVert G)} {u w : V} {b b' : Fin 2}
    (hU : classU Z u) (hU' : classU Z w) (h : G.Adj u w) :
    ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
      ⟨.clone u b, U_clone_not_mem_canonical (b := b) hU⟩
      ⟨.clone w b', U_clone_not_mem_canonical (b := b') hU'⟩ := by
  have a1 : ((gadget G).induce (canonicalCut Z)ᶜ).Adj
      ⟨.clone u b, U_clone_not_mem_canonical (b := b) hU⟩
      ⟨.port u w h, remain_port_of_U hU⟩ := by
    rw [induce_adj]; simp
  have a2 : ((gadget G).induce (canonicalCut Z)ᶜ).Adj
      ⟨.port u w h, remain_port_of_U hU⟩
      ⟨.port w u h.symm, remain_port_of_U hU'⟩ := by
    rw [induce_adj]; simp
  have a3 : ((gadget G).induce (canonicalCut Z)ᶜ).Adj
      ⟨.port w u h.symm, remain_port_of_U hU'⟩
      ⟨.clone w b', U_clone_not_mem_canonical (b := b') hU'⟩ := by
    rw [induce_adj]; simp
  exact a1.reachable.trans (a2.reachable.trans a3.reachable)

lemma Ugraph_reachable_to_clones {Z : Set (GadgetVert G)}
    {u0 w0 : {v // classU Z v}}
    (h : (G.induce {v | classU Z v}).Reachable u0 w0) (b b' : Fin 2) :
    ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
      ⟨.clone u0.val b, U_clone_not_mem_canonical (b := b) u0.property⟩
      ⟨.clone w0.val b', U_clone_not_mem_canonical (b := b') w0.property⟩ := by
  obtain ⟨p⟩ := h
  induction p generalizing b b' with
  | @nil u =>
      exact U_clones_remain_reachable (b := b) (b' := b') u.property
  | @cons x y z hadj q ih =>
      have hadjG : G.Adj x.val y.val := hadj
      exact (UU_three_step (b := b) (b' := 0) x.property y.property hadjG).trans
        (ih 0 b')

lemma remain_clone_reachable_own_port {Z : Set (GadgetVert G)}
    {v w : V} {h : G.Adj v w} {b : Fin 2}
    (hU : classU Z v) :
    ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
      ⟨.clone v b, U_clone_not_mem_canonical (b := b) hU⟩
      ⟨.port v w h, remain_port_of_U hU⟩ := by
  refine Adj.reachable ?_
  rw [induce_adj]
  simp

lemma remain_clone_reachable_S_port {Z : Set (GadgetVert G)}
    {s u : V} {h : G.Adj s u} {b : Fin 2}
    (hS : classS Z s) (hU : classU Z u) :
    ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
      ⟨.clone u b, U_clone_not_mem_canonical (b := b) hU⟩
      ⟨.port s u h, ST_port_not_mem_canonical hS⟩ := by
  have hown : ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
      ⟨.clone u b, U_clone_not_mem_canonical (b := b) hU⟩
      ⟨.port u s h.symm, remain_port_of_U hU⟩ :=
    remain_clone_reachable_own_port (b := b) hU
  have hadj : ((gadget G).induce (canonicalCut Z)ᶜ).Adj
      ⟨.port u s h.symm, remain_port_of_U hU⟩
      ⟨.port s u h, ST_port_not_mem_canonical hS⟩ := by
    rw [induce_adj]
    exact gadget_adj_mate h.symm
  exact hown.trans hadj.reachable

lemma exist_U_of_uComp_label {Z : Set (GadgetVert G)}
    {x : GadgetVert G} (hx : x ∉ canonicalCut Z)
    {c : (G.induce {w | classU Z w}).ConnectedComponent}
    (hL : remainLabel Z x hx = .uComp c) :
    ∃ v, ∃ hv : classU Z v, ∃ b : Fin 2,
      uComponent Z v hv = c ∧
        ((gadget G).induce (canonicalCut Z)ᶜ).Reachable
          ⟨.clone v b, U_clone_not_mem_canonical (b := b) hv⟩
          ⟨x, hx⟩ := by
  cases x with
  | clone v b =>
      rcases classTU_of_clone_remain hx with hT | hU
      · have : remainLabel Z (.clone v b) hx = .tClone v b :=
          remainLabel_clone_of_T hT hx
        cases this.symm.trans hL
      · refine ⟨v, hU, b, ?_, Reachable.rfl⟩
        simpa [remainLabel_clone_of_U hU hx] using hL
  | port v w h =>
      rcases classSU_of_port_remain hx with hS | hU
      · rcases classSTU Z w with hSw | hTw | hUw
        · have : remainLabel Z (.port v w h) hx = .ssEdge s(v, w) :=
            remainLabel_port_of_SS hS hSw hx
          cases this.symm.trans hL
        · have : remainLabel Z (.port v w h) hx = .stPort v w :=
            remainLabel_port_of_ST hS hTw hx
          cases this.symm.trans hL
        · refine ⟨w, hUw, 0, ?_, remain_clone_reachable_S_port (b := 0) hS hUw⟩
          simpa [remainLabel_port_of_SU hS hUw hx] using hL
      · refine ⟨v, hU, 0, ?_, remain_clone_reachable_own_port (b := 0) hU⟩
        simpa [remainLabel_port_of_U hU hx] using hL

lemma uComp_fiber_reachable {Z : Set (GadgetVert G)}
    {x y : GadgetVert G} (hx : x ∉ canonicalCut Z) (hy : y ∉ canonicalCut Z)
    {c : (G.induce {w | classU Z w}).ConnectedComponent}
    (hxL : remainLabel Z x hx = .uComp c)
    (hyL : remainLabel Z y hy = .uComp c) :
    ((gadget G).induce (canonicalCut Z)ᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨v, hv, b, hvC, hvx⟩ := exist_U_of_uComp_label hx hxL
  obtain ⟨w, hw, b', hwC, hwy⟩ := exist_U_of_uComp_label hy hyL
  have hUreach : (G.induce {z | classU Z z}).Reachable ⟨v, hv⟩ ⟨w, hw⟩ := by
    have : uComponent Z v hv = uComponent Z w hw := hvC.trans hwC.symm
    exact ConnectedComponent.exact this
  have hclones :=
    Ugraph_reachable_to_clones (u0 := ⟨v, hv⟩) (w0 := ⟨w, hw⟩) hUreach (b := b) (b' := b')
  exact hvx.symm.trans (hclones.trans hwy)

lemma remainLabel_eq_tClone {Z : Set (GadgetVert G)}
    {x : GadgetVert G} (hx : x ∉ canonicalCut Z) {v : V} {b : Fin 2}
    (h : remainLabel Z x hx = .tClone v b) :
    x = .clone v b ∧ classT Z v := by
  cases x with
  | clone v' b' =>
      rcases classTU_of_clone_remain hx with hT | hU
      · have h' := remainLabel_clone_of_T hT hx
        cases h'.symm.trans h
        exact ⟨rfl, hT⟩
      · have h' := remainLabel_clone_of_U hU hx
        cases h'.symm.trans h
  | port v' w hw =>
      rcases classSU_of_port_remain hx with hS | hU
      · rcases classSTU Z w with hSw | hTw | hUw
        · cases (remainLabel_port_of_SS hS hSw hx).symm.trans h
        · cases (remainLabel_port_of_ST hS hTw hx).symm.trans h
        · cases (remainLabel_port_of_SU hS hUw hx).symm.trans h
      · cases (remainLabel_port_of_U hU hx).symm.trans h

lemma remainLabel_eq_stPort {Z : Set (GadgetVert G)}
    {x : GadgetVert G} (hx : x ∉ canonicalCut Z) {s t : V}
    (h : remainLabel Z x hx = .stPort s t) :
    ∃ hw : G.Adj s t, x = .port s t hw ∧ classS Z s ∧ classT Z t := by
  cases x with
  | clone v b =>
      rcases classTU_of_clone_remain hx with hT | hU
      · cases (remainLabel_clone_of_T hT hx).symm.trans h
      · cases (remainLabel_clone_of_U hU hx).symm.trans h
  | port v w hw =>
      rcases classSU_of_port_remain hx with hS | hU
      · rcases classSTU Z w with hSw | hTw | hUw
        · cases (remainLabel_port_of_SS hS hSw hx).symm.trans h
        · have h' := remainLabel_port_of_ST hS hTw hx
          cases h'.symm.trans h
          exact ⟨hw, rfl, hS, hTw⟩
        · cases (remainLabel_port_of_SU hS hUw hx).symm.trans h
      · cases (remainLabel_port_of_U hU hx).symm.trans h

lemma remainLabel_eq_ssEdge {Z : Set (GadgetVert G)}
    {x : GadgetVert G} (hx : x ∉ canonicalCut Z) {e : Sym2 V}
    (h : remainLabel Z x hx = .ssEdge e) :
    ∃ s t, ∃ hw : G.Adj s t, e = s(s, t) ∧ classS Z s ∧ classS Z t ∧
      x = .port s t hw := by
  cases x with
  | clone v b =>
      rcases classTU_of_clone_remain hx with hT | hU
      · cases (remainLabel_clone_of_T hT hx).symm.trans h
      · cases (remainLabel_clone_of_U hU hx).symm.trans h
  | port v w hw =>
      rcases classSU_of_port_remain hx with hS | hU
      · rcases classSTU Z w with hSw | hTw | hUw
        · have h' := remainLabel_port_of_SS hS hSw hx
          cases h'.symm.trans h
          exact ⟨v, w, hw, rfl, hS, hSw, rfl⟩
        · cases (remainLabel_port_of_ST hS hTw hx).symm.trans h
        · cases (remainLabel_port_of_SU hS hUw hx).symm.trans h
      · cases (remainLabel_port_of_U hU hx).symm.trans h

lemma remainLabel_eq_uComp {Z : Set (GadgetVert G)}
    {x : GadgetVert G} (hx : x ∉ canonicalCut Z)
    {c : (G.induce {w | classU Z w}).ConnectedComponent}
    (h : remainLabel Z x hx = .uComp c) :
    remainLabel Z x hx = .uComp c :=
  h

lemma same_label_reachable {Z : Set (GadgetVert G)}
    {x y : GadgetVert G} (hx : x ∉ canonicalCut Z) (hy : y ∉ canonicalCut Z)
    (hL : remainLabel Z x hx = remainLabel Z y hy) :
    ((gadget G).induce (canonicalCut Z)ᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  cases hLbl : remainLabel Z x hx with
  | tClone v b =>
      have hxT := remainLabel_eq_tClone hx (hLbl)
      have hyT := remainLabel_eq_tClone hy (hL.symm.trans hLbl)
      rcases hxT with ⟨rfl, _⟩
      rcases hyT with ⟨rfl, _⟩
      exact Reachable.rfl
  | stPort s t =>
      obtain ⟨h1, rfl, _, _⟩ := remainLabel_eq_stPort hx (hLbl)
      obtain ⟨h2, rfl, _, _⟩ := remainLabel_eq_stPort hy (hL.symm.trans hLbl)
      exact Reachable.rfl
  | ssEdge e =>
      obtain ⟨s, t, hs, rfl, hSs, hSt, rfl⟩ := remainLabel_eq_ssEdge hx hLbl
      obtain ⟨s', t', hs', heq, hSs', hSt', rfl⟩ :=
        remainLabel_eq_ssEdge hy (hL.symm.trans hLbl)
      rcases (Sym2.eq_iff.mp heq) with hsame | hswap
      · rcases hsame with ⟨rfl, rfl⟩
        have : (⟨GadgetVert.port s t hs, hx⟩ :
            {z // z ∈ (canonicalCut Z)ᶜ}) =
          ⟨GadgetVert.port s t hs', hy⟩ := Subtype.ext rfl
        exact this ▸ Reachable.rfl
      · rcases hswap with ⟨rfl, rfl⟩
        have : (⟨GadgetVert.port t s hs', hy⟩ :
            {z // z ∈ (canonicalCut Z)ᶜ}) =
          ⟨GadgetVert.port t s hs.symm, ST_port_not_mem_canonical hSt⟩ :=
          Subtype.ext rfl
        exact this ▸ (SS_ports_remain_adj (hst := hs) hSs hSt).reachable
  | uComp c =>
      exact uComp_fiber_reachable hx hy hLbl (hL.symm.trans hLbl)

/-- Remainder connected-component support is exactly the equal-label fibre. -/
lemma remain_component_supp_eq_fiber {Z : Set (GadgetVert G)}
    (x : {z // z ∈ (canonicalCut Z)ᶜ}) :
    (((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk x).supp =
      {y : {z // z ∈ (canonicalCut Z)ᶜ} |
        remainLabel Z y y.property = remainLabel Z x x.property} := by
  ext y
  constructor
  · intro hy
    have hreach : ((gadget G).induce (canonicalCut Z)ᶜ).Reachable y x := by
      simpa [ConnectedComponent.mem_supp_iff] using hy
    exact remainLabel_eq_of_reachable hreach
  · intro hy
    simp only [mem_setOf_eq] at hy
    simp [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact same_label_reachable y.property x.property hy

/-! ## T-clone and S–T remainder counts -/

lemma clone_remain_of_T {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hT : classT Z v) : GadgetVert.clone v b ∉ canonicalCut Z :=
  fun h => not_classS_of_TU (.inl hT) ((clone_mem_canonicalCut_iff (Z := Z)).mp h)

lemma tClone_label {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hT : classT Z v) :
    remainLabel Z (.clone v b) (clone_remain_of_T hT) = .tClone v b :=
  remainLabel_clone_of_T hT _

lemma tClone_comp_injective {Z : Set (GadgetVert G)}
    {v v' : V} {b b' : Fin 2}
    (hT : classT Z v) (hT' : classT Z v')
    (h : ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
          ⟨.clone v b, clone_remain_of_T hT⟩ =
        ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
          ⟨.clone v' b', clone_remain_of_T hT'⟩) :
    v = v' ∧ b = b' := by
  have hR := ConnectedComponent.exact h
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_clone_of_T hT, remainLabel_clone_of_T hT'] at hL
  cases hL
  exact ⟨rfl, rfl⟩

lemma stPort_comp_injective {Z : Set (GadgetVert G)}
    {s s' t t' : V} {hst : G.Adj s t} {hst' : G.Adj s' t'}
    (hS : classS Z s) (hT : classT Z t)
    (hS' : classS Z s') (hT' : classT Z t')
    (h : ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
          ⟨.port s t hst, ST_port_not_mem_canonical hS⟩ =
        ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
          ⟨.port s' t' hst', ST_port_not_mem_canonical hS'⟩) :
    s = s' ∧ t = t' := by
  have hR := ConnectedComponent.exact h
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_port_of_ST hS hT, remainLabel_port_of_ST hS' hT'] at hL
  cases hL
  exact ⟨rfl, rfl⟩

lemma orderedEdgeCount_comm (A B : Finset V) :
    orderedEdgeCount G A B = orderedEdgeCount G B A := by
  simp only [orderedEdgeCount]
  let e : Equiv {p // p ∈ (A ×ˢ B).filter fun p => G.Adj p.1 p.2}
      {p // p ∈ (B ×ˢ A).filter fun p => G.Adj p.1 p.2} :=
    { toFun := fun p =>
        ⟨(p.1.2, p.1.1), by
          have hp := p.2
          simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩⟩
      invFun := fun p =>
        ⟨(p.1.2, p.1.1), by
          have hp := p.2
          simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext rfl }
  simpa [← Fintype.card_coe] using Fintype.card_congr e

lemma T_clone_component_odd' {Z : Set (GadgetVert G)} {v : V} {b : Fin 2}
    (hT : classT Z v) :
    Odd ((((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.clone v b, clone_remain_of_T hT⟩).supp.ncard) :=
  T_clone_component_odd hT

lemma ST_port_component_odd' {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hT : classT Z t) :
    Odd ((((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.port s t hst, ST_port_not_mem_canonical hS⟩).supp.ncard) :=
  ST_port_component_odd hS hT

lemma SS_port_component_even' {Z : Set (GadgetVert G)} {s t : V}
    {hst : G.Adj s t} (hS : classS Z s) (hS' : classS Z t) :
    Even ((((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.port s t hst, ST_port_not_mem_canonical hS⟩).supp.ncard) :=
  SS_port_component_even hS hS'

/-- Image of T-clones among remainder components. -/
def tCloneCompSet (Z : Set (GadgetVert G)) :
    Set ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
  {c | ∃ v, ∃ hT : classT Z v, ∃ b : Fin 2,
    c = ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
      ⟨.clone v b, clone_remain_of_T hT⟩}

lemma ncard_tCloneCompSet (Z : Set (GadgetVert G)) :
    (tCloneCompSet Z).ncard = 2 * (originalT Z).card := by
  let f : {v // classT Z v} × Fin 2 →
      ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
    fun p => ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
      ⟨.clone p.1.1 p.2, clone_remain_of_T p.1.2⟩
  have himg : tCloneCompSet Z = Set.range f := by
    ext c
    constructor
    · intro hc
      rcases hc with ⟨v, hT, b, rfl⟩
      exact ⟨⟨⟨v, hT⟩, b⟩, rfl⟩
    · intro ⟨⟨⟨v, hT⟩, b⟩, h⟩
      exact ⟨v, hT, b, h.symm⟩
  have hinj : Function.Injective f := by
    intro p q h
    have hvt := tClone_comp_injective p.1.2 q.1.2 h
    exact Prod.ext (Subtype.ext hvt.1) hvt.2
  rw [himg, ncard_range_of_injective hinj, Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  rw [mul_comm (Fintype.card {v // classT Z v})]
  simp [originalT, Fintype.card_subtype, Set.toFinset]

/-- Image of S–T ports among remainder components. -/
def stPortCompSet (Z : Set (GadgetVert G)) :
    Set ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
  {c | ∃ s t, ∃ hst : G.Adj s t, ∃ hS : classS Z s, ∃ hT : classT Z t,
    c = ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
      ⟨.port s t hst, ST_port_not_mem_canonical hS⟩}

lemma ncard_stPortCompSet (Z : Set (GadgetVert G)) :
    (stPortCompSet Z).ncard =
      orderedEdgeCount G (originalS Z) (originalT Z) := by
  let S := originalS Z
  let T := originalT Z
  let P := (S ×ˢ T).filter fun p => G.Adj p.1 p.2
  let f : {p : V × V // p ∈ P} →
      ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
    fun p =>
      have hS : classS Z p.1.1 := mem_originalS_iff.mp (by
        have := p.2
        simp only [P, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.1)
      have hT : classT Z p.1.2 := mem_originalT_iff.mp (by
        have := p.2
        simp only [P, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.2)
      have hst : G.Adj p.1.1 p.1.2 := by
        have := p.2
        simp only [P, Finset.mem_filter, Finset.mem_product] at this
        exact this.2
      ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.port p.1.1 p.1.2 hst, ST_port_not_mem_canonical hS⟩
  have himg : stPortCompSet Z = Set.range f := by
    ext c
    constructor
    · intro hc
      rcases hc with ⟨s, t, hst, hS, hT, rfl⟩
      refine ⟨⟨(s, t), ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨mem_originalS_iff.mpr hS, mem_originalT_iff.mpr hT⟩, hst⟩
      · rfl
    · intro ⟨p, hp⟩
      subst hp
      exact ⟨p.1.1, p.1.2, by
        have := p.2
        simp only [P, Finset.mem_filter] at this
        exact this.2, mem_originalS_iff.mp (by
          have := p.2
          simp only [P, Finset.mem_filter, Finset.mem_product] at this
          exact this.1.1), mem_originalT_iff.mp (by
          have := p.2
          simp only [P, Finset.mem_filter, Finset.mem_product] at this
          exact this.1.2), rfl⟩
  have hinj : Function.Injective f := by
    intro p q h
    have hS : classS Z p.1.1 := mem_originalS_iff.mp (by
      have := p.2
      simp only [P, Finset.mem_filter, Finset.mem_product] at this
      exact this.1.1)
    have hT : classT Z p.1.2 := mem_originalT_iff.mp (by
      have := p.2
      simp only [P, Finset.mem_filter, Finset.mem_product] at this
      exact this.1.2)
    have hS' : classS Z q.1.1 := mem_originalS_iff.mp (by
      have := q.2
      simp only [P, Finset.mem_filter, Finset.mem_product] at this
      exact this.1.1)
    have hT' : classT Z q.1.2 := mem_originalT_iff.mp (by
      have := q.2
      simp only [P, Finset.mem_filter, Finset.mem_product] at this
      exact this.1.2)
    have := stPort_comp_injective hS hT hS' hT' h
    ext <;> simp [this]
  rw [himg, ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

/-! ## Original U-component → actual remainder component -/

/-- Original vertex support of a `G[U]` component, mapped through `Subtype.val`. -/
noncomputable def uCompVerts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) : Finset V :=
  c.supp.toFinset.image Subtype.val

lemma mem_uCompVerts_iff {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V} :
    v ∈ uCompVerts Z c ↔
      ∃ hv : classU Z v, uComponent Z v hv = c := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨⟨w, hw⟩, hmem, rfl⟩
    refine ⟨hw, ?_⟩
    simpa [uComponent] using
      (ConnectedComponent.mem_supp_iff _ _).mp (Set.mem_toFinset.mp hmem)
  · rintro ⟨hv, h⟩
    refine Finset.mem_image.mpr ⟨⟨v, hv⟩, Set.mem_toFinset.mpr ?_, rfl⟩
    simpa [uComponent] using (ConnectedComponent.mem_supp_iff _ _).mpr h

lemma classU_of_mem_uCompVerts {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V}
    (hv : v ∈ uCompVerts Z c) : classU Z v :=
  (mem_uCompVerts_iff.mp hv).1

lemma uCompVerts_subset_originalU (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    uCompVerts Z c ⊆ originalU Z := by
  intro v hv
  exact mem_originalU_iff.mpr (classU_of_mem_uCompVerts hv)

lemma uComponent_eq_of_mem_uCompVerts {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V}
    (hv : v ∈ uCompVerts Z c) :
    uComponent Z v (classU_of_mem_uCompVerts hv) = c :=
  (mem_uCompVerts_iff.mp hv).2

/-- A representative original vertex of a `G[U]` component. Independent of
cardinality/parity; used only to name a surviving U-clone. -/
noncomputable def uCompRep (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    {v // classU Z v} :=
  Quot.out c

lemma uComponent_rep (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    uComponent Z (uCompRep Z c).1 (uCompRep Z c).2 = c := by
  unfold uComponent uCompRep connectedComponentMk
  exact Quot.out_eq c

lemma uCompRep_mem_verts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    (uCompRep Z c).1 ∈ uCompVerts Z c :=
  mem_uCompVerts_iff.mpr ⟨(uCompRep Z c).2, uComponent_rep Z c⟩

/-- Canonical remainder component of an original `G[U]` component, named by a
U-clone of a representative. Same-label reachability makes the choice
independent of the representative and of the clone bit. -/
noncomputable def uCompRemain (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
  ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
    ⟨.clone (uCompRep Z c).1 0,
      U_clone_not_mem_canonical (b := 0) (uCompRep Z c).2⟩

lemma remainLabel_uCompRep_clone {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {b : Fin 2} :
    remainLabel Z (.clone (uCompRep Z c).1 b)
      (U_clone_not_mem_canonical (b := b) (uCompRep Z c).2) = .uComp c := by
  rw [remainLabel_clone_of_U (uCompRep Z c).2]
  exact congrArg CanonicalLabel.uComp (uComponent_rep Z c)

lemma uCompRemain_eq_clone {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V}
    (hv : classU Z v) (hc : uComponent Z v hv = c) (b : Fin 2) :
    uCompRemain Z c =
      ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
        ⟨.clone v b, U_clone_not_mem_canonical (b := b) hv⟩ := by
  apply ConnectedComponent.sound
  have hx : remainLabel Z (.clone (uCompRep Z c).1 0)
      (U_clone_not_mem_canonical (b := 0) (uCompRep Z c).2) = .uComp c :=
    remainLabel_uCompRep_clone
  have hy : remainLabel Z (.clone v b) (U_clone_not_mem_canonical (b := b) hv) =
      .uComp c := by
    rw [remainLabel_clone_of_U hv, hc]
  exact same_label_reachable _ _ (hx.trans hy.symm)

lemma uCompRemain_eq_of_label {Z : Set (GadgetVert G)} {x : GadgetVert G}
    (hx : x ∉ canonicalCut Z)
    {c : (G.induce {w | classU Z w}).ConnectedComponent}
    (hL : remainLabel Z x hx = .uComp c) :
    ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk ⟨x, hx⟩ =
      uCompRemain Z c := by
  apply ConnectedComponent.sound
  have hy : remainLabel Z (.clone (uCompRep Z c).1 0)
      (U_clone_not_mem_canonical (b := 0) (uCompRep Z c).2) = .uComp c :=
    remainLabel_uCompRep_clone
  exact same_label_reachable _ _ (hL.trans hy.symm)

lemma uCompRemain_injective (Z : Set (GadgetVert G)) :
    Function.Injective (uCompRemain Z) := by
  intro c c' h
  have hR := ConnectedComponent.exact h
  have hL := remainLabel_eq_of_reachable hR
  simpa [remainLabel_uCompRep_clone] using hL

/-- Realized U remainder components: the image of actual `G[U]` components,
not the unrestricted `CanonicalLabel` type. -/
def uCompCompSet (Z : Set (GadgetVert G)) :
    Set ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
  Set.range (uCompRemain Z)

lemma mem_uCompCompSet_iff {Z : Set (GadgetVert G)}
    {C : ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent} :
    C ∈ uCompCompSet Z ↔
      ∃ c : (G.induce {w | classU Z w}).ConnectedComponent, C = uCompRemain Z c :=
  Set.mem_range.trans ⟨fun ⟨c, h⟩ => ⟨c, h.symm⟩, fun ⟨c, h⟩ => ⟨c, h.symm⟩⟩

lemma remain_uComp_mem_image {Z : Set (GadgetVert G)} {x : GadgetVert G}
    (hx : x ∉ canonicalCut Z)
    {c : (G.induce {w | classU Z w}).ConnectedComponent}
    (hL : remainLabel Z x hx = .uComp c) :
    ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk ⟨x, hx⟩ ∈
      uCompCompSet Z :=
  ⟨c, (uCompRemain_eq_of_label hx hL).symm⟩

/-! ## U-fibre vertices: owner clones, owner ports, S-attachment ports -/

/-- Clones owned by original vertices of `D`. -/
def uFiberClones (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) : Set (GadgetVert G) :=
  {x | ∃ v ∈ uCompVerts Z c, ∃ b : Fin 2, x = .clone v b}

/-- Ports owned by original vertices of `D` (including U→T ports). -/
def uFiberOwnPorts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) : Set (GadgetVert G) :=
  {x | ∃ v ∈ uCompVerts Z c, ∃ w, ∃ h : G.Adj v w, x = .port v w h}

/-- Ports owned by S whose target lies in `D`. -/
def uFiberSPorts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) : Set (GadgetVert G) :=
  {x | ∃ s, classS Z s ∧ ∃ v ∈ uCompVerts Z c, ∃ h : G.Adj s v, x = .port s v h}

/-- Actual U-label fibre as a set of gadget vertices. -/
def uFiberVerts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) : Set (GadgetVert G) :=
  {x | ∃ hx : x ∉ canonicalCut Z, remainLabel Z x hx = .uComp c}

lemma uFiberClones_not_mem_cut {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {x : GadgetVert G}
    (hx : x ∈ uFiberClones Z c) : x ∉ canonicalCut Z := by
  rcases hx with ⟨v, hv, b, rfl⟩
  exact U_clone_not_mem_canonical (b := b) (classU_of_mem_uCompVerts hv)

lemma uFiberOwnPorts_not_mem_cut {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {x : GadgetVert G}
    (hx : x ∈ uFiberOwnPorts Z c) : x ∉ canonicalCut Z := by
  rcases hx with ⟨v, hv, w, h, rfl⟩
  exact remain_port_of_U (classU_of_mem_uCompVerts hv)

lemma uFiberSPorts_not_mem_cut {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {x : GadgetVert G}
    (hx : x ∈ uFiberSPorts Z c) : x ∉ canonicalCut Z := by
  rcases hx with ⟨s, hS, v, hv, h, rfl⟩
  exact ST_port_not_mem_canonical hS

lemma remainLabel_uFiberClones {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {x : GadgetVert G}
    (hx : x ∈ uFiberClones Z c) :
    remainLabel Z x (uFiberClones_not_mem_cut hx) = .uComp c := by
  rcases hx with ⟨v, hv, b, rfl⟩
  rw [remainLabel_clone_of_U (classU_of_mem_uCompVerts hv)]
  exact congrArg CanonicalLabel.uComp (uComponent_eq_of_mem_uCompVerts hv)

lemma remainLabel_uFiberOwnPorts {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {x : GadgetVert G}
    (hx : x ∈ uFiberOwnPorts Z c) :
    remainLabel Z x (uFiberOwnPorts_not_mem_cut hx) = .uComp c := by
  rcases hx with ⟨v, hv, w, h, rfl⟩
  rw [remainLabel_port_of_U (classU_of_mem_uCompVerts hv)]
  exact congrArg CanonicalLabel.uComp (uComponent_eq_of_mem_uCompVerts hv)

lemma remainLabel_uFiberSPorts {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {x : GadgetVert G}
    (hx : x ∈ uFiberSPorts Z c) :
    remainLabel Z x (uFiberSPorts_not_mem_cut hx) = .uComp c := by
  rcases hx with ⟨s, hS, v, hv, h, rfl⟩
  rw [remainLabel_port_of_SU hS (classU_of_mem_uCompVerts hv)]
  exact congrArg CanonicalLabel.uComp (uComponent_eq_of_mem_uCompVerts hv)

lemma disjoint_uFiberClones_ownPorts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    Disjoint (uFiberClones Z c) (uFiberOwnPorts Z c) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨_, _, _, rfl⟩
  rcases hy with ⟨_, _, _, _, h⟩
  cases h

lemma disjoint_uFiberClones_sPorts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    Disjoint (uFiberClones Z c) (uFiberSPorts Z c) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨_, _, _, rfl⟩
  rcases hy with ⟨_, _, _, _, _, h⟩
  cases h

lemma disjoint_uFiberOwnPorts_sPorts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    Disjoint (uFiberOwnPorts Z c) (uFiberSPorts Z c) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨v, hv, w, h, rfl⟩
  rcases hy with ⟨s, hS, v', hv', h', heq⟩
  injection heq with hs _
  cases hs
  exact not_classS_of_TU (.inr (classU_of_mem_uCompVerts hv)) hS

lemma uFiberVerts_eq_union {Z : Set (GadgetVert G)}
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    uFiberVerts Z c =
      uFiberClones Z c ∪ uFiberOwnPorts Z c ∪ uFiberSPorts Z c := by
  ext x
  constructor
  · rintro ⟨hx, hL⟩
    cases x with
    | clone v b =>
        rcases classTU_of_clone_remain hx with hT | hU
        · cases (remainLabel_clone_of_T hT hx).symm.trans hL
        · have hv : v ∈ uCompVerts Z c :=
            mem_uCompVerts_iff.mpr ⟨hU, by
              simpa [remainLabel_clone_of_U hU hx] using hL⟩
          exact .inl (.inl ⟨v, hv, b, rfl⟩)
    | port v w h =>
        rcases classSU_of_port_remain hx with hS | hU
        · rcases classSTU Z w with hSw | hTw | hUw
          · cases (remainLabel_port_of_SS hS hSw hx).symm.trans hL
          · cases (remainLabel_port_of_ST hS hTw hx).symm.trans hL
          · have hw : w ∈ uCompVerts Z c :=
              mem_uCompVerts_iff.mpr ⟨hUw, by
                simpa [remainLabel_port_of_SU hS hUw hx] using hL⟩
            exact .inr ⟨v, hS, w, hw, h, rfl⟩
        · have hv : v ∈ uCompVerts Z c :=
            mem_uCompVerts_iff.mpr ⟨hU, by
              simpa [remainLabel_port_of_U hU hx] using hL⟩
          exact .inl (.inr ⟨v, hv, w, h, rfl⟩)
  · intro hx
    rcases (show x ∈ (uFiberClones Z c ∪ uFiberOwnPorts Z c) ∪ uFiberSPorts Z c from hx)
      with hAB | hC
    · rcases hAB with hA | hB
      · exact ⟨uFiberClones_not_mem_cut hA, remainLabel_uFiberClones hA⟩
      · exact ⟨uFiberOwnPorts_not_mem_cut hB, remainLabel_uFiberOwnPorts hB⟩
    · exact ⟨uFiberSPorts_not_mem_cut hC, remainLabel_uFiberSPorts hC⟩

lemma ncard_uFiberClones (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    (uFiberClones Z c).ncard = 2 * (uCompVerts Z c).card := by
  let f : {v // v ∈ uCompVerts Z c} × Fin 2 → GadgetVert G :=
    fun p => .clone p.1.1 p.2
  have himg : uFiberClones Z c = Set.range f := by
    ext x
    constructor
    · rintro ⟨v, hv, b, rfl⟩
      exact ⟨⟨⟨v, hv⟩, b⟩, rfl⟩
    · rintro ⟨⟨⟨v, hv⟩, b⟩, rfl⟩
      exact ⟨v, hv, b, rfl⟩
  have hinj : Function.Injective f := by
    intro p q h
    injection h with hv hb
    exact Prod.ext (Subtype.ext hv) hb
  rw [himg, ncard_range_of_injective hinj]
  simp [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]
  ring

lemma ncard_uFiberOwnPorts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    (uFiberOwnPorts Z c).ncard = ∑ v ∈ uCompVerts Z c, G.degree v := by
  let D := uCompVerts Z c
  let P := (D ×ˢ (Finset.univ : Finset V)).filter fun p => G.Adj p.1 p.2
  let f : {p : V × V // p ∈ P} → GadgetVert G :=
    fun p =>
      have hst : G.Adj p.1.1 p.1.2 := by
        have := p.2
        simp only [P, Finset.mem_filter] at this
        exact this.2
      .port p.1.1 p.1.2 hst
  have himg : uFiberOwnPorts Z c = Set.range f := by
    ext x
    constructor
    · rintro ⟨v, hv, w, h, rfl⟩
      refine ⟨⟨(v, w), ?_⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, Finset.mem_univ w⟩, h⟩
    · rintro ⟨p, rfl⟩
      refine ⟨p.1.1, ?_, p.1.2, ?_, rfl⟩
      · have := p.2
        simp only [P, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.1
      · have := p.2
        simp only [P, Finset.mem_filter] at this
        exact this.2
  have hinj : Function.Injective f := by
    intro p q h
    injection h with hv hw
    exact Subtype.ext (Prod.ext hv hw)
  have hcardP : P.card = ∑ v ∈ D, G.degree v := by
    simp only [P, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun v _hv => ?_
    simp [SimpleGraph.degree, neighborFinset, mem_neighborSet, Fintype.card_subtype]
  rw [himg, ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact hcardP

lemma ncard_uFiberSPorts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    (uFiberSPorts Z c).ncard =
      orderedEdgeCount G (originalS Z) (uCompVerts Z c) := by
  let S := originalS Z
  let D := uCompVerts Z c
  let P := (S ×ˢ D).filter fun p => G.Adj p.1 p.2
  let f : {p : V × V // p ∈ P} → GadgetVert G :=
    fun p =>
      have hst : G.Adj p.1.1 p.1.2 := by
        have := p.2
        simp only [P, Finset.mem_filter] at this
        exact this.2
      .port p.1.1 p.1.2 hst
  have himg : uFiberSPorts Z c = Set.range f := by
    ext x
    constructor
    · rintro ⟨s, hS, v, hv, h, rfl⟩
      refine ⟨⟨(s, v), ?_⟩, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨mem_originalS_iff.mpr hS, hv⟩, h⟩
    · rintro ⟨p, rfl⟩
      refine ⟨p.1.1, mem_originalS_iff.mp (by
        have := p.2
        simp only [P, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.1), p.1.2, ?_, ?_, rfl⟩
      · have := p.2
        simp only [P, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.2
      · have := p.2
        simp only [P, Finset.mem_filter] at this
        exact this.2
  have hinj : Function.Injective f := by
    intro p q h
    injection h with hv hw
    exact Subtype.ext (Prod.ext hv hw)
  rw [himg, ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

lemma ncard_uFiberVerts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    (uFiberVerts Z c).ncard =
      2 * (uCompVerts Z c).card + ∑ v ∈ uCompVerts Z c, G.degree v +
        orderedEdgeCount G (originalS Z) (uCompVerts Z c) := by
  rw [uFiberVerts_eq_union]
  have d1 := disjoint_uFiberClones_ownPorts Z c
  have d2 := disjoint_uFiberClones_sPorts Z c
  have d3 := disjoint_uFiberOwnPorts_sPorts Z c
  have dU : Disjoint (uFiberClones Z c ∪ uFiberOwnPorts Z c) (uFiberSPorts Z c) :=
    disjoint_union_left.mpr ⟨d2, d3⟩
  rw [ncard_union_eq dU, ncard_union_eq d1, ncard_uFiberClones, ncard_uFiberOwnPorts,
    ncard_uFiberSPorts]

lemma ncard_uCompRemain_supp (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    (uCompRemain Z c).supp.ncard = (uFiberVerts Z c).ncard := by
  have hsupp := remain_component_supp_eq_fiber
    (Z := Z)
    ⟨.clone (uCompRep Z c).1 0,
      U_clone_not_mem_canonical (b := 0) (uCompRep Z c).2⟩
  have hL : remainLabel Z (.clone (uCompRep Z c).1 0)
      (U_clone_not_mem_canonical (b := 0) (uCompRep Z c).2) = .uComp c :=
    remainLabel_uCompRep_clone
  have hs : (uCompRemain Z c).supp =
      {y : {z // z ∈ (canonicalCut Z)ᶜ} |
        remainLabel Z y y.property = .uComp c} := by
    simpa [uCompRemain, hL] using hsupp
  have himg : Subtype.val '' (uCompRemain Z c).supp = uFiberVerts Z c := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hs] at hy
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hLx⟩
      exact ⟨⟨x, hx⟩, by simpa [hs] using hLx, rfl⟩
  rw [← himg, ncard_image_of_injective _ Subtype.val_injective]

/-! ## Degree split and attachment parity -/

lemma orderedEdgeCount_eq_sum (A B : Finset V) :
    orderedEdgeCount G A B = ∑ a ∈ A, (G.neighborFinset a ∩ B).card := by
  simp only [orderedEdgeCount, neighborFinset_inter]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ha => ?_
  exact (Finset.card_filter (G.Adj a) B).symm

lemma orderedEdgeCount_self_eq_two_mul (A : Finset V) :
    orderedEdgeCount G A A = 2 * (G.induce (A : Set V)).edgeFinset.card := by
  classical
  let H := G.induce (A : Set V)
  let e : {p : V × V // p ∈ (A ×ˢ A).filter fun q => G.Adj q.1 q.2} ≃
      {xy : (↥(A : Set V)) × (↥(A : Set V)) // H.Adj xy.1 xy.2} :=
    { toFun := fun p =>
        ⟨(⟨p.1.1, (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).1⟩,
          ⟨p.1.2, (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).2⟩),
          (Finset.mem_filter.mp p.2).2⟩
      invFun := fun q =>
        ⟨(q.1.1.val, q.1.2.val),
          Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨q.1.1.property, q.1.2.property⟩, q.2⟩⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun q =>
        Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)) }
  have hP : ((A ×ˢ A).filter fun q => G.Adj q.1 q.2).card =
      (Finset.univ.filter fun xy : (↥(A : Set V)) × (↥(A : Set V)) =>
        H.Adj xy.1 xy.2).card := by
    simpa [← Fintype.card_coe] using Fintype.card_congr e
  exact hP.trans H.two_mul_card_edgeFinset.symm

lemma even_orderedEdgeCount_self (A : Finset V) :
    Even (orderedEdgeCount G A A) := by
  rw [orderedEdgeCount_self_eq_two_mul]
  exact even_two_mul _

lemma not_adj_uComp_outside {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v w : V}
    (hv : v ∈ uCompVerts Z c) (hwU : classU Z w)
    (hwD : w ∉ uCompVerts Z c) : ¬ G.Adj v w := by
  intro hadj
  have hvU := classU_of_mem_uCompVerts hv
  have hadj' : (G.induce {x | classU Z x}).Adj ⟨v, hvU⟩ ⟨w, hwU⟩ := hadj
  have hc : uComponent Z w hwU = uComponent Z v hvU :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hadj.symm)
  exact hwD (mem_uCompVerts_iff.mpr ⟨hwU, hc.trans (uComponent_eq_of_mem_uCompVerts hv)⟩)

lemma neighborFinset_uComp_inter_outside {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V}
    (hv : v ∈ uCompVerts Z c) :
    G.neighborFinset v ∩ (originalU Z \ uCompVerts Z c) = ∅ := by
  ext w
  simp only [Finset.mem_inter, mem_neighborFinset, Finset.mem_sdiff, Finset.notMem_empty,
    iff_false]
  intro ⟨hadj, hwU, hwD⟩
  exact not_adj_uComp_outside hv (mem_originalU_iff.mp hwU) hwD hadj

lemma neighborFinset_split_of_mem_uComp {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V}
    (hv : v ∈ uCompVerts Z c) :
    G.neighborFinset v =
      (G.neighborFinset v ∩ originalS Z) ∪
      (G.neighborFinset v ∩ originalT Z) ∪
      (G.neighborFinset v ∩ uCompVerts Z c) := by
  ext w
  simp only [Finset.mem_union, Finset.mem_inter, mem_neighborFinset]
  constructor
  · intro hadj
    have hmem : w ∈ originalS Z ∪ originalT Z ∪ originalU Z := by
      rw [originalSTU_union]; exact Finset.mem_univ w
    rw [Finset.mem_union, Finset.mem_union] at hmem
    rcases hmem with hST | hU
    · rcases hST with hS | hT
      · exact .inl (.inl ⟨hadj, hS⟩)
      · exact .inl (.inr ⟨hadj, hT⟩)
    · by_cases hwD : w ∈ uCompVerts Z c
      · exact .inr ⟨hadj, hwD⟩
      · exact (not_adj_uComp_outside hv (mem_originalU_iff.mp hU) hwD hadj).elim
  · intro h
    rcases h with hST | hD
    · rcases hST with hS | hT
      · exact hS.1
      · exact hT.1
    · exact hD.1

lemma disjoint_neighbor_STU {Z : Set (GadgetVert G)} {v : V} :
    Disjoint (G.neighborFinset v ∩ originalS Z) (G.neighborFinset v ∩ originalT Z) := by
  rw [Finset.disjoint_left]
  intro w hwS hwT
  exact Finset.disjoint_left.mp (disjoint_originalS_originalT Z)
    (Finset.mem_inter.mp hwS).2 (Finset.mem_inter.mp hwT).2

lemma disjoint_neighbor_S_D {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V} :
    Disjoint (G.neighborFinset v ∩ originalS Z) (G.neighborFinset v ∩ uCompVerts Z c) := by
  rw [Finset.disjoint_left]
  intro w hwS hwD
  exact Finset.disjoint_left.mp (disjoint_originalS_originalU Z)
    (Finset.mem_inter.mp hwS).2
    (uCompVerts_subset_originalU Z c (Finset.mem_inter.mp hwD).2)

lemma disjoint_neighbor_T_D {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V} :
    Disjoint (G.neighborFinset v ∩ originalT Z) (G.neighborFinset v ∩ uCompVerts Z c) := by
  rw [Finset.disjoint_left]
  intro w hwT hwD
  exact Finset.disjoint_left.mp (disjoint_originalT_originalU Z)
    (Finset.mem_inter.mp hwT).2
    (uCompVerts_subset_originalU Z c (Finset.mem_inter.mp hwD).2)

lemma degree_split_of_mem_uComp {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent} {v : V}
    (hv : v ∈ uCompVerts Z c) :
    G.degree v =
      (G.neighborFinset v ∩ originalS Z).card +
      (G.neighborFinset v ∩ originalT Z).card +
      (G.neighborFinset v ∩ uCompVerts Z c).card := by
  have dST := disjoint_neighbor_STU (Z := Z) (v := v)
  have dSD := disjoint_neighbor_S_D (Z := Z) (c := c) (v := v)
  have dTD := disjoint_neighbor_T_D (Z := Z) (c := c) (v := v)
  have dU : Disjoint
      ((G.neighborFinset v ∩ originalS Z) ∪ (G.neighborFinset v ∩ originalT Z))
      (G.neighborFinset v ∩ uCompVerts Z c) :=
    Finset.disjoint_union_left.mpr ⟨dSD, dTD⟩
  calc G.degree v
      = ((G.neighborFinset v ∩ originalS Z ∪ G.neighborFinset v ∩ originalT Z) ∪
          G.neighborFinset v ∩ uCompVerts Z c).card := by
            rw [SimpleGraph.degree]
            conv_lhs => rw [neighborFinset_split_of_mem_uComp hv]
    _ = (G.neighborFinset v ∩ originalS Z ∪ G.neighborFinset v ∩ originalT Z).card +
          (G.neighborFinset v ∩ uCompVerts Z c).card :=
            Finset.card_union_of_disjoint dU
    _ = (G.neighborFinset v ∩ originalS Z).card +
          (G.neighborFinset v ∩ originalT Z).card +
          (G.neighborFinset v ∩ uCompVerts Z c).card := by
            rw [Finset.card_union_of_disjoint dST]

lemma sum_degree_uCompVerts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    ∑ v ∈ uCompVerts Z c, G.degree v =
      orderedEdgeCount G (uCompVerts Z c) (originalS Z) +
      orderedEdgeCount G (uCompVerts Z c) (originalT Z) +
      orderedEdgeCount G (uCompVerts Z c) (uCompVerts Z c) := by
  rw [Finset.sum_congr rfl fun v hv => degree_split_of_mem_uComp hv,
    Finset.sum_add_distrib, Finset.sum_add_distrib, orderedEdgeCount_eq_sum,
    orderedEdgeCount_eq_sum, orderedEdgeCount_eq_sum]

lemma odd_uFiber_iff_attach {Z : Set (GadgetVert G)}
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    Odd (uFiberVerts Z c).ncard ↔
      Odd (orderedEdgeCount G (uCompVerts Z c) (originalT Z)) := by
  rw [ncard_uFiberVerts, sum_degree_uCompVerts]
  have h2 : Even (2 * (uCompVerts Z c).card) := even_two_mul _
  have hDD : Even (orderedEdgeCount G (uCompVerts Z c) (uCompVerts Z c)) :=
    even_orderedEdgeCount_self _
  have hSS : Even
      (orderedEdgeCount G (uCompVerts Z c) (originalS Z) +
        orderedEdgeCount G (originalS Z) (uCompVerts Z c)) := by
    rw [orderedEdgeCount_comm (uCompVerts Z c)]
    simpa [two_mul] using even_two_mul
      (orderedEdgeCount G (originalS Z) (uCompVerts Z c))
  have : (2 * (uCompVerts Z c).card +
        (orderedEdgeCount G (uCompVerts Z c) (originalS Z) +
          orderedEdgeCount G (uCompVerts Z c) (originalT Z) +
          orderedEdgeCount G (uCompVerts Z c) (uCompVerts Z c)) +
        orderedEdgeCount G (originalS Z) (uCompVerts Z c)) =
      (2 * (uCompVerts Z c).card) +
        (orderedEdgeCount G (uCompVerts Z c) (originalS Z) +
          orderedEdgeCount G (originalS Z) (uCompVerts Z c)) +
        orderedEdgeCount G (uCompVerts Z c) (uCompVerts Z c) +
        orderedEdgeCount G (uCompVerts Z c) (originalT Z) := by
    ac_rfl
  rw [this, Nat.odd_add']
  have heven : Even
      (2 * (uCompVerts Z c).card +
        (orderedEdgeCount G (uCompVerts Z c) (originalS Z) +
          orderedEdgeCount G (originalS Z) (uCompVerts Z c)) +
        orderedEdgeCount G (uCompVerts Z c) (uCompVerts Z c)) :=
    (h2.add hSS).add hDD
  simp [heven]

lemma odd_uCompRemain_iff_attach {Z : Set (GadgetVert G)}
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    Odd (uCompRemain Z c).supp.ncard ↔
      Odd (orderedEdgeCount G (uCompVerts Z c) (originalT Z)) := by
  rw [ncard_uCompRemain_supp]
  exact odd_uFiber_iff_attach c

/-! ## S–S remainder image and remainder classification -/

def ssEdgeCompSet (Z : Set (GadgetVert G)) :
    Set ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
  {C | ∃ s t, ∃ hst : G.Adj s t, ∃ hS : classS Z s, ∃ hS' : classS Z t,
    C = ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
      ⟨.port s t hst, ST_port_not_mem_canonical hS⟩}

lemma remain_component_classified {Z : Set (GadgetVert G)}
    (C : ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent) :
    C ∈ tCloneCompSet Z ∨ C ∈ stPortCompSet Z ∨
      C ∈ ssEdgeCompSet Z ∨ C ∈ uCompCompSet Z := by
  obtain ⟨x, hx⟩ := Quot.exists_rep C
  have hxC : ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk x = C := hx
  cases hL : remainLabel Z x.val x.property with
  | tClone v b =>
      obtain ⟨heq, hT⟩ := remainLabel_eq_tClone x.property hL
      refine .inl ⟨v, hT, b, ?_⟩
      have : x = ⟨.clone v b, clone_remain_of_T hT⟩ := Subtype.ext heq
      rw [this] at hxC
      exact hxC.symm
  | stPort s t =>
      obtain ⟨hst, heq, hS, hT⟩ := remainLabel_eq_stPort x.property hL
      refine .inr (.inl ⟨s, t, hst, hS, hT, ?_⟩)
      have : x = ⟨.port s t hst, ST_port_not_mem_canonical hS⟩ := Subtype.ext heq
      rw [this] at hxC
      exact hxC.symm
  | ssEdge e =>
      obtain ⟨s, t, hst, rfl, hS, hS', heq⟩ := remainLabel_eq_ssEdge x.property hL
      refine .inr (.inr (.inl ⟨s, t, hst, hS, hS', ?_⟩))
      have : x = ⟨.port s t hst, ST_port_not_mem_canonical hS⟩ := Subtype.ext heq
      rw [this] at hxC
      exact hxC.symm
  | uComp c =>
      refine .inr (.inr (.inr ⟨c, ?_⟩))
      exact (uCompRemain_eq_of_label x.property hL).symm.trans hxC

lemma tCloneCompSet_label {Z : Set (GadgetVert G)}
    {C : ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent}
    (hC : C ∈ tCloneCompSet Z) :
    ∃ v b, ∃ hT : classT Z v,
      remainLabel Z (.clone v b) (clone_remain_of_T hT) = .tClone v b ∧
        C = ((gadget G).induce (canonicalCut Z)ᶜ).connectedComponentMk
          ⟨.clone v b, clone_remain_of_T hT⟩ := by
  rcases hC with ⟨v, hT, b, rfl⟩
  exact ⟨v, b, hT, tClone_label hT, rfl⟩

lemma disjoint_tClone_stPort (Z : Set (GadgetVert G)) :
    Disjoint (tCloneCompSet Z) (stPortCompSet Z) := by
  rw [Set.disjoint_left]
  intro C hT hST
  rcases hT with ⟨v, hTv, b, rfl⟩
  rcases hST with ⟨s, t, hst, hS, hTt, hC⟩
  have hR := ConnectedComponent.exact hC
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_clone_of_T hTv, remainLabel_port_of_ST hS hTt] at hL
  cases hL

lemma disjoint_tClone_ssEdge (Z : Set (GadgetVert G)) :
    Disjoint (tCloneCompSet Z) (ssEdgeCompSet Z) := by
  rw [Set.disjoint_left]
  intro C hT hSS
  rcases hT with ⟨v, hTv, b, rfl⟩
  rcases hSS with ⟨s, t, hst, hS, hS', hC⟩
  have hR := ConnectedComponent.exact hC
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_clone_of_T hTv, remainLabel_port_of_SS hS hS'] at hL
  cases hL

lemma disjoint_tClone_uComp (Z : Set (GadgetVert G)) :
    Disjoint (tCloneCompSet Z) (uCompCompSet Z) := by
  rw [Set.disjoint_left]
  intro C hT hU
  rcases hT with ⟨v, hTv, b, rfl⟩
  rcases hU with ⟨c, hC⟩
  have hR := ConnectedComponent.exact hC
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_clone_of_T hTv, remainLabel_uCompRep_clone] at hL
  cases hL

lemma disjoint_stPort_ssEdge (Z : Set (GadgetVert G)) :
    Disjoint (stPortCompSet Z) (ssEdgeCompSet Z) := by
  rw [Set.disjoint_left]
  intro C hST hSS
  rcases hST with ⟨s, t, hst, hS, hT, rfl⟩
  rcases hSS with ⟨s', t', hst', hS', hS'', hC⟩
  have hR := ConnectedComponent.exact hC
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_port_of_ST hS hT, remainLabel_port_of_SS hS' hS''] at hL
  cases hL

lemma disjoint_stPort_uComp (Z : Set (GadgetVert G)) :
    Disjoint (stPortCompSet Z) (uCompCompSet Z) := by
  rw [Set.disjoint_left]
  intro C hST hU
  rcases hST with ⟨s, t, hst, hS, hT, rfl⟩
  rcases hU with ⟨c, hC⟩
  have hR := ConnectedComponent.exact hC
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_port_of_ST hS hT, remainLabel_uCompRep_clone] at hL
  cases hL

lemma disjoint_ssEdge_uComp (Z : Set (GadgetVert G)) :
    Disjoint (ssEdgeCompSet Z) (uCompCompSet Z) := by
  rw [Set.disjoint_left]
  intro C hSS hU
  rcases hSS with ⟨s, t, hst, hS, hS', rfl⟩
  rcases hU with ⟨c, hC⟩
  have hR := ConnectedComponent.exact hC
  have hL := remainLabel_eq_of_reachable hR
  rw [remainLabel_port_of_SS hS hS', remainLabel_uCompRep_clone] at hL
  cases hL

lemma tCloneCompSet_subset_odd (Z : Set (GadgetVert G)) :
    tCloneCompSet Z ⊆ ((gadget G).induce (canonicalCut Z)ᶜ).oddComponents := by
  intro C hC
  rcases hC with ⟨v, hT, b, rfl⟩
  exact T_clone_component_odd' hT

lemma stPortCompSet_subset_odd (Z : Set (GadgetVert G)) :
    stPortCompSet Z ⊆ ((gadget G).induce (canonicalCut Z)ᶜ).oddComponents := by
  intro C hC
  rcases hC with ⟨s, t, hst, hS, hT, rfl⟩
  exact ST_port_component_odd' hS hT

lemma ssEdgeCompSet_even {Z : Set (GadgetVert G)}
    {C : ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent}
    (hC : C ∈ ssEdgeCompSet Z) : Even C.supp.ncard := by
  rcases hC with ⟨s, t, hst, hS, hS', rfl⟩
  exact SS_port_component_even' hS hS'

lemma ssEdgeCompSet_disjoint_odd (Z : Set (GadgetVert G)) :
    Disjoint (ssEdgeCompSet Z)
      ((gadget G).induce (canonicalCut Z)ᶜ).oddComponents := by
  rw [Set.disjoint_left]
  intro C hSS hOdd
  exact Nat.not_odd_iff_even.2 (ssEdgeCompSet_even hSS) hOdd

/-- Odd U remainder components: realized U fibres with odd attachment `e(D,T)`. -/
def oddUCompSet (Z : Set (GadgetVert G)) :
    Set ((gadget G).induce (canonicalCut Z)ᶜ).ConnectedComponent :=
  {C | ∃ c : (G.induce {w | classU Z w}).ConnectedComponent,
    Odd (orderedEdgeCount G (uCompVerts Z c) (originalT Z)) ∧
      C = uCompRemain Z c}

lemma oddUCompSet_eq_image (Z : Set (GadgetVert G)) :
    oddUCompSet Z =
      uCompRemain Z '' {c | Odd (orderedEdgeCount G (uCompVerts Z c) (originalT Z))} := by
  ext C
  constructor
  · rintro ⟨c, hodd, rfl⟩
    exact ⟨c, hodd, rfl⟩
  · rintro ⟨c, hodd, rfl⟩
    exact ⟨c, hodd, rfl⟩

lemma ncard_oddUCompSet (Z : Set (GadgetVert G)) :
    (oddUCompSet Z).ncard =
      ((Finset.univ : Finset ((G.induce {w | classU Z w}).ConnectedComponent)).filter
        fun c => Odd (orderedEdgeCount G (uCompVerts Z c) (originalT Z))).card := by
  rw [oddUCompSet_eq_image, ncard_image_of_injective _ (uCompRemain_injective Z),
    ncard_eq_toFinset_card']
  congr 1
  ext c
  simp

lemma oddUCompSet_subset_odd (Z : Set (GadgetVert G)) :
    oddUCompSet Z ⊆ ((gadget G).induce (canonicalCut Z)ᶜ).oddComponents := by
  intro C hC
  rcases hC with ⟨c, hodd, rfl⟩
  exact (odd_uCompRemain_iff_attach c).mpr hodd

lemma uComp_odd_mem_oddU {Z : Set (GadgetVert G)}
    {c : (G.induce {w | classU Z w}).ConnectedComponent}
    (hodd : Odd (uCompRemain Z c).supp.ncard) :
    uCompRemain Z c ∈ oddUCompSet Z :=
  ⟨c, (odd_uCompRemain_iff_attach c).mp hodd, rfl⟩

lemma oddComponents_eq_union (Z : Set (GadgetVert G)) :
    ((gadget G).induce (canonicalCut Z)ᶜ).oddComponents =
      tCloneCompSet Z ∪ stPortCompSet Z ∪ oddUCompSet Z := by
  ext C
  constructor
  · intro hOdd
    rcases remain_component_classified C with hT | hST | hSS | hU
    · exact .inl (.inl hT)
    · exact .inl (.inr hST)
    · exact (ssEdgeCompSet_disjoint_odd Z).le_bot ⟨hSS, hOdd⟩ |>.elim
    · rcases hU with ⟨c, rfl⟩
      exact .inr (uComp_odd_mem_oddU hOdd)
  · intro h
    rcases h with hAB | hU
    · rcases hAB with hT | hST
      · exact tCloneCompSet_subset_odd Z hT
      · exact stPortCompSet_subset_odd Z hST
    · exact oddUCompSet_subset_odd Z hU

lemma disjoint_tClone_oddU (Z : Set (GadgetVert G)) :
    Disjoint (tCloneCompSet Z) (oddUCompSet Z) :=
  disjoint_tClone_uComp Z |>.mono_right (by
    intro C h; rcases h with ⟨c, _, rfl⟩; exact ⟨c, rfl⟩)

lemma disjoint_stPort_oddU (Z : Set (GadgetVert G)) :
    Disjoint (stPortCompSet Z) (oddUCompSet Z) :=
  disjoint_stPort_uComp Z |>.mono_right (by
    intro C h; rcases h with ⟨c, _, rfl⟩; exact ⟨c, rfl⟩)

/-! ## Transport `G[U]` components to remainder `h(S,T)` -/

noncomputable def classUIso (Z : Set (GadgetVert G)) :
    G.induce {w | classU Z w} ≃g
      G.induce ((originalS Z ∪ originalT Z : Finset V) : Set V)ᶜ where
  toEquiv := Set.equivOfEq (classUSet_eq_remainder Z)
  map_rel_iff' := by
    intro a b
    simp [comap_adj]

lemma classUIso_val (Z : Set (GadgetVert G))
    (v : {w // classU Z w}) :
    ((classUIso Z) v).val = v.val :=
  rfl

lemma uCompVerts_eq_componentVerts (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    uCompVerts Z c =
      componentVerts G (originalS Z) (originalT Z)
        ((classUIso Z).connectedComponentEquiv c) := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvU, hc⟩ := mem_uCompVerts_iff.mp hv
    refine Finset.mem_image.mpr ⟨classUIso Z ⟨v, hvU⟩, ?_, rfl⟩
    rw [Set.mem_toFinset, ConnectedComponent.mem_supp_iff, Iso.connectedComponentEquiv_apply]
    have hc' : (G.induce {w | classU Z w}).connectedComponentMk ⟨v, hvU⟩ = c := by
      simpa [uComponent] using hc
    rw [← hc', ConnectedComponent.map_mk]
    rfl
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨w, hmem, rfl⟩
    have hw := (ConnectedComponent.mem_supp_iff _ _).mp (Set.mem_toFinset.mp hmem)
    have hvU : classU Z w.val :=
      (Set.ext_iff.mp (classUSet_eq_remainder Z) w.val).mpr w.property
    have : uComponent Z w.val hvU = c := by
      apply (classUIso Z).connectedComponentEquiv.injective
      rw [Iso.connectedComponentEquiv_apply, uComponent, ConnectedComponent.map_mk]
      exact hw
    exact mem_uCompVerts_iff.mpr ⟨hvU, this⟩

lemma componentAttach_uComp (Z : Set (GadgetVert G))
    (c : (G.induce {w | classU Z w}).ConnectedComponent) :
    componentAttach G (originalS Z) (originalT Z)
        ((classUIso Z).connectedComponentEquiv c) =
      orderedEdgeCount G (uCompVerts Z c) (originalT Z) := by
  simp [componentAttach, uCompVerts_eq_componentVerts]

lemma ncard_oddUCompSet_eq_hCount (Z : Set (GadgetVert G)) :
    (oddUCompSet Z).ncard = hCount G (originalS Z) (originalT Z) := by
  rw [ncard_oddUCompSet, hCount]
  let e := (classUIso Z).connectedComponentEquiv
  let P := (Finset.univ : Finset ((G.induce {w | classU Z w}).ConnectedComponent)).filter
    fun c => Odd (orderedEdgeCount G (uCompVerts Z c) (originalT Z))
  let Q := (Finset.univ : Finset
      ((G.induce ((originalS Z ∪ originalT Z : Finset V) : Set V)ᶜ).ConnectedComponent)).filter
    fun c => Odd (componentAttach G (originalS Z) (originalT Z) c)
  have himg : P.map e.toEmbedding = Q := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_map.mp hc with ⟨c', hc', rfl⟩
      rw [Finset.mem_filter] at hc' ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa using (componentAttach_uComp Z c').symm ▸ hc'.2
    · intro hc
      refine Finset.mem_map.mpr ⟨e.symm c, ?_, e.apply_symm_apply c⟩
      rw [Finset.mem_filter] at hc ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hA := componentAttach_uComp Z (e.symm c)
      rw [e.apply_symm_apply] at hA
      exact hA.symm ▸ hc.2
  rw [← Finset.card_map e.toEmbedding, himg]

lemma ncard_oddComponents_canonical (Z : Set (GadgetVert G)) :
    ((gadget G).induce (canonicalCut Z)ᶜ).oddComponents.ncard =
      2 * (originalT Z).card +
        orderedEdgeCount G (originalS Z) (originalT Z) +
        hCount G (originalS Z) (originalT Z) := by
  rw [oddComponents_eq_union]
  have d1 := disjoint_tClone_stPort Z
  have d2 := disjoint_tClone_oddU Z
  have d3 := disjoint_stPort_oddU Z
  have dU : Disjoint (tCloneCompSet Z ∪ stPortCompSet Z) (oddUCompSet Z) :=
    disjoint_union_left.mpr ⟨d2, d3⟩
  rw [ncard_union_eq dU, ncard_union_eq d1, ncard_tCloneCompSet, ncard_stPortCompSet,
    ncard_oddUCompSet_eq_hCount]

theorem oddComponentCount_canonicalCut (Z : Set (GadgetVert G)) :
    oddComponentCount (gadget G) (canonicalCut Z) =
      2 * (originalT Z).card +
        orderedEdgeCount G (originalS Z) (originalT Z) +
        hCount G (originalS Z) (originalT Z) := by
  simpa [oddComponentCount] using ncard_oddComponents_canonical Z

/-! ## `Σ_T d_G = Σ_T degDelete S + e(S,T)` and `def = −Δ` -/

lemma degree_eq_degDelete_add_toS (S : Finset V) (t : V) :
    G.degree t = degDelete G S t + (G.neighborFinset t ∩ S).card := by
  have hun : G.neighborFinset t =
      G.neighborFinset t \ S ∪ G.neighborFinset t ∩ S := by
    ext w; simp; tauto
  have hd : Disjoint (G.neighborFinset t \ S) (G.neighborFinset t ∩ S) :=
    Finset.disjoint_sdiff_inter _ _
  calc G.degree t
      = (G.neighborFinset t \ S ∪ G.neighborFinset t ∩ S).card := by
          rw [SimpleGraph.degree]
          conv_lhs => rw [hun]
    _ = (G.neighborFinset t \ S).card + (G.neighborFinset t ∩ S).card :=
          Finset.card_union_of_disjoint hd
    _ = degDelete G S t + (G.neighborFinset t ∩ S).card := rfl

lemma sum_degree_originalT (Z : Set (GadgetVert G)) :
    ∑ t ∈ originalT Z, G.degree t =
      ∑ t ∈ originalT Z, degDelete G (originalS Z) t +
        orderedEdgeCount G (originalS Z) (originalT Z) := by
  rw [Finset.sum_congr rfl fun t _ => degree_eq_degDelete_add_toS (originalS Z) t,
    Finset.sum_add_distrib, ← orderedEdgeCount_eq_sum (originalT Z) (originalS Z),
    orderedEdgeCount_comm]

theorem signedDeficiency_canonicalCut_eq_neg_delta (Z : Set (GadgetVert G)) :
    signedDeficiency (gadget G) (canonicalCut Z) =
      -delta G (originalS Z) (originalT Z) := by
  have hodd := oddComponentCount_canonicalCut Z
  have hcut := ncard_canonicalCut_original Z
  have hdeg := sum_degree_originalT Z
  simp only [signedDeficiency, delta, hodd, hcut]
  push_cast
  have hdegZ :
      (∑ t ∈ originalT Z, (G.degree t : ℤ)) =
        (∑ t ∈ originalT Z, (degDelete G (originalS Z) t : ℤ)) +
          (orderedEdgeCount G (originalS Z) (originalT Z) : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_add, hdeg]
  rw [hdegZ]
  ring

end TwoFactor
end Nikoghosyan
