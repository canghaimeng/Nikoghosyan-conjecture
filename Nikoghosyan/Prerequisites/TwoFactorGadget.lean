/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

/-!
# Two-clone Tutte gadget for spanning 2-regular subgraphs

Coordinator construction from `reports/TWO_FACTOR_GADGET_INTERFACE.md`.

For each original vertex `v` there are clones `(v,0)` and `(v,1)`. For each
original incidence `v ~ w` there is a port `(v,w)`. Both clones of `v` are
adjacent to every port of `v`, and port `(v,w)` is adjacent to port `(w,v)`.
Gadget edges are auxiliary: they are not original edges of `G`.
-/

universe u

namespace Nikoghosyan
namespace TwoFactor

open SimpleGraph
set_option linter.unusedSectionVars false

variable {V : Type u} (G : SimpleGraph V)

/-- Tagged gadget vertices: two clones of each original vertex, plus one port
per original incidence. -/
inductive GadgetVert (G : SimpleGraph V) where
  | clone : V → Fin 2 → GadgetVert G
  | port : (v w : V) → G.Adj v w → GadgetVert G

instance [DecidableEq V] : DecidableEq (GadgetVert G) := fun a b =>
  match a, b with
  | .clone v b, .clone v' b' =>
      if h : v = v' ∧ b = b' then
        .isTrue (by rcases h with ⟨rfl, rfl⟩; rfl)
      else
        .isFalse (by intro h'; exact h (by cases h'; exact ⟨rfl, rfl⟩))
  | .port v w _, .port v' w' _ =>
      if h : v = v' ∧ w = w' then
        .isTrue (by rcases h with ⟨rfl, rfl⟩; rfl)
      else
        .isFalse (by intro h'; exact h (by cases h'; exact ⟨rfl, rfl⟩))
  | .clone _ _, .port _ _ _ => .isFalse (by intro h; cases h)
  | .port _ _ _, .clone _ _ => .isFalse (by intro h; cases h)

/-- Adjacency of the two-clone gadget. -/
def GadgetAdj : GadgetVert G → GadgetVert G → Prop
  | .clone v _, .port v' _ _ => v = v'
  | .port v' _ _, .clone v _ => v = v'
  | .port v w _, .port v' w' _ => v = w' ∧ w = v'
  | .clone _ _, .clone _ _ => False

lemma gadgetAdj_symm {x y : GadgetVert G} : GadgetAdj G x y → GadgetAdj G y x := by
  cases x <;> cases y <;> intro h <;> simp_all [GadgetAdj]

lemma gadgetAdj_irrefl (x : GadgetVert G) : ¬ GadgetAdj G x x := by
  cases x with
  | clone => simp [GadgetAdj]
  | port v w h =>
      intro h'
      exact h.ne (by simp [GadgetAdj] at h'; exact h'.1)

instance [DecidableEq V] : DecidableRel (GadgetAdj G) := fun x y =>
  match x, y with
  | .clone v _, .port v' _ _ => inferInstanceAs (Decidable (v = v'))
  | .port v' _ _, .clone v _ => inferInstanceAs (Decidable (v = v'))
  | .port v w _, .port v' w' _ => inferInstanceAs (Decidable (v = w' ∧ w = v'))
  | .clone _ _, .clone _ _ => isFalse fun h => h

/-- The two-clone gadget graph. -/
def gadget : SimpleGraph (GadgetVert G) where
  Adj := GadgetAdj G
  symm := ⟨fun _ _ => gadgetAdj_symm (G := G)⟩
  loopless := ⟨gadgetAdj_irrefl G⟩

variable {G}

@[simp] lemma gadget_adj_clone_port {v v' w : V} {b : Fin 2} {h : G.Adj v' w} :
    (gadget G).Adj (.clone v b) (.port v' w h) ↔ v = v' := Iff.rfl

@[simp] lemma gadget_adj_port_clone {v v' w : V} {b : Fin 2} {h : G.Adj v' w} :
    (gadget G).Adj (.port v' w h) (.clone v b) ↔ v = v' := Iff.rfl

@[simp] lemma gadget_adj_port_port {v w v' w' : V} {h : G.Adj v w} {h' : G.Adj v' w'} :
    (gadget G).Adj (.port v w h) (.port v' w' h') ↔ v = w' ∧ w = v' := Iff.rfl

@[simp] lemma not_gadget_adj_clone_clone {v v' : V} {b b' : Fin 2} :
    ¬ (gadget G).Adj (.clone v b) (.clone v' b') := by
  simp [gadget, GadgetAdj]

lemma gadget_adj_mate {v w : V} (h : G.Adj v w) :
    (gadget G).Adj (.port v w h) (.port w v h.symm) := by simp

lemma clone_adj_iff {v : V} {b : Fin 2} {x : GadgetVert G} :
    (gadget G).Adj (.clone v b) x ↔ ∃ w, ∃ h : G.Adj v w, x = .port v w h := by
  cases x with
  | clone => simp
  | port v' w h =>
      constructor
      · intro hv
        cases hv
        exact ⟨w, h, rfl⟩
      · rintro ⟨w', h', hport⟩
        injection hport with hv hw
        cases hv
        exact rfl

lemma port_adj_iff {v w : V} {h : G.Adj v w} {x : GadgetVert G} :
    (gadget G).Adj (.port v w h) x ↔
      (∃ b : Fin 2, x = .clone v b) ∨ ∃ h' : G.Adj w v, x = .port w v h' := by
  cases x with
  | clone v' b =>
      constructor
      · intro hv
        exact .inl ⟨b, by cases hv; rfl⟩
      · intro hx
        rcases hx with ⟨b', hb'⟩ | ⟨_, hport⟩
        · cases hb'; simp
        · cases hport
  | port v' w' h' =>
      constructor
      · intro hv
        rcases hv with ⟨rfl, rfl⟩
        exact .inr ⟨h.symm, rfl⟩
      · intro hx
        rcases hx with ⟨_, hb⟩ | ⟨_, hport⟩
        · cases hb
        · injection hport with hv hw
          cases hv
          cases hw
          exact ⟨rfl, rfl⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance : Fintype (GadgetVert G) :=
  Fintype.ofEquiv (V × Fin 2 ⊕ { p : V × V // G.Adj p.1 p.2 })
    { toFun := fun
        | .inl ⟨v, b⟩ => .clone v b
        | .inr ⟨⟨v, w⟩, h⟩ => .port v w h
      invFun := fun
        | .clone v b => .inl ⟨v, b⟩
        | .port v w h => .inr ⟨⟨v, w⟩, h⟩
      left_inv := fun
        | .inl _ => rfl
        | .inr _ => rfl
      right_inv := fun
        | .clone _ _ => rfl
        | .port _ _ _ => rfl }

instance : DecidableRel (gadget G).Adj :=
  inferInstanceAs (DecidableRel (GadgetAdj G))

/-- Spanning subgraph in which every original vertex has degree exactly two. -/
def IsSpanningDegreeTwo (F : G.Subgraph) : Prop :=
  F.IsSpanning ∧ ∀ v : V, (F.neighborSet v).ncard = 2

noncomputable section

open Classical

/-- Equivalence `Fin 2 ≃ F.neighborSet v` from a two-element neighbour set. -/
noncomputable def twoNbr (F : G.Subgraph) (v : V)
    (h : (F.neighborSet v).ncard = 2) : Fin 2 ≃ F.neighborSet v :=
  have : Fintype (F.neighborSet v) := Fintype.ofFinite _
  (Fintype.equivFinOfCardEq (by
    rw [Set.ncard_eq_toFinset_card' (F.neighborSet v), Set.toFinset_card] at h
    exact h)).symm

lemma twoNbr_apply_mem (F : G.Subgraph) (v : V)
    (h : (F.neighborSet v).ncard = 2) (b : Fin 2) :
    (twoNbr F v h b : V) ∈ F.neighborSet v :=
  (twoNbr F v h b).property

lemma twoNbr_apply_symm (F : G.Subgraph) (v : V)
    (h : (F.neighborSet v).ncard = 2) (w : F.neighborSet v) :
    twoNbr F v h ((twoNbr F v h).symm w) = w :=
  Equiv.apply_symm_apply _ _

lemma twoNbr_symm_apply (F : G.Subgraph) (v : V)
    (h : (F.neighborSet v).ncard = 2) (b : Fin 2) :
    (twoNbr F v h).symm (twoNbr F v h b) = b :=
  Equiv.symm_apply_apply _ _

/-- Unique gadget partner determined by a spanning degree-two subgraph. -/
noncomputable def factorPartner (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) : GadgetVert G → GadgetVert G
  | .clone v b =>
      .port v (twoNbr F v (hdeg v) b : V)
        (F.adj_sub (twoNbr_apply_mem F v (hdeg v) b))
  | .port v w hvw =>
      if hF : w ∈ F.neighborSet v then
        .clone v ((twoNbr F v (hdeg v)).symm ⟨w, hF⟩)
      else
        .port w v hvw.symm

lemma factorPartner_adj (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) (x : GadgetVert G) :
    (gadget G).Adj x (factorPartner F hdeg x) := by
  cases x with
  | clone v b => simp [factorPartner]
  | port v w hvw =>
      by_cases hF : w ∈ F.neighborSet v
      · simp [factorPartner, hF]
      · simp [factorPartner, hF]

lemma factorPartner_clone (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) (v : V) (b : Fin 2) :
    factorPartner F hdeg (.clone v b) =
      .port v (twoNbr F v (hdeg v) b : V)
        (F.adj_sub (twoNbr_apply_mem F v (hdeg v) b)) := rfl

lemma factorPartner_port_of_mem (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) {v w : V} (hvw : G.Adj v w)
    (hF : w ∈ F.neighborSet v) :
    factorPartner F hdeg (.port v w hvw) =
      .clone v ((twoNbr F v (hdeg v)).symm ⟨w, hF⟩) := by
  simp [factorPartner, hF]

lemma factorPartner_port_of_notMem (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) {v w : V} (hvw : G.Adj v w)
    (hF : w ∉ F.neighborSet v) :
    factorPartner F hdeg (.port v w hvw) = .port w v hvw.symm := by
  simp [factorPartner, hF]

lemma factorPartner_involutive (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) :
    Function.Involutive (factorPartner F hdeg) := by
  intro x
  cases x with
  | clone v b =>
      rw [factorPartner_clone, factorPartner_port_of_mem F hdeg _
        (twoNbr_apply_mem F v (hdeg v) b)]
      simp
  | port v w hvw =>
      by_cases hF : w ∈ F.neighborSet v
      · rw [factorPartner_port_of_mem F hdeg hvw hF, factorPartner_clone]
        simp
      · have hF' : v ∉ F.neighborSet w := by
          intro hv
          exact hF (by
            simpa [Subgraph.mem_neighborSet] using (hv : F.Adj w v).symm)
        rw [factorPartner_port_of_notMem F hdeg hvw hF,
            factorPartner_port_of_notMem F hdeg hvw.symm hF']

/-- Perfect matching of the gadget built from a spanning degree-two subgraph. -/
noncomputable def matchingFromDegreeTwo (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) : Subgraph (gadget G) where
  verts := Set.univ
  Adj x y := y = factorPartner F hdeg x
  adj_sub {x y} h := h ▸ factorPartner_adj F hdeg x
  edge_vert {_ _} _ := trivial
  symm := ⟨fun x y h => by
    change y = factorPartner F hdeg x at h
    rw [h, factorPartner_involutive F hdeg x]⟩

theorem matchingFromDegreeTwo_isPerfectMatching (F : G.Subgraph)
    (hdeg : ∀ v, (F.neighborSet v).ncard = 2) :
    (matchingFromDegreeTwo F hdeg).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro x
  refine ⟨factorPartner F hdeg x, rfl, ?_⟩
  intro y hy
  exact hy

/-- One direction of the gadget reduction: a spanning original degree-two
subgraph produces a perfect matching of the two-clone gadget. -/
theorem exists_gadget_perfectMatching_of_spanningDegreeTwo {F : G.Subgraph}
    (hF : IsSpanningDegreeTwo F) :
    ∃ M : Subgraph (gadget G), M.IsPerfectMatching :=
  ⟨matchingFromDegreeTwo F hF.2, matchingFromDegreeTwo_isPerfectMatching F hF.2⟩

lemma clone_matched_to_own_port {M : Subgraph (gadget G)}
    (hM : M.IsPerfectMatching) (v : V) (b : Fin 2) :
    ∃ w, ∃ h : G.Adj v w, M.Adj (.clone v b) (.port v w h) := by
  obtain ⟨x, hx, _⟩ := (Subgraph.isPerfectMatching_iff.mp hM) (.clone v b)
  obtain ⟨w, h, rfl⟩ := clone_adj_iff.mp (M.adj_sub hx)
  exact ⟨w, h, hx⟩

lemma port_partner_cases {M : Subgraph (gadget G)} (hM : M.IsPerfectMatching)
    {v w : V} (hvw : G.Adj v w) :
    (∃ b : Fin 2, M.Adj (.port v w hvw) (.clone v b)) ∨
      ∃ h' : G.Adj w v, M.Adj (.port v w hvw) (.port w v h') := by
  obtain ⟨x, hx, _⟩ := (Subgraph.isPerfectMatching_iff.mp hM) (.port v w hvw)
  rcases port_adj_iff.mp (M.adj_sub hx) with ⟨b, rfl⟩ | ⟨h', rfl⟩
  · exact .inl ⟨b, hx⟩
  · exact .inr ⟨h', hx⟩

lemma gadgetSubgraph_adj_comm {M : Subgraph (gadget G)} {x y : GadgetVert G}
    (h : M.Adj x y) : M.Adj y x :=
  M.symm.symm x y h

lemma not_clone_eq_port {v w w' : V} {b : Fin 2} {h : G.Adj w w'} :
    (GadgetVert.clone v b : GadgetVert G) ≠ .port w w' h := by
  intro h'; cases h'

lemma locally_matched_of_not_mate {M : Subgraph (gadget G)}
    (hM : M.IsPerfectMatching) {v w : V} (hvw : G.Adj v w)
    (hne : ∀ h' : G.Adj w v, ¬ M.Adj (.port v w hvw) (.port w v h')) :
    ∃ b : Fin 2, M.Adj (.port v w hvw) (.clone v b) := by
  rcases port_partner_cases hM hvw with h | ⟨h', hm⟩
  · exact h
  · exact (hne h' hm).elim

lemma locally_matched_symm {M : Subgraph (gadget G)} (hM : M.IsPerfectMatching)
    {v w : V} (hvw : G.Adj v w) :
    (∃ b : Fin 2, M.Adj (.port v w hvw) (.clone v b)) ↔
      ∃ b : Fin 2, M.Adj (.port w v hvw.symm) (.clone w b) := by
  constructor
  · rintro ⟨b, hb⟩
    refine locally_matched_of_not_mate hM hvw.symm ?_
    intro h'' hm
    obtain ⟨x, hx, hu⟩ := (Subgraph.isPerfectMatching_iff.mp hM) (.port v w hvw)
    have h1 := hu _ hb
    have h2 := hu _ (gadgetSubgraph_adj_comm hm)
    exact not_clone_eq_port (h1.trans h2.symm)
  · rintro ⟨b, hb⟩
    refine locally_matched_of_not_mate hM hvw ?_
    intro h'' hm
    obtain ⟨x, hx, hu⟩ := (Subgraph.isPerfectMatching_iff.mp hM) (.port w v hvw.symm)
    have h1 := hu _ hb
    have h2 := hu _ (gadgetSubgraph_adj_comm hm)
    exact not_clone_eq_port (h1.trans h2.symm)

/-- Original spanning degree-two subgraph recovered from a gadget perfect matching. -/
def degreeTwoFromMatching (M : Subgraph (gadget G)) (hM : M.IsPerfectMatching) :
    G.Subgraph where
  verts := Set.univ
  Adj v w := ∃ hvw : G.Adj v w, ∃ b : Fin 2, M.Adj (.port v w hvw) (.clone v b)
  adj_sub {_ _} h := h.1
  edge_vert {_ _} _ := trivial
  symm := ⟨fun v w h => by
    obtain ⟨hvw, b, hb⟩ := h
    obtain ⟨b', hb'⟩ := (locally_matched_symm hM hvw).mp ⟨b, hb⟩
    exact ⟨hvw.symm, b', hb'⟩⟩

lemma clones_match_distinct_ports {M : Subgraph (gadget G)}
    (hM : M.IsPerfectMatching) (v : V) :
    ∀ {w0 w1 : V} {h0 : G.Adj v w0} {h1 : G.Adj v w1},
      M.Adj (.clone v 0) (.port v w0 h0) →
      M.Adj (.clone v 1) (.port v w1 h1) → w0 ≠ w1 := by
  intro w0 w1 h0 h1 hM0 hM1 hw
  cases hw
  cases Subsingleton.elim h1 h0
  obtain ⟨x, hx, hu⟩ := (Subgraph.isPerfectMatching_iff.mp hM) (.port v w0 h0)
  have hx0 := hu (.clone v 0) (gadgetSubgraph_adj_comm hM0)
  have hx1 := hu (.clone v 1) (gadgetSubgraph_adj_comm hM1)
  injection (hx0.trans hx1.symm) with _ hbit
  exact (Fin.zero_ne_one hbit).elim

theorem exists_spanningDegreeTwo_of_gadget_perfectMatching
    {M : Subgraph (gadget G)} (hM : M.IsPerfectMatching) :
    IsSpanningDegreeTwo (degreeTwoFromMatching M hM) := by
  refine ⟨fun _ => trivial, fun v => ?_⟩
  obtain ⟨w0, h0, hM0⟩ := clone_matched_to_own_port hM v 0
  obtain ⟨w1, h1, hM1⟩ := clone_matched_to_own_port hM v 1
  have hne : w0 ≠ w1 := clones_match_distinct_ports hM v hM0 hM1
  have loc0 : (degreeTwoFromMatching M hM).Adj v w0 := ⟨h0, ⟨0, gadgetSubgraph_adj_comm hM0⟩⟩
  have loc1 : (degreeTwoFromMatching M hM).Adj v w1 := ⟨h1, ⟨1, gadgetSubgraph_adj_comm hM1⟩⟩
  have hsup : ({w0, w1} : Set V) ⊆ (degreeTwoFromMatching M hM).neighborSet v := by
    intro w hw
    rcases hw with rfl | rfl
    · exact loc0
    · exact loc1
  have hsub : (degreeTwoFromMatching M hM).neighborSet v ⊆ ({w0, w1} : Set V) := by
    intro w hw
    obtain ⟨hvw, b, hb⟩ := hw
    obtain ⟨x, hx, hu⟩ := (Subgraph.isPerfectMatching_iff.mp hM) (.clone v b)
    have hxport := hu (.port v w hvw) (gadgetSubgraph_adj_comm hb)
    have : b = 0 ∨ b = 1 := by
      revert b; intro b; fin_cases b <;> simp
    rcases this with rfl | rfl
    · have heq := hu (.port v w0 h0) hM0
      have hports : (.port v w hvw : GadgetVert G) = .port v w0 h0 :=
        hxport.trans heq.symm
      injection hports with _ hw
      exact .inl hw
    · have heq := hu (.port v w1 h1) hM1
      have hports : (.port v w hvw : GadgetVert G) = .port v w1 h1 :=
        hxport.trans heq.symm
      injection hports with _ hw
      exact .inr hw
  have hcard : ({w0, w1} : Set V).ncard = 2 := Set.ncard_pair hne
  exact le_antisymm
    ((Set.ncard_le_ncard hsub).trans_eq hcard)
    (hcard.symm.trans_le (Set.ncard_le_ncard hsup))

/-- A graph has a spanning degree-two subgraph if and only if its two-clone
gadget has a perfect matching. -/
theorem gadget_perfectMatching_iff_spanningDegreeTwo :
    (∃ M : Subgraph (gadget G), M.IsPerfectMatching) ↔
      ∃ F : G.Subgraph, IsSpanningDegreeTwo F := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨degreeTwoFromMatching M hM,
      exists_spanningDegreeTwo_of_gadget_perfectMatching hM⟩
  · rintro ⟨F, hF⟩
    exact exists_gadget_perfectMatching_of_spanningDegreeTwo hF

end

end TwoFactor
end Nikoghosyan
