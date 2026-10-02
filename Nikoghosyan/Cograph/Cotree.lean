/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.Decomposition

/-!
# Cotree constructibility on an ambient finset

A `CotreeOn G U` is a well-founded union/join decomposition of the induced
subgraph on `U`, using only original `G`-edges. This is equivalent to actual
`P4`-freeness of `U`; a cotree is never assumed in place of `IsCograph`.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Recursive cotree constructibility of the induced subgraph on an ambient
finset. The empty graph and every singleton are constructible; disjoint union
and complete join of constructible induced subgraphs remain constructible.
Both join sides are required nonempty so that a join is a genuine nontrivial
complete join. -/
inductive CotreeOn (G : SimpleGraph V) : Finset V → Prop
  | empty : CotreeOn G ∅
  | singleton (v : V) : CotreeOn G {v}
  | disjointUnion {A B : Finset V}
      (hdisj : Disjoint A B)
      (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
      (hA : CotreeOn G A) (hB : CotreeOn G B) :
      CotreeOn G (A ∪ B)
  | completeJoin {A B : Finset V}
      (hAne : A.Nonempty) (hBne : B.Nonempty)
      (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
      (hA : CotreeOn G A) (hB : CotreeOn G B) :
      CotreeOn G (A ∪ B)

variable {G : SimpleGraph V}

lemma isCograph_of_cotreeOn {U : Finset V} (h : CotreeOn G U) : IsCograph G U := by
  induction h with
  | empty =>
    intro a _ _ _ ha
    exact (Finset.notMem_empty a ha).elim
  | singleton v =>
    intro a b c d ha hb hc hd hp
    have ha' : a = v := Finset.mem_singleton.mp ha
    have hb' : b = v := Finset.mem_singleton.mp hb
    subst ha'
    subst hb'
    exact hp.ne_ab rfl
  | disjointUnion hdisj hnocross hA hB ihA ihB =>
    exact isCograph_union_of_no_cross hnocross ihA ihB
  | completeJoin hAne hBne hAB hA hB ihA ihB =>
    exact isCograph_union_of_complete_join hAB ihA ihB

lemma cotreeOn_of_isCograph {U : Finset V} (hU : IsCograph G U) : CotreeOn G U := by
  suffices ∀ n (W : Finset V), W.card = n → IsCograph G W → CotreeOn G W from
    this U.card U rfl hU
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W hWcard hW
    match n with
    | 0 =>
      have : W = ∅ := Finset.card_eq_zero.mp hWcard
      subst this
      exact CotreeOn.empty
    | 1 =>
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hWcard
      subst hv
      exact CotreeOn.singleton v
    | n + 2 =>
      have h2 : 2 ≤ W.card := by omega
      by_cases hconn : (G.induce (W : Set V)).Connected
      · obtain ⟨A, B, hAU, hBU, hAne, hBne, -, hcover, hAB, hAcard, hBcard⟩ :=
          exists_complete_join_on (U := W) hW hconn h2
        have hA : CotreeOn G A :=
          ih A.card (by omega) A rfl (isCograph_mono hW hAU)
        have hB : CotreeOn G B :=
          ih B.card (by omega) B rfl (isCograph_mono hW hBU)
        have : CotreeOn G (A ∪ B) :=
          CotreeOn.completeJoin hAne hBne hAB hA hB
        simpa [hcover] using this
      · have hWne : W.Nonempty :=
          Finset.card_pos.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) h2)
        obtain ⟨A, B, hAU, hBU, -, -, hdisj, hcover, hnocross, hAcard, hBcard⟩ :=
          exists_disjoint_union_on (U := W) hconn hWne
        have hA : CotreeOn G A :=
          ih A.card (by omega) A rfl (isCograph_mono hW hAU)
        have hB : CotreeOn G B :=
          ih B.card (by omega) B rfl (isCograph_mono hW hBU)
        have : CotreeOn G (A ∪ B) :=
          CotreeOn.disjointUnion hdisj hnocross hA hB
        simpa [hcover] using this

/-- Recursive union/join constructibility of an induced subgraph is equivalent
to actual induced-`P4`-freeness of that vertex set. -/
lemma cotreeOn_iff_isCograph {U : Finset V} : CotreeOn G U ↔ IsCograph G U :=
  ⟨isCograph_of_cotreeOn, cotreeOn_of_isCograph⟩

/-- Whole-graph form of the cotree characterisation. -/
def CotreeConstructible (G : SimpleGraph V) : Prop :=
  CotreeOn G Finset.univ

lemma cotreeConstructible_iff_isCographGraph :
    CotreeConstructible G ↔ IsCographGraph G := by
  rw [CotreeConstructible, cotreeOn_iff_isCograph, isCographGraph_iff_univ]

end Cograph
end Nikoghosyan
