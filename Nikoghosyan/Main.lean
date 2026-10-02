/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.RemainingCase
import Nikoghosyan.Prerequisites.TwoFactorBarrier

/-!
# Manuscript `thm:main`

Every finite simple 1-tough graph of order at least three with no induced
`P₄ ∪ P₁` has a spanning original-edge cycle. Classical `DecidableRel` is
introduced inside the proof, not as a graph hypothesis. No supplied
factor, canonical groups, cut, or locality callback appears in the
exported type.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A one-cycle factor is a spanning original-edge cycle. -/
lemma exists_spanning_graphCycle_of_min_card_one
    (F : CycleFactor G) (hF : F.card = 1) :
    ∃ c : GraphCycle G, c.support = univ := by
  obtain ⟨a, w, hw, hs, _hord⟩ :=
    CycleFactor.exists_hamiltonian_cycle_of_card_one F hF
  exact ⟨⟨a, w, hw⟩, hs⟩

/-- Factor existence plus minimum selection. Classical adjacency
decidability is introduced inside the proof. -/
lemma exists_min_cycleFactor_of_oneTough_noInducedP4UnionP1
    (hord : 3 ≤ Fintype.card V)
    (hT : OneTough G)
    (hpat : NoInducedP4UnionP1 G) :
    ∃ F : CycleFactor G, ∀ F' : CycleFactor G, F.card ≤ F'.card := by
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨F0⟩ :=
    TwoFactor.exists_cycleFactor_of_oneTough_noInducedP4UnionP1 hord hT hpat
  obtain ⟨F, _hle, hmin⟩ := CycleFactor.exists_min_of_exists F0
  exact ⟨F, hmin⟩

/-- Manuscript `thm:main`: a finite simple 1-tough graph of order at
least three with no induced `P₄ ∪ P₁` has a spanning original-edge
cycle. -/
theorem exists_spanning_graphCycle_of_oneTough_noInducedP4UnionP1
    (hord : 3 ≤ Fintype.card V)
    (hT : OneTough G)
    (hpat : NoInducedP4UnionP1 G) :
    ∃ c : GraphCycle G, c.support = univ := by
  obtain ⟨F, hmin⟩ :=
    exists_min_cycleFactor_of_oneTough_noInducedP4UnionP1 hord hT hpat
  by_cases h1 : F.card = 1
  · exact exists_spanning_graphCycle_of_min_card_one F h1
  · by_cases hHam : G.IsHamiltonian
    · exact (isHamiltonian_iff_exists_spanning_graphCycle hord).1 hHam
    · exact (remaining_min_factor_not_hamiltonian hT hord hpat F hmin hHam).elim

/-- Mathlib Hamiltonicity of the same host. -/
theorem isHamiltonian_of_oneTough_noInducedP4UnionP1
    (hord : 3 ≤ Fintype.card V)
    (hT : OneTough G)
    (hpat : NoInducedP4UnionP1 G) :
    G.IsHamiltonian :=
  (isHamiltonian_iff_exists_spanning_graphCycle hord).2
    (exists_spanning_graphCycle_of_oneTough_noInducedP4UnionP1 hord hT hpat)

end Nikoghosyan
