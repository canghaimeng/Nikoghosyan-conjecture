/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalFullSpectrum

/-!
# All-cograph original Hamilton cycle from the full terminal spectrum

An `AllCographSides` partition of a 1-tough cofree host carries a repaired
terminal hypothesis on `K = B ∪ W`. The numerical choice
`q = max(p(K), m - |U|)` lies in the original-B spectrum interval, so the
full spectrum supplies an actual `B`-ended cover of that cardinality.
The already-checked endpoint-seam assembly then yields a spanning original
cycle.

This is the all-cograph case of the manuscript. The remaining host cases
(non-cograph blocks, later mixed replacements) are out of scope here.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace AllCographSides

variable (P : AllCographSides G)

lemma B_nonempty : P.B.Nonempty := by
  refine card_pos.mp ?_
  have hm := P.hm
  have hcard := P.hBcard
  omega

/-- The numerical all-cograph index `chosenQ` lies in the original-B
spectrum interval once a minimum `B`-ended cover of `K` exists. -/
lemma chosenQ_mem_full_interval (hT : OneTough G) (hpat : NoInducedP4UnionP1 G) :
    pathCoverNumber G (P.B ∪ P.W) ≤ P.chosenQ ∧
      P.chosenQ + pathCoverNumber G ((P.B ∪ P.W) \ P.B) ≤ P.B.card := by
  have hrep := P.repairedTerminalHypothesis_of_oneTough hpat hT
  have hmin := exists_general_min_terminalCover hrep P.B_nonempty
  have hmem := q_max_mem_interval_of_sides P hT hmin
  have hpW :
      pathCoverNumber G ((P.B ∪ P.W) \ P.B) = pathCoverNumber G P.W := by
    simp [P.K_sdiff_B]
  refine ⟨hmem.1, ?_⟩
  simpa [AllCographSides.chosenQ, hpW] using hmem.2

/-- Actual original-edge `B`-ended cover of `K` of cardinality `chosenQ`. -/
theorem exists_terminalCover_chosenQ (hT : OneTough G)
    (hpat : NoInducedP4UnionP1 G) :
    ∃ pcK : PathCover G (P.B ∪ P.W),
      pcK.card = P.chosenQ ∧ IsTerminalCover (G := G) P.B pcK := by
  have hrep := P.repairedTerminalHypothesis_of_oneTough hpat hT
  obtain ⟨hlo, hhi⟩ := P.chosenQ_mem_full_interval hT hpat
  exact exists_terminalCover_of_card hrep P.B_nonempty P.chosenQ hlo hhi

end AllCographSides

/-- All-cograph original Hamilton cycle: a globally minimum all-cograph
original-edge factor of a 1-tough cofree host of order at least three is
Hamiltonian. The `B`-terminal cover of cardinality `chosenQ` is supplied
by the full original-B spectrum rather than by ordinary refinement. -/
theorem all_cograph_hamiltonian
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G) (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support) :
    ∃ c : GraphCycle G, c.support = univ :=
  min_all_cograph_hamiltonian_of_chosen_terminal_cover hT hord hpat F hmin hcog
    (fun P => P.exists_terminalCover_chosenQ hT hpat)

end Nikoghosyan
