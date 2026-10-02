/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.TerminalConstruction
import Nikoghosyan.Prerequisites.TerminalPieces

/-!
# Necessary terminal spectrum interval

Any actual `B`-terminal original-edge cover of cardinality `q` satisfies
`q + p(K \ B) ≤ |B|` by leftoverCover. Combined with a minimum `B`-terminal
cover of size `p(K)`, the candidate interval is
`[p(K), |B| - p(K \ B)]`. Realizing every intermediate `q` still requires a
B-preserving leftover merge; ordinary `splitOne` does not keep B-ends.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma terminalCover_card_add_pathCoverNumber_le {K B : Finset V}
    (hBK : B ⊆ K) (hInd : Independent (G := G) B)
    {pc : PathCover G K} (hterm : IsTerminalCover (G := G) B pc) :
    pc.card + pathCoverNumber G (K \ B) ≤ B.card :=
  pathCoverNumber_add_le_card_B hBK hInd hterm

/-- If a minimum `B`-terminal cover exists, the repaired interval is
nonempty: `p(K) ≤ |B| - p(K \ B)`. -/
lemma pathCoverNumber_le_card_B_sub {K B : Finset V}
    (hBK : B ⊆ K) (hInd : Independent (G := G) B)
    (hmin : ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc) :
    pathCoverNumber G K + pathCoverNumber G (K \ B) ≤ B.card := by
  obtain ⟨pc, hcard, hterm⟩ := hmin
  have hle := pathCoverNumber_add_le_card_B hBK hInd hterm
  omega

lemma exists_terminalCover_card_pathCoverNumber {K B : Finset V}
    (hmin : ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc) :
    ∃ pc : PathCover G K,
      pc.card = pathCoverNumber G K ∧ IsTerminalCover (G := G) B pc :=
  hmin

/-- Host capacities already give `p(K) ≤ m` and `p(W) ≤ |U|`. Choosing
`q = max(p(K), m - |U|)` therefore lies in `[p(K), |B| - p(W)]` once a
minimum `B`-terminal cover of `K = B ∪ W` exists. -/
lemma q_max_mem_interval_of_sides (P : AllCographSides G)
    (htough : OneTough G)
    (hmin : ∃ pc : PathCover G (P.B ∪ P.W),
      pc.card = pathCoverNumber G (P.B ∪ P.W) ∧
        IsTerminalCover (G := G) P.B pc) :
    let q := max (pathCoverNumber G (P.B ∪ P.W)) (P.m - P.U.card)
    pathCoverNumber G (P.B ∪ P.W) ≤ q ∧
      q + pathCoverNumber G P.W ≤ P.B.card := by
  intro q
  have hKW : (P.B ∪ P.W) \ P.B = P.W := P.K_sdiff_B
  have hle := pathCoverNumber_le_card_B_sub (G := G)
    P.B_subset_K P.hBind hmin
  have hpW : pathCoverNumber G ((P.B ∪ P.W) \ P.B) = pathCoverNumber G P.W := by
    simp [hKW]
  have hcapU : pathCoverNumber G P.W ≤ P.U.card :=
    pathCoverNumber_W_le_card_U_of_sides P htough
  have hm : P.B.card = P.m := P.hBcard
  constructor
  · exact le_max_left _ _
  · have h1 :
        pathCoverNumber G (P.B ∪ P.W) + pathCoverNumber G P.W ≤ P.B.card := by
      simpa [hpW] using hle
    have h2 : P.m - P.U.card + pathCoverNumber G P.W ≤ P.B.card := by
      by_cases hUm : P.U.card ≤ P.m
      · have hcancel : P.m - P.U.card + P.U.card = P.m := Nat.sub_add_cancel hUm
        omega
      · have : P.m - P.U.card = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hUm)
        omega
    have hmax :
        max (pathCoverNumber G (P.B ∪ P.W)) (P.m - P.U.card) +
            pathCoverNumber G P.W ≤ P.B.card := by
      by_cases hcmp :
          pathCoverNumber G (P.B ∪ P.W) ≤ P.m - P.U.card
      · have : max (pathCoverNumber G (P.B ∪ P.W)) (P.m - P.U.card) =
            P.m - P.U.card := max_eq_right hcmp
        simpa [this] using h2
      · have : max (pathCoverNumber G (P.B ∪ P.W)) (P.m - P.U.card) =
            pathCoverNumber G (P.B ∪ P.W) :=
          max_eq_left (le_of_not_ge hcmp)
        simpa [this] using h1
    simpa [q] using hmax

end Nikoghosyan
