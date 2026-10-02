/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.EndpointSeamAssembly
import Nikoghosyan.AllCographStructure
import Nikoghosyan.Cograph.PathCoverRefinement

/-!
Phase 13 specialization: original-edge cycle from actual endpoint covers
of an `AllCographSides` partition.

A `k`-cover of `U` and a `B`-ended `q`-cover of `K = B ∪ W` with `k + q = m`
join by `PathCover.appendDisjoint` (no no-cross premise). Every `A`-vertex
is originally adjacent to every joined-path endpoint by `hAU` on `U`-paths
and `hAB` on `B`-terminal `K`-paths. Generic endpoint-seam assembly then
yields a genuine original cycle whose support is exactly `V(G)`.

This wrapper is not `all:thm:all-cograph`. Closing that theorem still
requires a kernel-checked `B`-terminal spectrum supplying the `K`-cover;
ordinary refinement is used only for the `U`-cover.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace AllCographSides

variable (P : AllCographSides G)

lemma disjoint_A_UK : Disjoint P.A (P.U ∪ (P.B ∪ P.W)) :=
  disjoint_union_right.2 ⟨P.hdisjAU, P.disjoint_A_K⟩

lemma cover_A_UK : P.A ∪ (P.U ∪ (P.B ∪ P.W)) = univ := by
  simpa [union_assoc, union_left_comm, union_comm] using P.hcover

/-- Original `A`–endpoint seams on an ordinary `U`-cover. -/
lemma seams_of_U_cover (pcU : PathCover G P.U) {a : V} (ha : a ∈ P.A)
    {p : GraphPath G} (hp : p ∈ pcU.paths) :
    G.Adj a p.start ∧ G.Adj a p.finish := by
  have hend := PathCover.endpoints_mem pcU hp
  exact ⟨P.hAU ha hend.1, P.hAU ha hend.2⟩

/-- Original `A`–endpoint seams on a `B`-terminal cover of `K = B ∪ W`.
No completeness of `A` to `W` is used. -/
lemma seams_of_K_cover (pcK : PathCover G (P.B ∪ P.W))
    (hterm : IsTerminalCover (G := G) P.B pcK) {a : V} (ha : a ∈ P.A)
    {p : GraphPath G} (hp : p ∈ pcK.paths) :
    G.Adj a p.start ∧ G.Adj a p.finish := by
  have ht := hterm p hp
  exact ⟨P.hAB ha ht.1, P.hAB ha ht.2⟩

/-- Joined actual cover of `U ∪ K`. Support disjointness of the two
carriers is enough; no no-cross hypothesis is required to concatenate. -/
noncomputable def joinedCover (pcU : PathCover G P.U)
    (pcK : PathCover G (P.B ∪ P.W)) :
    PathCover G (P.U ∪ (P.B ∪ P.W)) :=
  PathCover.appendDisjoint P.disjoint_U_K pcU pcK

lemma joinedCover_card (pcU : PathCover G P.U)
    (pcK : PathCover G (P.B ∪ P.W)) :
    (P.joinedCover pcU pcK).card = pcU.card + pcK.card :=
  PathCover.appendDisjoint_card P.disjoint_U_K pcU pcK

lemma seams_of_joinedCover (pcU : PathCover G P.U)
    (pcK : PathCover G (P.B ∪ P.W))
    (hterm : IsTerminalCover (G := G) P.B pcK) {a : V} (ha : a ∈ P.A)
    {p : GraphPath G} (hp : p ∈ (P.joinedCover pcU pcK).paths) :
    G.Adj a p.start ∧ G.Adj a p.finish := by
  rcases (PathCover.appendDisjoint_mem_iff P.disjoint_U_K pcU pcK).1 hp with hU | hK
  · exact P.seams_of_U_cover pcU ha hU
  · exact P.seams_of_K_cover pcK hterm ha hK

/-- Precise conditional original cycle from actual `U` and `B`-terminal
`K` covers of complementary cardinalities summing to `m`. -/
theorem exists_original_cycle_of_endpoint_covers
    (pcU : PathCover G P.U) (pcK : PathCover G (P.B ∪ P.W))
    (hterm : IsTerminalCover (G := G) P.B pcK)
    (hsum : pcU.card + pcK.card = P.m) :
    ∃ c : GraphCycle G, c.support = (univ : Finset V) := by
  have hcard : P.A.card = (P.joinedCover pcU pcK).card := by
    rw [P.hAcard, P.joinedCover_card, hsum]
  obtain ⟨c, hc⟩ :=
    exists_original_cycle_of_endpoint_seams (A := P.A)
      (K := P.U ∪ (P.B ∪ P.W)) (P.joinedCover pcU pcK) hcard P.disjoint_A_UK
      (fun a ha p hp => P.seams_of_joinedCover pcU pcK hterm ha hp)
      (by simpa [P.hAcard] using P.hm)
  refine ⟨c, hc.trans P.cover_A_UK⟩

/-! ### Numerical choice `q = max(p(K), m - |U|)`, `k = m - q` -/

/-- Spectrum index for a `B`-terminal cover of `K`. -/
noncomputable def chosenQ : ℕ :=
  max (pathCoverNumber G (P.B ∪ P.W)) (P.m - P.U.card)

/-- Ordinary refinement index for a `U`-cover. -/
noncomputable def chosenK : ℕ :=
  P.m - P.chosenQ

lemma chosenQ_le_m (hT : OneTough G) : P.chosenQ ≤ P.m := by
  have hadd := pathCoverNumber_add_le_m P hT
  have hpK : pathCoverNumber G (P.B ∪ P.W) ≤ P.m := by omega
  have hrest : P.m - P.U.card ≤ P.m := Nat.sub_le _ _
  exact max_le hpK hrest

lemma chosenQ_ge_pathCover_K : pathCoverNumber G (P.B ∪ P.W) ≤ P.chosenQ :=
  le_max_left _ _

lemma chosenK_add_chosenQ (hT : OneTough G) : P.chosenK + P.chosenQ = P.m :=
  Nat.sub_add_cancel (P.chosenQ_le_m hT)

lemma chosenK_le_card_U : P.chosenK ≤ P.U.card := by
  have hrest : P.m - P.U.card ≤ P.chosenQ := le_max_right _ _
  have hgoal : P.m ≤ P.chosenQ + P.U.card := Nat.le_add_of_sub_le hrest
  simpa [chosenK] using Nat.sub_le_iff_le_add'.2 hgoal

lemma chosenK_ge_pathCover_U (hT : OneTough G) :
    pathCoverNumber G P.U ≤ P.chosenK := by
  have hadd := pathCoverNumber_add_le_m P hT
  have hq : pathCoverNumber G (P.B ∪ P.W) ≤ P.chosenQ := P.chosenQ_ge_pathCover_K
  have hqm : P.chosenQ ≤ P.m := P.chosenQ_le_m hT
  have hU : pathCoverNumber G P.U ≤ P.U.card := pathCoverNumber_le_card (G := G) P.U
  unfold chosenK chosenQ at *
  omega

/-- Realize the ordinary `U`-cover of size `k = m - q` by path-cover
refinement. This is permitted on `U`; it is not permitted as a substitute
for a `B`-terminal cover of `K`. -/
lemma exists_U_cover_of_chosen (hT : OneTough G) :
    ∃ pcU : PathCover G P.U, pcU.card = P.chosenK :=
  exists_pathCover_card (G := G) P.U (P.chosenK_ge_pathCover_U hT)
    P.chosenK_le_card_U

/-- Original spanning cycle from a `B`-terminal cover of `K` of the chosen
cardinality, together with the refined `U`-cover. -/
theorem exists_univ_cycle_of_chosen_terminal_cover (hT : OneTough G)
    (pcK : PathCover G (P.B ∪ P.W))
    (hcard : pcK.card = P.chosenQ)
    (hterm : IsTerminalCover (G := G) P.B pcK) :
    ∃ c : GraphCycle G, c.support = (univ : Finset V) := by
  obtain ⟨pcU, hU⟩ := P.exists_U_cover_of_chosen hT
  have hsum : pcU.card + pcK.card = P.m := by
    rw [hU, hcard, P.chosenK_add_chosenQ hT]
  exact P.exists_original_cycle_of_endpoint_covers pcU pcK hterm hsum

end AllCographSides

/-- Conditional all-cograph Hamiltonicity: a globally minimum all-cograph
original-edge factor is Hamiltonian, or else an `AllCographSides` partition
together with a `B`-terminal cover of the chosen cardinality yields a
spanning original cycle. The unconditioned `all:thm:all-cograph` remains
OPEN until a kernel-checked terminal spectrum supplies that cover. -/
theorem min_all_cograph_hamiltonian_of_chosen_terminal_cover
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G) (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support)
    (hspec : ∀ P : AllCographSides G,
      ∃ pcK : PathCover G (P.B ∪ P.W),
        pcK.card = P.chosenQ ∧ IsTerminalCover (G := G) P.B pcK) :
    ∃ c : GraphCycle G, c.support = univ := by
  rcases min_all_cograph_hamiltonian_or_sides hT hord hpat F hmin hcog with h | hP
  · exact h
  · obtain ⟨P⟩ := hP
    obtain ⟨pcK, hcard, hterm⟩ := hspec P
    exact P.exists_univ_cycle_of_chosen_terminal_cover hT pcK hcard hterm

end Nikoghosyan
