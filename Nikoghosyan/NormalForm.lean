/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.TwoCycles

/-!
# Manuscript `prop:normal-form` (core clauses)

On a globally minimum original-edge cycle factor of a 1-tough cofree
non-Hamiltonian host of order at least three:

* the factor has at least three cycles;
* exactly one factor block is a noncograph;
* every satellite relative to that unique core is not all-strict, hence
  every satellite row is saturated with a common proper canonical tight
  gate and cograph remainder.

The remaining manuscript group clauses (distinct-gate satellites
anticomplete, at least two groups, each whole group a cograph) are
recorded as OPEN and are not used as premises.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A globally minimum original-edge factor of a non-Hamiltonian 1-tough
cofree host of order at least three has at least three cycles: cardinal
one is Hamiltonian, and cardinal two is Hamiltonian by `thm:two-cycles`. -/
theorem three_le_card_of_min_nonHamiltonian
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (_hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian) :
    3 ≤ F.card := by
  have h1 : 1 ≤ F.card := F.one_le_card hord
  have hne1 : F.card ≠ 1 := by
    intro h
    exact hNonHam (F.isHamiltonian_of_card_one h)
  have hne2 : F.card ≠ 2 := by
    intro h
    exact hNonHam (two_cycle_factor_isHamiltonian hT hord hpat F h)
  omega

/-- At least one noncograph block: an all-cograph minimum factor is
Hamiltonian by the proved all-cograph closure. -/
theorem exists_noncograph_block_of_min
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian) :
    ∃ i : Fin F.card, ¬ IsCograph G (F.getCycle i).support := by
  by_contra hnone
  have hcog : ∀ i : Fin F.card, IsCograph G (F.getCycle i).support := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  obtain ⟨c, hc⟩ := all_cograph_hamiltonian hT hord hpat F hmin hcog
  exact hNonHam ((isHamiltonian_iff_exists_spanning_graphCycle hord).2 ⟨c, hc⟩)

/-- At most one noncograph block: two distinct noncograph factor cycles
admit an original cycle on their union (pair toughness of noncograph
blocks plus the induced two-cycle theorem), contradicting global
minimum-factor two-block replacement. -/
theorem not_two_noncograph_of_min
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {i j : Fin F.card} (hij : i ≠ j)
    (hH : ¬ IsCograph G (F.getCycle i).support)
    (hD : ¬ IsCograph G (F.getCycle j).support) :
    False := by
  obtain ⟨C, hC⟩ :=
    exists_original_cycle_of_two_noncograph_cycles
      (F.getCycle i) (F.getCycle j) (F.disjoint_getCycle hij) hpat hH hD
  exact not_exists_union_cycle_of_min F hmin hij C hC

/-- Exactly one noncograph block of a globally minimum original-edge
factor of a non-Hamiltonian 1-tough cofree host of order at least three. -/
theorem existsUnique_noncograph_block_of_min
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian) :
    ∃! i : Fin F.card, ¬ IsCograph G (F.getCycle i).support := by
  obtain ⟨i, hi⟩ := exists_noncograph_block_of_min hT hord hpat F hmin hNonHam
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hne
  exact not_two_noncograph_of_min hpat F hmin (Ne.symm hne) hi hj

theorem isCograph_of_ne_unique_core
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian)
    {i j : Fin F.card}
    (hi : ¬ IsCograph G (F.getCycle i).support)
    (hij : i ≠ j) :
    IsCograph G (F.getCycle j).support := by
  obtain ⟨k, hk, huniq⟩ :=
    existsUnique_noncograph_block_of_min hT hord hpat F hmin hNonHam
  have hik : i = k := huniq i hi
  by_contra hj
  have hjk : j = k := huniq j hj
  exact hij (hik.trans hjk.symm)

/-- Opening a satellite cycle and applying the Hamiltonian prefix theorem
produces a two-block original merge, which a globally minimum factor
forbids. Thus no satellite of a noncograph core can be all-strict. -/
theorem satellite_not_allstrict_of_min
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {i j : Fin F.card} (hij : i ≠ j)
    (_hH : ¬ IsCograph G (F.getCycle i).support)
    (hstrict : ∀ v ∈ (F.getCycle j).support,
        (rowProfile (G := G) (F.getCycle i).support v).Nonempty ∧
          IsCograph G
              ((F.getCycle i).support \
                rowProfile (G := G) (F.getCycle i).support v) ∧
            pathCoverNumber G
                ((F.getCycle i).support \
                  rowProfile (G := G) (F.getCycle i).support v) <
              (rowProfile (G := G) (F.getCycle i).support v).card) :
    False := by
  set cH := F.getCycle i
  set cD := F.getCycle j
  have hdisj : Disjoint cH.support cD.support := F.disjoint_getCycle hij
  obtain ⟨r, hr, _, _⟩ := exists_path_open_succ cD cD.start_mem_support
  have hdisj' : Disjoint cH.support r.support := by simpa [hr] using hdisj
  have hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        NoTightContainer G cH.support (rowProfile (G := G) cH.support v) := by
    intro v hv
    have hvD : v ∈ cD.support := by simpa [hr] using hv
    obtain ⟨hAne, _hcog, hlt⟩ := hstrict v hvD
    refine ⟨hAne, ?_⟩
    exact (noTightContainer_iff_strict_pathCover_of_host
      cH r hdisj' hv hAne hpat).2 hlt
  obtain ⟨γ, hγ⟩ :=
    exists_original_cycle_of_hamiltonian_prefix_of_global
      cH r hdisj' hrow hpat
  have hspan : γ.support = cH.support ∪ cD.support := by simpa [hr] using hγ
  exact not_exists_union_cycle_of_min F hmin hij γ hspan

/-- Satellite dichotomy specialised to a minimum factor: after excluding
all-strict rows by prefix merge, every satellite row is saturated and
shares one common proper canonical tight gate containing all attachments,
with cograph remainder. -/
theorem satellite_saturated_common_gate_of_min
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {i j : Fin F.card} (hij : i ≠ j)
    (hH : ¬ IsCograph G (F.getCycle i).support) :
    ∃ S : Finset V,
      Cograph.Tight (G := G) (F.getCycle i).support S ∧
        S ⊂ (F.getCycle i).support ∧
          (∀ v ∈ (F.getCycle j).support,
            (rowProfile (G := G) (F.getCycle i).support v).Nonempty ∧
              IsCograph G
                  ((F.getCycle i).support \
                    rowProfile (G := G) (F.getCycle i).support v) ∧
                Cograph.Saturated (G := G) (F.getCycle i).support
                  (rowProfile (G := G) (F.getCycle i).support v) ∧
                  Cograph.canonicalContainer (G := G)
                      (F.getCycle i).support
                      (rowProfile (G := G) (F.getCycle i).support v) =
                    S ∧
                    rowProfile (G := G) (F.getCycle i).support v ⊆ S) ∧
            (∀ x ∈ (F.getCycle i).support, ∀ y ∈ (F.getCycle j).support,
              G.Adj x y → x ∈ S) := by
  rcases pair_profile_dichotomy_of_min F hmin hpat hij hH with hstrict | hsat
  · exact (satellite_not_allstrict_of_min hpat F hmin hij hH hstrict).elim
  · exact hsat

/-- Consecutive satellite rows are incompatible in the already-checked
sense: if either is saturated then both are saturated and share the same
canonical container. -/
theorem satellite_adjacent_rows_incompatible_of_min
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {i j : Fin F.card} (hij : i ≠ j)
    (hH : ¬ IsCograph G (F.getCycle i).support)
    {u : V} (hu : u ∈ (F.getCycle j).support)
    (hSat :
      Cograph.Saturated (G := G) (F.getCycle i).support
          (rowProfile (G := G) (F.getCycle i).support u) ∨
        Cograph.Saturated (G := G) (F.getCycle i).support
          (rowProfile (G := G) (F.getCycle i).support
            ((F.getCycle j).succAt hu))) :
    Cograph.Saturated (G := G) (F.getCycle i).support
        (rowProfile (G := G) (F.getCycle i).support u) ∧
      Cograph.Saturated (G := G) (F.getCycle i).support
        (rowProfile (G := G) (F.getCycle i).support
          ((F.getCycle j).succAt hu)) ∧
      Cograph.canonicalContainer (G := G) (F.getCycle i).support
          (rowProfile (G := G) (F.getCycle i).support u) =
        Cograph.canonicalContainer (G := G) (F.getCycle i).support
          (rowProfile (G := G) (F.getCycle i).support
            ((F.getCycle j).succAt hu)) :=
  adjacent_rows_incompatible (F.getCycle i) (F.getCycle j)
    (F.disjoint_getCycle hij) hH hpat
    (fun C hC => not_exists_union_cycle_of_min F hmin hij C hC) hu hSat

/-- Core of manuscript `prop:normal-form`: at least three cycles, a unique
noncograph core, every other block a cograph satellite with a common
proper saturated gate into the core.

OPEN (not claimed): distinct-gate satellites are anticomplete via a
three-block original cycle; there are at least two groups via an original
full-host tight cut; each whole group is a cograph. -/
theorem min_factor_normal_form_core
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian) :
    3 ≤ F.card ∧
      ∃ i : Fin F.card,
        (¬ IsCograph G (F.getCycle i).support) ∧
          (∀ j : Fin F.card, j ≠ i →
            IsCograph G (F.getCycle j).support) ∧
          ∀ j : Fin F.card, j ≠ i →
            ∃ S : Finset V,
              Cograph.Tight (G := G) (F.getCycle i).support S ∧
                S ⊂ (F.getCycle i).support ∧
                  (∀ v ∈ (F.getCycle j).support,
                    (rowProfile (G := G) (F.getCycle i).support v).Nonempty ∧
                      IsCograph G
                          ((F.getCycle i).support \
                            rowProfile (G := G) (F.getCycle i).support v) ∧
                        Cograph.Saturated (G := G) (F.getCycle i).support
                          (rowProfile (G := G) (F.getCycle i).support v) ∧
                          Cograph.canonicalContainer (G := G)
                              (F.getCycle i).support
                              (rowProfile (G := G) (F.getCycle i).support v) =
                            S ∧
                            rowProfile (G := G) (F.getCycle i).support v ⊆ S) ∧
                    (∀ x ∈ (F.getCycle i).support,
                      ∀ y ∈ (F.getCycle j).support, G.Adj x y → x ∈ S) := by
  refine ⟨three_le_card_of_min_nonHamiltonian hT hord hpat F hmin hNonHam, ?_⟩
  obtain ⟨i, hi, huniq⟩ :=
    existsUnique_noncograph_block_of_min hT hord hpat F hmin hNonHam
  refine ⟨i, hi, ?_, ?_⟩
  · intro j hj
    by_contra hnc
    exact hj (huniq j hnc)
  · intro j hj
    exact satellite_saturated_common_gate_of_min hpat F hmin (Ne.symm hj) hi

end Nikoghosyan
