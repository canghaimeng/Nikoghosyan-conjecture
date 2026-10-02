/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Authors: Nikoghosyan formalization team
-/
import Nikoghosyan.HamiltonianPrefix
import Nikoghosyan.Cograph.ProtectedInduction

/-!
Compose the proved protected sufficient theorem with the previously checked
original-edge insertion and actual prefix induction. No insertion callback
remains on the exported caller-facing theorems.
-/

namespace Nikoghosyan

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem profileEndedSpanningPath_proved : ProfileEndedSpanningPath G := by
  intro c x hx hJ hK
  have hAne := rowProfile_nonempty_of_oneToughOn_cycle c hx hJ
  have hstrict := strict_pathCover_of_oneToughOn_cycle c hx hJ hK
  obtain ⟨p, hp, hs, hf, _hne, _hP⟩ :=
    Cograph.exists_protectedAt_of_strict_of_canonical c rfl
      (rowProfile_subset (G := G) c.support x) hAne hK hstrict
  exact ⟨p, hp, hs, hf⟩

theorem exists_original_cycle_of_vertex_insertion
    (c : GraphCycle G) {x : V} (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support))
    (hK : IsCograph G (c.support \ rowProfile (G := G) c.support x)) :
    ∃ γ : GraphCycle G,
      γ.support = insert x c.support ∧ 3 ≤ γ.support.card :=
  exists_inserted_cycle_of_profileEndedSpanningPath profileEndedSpanningPath_proved
    c hx hJ hK

theorem exists_original_cycle_of_hamiltonian_prefix
    (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v))
    (hOn : NoInducedP4UnionP1On G (c.support ∪ r.support)) :
    ∃ γ : GraphCycle G, γ.support = c.support ∪ r.support :=
  exists_cycle_union_of_profileEndedSpanningPath profileEndedSpanningPath_proved
    c r hdisj hrow hOn

theorem exists_original_cycle_of_hamiltonian_prefix_of_global
    (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v))
    (hpat : NoInducedP4UnionP1 G) :
    ∃ γ : GraphCycle G, γ.support = c.support ∪ r.support :=
  exists_cycle_union_of_profileEndedSpanningPath_of_global
    profileEndedSpanningPath_proved c r hdisj hrow hpat

theorem exists_original_univ_cycle_of_deleted_vertex_cycle
    (hT : OneTough G) (hpat : NoInducedP4UnionP1 G)
    (c : GraphCycle G) (x : V) (hc : c.support = univ.erase x) :
    ∃ γ : GraphCycle G, γ.support = univ := by
  have hx : x ∉ c.support := by simp [hc]
  have hins : insert x c.support = univ := by
    rw [hc]
    exact insert_erase (mem_univ x)
  have hJ : OneToughOn G (insert x c.support) := by
    rw [hins]
    exact OneToughOn.univ_iff.2 hT
  have hK : IsCograph G (c.support \ rowProfile (G := G) c.support x) :=
    isCograph_current_remainder c hx
      (NoInducedP4UnionP1On.of_global hpat (insert x c.support))
  obtain ⟨γ, hγ, _⟩ := exists_original_cycle_of_vertex_insertion c hx hJ hK
  exact ⟨γ, hγ.trans hins⟩

end Nikoghosyan
