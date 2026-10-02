import Mathlib.Order.Lattice.Nat
import Nikoghosyan.Paths

/-!
Path covers of an induced original vertex set, the minimum cover number,
and eligibility / ineligibility.
-/

set_option linter.unusedSectionVars false

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A path cover of an original induced vertex set: nonempty simple original
paths, pairwise disjoint supports, union exactly `U`. Singleton paths are
allowed; the empty set has the empty cover. -/
structure PathCover (U : Finset V) where
  paths : List (GraphPath G)
  disjoint : paths.Pairwise fun p q => Disjoint p.support q.support
  mem_iff : ∀ x, x ∈ U ↔ ∃ p ∈ paths, x ∈ p.support

namespace PathCover

variable {G}

/-- Number of paths in the cover. -/
def card {U : Finset V} (pc : PathCover G U) : ℕ :=
  pc.paths.length

lemma support_subset {U : Finset V} (pc : PathCover G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) : p.support ⊆ U := by
  intro x hx
  exact (pc.mem_iff x).2 ⟨p, hp, hx⟩

/-- The singleton cover of `U`. -/
noncomputable def singletons (U : Finset V) : PathCover G U where
  paths := U.toList.map GraphPath.singleton
  disjoint := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ U.nodup_toList
    intro a b hne
    change Disjoint {a} {b}
    rw [disjoint_iff_inter_eq_empty]
    simp [hne]
  mem_iff := by
    intro x
    constructor
    · intro hx
      refine ⟨GraphPath.singleton x, ?_, ?_⟩
      · exact List.mem_map.2 ⟨x, Finset.mem_toList.2 hx, rfl⟩
      · simp
    · intro ⟨p, hp, hx⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp
      have : x = y := by simpa using hx
      subst this
      exact Finset.mem_toList.1 hy

@[simp]
lemma singletons_card (U : Finset V) :
    (singletons (G := G) U).card = U.card := by
  simp [singletons, card]

lemma exists_singleton_cover (U : Finset V) :
    ∃ pc : PathCover G U, pc.card = U.card :=
  ⟨singletons U, singletons_card U⟩

end PathCover

/-- Minimum path-cover number `p(U)` of the induced subgraph on `U`.
This is defined extensionally as the infimum of cover cardinalities.
The empty set has cover number zero. -/
noncomputable def pathCoverNumber (U : Finset V) : ℕ :=
  sInf {n | ∃ pc : PathCover G U, pc.card = n}

lemma pathCoverNumber_mem (U : Finset V) :
    pathCoverNumber G U ∈ {n | ∃ pc : PathCover G U, pc.card = n} := by
  refine Nat.sInf_mem ?_
  exact ⟨U.card, PathCover.exists_singleton_cover (G := G) U⟩

lemma exists_min_pathCover (U : Finset V) :
    ∃ pc : PathCover G U, pc.card = pathCoverNumber G U :=
  pathCoverNumber_mem (G := G) U

lemma pathCoverNumber_le {U : Finset V} (pc : PathCover G U) :
    pathCoverNumber G U ≤ pc.card :=
  Nat.sInf_le ⟨pc, rfl⟩

lemma pathCoverNumber_le_card (U : Finset V) :
    pathCoverNumber G U ≤ U.card := by
  simpa using pathCoverNumber_le (G := G) (PathCover.singletons (G := G) U)

lemma pathCoverNumber_empty : pathCoverNumber G ∅ = 0 := by
  have hle := pathCoverNumber_le_card (G := G) ∅
  simpa using hle

/-- A vertex is eligible in `U` if it is an endpoint of some path in some
minimum path cover of `U`. Eligibility does not prescribe a simultaneous
endpoint tuple. -/
def Eligible (U : Finset V) (x : V) : Prop :=
  ∃ pc : PathCover G U, pc.card = pathCoverNumber G U ∧
    ∃ p ∈ pc.paths, x = p.start ∨ x = p.finish

/-- Eligible vertex set `E(U)`. -/
noncomputable def eligibleSet (U : Finset V) : Finset V :=
  U.filter (Eligible G U)

/-- Ineligible vertex set `F(U) = U \ E(U)`. -/
noncomputable def ineligibleSet (U : Finset V) : Finset V :=
  U.filter fun x => ¬ Eligible G U x

lemma eligibleSet_union_ineligibleSet (U : Finset V) :
    eligibleSet G U ∪ ineligibleSet G U = U := by
  ext x
  simp [eligibleSet, ineligibleSet]
  tauto

lemma mem_eligibleSet_iff {U : Finset V} {x : V} :
    x ∈ eligibleSet G U ↔ x ∈ U ∧ Eligible G U x := by
  simp [eligibleSet]

lemma mem_ineligibleSet_iff {U : Finset V} {x : V} :
    x ∈ ineligibleSet G U ↔ x ∈ U ∧ ¬ Eligible G U x := by
  simp [ineligibleSet]

lemma Eligible.mem {U : Finset V} {x : V} (h : Eligible G U x) : x ∈ U := by
  obtain ⟨pc, _, p, hp, hx⟩ := h
  have : x ∈ p.support := by
    rcases hx with rfl | rfl
    · exact p.start_mem_support
    · exact p.finish_mem_support
  exact (pc.mem_iff x).2 ⟨p, hp, this⟩

lemma eligibleSet_subset (U : Finset V) : eligibleSet G U ⊆ U :=
  filter_subset _ _

lemma ineligibleSet_subset (U : Finset V) : ineligibleSet G U ⊆ U :=
  filter_subset _ _

lemma disjoint_eligibleSet_ineligibleSet (U : Finset V) :
    Disjoint (eligibleSet G U) (ineligibleSet G U) := by
  rw [disjoint_iff_inter_eq_empty]
  ext x
  simp [eligibleSet, ineligibleSet]
  tauto

end Nikoghosyan
