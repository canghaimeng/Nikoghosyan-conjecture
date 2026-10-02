import Nikoghosyan.PathCover

/-!
Spanning original-edge cycle factors of order at least three, the
single-cycle Hamiltonicity criterion, and existence of a minimum-cycle
factor from any factor.
-/

set_option linter.unusedSectionVars false

open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A simple original-edge cycle. `Walk.IsCycle` already forces length at
least three in a simple graph. -/
structure GraphCycle where
  start : V
  walk : G.Walk start start
  isCycle : walk.IsCycle

namespace GraphCycle

variable {G}

def support (c : GraphCycle G) : Finset V :=
  c.walk.support.toFinset

lemma three_le_length (c : GraphCycle G) : 3 ≤ c.walk.length :=
  c.isCycle.three_le_length

lemma start_mem_support (c : GraphCycle G) : c.start ∈ c.support := by
  simp [support, Walk.start_mem_support]

lemma support_nonempty (c : GraphCycle G) : c.support.Nonempty :=
  ⟨c.start, c.start_mem_support⟩

lemma card_support (c : GraphCycle G) : c.support.card = c.walk.length := by
  have htail := c.isCycle.support_nodup
  have hstart : c.start ∈ c.walk.support.tail :=
    c.walk.end_mem_tail_support c.isCycle.not_nil
  cases hcwalk : c.walk with
  | nil =>
    exact (c.isCycle.not_nil (by simp [hcwalk])).elim
  | cons h q =>
    have hs : c.walk.support = c.start :: q.support := by
      simp [hcwalk]
    have hlen : q.support.length = c.walk.length := by
      simp [hcwalk, Walk.length_support, Walk.length_cons]
    have htail' : q.support.Nodup := by
      simpa [hcwalk] using htail
    have hstart' : c.start ∈ q.support := by
      simpa [hcwalk] using hstart
    have heq : c.walk.support.toFinset = q.support.toFinset := by
      simp [hs, insert_eq_of_mem (List.mem_toFinset.2 hstart')]
    have hcard : q.support.toFinset.card = q.support.length :=
      List.toFinset_card_of_nodup htail'
    simp [support, heq, hcard, hlen, hcwalk]

lemma three_le_card_support (c : GraphCycle G) : 3 ≤ c.support.card := by
  simpa [c.card_support] using c.three_le_length

/-- Reverse a cycle, preserving original edges. -/
def reverse (c : GraphCycle G) : GraphCycle G where
  start := c.start
  walk := c.walk.reverse
  isCycle := c.isCycle.reverse

@[simp]
lemma support_reverse (c : GraphCycle G) : c.reverse.support = c.support := by
  simp [reverse, support, Walk.support_reverse]

end GraphCycle

/-- A spanning partition of `G` into simple original-edge cycles of order
at least three. This is a 2-factor presented as its cycle list. -/
structure CycleFactor where
  cycles : List (GraphCycle G)
  disjoint : cycles.Pairwise fun c d => Disjoint c.support d.support
  mem_iff : ∀ x : V, ∃ c ∈ cycles, x ∈ c.support

namespace CycleFactor

variable {G}

def card (F : CycleFactor G) : ℕ :=
  F.cycles.length

/-- A one-cycle factor is a genuine spanning original-edge cycle of order
at least three. Mathlib's `IsHamiltonian` singleton convention is not used
here. -/
lemma exists_hamiltonian_cycle_of_card_one (F : CycleFactor G) (hF : F.card = 1) :
    ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.support.toFinset = univ ∧
      3 ≤ Fintype.card V := by
  cases hcs : F.cycles with
  | nil =>
    simp [card, hcs] at hF
  | cons c rest =>
    have hrest : rest = [] := by
      simp [card, hcs] at hF
      cases rest with
      | nil => rfl
      | cons _ _ => simp at hF
    subst hrest
    have hmem : ∀ x : V, x ∈ c.support := by
      intro x
      obtain ⟨d, hd, hx⟩ := F.mem_iff x
      have : d = c := by
        have : d ∈ [c] := by simpa [hcs] using hd
        simpa using this
      simpa [this] using hx
    have hsupp : c.support = univ := eq_univ_of_forall hmem
    refine ⟨c.start, c.walk, c.isCycle, hsupp, ?_⟩
    have := c.three_le_card_support
    simpa [hsupp] using this

/-- From any cycle factor, a factor of globally minimum cycle count exists. -/
lemma exists_min_of_exists (F0 : CycleFactor G) :
    ∃ F : CycleFactor G,
      F.card ≤ F0.card ∧ ∀ F' : CycleFactor G, F.card ≤ F'.card := by
  let S : Set ℕ := {n | ∃ F : CycleFactor G, F.card = n}
  have hne : S.Nonempty := ⟨F0.card, F0, rfl⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  obtain ⟨F, hF⟩ := hmem
  refine ⟨F, ?_, ?_⟩
  · exact hF ▸ Nat.sInf_le (s := S) ⟨F0, rfl⟩
  · intro F'
    exact hF ▸ Nat.sInf_le (s := S) ⟨F', rfl⟩

end CycleFactor

end Nikoghosyan
