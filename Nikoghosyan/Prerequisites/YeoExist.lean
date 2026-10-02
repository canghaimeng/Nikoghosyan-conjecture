/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.YeoOrder

/-!
Cusp-minimization ingredients toward unrestricted-color `yeo_separator`.

This module begins FSCD 2025 Lemma 6: Fact 1 (orientation of a
no-cusp-at-v cycle) and the first-reentry vertex of a detour. The two-cycle
construction and closed-count comparison remain OPEN; `yeo_separator`
remains OPEN.

Source: Di Guardia–Laurent–Tortora de Falco–Vaux Auclair, FSCD 2025,
Lemma 6 / Fact 1.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Function SimpleGraph

namespace Nikoghosyan
namespace Yeo

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [DecidableEq C]
variable {G : SimpleGraph V}

/-- FSCD Fact 1: a closed walk with no wrap-around cusp at its source has,
for every color `α`, either starting color ≠ `α` or the reverse starting
color ≠ `α`. -/
theorem startColor_ne_or_reverse {u : V} (ω : G.Walk u u) (c : EdgeColoring G C)
    (hω : ¬ ω.Nil)
    (hnocusp : c.dartColor (ω.firstDart hω) ≠ c.dartColor (ω.lastDart hω))
    (α : C) :
    c.dartColor (ω.firstDart hω) ≠ α ∨
      c.dartColor (ω.reverse.firstDart (not_nil_reverse hω)) ≠ α := by
  by_contra h
  push Not at h
  have hfirst : c.dartColor (ω.firstDart hω) = α := h.1
  have hrev : c.dartColor (ω.reverse.firstDart (not_nil_reverse hω)) = α := h.2
  rw [firstDart_reverse hω (not_nil_reverse hω), EdgeColoring.dartColor_symm] at hrev
  exact hnocusp (hfirst.trans hrev.symm)

lemma end_mem_support_tail {u v : V} {p : G.Walk u v} (_hp : ¬ p.Nil)
    (hne : u ≠ v) : v ∈ p.support.tail := by
  have : v ∈ p.support := Walk.end_mem_support p
  rw [Walk.mem_support_iff] at this
  exact this.resolve_left hne.symm

/-- First reentry vertex of a nonempty open path into a host list `S`:
the `takeUntil` prefix ending at the first tail vertex in `S` is nonempty. -/
theorem exists_first_reentry_vertex {u w : V} {q : G.Walk u w}
    (hq : q.IsPath) (hqnil : ¬ q.Nil) (hne : u ≠ w)
    {S : List V} (hw : w ∈ S) :
    ∃ (x : V) (hx : x ∈ q.support),
      x ∈ S ∧ ¬ (q.takeUntil x hx).Nil ∧ x ∈ q.support.tail := by
  have hwtail : w ∈ q.support.tail := end_mem_support_tail hqnil hne
  let p : V → Bool := fun a => decide (a ∈ S)
  have hi : q.support.tail.findIdx p < q.support.tail.length := by
    refine List.findIdx_lt_length_of_exists ?_
    exact ⟨w, hwtail, by simp [p, hw]⟩
  set x := q.support.tail[q.support.tail.findIdx p]
  have hxtail : x ∈ q.support.tail := List.getElem_mem _
  have hxsup : x ∈ q.support := List.mem_of_mem_tail hxtail
  have hxS : x ∈ S := by
    have hget := List.findIdx_getElem (xs := q.support.tail) (w := hi)
    simpa [x, p] using hget
  exact ⟨x, hxsup, hxS, not_nil_takeUntil_of_mem_tail hq hxtail, hxtail⟩

end Yeo
end Nikoghosyan


