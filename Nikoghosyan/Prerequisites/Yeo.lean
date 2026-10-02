/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.YeoSplit

/-!
Cusp counts, the vertex-color strict order of FSCD 2025, and the edgeless
case of Yeo's unrestricted-color separator theorem.

Source: Di Guardia–Laurent–Tortora de Falco–Vaux Auclair, FSCD 2025,
Sections 2–3 and 6.1, specialized to ordinary undirected edge colors.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan
namespace Yeo

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [DecidableEq C]
variable {G : SimpleGraph V}

/-- Number of internal cusps of a walk: consecutive darts of equal color,
not wrapping around at a closed walk. -/
def internalCuspCount {u v : V} (w : G.Walk u v) (c : EdgeColoring G C) : ℕ :=
  ((w.darts.zip w.darts.tail).filter
    (fun p => c.dartColor p.1 = c.dartColor p.2)).length

/-- Closed-walk cusp count, including the wrap-around comparison of last
versus first dart. -/
def closedCuspCount {u : V} (w : G.Walk u u) (c : EdgeColoring G C) : ℕ :=
  internalCuspCount w c +
    if h : ¬ w.Nil then
      if c.dartColor (w.firstDart h) = c.dartColor (w.lastDart h) then 1 else 0
    else 0

lemma usedColors_eq_empty_of_not_adj (c : EdgeColoring G C)
    (h : ∀ u v : V, ¬ G.Adj u v) : c.usedColors = ∅ := by
  ext α
  constructor
  · intro hα
    rw [EdgeColoring.usedColors, mem_biUnion] at hα
    obtain ⟨u, _, hu⟩ := hα
    rw [mem_biUnion] at hu
    obtain ⟨v, _, hv⟩ := hu
    split_ifs at hv with hadj
    · exact (h u v hadj).elim
    · exact (notMem_empty α hv).elim
  · intro hα
    exact (notMem_empty α hα).elim

lemma not_adj_of_usedColors_eq_empty (c : EdgeColoring G C)
    (h : c.usedColors = ∅) {u v : V} : ¬ G.Adj u v := by
  intro hadj
  have : c.color hadj ∈ c.usedColors := c.mem_usedColors_color hadj
  simpa [h] using this

/-- An edgeless nonempty graph has a (vacuous) Yeo splitter at every vertex. -/
theorem exists_splittingVertex_of_edgeless (c : EdgeColoring G C) [Nonempty V]
    (h : ∀ u v : V, ¬ G.Adj u v) :
    ∃ v : V, SplittingVertex c v :=
  ⟨Classical.arbitrary V, SplittingVertex.of_not_adj c _
    (fun w => h _ w)⟩

/-- FSCD Definition 3: a simple open internally cusp-free path from `v` to `u`
whose starting color is not `α` and whose ending color is `β`. -/
def CuspFreeReach (c : EdgeColoring G C) (v u : V) (α β : C) : Prop :=
  ∃ (p : G.Walk v u) (_hp : p.IsPath) (hnil : ¬ p.Nil),
    internalCuspCount p c = 0 ∧
      c.dartColor (p.firstDart hnil) ≠ α ∧
        c.dartColor (p.lastDart hnil) = β

/-- FSCD Definition 3, strict form `◁`: a `CuspFreeReach` witness `p` such
that no further cusp-free `↱`-step from `u` lands on `p`. -/
def StrictCuspFreeReach (c : EdgeColoring G C) (v u : V) (α β : C) : Prop :=
  ∃ (p : G.Walk v u) (_hp : p.IsPath) (hnil : ¬ p.Nil),
    internalCuspCount p c = 0 ∧
      c.dartColor (p.firstDart hnil) ≠ α ∧
        c.dartColor (p.lastDart hnil) = β ∧
          ∀ {w : V} (q : G.Walk u w) (_hq : q.IsPath) (hqnil : ¬ q.Nil),
            internalCuspCount q c = 0 →
              c.dartColor (q.firstDart hqnil) ≠ β →
                w ∉ p.support

lemma CuspFreeReach.of_strict {c : EdgeColoring G C} {v u : V} {α β : C}
    (h : StrictCuspFreeReach c v u α β) : CuspFreeReach c v u α β := by
  obtain ⟨p, hp, hnil, hinter, hstart, hend, _⟩ := h
  exact ⟨p, hp, hnil, hinter, hstart, hend⟩

lemma isPath_nil_of_eq {u : V} {p : G.Walk u u} (hp : p.IsPath) : p.Nil :=
  (Walk.isPath_iff_nil).1 hp

lemma not_CuspFreeReach_self (c : EdgeColoring G C) (v : V) (α β : C) :
    ¬ CuspFreeReach c v v α β := by
  intro h
  obtain ⟨p, hp, hnil, _⟩ := h
  exact hnil (isPath_nil_of_eq hp)

lemma not_StrictCuspFreeReach_self (c : EdgeColoring G C) (v : V) (α β : C) :
    ¬ StrictCuspFreeReach c v v α β := by
  intro h
  exact not_CuspFreeReach_self c v α β (CuspFreeReach.of_strict h)

/-- A used vertex-color pair. Finite because `V` is finite and only colors
actually occurring on `G` are kept. No `Fintype C` is required. -/
abbrev UsedPair (c : EdgeColoring G C) :=
  V × { α : C // α ∈ c.usedColors }

noncomputable instance (c : EdgeColoring G C) : Fintype (UsedPair c) :=
  inferInstance

lemma UsedPair.nonempty (c : EdgeColoring G C) [Nonempty V]
    (h : c.usedColors.Nonempty) : Nonempty (UsedPair c) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨(Classical.arbitrary V, ⟨α, hα⟩)⟩

/-- The relation `◁` on used pairs. -/
def usedLt (c : EdgeColoring G C) : UsedPair c → UsedPair c → Prop :=
  fun p q => StrictCuspFreeReach c p.1 q.1 p.2.1 q.2.1

lemma usedLt_irrefl (c : EdgeColoring G C) (p : UsedPair c) :
    ¬ usedLt c p p :=
  not_StrictCuspFreeReach_self c p.1 p.2.1 p.2.1

/-- Isolated vertices (and the edgeless graph) are splitters; this is the
base of `yeo_separator` when no color actually occurs. -/
theorem yeo_separator_of_usedColors_empty (c : EdgeColoring G C) [Nonempty V]
    (h : c.usedColors = ∅) :
    ∃ v : V, SplittingVertex c v :=
  exists_splittingVertex_of_edgeless c
    (fun u v => not_adj_of_usedColors_eq_empty (u := u) (v := v) c h)

lemma IsCycle.length_le_card {u : V} {w : G.Walk u u} (h : w.IsCycle) :
    w.length ≤ Fintype.card V := by
  have h3 : 3 ≤ w.length := h.three_le_length
  let f : Fin w.length → V := fun i => w.getVert i.1
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hi : i.1 ≤ w.length - 1 := Nat.le_pred_of_lt i.2
    have hj : j.1 ≤ w.length - 1 := Nat.le_pred_of_lt j.2
    exact h.getVert_injOn' hi hj hij
  simpa using Fintype.card_le_of_injective f hinj

/-- On at most two vertices there is no genuine cycle, so every vertex is a
Yeo splitter. -/
theorem yeo_separator_of_card_le_two (c : EdgeColoring G C) [Nonempty V]
    (hV : Fintype.card V ≤ 2) :
    ∃ v : V, SplittingVertex c v := by
  refine ⟨Classical.arbitrary V, ?_⟩
  rw [splittingVertex_iff_cycleSplittingVertex]
  intro u w hcyc _hv
  have : 3 ≤ Fintype.card V :=
    le_trans hcyc.three_le_length (IsCycle.length_le_card hcyc)
  omega

end Yeo
end Nikoghosyan
