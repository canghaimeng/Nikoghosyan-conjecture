/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.PathIncidences

/-!
Actual bounded-path boundary return and the corresponding prefix rotation.

For a simple original-edge path `p` and a vertex set `U0`, `boundaryEdges`
is the finset of *actual walk edges* of `p` with exactly one end in `U0`.
If `p.start ∈ U0` and that finset has cardinality at least two, there is a
strict index `i < p.walk.length` with `getVert i ∉ U0` and
`getVert (i+1) ∈ U0`. The corresponding `PrefixEdgeFactor` is derived from
`exists_factorAtIndex`. The tail is outside `U0`, hence distinct from the
start, and the strict index makes it distinct from the finish. No entering
dart is assumed on an arbitrary path.

The membership word along indices `0, …, length` starts true. With no
false→true transition, after the first true→false transition the word
never returns, so there is at most one crossing. `IsPath` implies
`IsTrail`, so distinct undirected walk edges have distinct occurrence
indices, giving the actual boundary-edge / crossing-index correspondence.
Only indices `0, …, length` are used; `getVert` beyond length is capped.

The rotation package takes an actual entering factor whose tail lies in a
designated original `A`, whose head lies in `X`, and whose old start `y`
lies in `Y`, together with an original complete-join edge `y—x`. The
rotated path starts at that `A`-vertex, keeps the old finish and support,
preserves `ProtectedAt` at the original `A`, loses exactly the selected
boundary edge `a—x`, and gains an internal-`U0` edge `y—x`. The hypothesis
`2 ≤ boundaryEdges.card` is a legitimate operation input; G2 must derive
it from the fixed-cycle internal-2 / endpoint-1 bridge. This module does
not close `prof:thm:protected` or `thm:main`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

/-- An undirected edge has exactly one end in `U0`. -/
def endsStraddle (e : Sym2 V) (U0 : Finset V) : Prop :=
  (∃ x ∈ e, x ∈ U0) ∧ (∃ y ∈ e, y ∉ U0)

lemma endsStraddle_iff {a b : V} {U0 : Finset V} :
    endsStraddle s(a, b) U0 ↔ ((a ∈ U0) ≠ (b ∈ U0)) := by
  constructor
  · rintro ⟨⟨x, hx, hxU⟩, ⟨y, hy, hyU⟩⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · rcases Sym2.mem_iff.mp hy with rfl | rfl
      · exact (hyU hxU).elim
      · intro heq
        exact hyU ((iff_of_eq heq).mp hxU)
    · rcases Sym2.mem_iff.mp hy with rfl | rfl
      · intro heq
        exact hyU ((iff_of_eq heq).mpr hxU)
      · exact (hyU hxU).elim
  · intro hne
    by_cases ha : a ∈ U0
    · refine ⟨⟨a, by simp, ha⟩, ⟨b, by simp, ?_⟩⟩
      intro hb
      exact hne (propext ⟨fun _ => hb, fun _ => ha⟩)
    · have hb : b ∈ U0 := by
        by_contra hb
        exact hne (propext ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩)
      exact ⟨⟨b, by simp, hb⟩, ⟨a, by simp, ha⟩⟩

lemma endsStraddle_of_outside_inside {a b : V} {U0 : Finset V}
    (ha : a ∉ U0) (hb : b ∈ U0) : endsStraddle s(a, b) U0 :=
  endsStraddle_iff.2 (fun heq => ha ((iff_of_eq heq).mpr hb))

lemma not_endsStraddle_of_both {a b : V} {U0 : Finset V}
    (ha : a ∈ U0) (hb : b ∈ U0) : ¬ endsStraddle s(a, b) U0 := by
  intro h
  exact (endsStraddle_iff.1 h) (propext ⟨fun _ => hb, fun _ => ha⟩)

lemma not_endsStraddle_of_neither {a b : V} {U0 : Finset V}
    (ha : a ∉ U0) (hb : b ∉ U0) : ¬ endsStraddle s(a, b) U0 := by
  intro h
  exact (endsStraddle_iff.1 h)
    (propext ⟨fun h' => (ha h').elim, fun h' => (hb h').elim⟩)

/-- Actual walk edges of `p` with exactly one end in `U0`. These are
edges of the path, not all edges of `G`. -/
noncomputable def boundaryEdges (p : GraphPath G) (U0 : Finset V) : Finset (Sym2 V) :=
  p.edges.filter fun e => endsStraddle e U0

lemma mem_boundaryEdges_iff {p : GraphPath G} {U0 : Finset V} {e : Sym2 V} :
    e ∈ p.boundaryEdges U0 ↔ e ∈ p.edges ∧ endsStraddle e U0 := by
  simp [boundaryEdges]

lemma boundaryEdges_subset_edges (p : GraphPath G) (U0 : Finset V) :
    p.boundaryEdges U0 ⊆ p.edges :=
  filter_subset _ _

/-- Crossing indices in `0, …, length-1`: consecutive vertices straddle
`U0`. Capped indices `≥ length` are excluded. -/
noncomputable def crossingIndexSet (p : GraphPath G) (U0 : Finset V) : Finset ℕ :=
  (Finset.range p.walk.length).filter fun i =>
    (p.walk.getVert i ∈ U0) ≠ (p.walk.getVert (i + 1) ∈ U0)

lemma mem_crossingIndexSet_iff {p : GraphPath G} {U0 : Finset V} {i : ℕ} :
    i ∈ p.crossingIndexSet U0 ↔
      i < p.walk.length ∧
        ((p.walk.getVert i ∈ U0) ≠ (p.walk.getVert (i + 1) ∈ U0)) := by
  simp [crossingIndexSet, mem_range]

lemma crossingEdge_mem_edges (p : GraphPath G) {i : ℕ}
    (hi : i < p.walk.length) :
    s(p.walk.getVert i, p.walk.getVert (i + 1)) ∈ p.edges := by
  have hiE : i < p.walk.edges.length := by simpa [Walk.length_edges] using hi
  exact mem_edges_iff.2 (List.mem_iff_getElem.2 ⟨i, hiE, Walk.getElem_edges hiE⟩)

lemma injOn_crossingEdge (p : GraphPath G) (U0 : Finset V) :
    Set.InjOn (fun i => s(p.walk.getVert i, p.walk.getVert (i + 1)))
      (p.crossingIndexSet U0) := by
  intro i hi j hj heq
  have hiL : i < p.walk.length := (mem_crossingIndexSet_iff.1 hi).1
  have hjL : j < p.walk.length := (mem_crossingIndexSet_iff.1 hj).1
  have hiE : i < p.walk.edges.length := by simpa [Walk.length_edges] using hiL
  have hjE : j < p.walk.edges.length := by simpa [Walk.length_edges] using hjL
  have hnod := p.isPath.isTrail.edges_nodup
  have hidx : p.walk.edges[i] = p.walk.edges[j] := by
    rw [Walk.getElem_edges (p := p.walk) hiE, Walk.getElem_edges (p := p.walk) hjE]
    exact heq
  have hinj := List.nodup_iff_injective_getElem.1 hnod
  have hij : (⟨i, hiE⟩ : Fin p.walk.edges.length) = ⟨j, hjE⟩ :=
    hinj hidx
  exact Fin.val_eq_of_eq hij

lemma image_crossingIndexSet (p : GraphPath G) (U0 : Finset V) :
    (p.crossingIndexSet U0).image
        (fun i => s(p.walk.getVert i, p.walk.getVert (i + 1))) =
      p.boundaryEdges U0 := by
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he
    obtain ⟨hiL, hxor⟩ := mem_crossingIndexSet_iff.1 hi
    exact mem_boundaryEdges_iff.2
      ⟨p.crossingEdge_mem_edges hiL, endsStraddle_iff.2 hxor⟩
  · intro he
    obtain ⟨heE, hstr⟩ := mem_boundaryEdges_iff.1 he
    obtain ⟨i, hiE, hie⟩ := List.mem_iff_getElem.1 (mem_edges_iff.1 heE)
    have hiL : i < p.walk.length := by simpa [Walk.length_edges] using hiE
    have hpair : e = s(p.walk.getVert i, p.walk.getVert (i + 1)) := by
      rw [← Walk.getElem_edges hiE, hie]
    have hxor : (p.walk.getVert i ∈ U0) ≠ (p.walk.getVert (i + 1) ∈ U0) := by
      have : endsStraddle s(p.walk.getVert i, p.walk.getVert (i + 1)) U0 := by
        simpa [hpair] using hstr
      exact endsStraddle_iff.1 this
    refine mem_image.2 ⟨i, mem_crossingIndexSet_iff.2 ⟨hiL, hxor⟩, hpair.symm⟩

/-- Crossing indices are in bijection with actual boundary walk edges. -/
theorem card_crossingIndexSet (p : GraphPath G) (U0 : Finset V) :
    (p.crossingIndexSet U0).card = (p.boundaryEdges U0).card := by
  rw [← p.image_crossingIndexSet U0]
  exact (Finset.card_image_of_injOn (p.injOn_crossingEdge U0)).symm

lemma no_entering_imp_succ_not_mem {p : GraphPath G} {U0 : Finset V}
    (hno : ∀ i < p.walk.length,
      ¬ (p.walk.getVert i ∉ U0 ∧ p.walk.getVert (i + 1) ∈ U0))
    {j : ℕ} (hj : j < p.walk.length) (hj0 : p.walk.getVert j ∉ U0) :
    p.walk.getVert (j + 1) ∉ U0 := by
  intro hj1
  exact hno j hj ⟨hj0, hj1⟩

/-- After a true→false transition, the membership word never returns if
there is no false→true transition. -/
lemma getVert_not_mem_U0_of_ge {p : GraphPath G} {U0 : Finset V} {i k : ℕ}
    (hno : ∀ j < p.walk.length,
      ¬ (p.walk.getVert j ∉ U0 ∧ p.walk.getVert (j + 1) ∈ U0))
    (_hi : i < p.walk.length) (hnot : p.walk.getVert (i + 1) ∉ U0)
    (hik : i + 1 ≤ k) (hk : k ≤ p.walk.length) :
    p.walk.getVert k ∉ U0 := by
  have hshift : ∀ t, i + 1 + t ≤ p.walk.length →
      p.walk.getVert (i + 1 + t) ∉ U0 := by
    intro t ht
    induction t with
    | zero => exact hnot
    | succ t ih =>
      have hlt : i + 1 + t < p.walk.length := by omega
      exact no_entering_imp_succ_not_mem (p := p) (U0 := U0) hno hlt
        (ih (by omega))
  have ht : k = i + 1 + (k - (i + 1)) := by omega
  rw [ht]
  exact hshift (k - (i + 1)) (by omega)

lemma crossing_subset_leaving_of_no_entering {p : GraphPath G} {U0 : Finset V}
    (hno : ∀ i < p.walk.length,
      ¬ (p.walk.getVert i ∉ U0 ∧ p.walk.getVert (i + 1) ∈ U0))
    {i : ℕ} (hi : i ∈ p.crossingIndexSet U0) :
    p.walk.getVert i ∈ U0 ∧ p.walk.getVert (i + 1) ∉ U0 := by
  obtain ⟨hiL, hxor⟩ := mem_crossingIndexSet_iff.1 hi
  by_cases hin : p.walk.getVert i ∈ U0
  · refine ⟨hin, ?_⟩
    intro hsucc
    exact hxor (propext ⟨fun _ => hsucc, fun _ => hin⟩)
  · have hsucc : p.walk.getVert (i + 1) ∉ U0 :=
      no_entering_imp_succ_not_mem (p := p) (U0 := U0) hno hiL hin
    exact (hxor (propext ⟨fun h => (hin h).elim, fun h => (hsucc h).elim⟩)).elim

/-- With no entering dart, a path that starts in `U0` has at most one
crossing index. -/
theorem card_crossingIndexSet_le_one_of_no_entering (p : GraphPath G)
    (U0 : Finset V) (_hs : p.start ∈ U0)
    (hno : ∀ i < p.walk.length,
      ¬ (p.walk.getVert i ∉ U0 ∧ p.walk.getVert (i + 1) ∈ U0)) :
    (p.crossingIndexSet U0).card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  intro i hi j hj
  obtain ⟨hiL, _⟩ := mem_crossingIndexSet_iff.1 hi
  obtain ⟨hjL, _⟩ := mem_crossingIndexSet_iff.1 hj
  obtain ⟨hiIn, hiOut⟩ :=
    crossing_subset_leaving_of_no_entering (p := p) (U0 := U0) hno hi
  obtain ⟨hjIn, _⟩ :=
    crossing_subset_leaving_of_no_entering (p := p) (U0 := U0) hno hj
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · have : p.walk.getVert j ∉ U0 :=
      getVert_not_mem_U0_of_ge (p := p) (U0 := U0) hno hiL hiOut
        (by omega) (le_of_lt hjL)
    exact (this hjIn).elim
  · rfl
  · have : p.walk.getVert i ∉ U0 :=
      getVert_not_mem_U0_of_ge (p := p) (U0 := U0) hno hjL
        (crossing_subset_leaving_of_no_entering (p := p) (U0 := U0) hno hj).2
        (by omega) (le_of_lt hiL)
    exact (this hiIn).elim

/-- If `p` starts in `U0` and has at least two actual boundary walk edges,
an entering dart exists. -/
theorem exists_enteringIndex (p : GraphPath G) (U0 : Finset V)
    (hs : p.start ∈ U0) (h2 : 2 ≤ (p.boundaryEdges U0).card) :
    ∃ i, i < p.walk.length ∧
      p.walk.getVert i ∉ U0 ∧ p.walk.getVert (i + 1) ∈ U0 := by
  by_contra h
  have hno : ∀ i < p.walk.length,
      ¬ (p.walk.getVert i ∉ U0 ∧ p.walk.getVert (i + 1) ∈ U0) := by
    intro i hi ⟨h0, h1⟩
    exact h ⟨i, hi, h0, h1⟩
  have hle : (p.boundaryEdges U0).card ≤ 1 := by
    simpa [p.card_crossingIndexSet U0] using
      p.card_crossingIndexSet_le_one_of_no_entering U0 hs hno
  omega

lemma entering_ne_start (p : GraphPath G) {U0 : Finset V} {i : ℕ}
    (hs : p.start ∈ U0) (hi0 : p.walk.getVert i ∉ U0) :
    p.walk.getVert i ≠ p.start := by
  intro heq
  rw [heq] at hi0
  exact hi0 hs

lemma entering_ne_finish (p : GraphPath G) {i : ℕ}
    (hi : i < p.walk.length) :
    p.walk.getVert i ≠ p.finish :=
  p.getVert_ne_finish_of_lt hi

/-- Derive the actual `PrefixEdgeFactor` at the entering dart. The tail
differs from both endpoints of `p`. -/
theorem exists_enteringFactor (p : GraphPath G) (U0 : Finset V)
    (hs : p.start ∈ U0) (h2 : 2 ≤ (p.boundaryEdges U0).card) :
    ∃ (i : ℕ) (F : PrefixEdgeFactor p (p.walk.getVert i) (p.walk.getVert (i + 1))),
      i < p.walk.length ∧
        p.walk.getVert i ∉ U0 ∧
          p.walk.getVert (i + 1) ∈ U0 ∧
            p.walk.getVert i ≠ p.start ∧
              p.walk.getVert i ≠ p.finish := by
  obtain ⟨i, hi, h0, h1⟩ := p.exists_enteringIndex U0 hs h2
  obtain ⟨F, _hT⟩ := p.exists_factorAtIndex hi
  exact ⟨i, F, hi, h0, h1, p.entering_ne_start (U0 := U0) hs h0,
    p.entering_ne_finish hi⟩

/-! ### Rotation at an actual entering boundary dart -/

namespace PrefixEdgeFactor

variable {p : GraphPath G} {a x : V}

/-- The selected entering edge is an actual boundary walk edge. -/
lemma old_mem_boundaryEdges (F : PrefixEdgeFactor p a x) (U0 : Finset V)
    (ha : a ∉ U0) (hx : x ∈ U0) :
    s(a, x) ∈ p.boundaryEdges U0 :=
  mem_boundaryEdges_iff.2 ⟨F.old_mem_edges, endsStraddle_of_outside_inside ha hx⟩

lemma new_not_mem_boundaryEdges (F : PrefixEdgeFactor p a x) (U0 : Finset V)
    (hyx : G.Adj p.start x) (hy : p.start ∈ U0) (hx : x ∈ U0) :
    s(p.start, x) ∉ (F.rotate hyx).boundaryEdges U0 := by
  intro h
  exact not_endsStraddle_of_both hy hx (mem_boundaryEdges_iff.1 h).2

/-- After rotating an entering dart `a → x` across the original chord
`y—x` with `y, x ∈ U0` and `a ∉ U0`, the actual boundary finset loses
exactly the selected edge `a—x`. The new chord is internal to `U0`. -/
theorem boundaryEdges_rotate (F : PrefixEdgeFactor p a x) (U0 : Finset V)
    (hyx : G.Adj p.start x) (_ha : a ∉ U0) (hx : x ∈ U0) (hy : p.start ∈ U0) :
    (F.rotate hyx).boundaryEdges U0 = (p.boundaryEdges U0).erase s(a, x) := by
  ext e
  simp only [mem_boundaryEdges_iff, F.rotate_edges, mem_erase, mem_union,
    mem_singleton]
  constructor
  · rintro ⟨hmem, hstr⟩
    rcases hmem with h | rfl
    · exact ⟨h.1, ⟨h.2, hstr⟩⟩
    · exact (not_endsStraddle_of_both hy hx hstr).elim
  · rintro ⟨hne, ⟨hmem, hstr⟩⟩
    exact ⟨Or.inl ⟨hne, hmem⟩, hstr⟩

lemma rotate_start_eq_tail (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) :
    (F.rotate hyx).start = a :=
  F.rotate_start hyx

lemma rotate_finish_eq_old (F : PrefixEdgeFactor p a x)
    (hyx : G.Adj p.start x) :
    (F.rotate hyx).finish = p.finish :=
  F.rotate_finish hyx

/-- The gained chord `y—x` has both ends in `U0`. -/
lemma new_edge_internalU0 (F : PrefixEdgeFactor p a x) (U0 : Finset V)
    (hyx : G.Adj p.start x) (hy : p.start ∈ U0) (hx : x ∈ U0) :
    p.start ∈ U0 ∧ x ∈ U0 ∧ s(p.start, x) ∈ (F.rotate hyx).edges :=
  ⟨hy, hx, F.new_edge_mem_rotate hyx⟩

/-- Rotation at an entering `A`–`X` dart with original complete-join
`Y`–`X` edge `y—x`. The new start is the original-`A` tail, the finish
and support are unchanged, original-`A` protection is preserved, and the
boundary finset at `U0` loses exactly `a—x`. `Y` and `X` lie outside
`A`. This does not construct the entering dart on an arbitrary path. -/
theorem returnRotate_spec (F : PrefixEdgeFactor p a x)
    {U0 A : Finset V} (hyx : G.Adj p.start x)
    (haU : a ∉ U0) (hxU : x ∈ U0) (hyU : p.start ∈ U0)
    (haA : a ∈ A) (hyA : p.start ∉ A) (hxA : x ∉ A)
    {c : GraphCycle G} (hP : p.ProtectedAt c A) :
    (F.rotate hyx).start = a ∧
      (F.rotate hyx).start ∈ A ∧
        (F.rotate hyx).finish = p.finish ∧
          (F.rotate hyx).support = p.support ∧
            (F.rotate hyx).ProtectedAt c A ∧
              (F.rotate hyx).boundaryEdges U0 =
                (p.boundaryEdges U0).erase s(a, x) ∧
                s(p.start, x) ∈ (F.rotate hyx).edges ∧
                  ¬ endsStraddle s(p.start, x) U0 := by
  refine ⟨F.rotate_start hyx, by simpa [F.rotate_start] using haA,
    F.rotate_finish hyx, F.rotate_support hyx,
    F.protectedAt_rotate hyx haA hyA hxA hP,
    F.boundaryEdges_rotate U0 hyx haU hxU hyU,
    F.new_edge_mem_rotate hyx, not_endsStraddle_of_both hyU hxU⟩

/-- Complete-join form: `y ∈ Y`, `x ∈ X`, and every `Y`–`X` pair is an
original edge. The join hypothesis is an operation input. -/
theorem returnRotate_of_completeJoin (F : PrefixEdgeFactor p a x)
    {U0 A X Y : Finset V}
    (hyY : p.start ∈ Y) (hxX : x ∈ X)
    (hjoin : ∀ y ∈ Y, ∀ z ∈ X, G.Adj y z)
    (haU : a ∉ U0) (hxU : x ∈ U0) (hyU : p.start ∈ U0)
    (haA : a ∈ A) (hyA : p.start ∉ A) (hxA : x ∉ A)
    {c : GraphCycle G} (hP : p.ProtectedAt c A) :
    let hyx := hjoin p.start hyY x hxX
    (F.rotate hyx).start = a ∧
      (F.rotate hyx).finish = p.finish ∧
        (F.rotate hyx).support = p.support ∧
          (F.rotate hyx).ProtectedAt c A ∧
            (F.rotate hyx).boundaryEdges U0 =
              (p.boundaryEdges U0).erase s(a, x) := by
  intro hyx
  obtain ⟨hst, _, hfin, hsup, hProt, hbd, _, _⟩ :=
    F.returnRotate_spec (U0 := U0) (A := A) hyx haU hxU hyU haA hyA hxA hP
  exact ⟨hst, hfin, hsup, hProt, hbd⟩

end PrefixEdgeFactor

/-- Package: from `p.start ∈ U0` and at least two actual boundary edges,
produce the entering factor and apply prefix rotation across an original
`Y`–`X` complete-join chord. The maps sending an entering dart to
`A` / `X` are operation inputs that G2 must derive from the cycle
boundary. -/
theorem exists_returnRotate (p : GraphPath G) (U0 : Finset V)
    (hs : p.start ∈ U0) (h2 : 2 ≤ (p.boundaryEdges U0).card)
    {A X Y : Finset V} {c : GraphCycle G}
    (hjoin : ∀ y ∈ Y, ∀ z ∈ X, G.Adj y z)
    (hyY : p.start ∈ Y)
    (hP : p.ProtectedAt c A)
    (hAout : Disjoint A U0)
    (hYU : Y ⊆ U0) (hXU : X ⊆ U0)
    (henterX : ∀ i, i < p.walk.length → p.walk.getVert i ∉ U0 →
      p.walk.getVert (i + 1) ∈ U0 → p.walk.getVert (i + 1) ∈ X)
    (henterA : ∀ i, i < p.walk.length → p.walk.getVert i ∉ U0 →
      p.walk.getVert (i + 1) ∈ U0 → p.walk.getVert i ∈ A) :
    ∃ (i : ℕ) (F : PrefixEdgeFactor p (p.walk.getVert i) (p.walk.getVert (i + 1)))
      (hyx : G.Adj p.start (p.walk.getVert (i + 1))),
      i < p.walk.length ∧
        p.walk.getVert i ∉ U0 ∧
          p.walk.getVert (i + 1) ∈ U0 ∧
            p.walk.getVert i ∈ A ∧
              p.walk.getVert (i + 1) ∈ X ∧
                (F.rotate hyx).start = p.walk.getVert i ∧
                  (F.rotate hyx).support = p.support ∧
                    (F.rotate hyx).ProtectedAt c A := by
  obtain ⟨i, F, hi, h0, h1, _, _⟩ := p.exists_enteringFactor U0 hs h2
  have hxX : p.walk.getVert (i + 1) ∈ X := henterX i hi h0 h1
  have haA : p.walk.getVert i ∈ A := henterA i hi h0 h1
  have hyA : p.start ∉ A := fun h => (disjoint_left.1 hAout h) (hYU hyY)
  have hxA : p.walk.getVert (i + 1) ∉ A :=
    fun h => (disjoint_left.1 hAout h) (hXU hxX)
  have hyx : G.Adj p.start (p.walk.getVert (i + 1)) := hjoin p.start hyY _ hxX
  obtain ⟨hst, hfin, hsup, hProt, _⟩ :=
    F.returnRotate_of_completeJoin (U0 := U0) (A := A) (X := X) (Y := Y)
      hyY hxX hjoin h0 h1 hs haA hyA hxA hP
  exact ⟨i, F, hyx, hi, h0, h1, haA, hxX, hst, hsup, hProt⟩

end GraphPath

end Nikoghosyan
