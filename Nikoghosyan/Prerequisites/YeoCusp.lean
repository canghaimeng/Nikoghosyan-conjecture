/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.YeoExist

/-!
FSCD 2025 Lemma 6 (cusp minimization), Proposition 7 (nonsplitting growth)
and unrestricted-color `yeo_separator`.

Ordinary symmetric edge colors; no `Fintype C`. Source: Di Guardia–Laurent–
Tortora de Falco–Vaux Auclair, FSCD 2025, Section 3.
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

lemma not_nil_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : ¬ p.Nil) : ¬ (p.append q).Nil := by
  cases p with
  | nil => exact (hp Walk.nil_nil).elim
  | cons h p' => simp

lemma closedCuspCount_eq_internal_of_nocusp {u : V} {ω : G.Walk u u}
    (c : EdgeColoring G C) (hω : ¬ ω.Nil)
    (hnocusp : c.dartColor (ω.firstDart hω) ≠ c.dartColor (ω.lastDart hω)) :
    closedCuspCount ω c = internalCuspCount ω c := by
  unfold closedCuspCount
  simp [hω, hnocusp]

lemma closedCuspCount_eq_zero_iff {u : V} {ω : G.Walk u u}
    (c : EdgeColoring G C) (hω : ¬ ω.Nil) :
    closedCuspCount ω c = 0 ↔
      internalCuspCount ω c = 0 ∧
        c.dartColor (ω.firstDart hω) ≠ c.dartColor (ω.lastDart hω) := by
  simp [closedCuspCount, hω]

lemma isProperlyColored_iff_isCycle_closedCuspCount_eq_zero {u : V}
    {ω : G.Walk u u} (c : EdgeColoring G C) :
    IsProperlyColored ω c ↔ ω.IsCycle ∧ closedCuspCount ω c = 0 := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hω : ¬ ω.Nil := h.1.not_nil
    rw [closedCuspCount_eq_zero_iff c hω]
    exact ⟨(isAlternating_iff_internalCuspCount_eq_zero ω c).1 h.2.1, h.2.2 hω⟩
  · intro ⟨hcyc, h0⟩
    have hω : ¬ ω.Nil := hcyc.not_nil
    rw [closedCuspCount_eq_zero_iff c hω] at h0
    exact ⟨hcyc, (isAlternating_iff_internalCuspCount_eq_zero ω c).2 h0.1, fun _ => h0.2⟩

lemma Walk_append_left_cancel {u v w : V} {p : G.Walk u v}
    {q₁ q₂ : G.Walk v w} (h : p.append q₁ = p.append q₂) : q₁ = q₂ := by
  induction p with
  | nil => simpa using h
  | cons hadj p ih =>
    apply ih
    simpa using h

/-- Closing two internally vertex-disjoint nonempty paths of total length at
least three yields a genuine simple cycle. -/
lemma isCycle_append_of_paths {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath) (hpnil : ¬ p.Nil) (_hqnil : ¬ q.Nil)
    (hdisj : ∀ x ∈ q.support.tail, x = u ∨ x ∉ p.support)
    (h3 : 3 ≤ p.length + q.length) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · cases p with
    | nil => exact (hpnil Walk.nil_nil).elim
    | cons hadj p' =>
      simp only [Walk.cons_append, Walk.tail_cons]
      have hp' : p'.IsPath := hp.of_cons
      have hu_not : u ∉ p'.support := (Walk.cons_isPath_iff _ _).1 hp |>.2
      have hdisj' : ∀ x ∈ q.support.tail, x ∉ p'.support := by
        intro x hx hxP'
        rcases hdisj x hx with rfl | hnot
        · exact hu_not hxP'
        · exact hnot (List.mem_cons_of_mem _ hxP')
      convert isPath_append hp' hq hdisj'
      simp [Walk.isPath_copy]
  · simpa [Walk.length_append] using h3

lemma isPath_dropUntil_of_cycle {v w : V} {ω : G.Walk v v}
    (hcyc : ω.IsCycle) (hw : w ∈ ω.support) (hne : w ≠ v) :
    (ω.dropUntil w hw).IsPath := by
  have htake : ¬ (ω.takeUntil w hw).Nil := Walk.not_nil_of_ne hne.symm
  have hcyc' : ((ω.takeUntil w hw).append (ω.dropUntil w hw)).IsCycle := by
    convert hcyc
    exact Walk.take_spec ω hw
  exact hcyc'.isPath_of_append_right htake

lemma takeUntil_end_of_isPath {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.takeUntil v p.end_mem_support = p := by
  have hdrop : (p.dropUntil v p.end_mem_support).Nil :=
    (Walk.isPath_iff_nil).1 (hp.dropUntil p.end_mem_support)
  have happ := Walk.take_spec p p.end_mem_support
  cases hnil : p.dropUntil v p.end_mem_support with
  | nil => simpa [hnil] using happ
  | cons h q =>
    have : ¬ (p.dropUntil v p.end_mem_support).Nil := by simp [hnil]
    exact (this hdrop).elim

lemma dropUntil_reverse_eq {v u : V} {ω : G.Walk v v}
    (hcyc : ω.IsCycle) (hu : u ∈ ω.support) (hne : u ≠ v) :
    ω.reverse.dropUntil u (by simp [Walk.support_reverse, hu]) =
      (ω.takeUntil u hu).reverse := by
  have hdropPath : (ω.dropUntil u hu).IsPath :=
    isPath_dropUntil_of_cycle hcyc hu hne
  have hrev : ω.reverse =
      (ω.dropUntil u hu).reverse.append (ω.takeUntil u hu).reverse := by
    rw [← Walk.reverse_append, Walk.take_spec]
  have huL : u ∈ (ω.dropUntil u hu).reverse.support := by
    simp [Walk.support_reverse]
  have htake_eq :
      ω.reverse.takeUntil u (by simp [Walk.support_reverse, hu]) =
        (ω.dropUntil u hu).reverse := by
    have hmem :
        u ∈ ((ω.dropUntil u hu).reverse.append
          (ω.takeUntil u hu).reverse).support := by
      rw [← hrev]; simp [Walk.support_reverse, hu]
    have h := Walk.takeUntil_append_of_mem_left
      (ω.dropUntil u hu).reverse (ω.takeUntil u hu).reverse huL
    convert h.trans (takeUntil_end_of_isPath hdropPath.reverse)
  have happ := Walk.take_spec ω.reverse
    (by simp [Walk.support_reverse, hu] : u ∈ ω.reverse.support)
  have hcomp :
      (ω.dropUntil u hu).reverse.append
        (ω.reverse.dropUntil u (by simp [Walk.support_reverse, hu])) =
      (ω.dropUntil u hu).reverse.append (ω.takeUntil u hu).reverse := by
    calc
      _ = ω.reverse := by
        rw [← htake_eq]
        exact happ
      _ = _ := hrev
  exact Walk_append_left_cancel hcomp

lemma takeUntil_reverse_eq {v u : V} {ω : G.Walk v v}
    (hcyc : ω.IsCycle) (hu : u ∈ ω.support) (hne : u ≠ v) :
    ω.reverse.takeUntil u (by simp [Walk.support_reverse, hu]) =
      (ω.dropUntil u hu).reverse := by
  have hdropPath : (ω.dropUntil u hu).IsPath :=
    isPath_dropUntil_of_cycle hcyc hu hne
  have hrev : ω.reverse =
      (ω.dropUntil u hu).reverse.append (ω.takeUntil u hu).reverse := by
    rw [← Walk.reverse_append, Walk.take_spec]
  have huL : u ∈ (ω.dropUntil u hu).reverse.support := by
    simp [Walk.support_reverse]
  have hmem :
      u ∈ ((ω.dropUntil u hu).reverse.append
        (ω.takeUntil u hu).reverse).support := by
    rw [← hrev]; simp [Walk.support_reverse, hu]
  have h := Walk.takeUntil_append_of_mem_left
    (ω.dropUntil u hu).reverse (ω.takeUntil u hu).reverse huL
  convert h.trans (takeUntil_end_of_isPath hdropPath.reverse)

lemma mem_support_takeUntil_or_dropUntil {u v w : V} {p : G.Walk v w}
    (hu : u ∈ p.support) {x : V} (hx : x ∈ p.support) :
    x ∈ (p.takeUntil u hu).support ∨ x ∈ (p.dropUntil u hu).support := by
  have happ := Walk.take_spec p hu
  rw [← happ, Walk.mem_support_append_iff] at hx
  exact hx

lemma support_tail_takeUntil_prefix {u v x : V} {q : G.Walk u v}
    (hx : x ∈ q.support) (hnil : ¬ (q.takeUntil x hx).Nil) :
    (q.takeUntil x hx).support.tail <+: q.support.tail := by
  obtain ⟨t, ht⟩ := Walk.support_takeUntil_prefix_support q hx
  have hcons_take :
      (q.takeUntil x hx).support =
        u :: (q.takeUntil x hx).support.tail := by
    conv_lhs => rw [← List.cons_head_tail (Walk.support_ne_nil _)]
    rw [Walk.head_support]
  have hcons_q : q.support = u :: q.support.tail := by
    conv_lhs => rw [← List.cons_head_tail (Walk.support_ne_nil _)]
    rw [Walk.head_support]
  refine ⟨t, ?_⟩
  have ht' : (u :: (q.takeUntil x hx).support.tail) ++ t = u :: q.support.tail := by
    rwa [← hcons_take, ← hcons_q]
  simp only [List.cons_append] at ht'
  exact (List.cons_inj_right u).mp ht'

/-- First reentry of a nonempty open path onto a host list, with the prefix
internally avoiding the host except at the reentry vertex. -/
theorem first_reentry_spec {u w : V} {q : G.Walk u w}
    (hq : q.IsPath) (hqnil : ¬ q.Nil) (hne : u ≠ w)
    {S : List V} (hw : w ∈ S) :
    ∃ (x : V) (hx : x ∈ q.support),
      x ∈ S ∧ ¬ (q.takeUntil x hx).Nil ∧ x ∈ q.support.tail ∧
        (∀ y ∈ (q.takeUntil x hx).support.tail, y ∈ S → y = x) := by
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
  have hnil : ¬ (q.takeUntil x hxsup).Nil := not_nil_takeUntil_of_mem_tail hq hxtail
  refine ⟨x, hxsup, hxS, hnil, hxtail, ?_⟩
  intro y hy hyS
  have hpref := support_tail_takeUntil_prefix hxsup hnil
  have hy_tail : y ∈ q.support.tail := hpref.subset hy
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.1 hy_tail
  have hnodup : q.support.tail.Nodup := hq.support_nodup.tail
  have hx_idx : q.support.idxOf x = q.support.tail.findIdx p + 1 := by
    have hlt : q.support.tail.findIdx p + 1 < q.support.length := by
      have := hi
      simp [List.length_tail] at this ⊢
      omega
    have hxget : q.support[q.support.tail.findIdx p + 1] = x := by
      have := List.getElem_tail (l := q.support) (i := q.support.tail.findIdx p)
        (h := by simpa [List.length_tail] using hi)
      simpa [x] using this.symm
    have := hq.support_nodup.idxOf_getElem (i := q.support.tail.findIdx p + 1) hlt
    simpa [hxget] using this
  have hlen_take : (q.takeUntil x hxsup).length = q.support.tail.findIdx p + 1 := by
    rw [Walk.length_takeUntil, hx_idx]
  have hlen_tail :
      (q.takeUntil x hxsup).support.tail.length =
        q.support.tail.findIdx p + 1 := by
    simp [List.length_tail, Walk.length_support, hlen_take]
  obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.1 hy
  have hk_lt : k < q.support.tail.findIdx p + 1 :=
    hlen_tail ▸ hk
  have hpre_get :
      (q.takeUntil x hxsup).support.tail[k] = q.support.tail[k] := by
    have hpf := List.IsPrefix.getElem hpref hk
    exact hpf
  have : q.support.tail[k] = y := by
    rw [← hpre_get, hky]
  have hklen : k < q.support.tail.length :=
    lt_of_lt_of_le hk_lt (Nat.succ_le_of_lt hi)
  have hjk : j = k := by
    apply (List.Nodup.getElem_inj_iff hnodup (hi := hj) (hj := hklen)).mp
    rw [hjy, this]
  have hj_le : j ≤ q.support.tail.findIdx p := by
    omega
  have hj_not_lt : ¬ j < q.support.tail.findIdx p := by
    intro hjlt
    have hfalse := List.not_of_lt_findIdx (p := p) hjlt
    have : p (q.support.tail[j]) = true := by
      simp [p, hjy, hyS]
    exact of_decide_eq_false hfalse (by simpa [p, hjy] using hyS)
  have : j = q.support.tail.findIdx p := le_antisymm hj_le (Nat.le_of_not_gt hj_not_lt)
  subst this
  simp [x, hjy]

lemma nocusp_reverse {v : V} {ω : G.Walk v v} (c : EdgeColoring G C)
    (hω : ¬ ω.Nil)
    (hnocusp : c.dartColor (ω.firstDart hω) ≠ c.dartColor (ω.lastDart hω)) :
    c.dartColor (ω.reverse.firstDart (not_nil_reverse hω)) ≠
      c.dartColor (ω.reverse.lastDart (not_nil_reverse hω)) := by
  rw [firstDart_reverse hω, lastDart_reverse hω, EdgeColoring.dartColor_symm,
    EdgeColoring.dartColor_symm]
  exact hnocusp.symm

lemma internalCuspCount_take_drop {u v w : V} {p : G.Walk u v}
    (c : EdgeColoring G C) (hw : w ∈ p.support)
    (ht : ¬ (p.takeUntil w hw).Nil) (hd : ¬ (p.dropUntil w hw).Nil) :
    internalCuspCount p c =
      internalCuspCount (p.takeUntil w hw) c +
        internalCuspCount (p.dropUntil w hw) c +
          seamCusp c (p.takeUntil w hw) (p.dropUntil w hw) ht hd := by
  have happ := Walk.take_spec p hw
  have h := internalCuspCount_append (p := p.takeUntil w hw)
    (q := p.dropUntil w hw) c ht hd
  simpa [happ] using h

lemma CuspFreeReach.of_takeUntil {u v w : V} {α : C} {q : G.Walk u v}
    (c : EdgeColoring G C) (hq : q.IsPath) (hqnil : ¬ q.Nil)
    (hq0 : internalCuspCount q c = 0)
    (hqfirst : c.dartColor (q.firstDart hqnil) ≠ α)
    (hw : w ∈ q.support) (hnil : ¬ (q.takeUntil w hw).Nil) :
    CuspFreeReach c u w α (c.dartColor ((q.takeUntil w hw).lastDart hnil)) :=
  ⟨q.takeUntil w hw, hq.takeUntil hw, hnil,
    internalCuspCount_takeUntil c hw hq0,
    by rw [firstDart_takeUntil hw hnil]; exact hqfirst, rfl⟩

lemma cycle_take_drop_inter {v u x : V} {ω : G.Walk v v}
    (hcyc : ω.IsCycle) (hu : u ∈ ω.support) (hne : u ≠ v)
    (hxT : x ∈ (ω.takeUntil u hu).support)
    (hxD : x ∈ (ω.dropUntil u hu).support) :
    x = u ∨ x = v := by
  have happ : (ω.takeUntil u hu).append (ω.dropUntil u hu) = ω := Walk.take_spec ω hu
  have hdis :
      (ω.takeUntil u hu).support.tail.Disjoint (ω.dropUntil u hu).support.tail := by
    have : ((ω.takeUntil u hu).support.tail ++
        (ω.dropUntil u hu).support.tail).Nodup := by
      rw [← Walk.tail_support_append, happ]
      exact hcyc.support_nodup
    exact List.disjoint_of_nodup_append this
  rw [Walk.mem_support_iff] at hxT hxD
  rcases hxT with rfl | hxT
  · exact Or.inr rfl
  rcases hxD with rfl | hxD
  · exact Or.inl rfl
  exact (hdis hxT hxD).elim

lemma seamCusp_eq_one_iff {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (c : EdgeColoring G C) (hp : ¬ p.Nil) (hq : ¬ q.Nil) :
    seamCusp c p q hp hq = 1 ↔
      c.dartColor (p.lastDart hp) = c.dartColor (q.firstDart hq) := by
  unfold seamCusp
  split_ifs <;> simp_all

lemma seamCusp_eq_zero_iff {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (c : EdgeColoring G C) (hp : ¬ p.Nil) (hq : ¬ q.Nil) :
    seamCusp c p q hp hq = 0 ↔
      c.dartColor (p.lastDart hp) ≠ c.dartColor (q.firstDart hq) := by
  unfold seamCusp
  split_ifs <;> simp_all

lemma seamCusp_le_one {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (c : EdgeColoring G C) (hp : ¬ p.Nil) (hq : ¬ q.Nil) :
    seamCusp c p q hp hq ≤ 1 := by
  unfold seamCusp
  split_ifs <;> omega

lemma mem_support_of_mem_takeUntil {u v w x : V} {p : G.Walk u v}
    (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
    x ∈ p.support :=
  (Walk.support_takeUntil_subset_support p hw) hx

lemma mem_support_of_mem_dropUntil {u v w x : V} {p : G.Walk u v}
    (hw : w ∈ p.support) (hx : x ∈ (p.dropUntil w hw).support) :
    x ∈ p.support := by
  have happ := Walk.take_spec p hw
  have : x ∈ ((p.takeUntil w hw).append (p.dropUntil w hw)).support :=
    Walk.support_subset_support_append_right _ _ hx
  simpa [happ] using this

lemma path_start_not_mem_dropUntil {u v w : V} {p : G.Walk u v}
    (hp : p.IsPath) (hw : w ∈ p.support) (hne : u ≠ w) :
    u ∉ (p.dropUntil w hw).support := by
  intro hmem
  have htake : ¬ (p.takeUntil w hw).Nil := Walk.not_nil_of_ne hne
  have happ := Walk.take_spec p hw
  have hsup :
      p.support =
        (p.takeUntil w hw).support.dropLast ++ (p.dropUntil w hw).support := by
    have h := Walk.support_append_eq_support_dropLast_append
      (p.takeUntil w hw) (p.dropUntil w hw)
    rwa [happ] at h
  have hlen : 2 ≤ (p.takeUntil w hw).support.length := by
    have hs := Walk.length_support (p.takeUntil w hw)
    have : 1 ≤ (p.takeUntil w hw).length :=
      Nat.succ_le_of_lt (Walk.not_nil_iff_lt_length.1 htake)
    omega
  have hdl : (p.takeUntil w hw).support.dropLast ≠ [] := by
    intro hnil
    have : (p.takeUntil w hw).support.length ≤ 1 :=
      (List.dropLast_eq_nil_iff).1 hnil
    omega
  have hu_left : u ∈ (p.takeUntil w hw).support.dropLast := by
    cases hs : (p.takeUntil w hw).support with
    | nil =>
      exact (Walk.support_ne_nil (p.takeUntil w hw) hs).elim
    | cons a as =>
      have ha : a = u := by
        have := Walk.head_support (p.takeUntil w hw)
        simp [hs] at this
        exact this
      have has : as ≠ [] := by
        intro hnil
        simp [hs, hnil] at hlen
      subst ha
      simp [hs, List.dropLast_cons_of_ne_nil has]
  have hnod : p.support.Nodup := hp.support_nodup
  have hdis :
      (p.takeUntil w hw).support.dropLast.Disjoint (p.dropUntil w hw).support := by
    have hnod' : ((p.takeUntil w hw).support.dropLast ++
        (p.dropUntil w hw).support).Nodup := by
      simpa [hsup] using hnod
    exact List.disjoint_of_nodup_append hnod'
  exact hdis hu_left hmem

lemma eq_cons_nil_of_length_one {u v : V} {p : G.Walk u v}
    (h1 : p.length = 1) : ∃ h : G.Adj u v, p = Walk.cons h Walk.nil := by
  cases p with
  | nil => simp at h1
  | cons h p' =>
    cases p' with
    | nil => exact ⟨h, rfl⟩
    | cons h2 p'' =>
      simp [Walk.length_cons] at h1

lemma dartColor_length_one_symm {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (c : EdgeColoring G C) (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (h1 : p.length = 1) (h2 : q.length = 1) :
    c.dartColor (p.lastDart hp) = c.dartColor (q.firstDart hq) := by
  obtain ⟨hpadj, rfl⟩ := eq_cons_nil_of_length_one h1
  obtain ⟨hqadj, rfl⟩ := eq_cons_nil_of_length_one h2
  simp [Walk.lastDart, Walk.firstDart, Walk.penultimate, EdgeColoring.dartColor]
  exact (c.color_symm hpadj).trans (c.color_proof _ _)

lemma dartColor_length_one_same {u v : V} {p q : G.Walk u v}
    (c : EdgeColoring G C) (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (h1 : p.length = 1) (h2 : q.length = 1) :
    c.dartColor (p.firstDart hp) = c.dartColor (q.firstDart hq) := by
  obtain ⟨hpadj, rfl⟩ := eq_cons_nil_of_length_one h1
  obtain ⟨hqadj, rfl⟩ := eq_cons_nil_of_length_one h2
  simp [Walk.firstDart, EdgeColoring.dartColor, EdgeColoring.color_proof]

/-- Oriented FSCD Lemma 6: detour already reenters first at `w` on the
`u`-to-`v` arc of `ω`. -/
theorem cusp_minimization_oriented {v u w : V} {α β : C}
    (ω : G.Walk v v) (c : EdgeColoring G C)
    (hcyc : ω.IsCycle)
    (hnocusp : c.dartColor (ω.firstDart hcyc.not_nil) ≠
      c.dartColor (ω.lastDart hcyc.not_nil))
    (hu : u ∈ ω.support) (hne_uv : u ≠ v)
    (hcusp :
      c.dartColor ((ω.takeUntil u hu).lastDart (Walk.not_nil_of_ne hne_uv.symm)) = α ∧
        c.dartColor ((ω.dropUntil u hu).firstDart (Walk.not_nil_of_ne hne_uv)) = α)
    {q : G.Walk u w}
    (hq : q.IsPath) (hqnil : ¬ q.Nil)
    (hq0 : internalCuspCount q c = 0)
    (hqfirst : c.dartColor (q.firstDart hqnil) ≠ α)
    (hqlast : c.dartColor (q.lastDart hqnil) = β)
    (hw : w ∈ (ω.dropUntil u hu).support)
    (hinter : ∀ x ∈ q.support.tail, x ∈ ω.support → x = w)
    (hstart : w = v → β ≠ c.dartColor (ω.firstDart hcyc.not_nil)) :
    HasProperlyColoredCycle c ∨
      ∃ (ω' : G.Walk v v) (hcyc' : ω'.IsCycle),
        c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
            c.dartColor (ω'.lastDart hcyc'.not_nil) ∧
          closedCuspCount ω' c < closedCuspCount ω c := by
  set VU := ω.takeUntil u hu
  set UV := ω.dropUntil u hu
  have hVU : VU.IsPath := hcyc.isPath_takeUntil hu
  have hUV : UV.IsPath := isPath_dropUntil_of_cycle hcyc hu hne_uv
  have hVUnil : ¬ VU.Nil := Walk.not_nil_of_ne hne_uv.symm
  have hUVnil : ¬ UV.Nil := Walk.not_nil_of_ne hne_uv
  have hne_uw : u ≠ w := mt (Walk.IsPath.nil_iff_eq hq).2 hqnil
  have hωint0 : closedCuspCount ω c = internalCuspCount ω c :=
    closedCuspCount_eq_internal_of_nocusp c hcyc.not_nil hnocusp
  have hseamU : seamCusp c VU UV hVUnil hUVnil = 1 :=
    (seamCusp_eq_one_iff c hVUnil hUVnil).2 (hcusp.1.trans hcusp.2.symm)
  have hinterω := internalCuspCount_take_drop c hu hVUnil hUVnil
  have hVUpos : 1 ≤ VU.length := Nat.succ_le_of_lt (Walk.not_nil_iff_lt_length.1 hVUnil)
  have hqpos : 1 ≤ q.length := Nat.succ_le_of_lt (Walk.not_nil_iff_lt_length.1 hqnil)
  by_cases hwv : w = v
  · subst w
    have hdisj : ∀ x ∈ q.support.tail, x = v ∨ x ∉ VU.support := by
      intro x hx
      by_cases hxv : x = v
      · exact Or.inl hxv
      · exact Or.inr fun hxVU =>
          hxv (hinter x hx (mem_support_of_mem_takeUntil hu hxVU))
    have h3 : 3 ≤ VU.length + q.length := by
      refine le_of_not_gt fun hlt => ?_
      have hsum : VU.length + q.length = 2 := by omega
      have hVU1 : VU.length = 1 := by omega
      have hq1 : q.length = 1 := by omega
      have hse := dartColor_length_one_symm c hVUnil hqnil hVU1 hq1
      exact hqfirst (hse.symm.trans hcusp.1)
    have hcyc' : (VU.append q).IsCycle :=
      isCycle_append_of_paths hVU hq hVUnil hqnil hdisj h3
    have hfirst :
        c.dartColor ((VU.append q).firstDart hcyc'.not_nil) =
          c.dartColor (ω.firstDart hcyc.not_nil) := by
      rw [firstDart_append_of_not_nil_left hVUnil]
      simp [VU, firstDart_takeUntil hu hVUnil, firstDart_proof]
    have hlast :
        c.dartColor ((VU.append q).lastDart hcyc'.not_nil) = β := by
      rw [lastDart_append_of_not_nil_right hqnil, hqlast]
    have hn' :
        c.dartColor ((VU.append q).firstDart hcyc'.not_nil) ≠
          c.dartColor ((VU.append q).lastDart hcyc'.not_nil) := by
      rw [hfirst, hlast]; exact (hstart rfl).symm
    have hω'int : internalCuspCount (VU.append q) c = internalCuspCount VU c := by
      rw [internalCuspCount_append c hVUnil hqnil, hq0]
      have : seamCusp c VU q hVUnil hqnil = 0 :=
        (seamCusp_eq_zero_iff c hVUnil hqnil).2 (fun hcol => hqfirst (hcusp.1 ▸ hcol.symm))
      omega
    refine Or.inr ⟨VU.append q, hcyc', hn', ?_⟩
    rw [hωint0, closedCuspCount_eq_internal_of_nocusp c hcyc'.not_nil hn',
      hω'int]
    have : internalCuspCount ω c =
        internalCuspCount VU c + internalCuspCount UV c + 1 := by
      simpa [VU, UV, hseamU] using hinterω
    omega
  · have hWUnil : ¬ (UV.takeUntil w hw).Nil := Walk.not_nil_of_ne hne_uw
    have hWVnil : ¬ (UV.dropUntil w hw).Nil :=
      Walk.not_nil_of_ne (fun h => hwv h)
    set UW := UV.takeUntil w hw
    set WV := UV.dropUntil w hw
    have hUW : UW.IsPath := hUV.takeUntil hw
    have hWV : WV.IsPath := hUV.dropUntil hw
    have hWVpos : 1 ≤ WV.length :=
      Nat.succ_le_of_lt (Walk.not_nil_iff_lt_length.1 hWVnil)
    have hAdisj : ∀ x ∈ q.support.tail, x ∉ VU.support := by
      intro x hx hxVU
      have hxω := mem_support_of_mem_takeUntil hu hxVU
      have hxw : x = w := hinter x hx hxω
      subst hxw
      rcases cycle_take_drop_inter hcyc hu hne_uv hxVU hw with rfl | rfl
      · exact hne_uw rfl
      · exact hwv rfl
    have hA : (VU.append q).IsPath := isPath_append hVU hq hAdisj
    have hAnil : ¬ (VU.append q).Nil := not_nil_append_right hqnil
    have hdisjC : ∀ x ∈ WV.support.tail, x = v ∨ x ∉ (VU.append q).support := by
      intro x hx
      by_cases hxv : x = v
      · exact Or.inl hxv
      · right
        intro hxA
        have hxWV : x ∈ WV.support := List.mem_of_mem_tail hx
        have hxUV := mem_support_of_mem_dropUntil hw hxWV
        have hxω := mem_support_of_mem_dropUntil hu hxUV
        rw [Walk.mem_support_append_iff] at hxA
        rcases hxA with hxVU | hxq
        · rcases cycle_take_drop_inter hcyc hu hne_uv hxVU hxUV with huEq | hvEq
          · exact path_start_not_mem_dropUntil hUV hw hne_uw (by
              have : u ∈ WV.support := huEq ▸ hxWV
              convert this)
          · exact hxv hvEq
        · rw [Walk.mem_support_iff] at hxq
          rcases hxq with hxu | hxqt
          · exact path_start_not_mem_dropUntil hUV hw hne_uw (by
              have : u ∈ WV.support := hxu ▸ hxWV
              convert this)
          · have hxw : x = w := hinter x hxqt hxω
            subst hxw
            exact not_mem_support_tail_of_isPath hWV hx
    have h3 : 3 ≤ (VU.append q).length + WV.length := by
      simp [Walk.length_append]; omega
    have hcyc' : ((VU.append q).append WV).IsCycle :=
      isCycle_append_of_paths hA hWV hAnil hWVnil hdisjC h3
    set ω' := (VU.append q).append WV
    have hfirst' :
        c.dartColor (ω'.firstDart hcyc'.not_nil) =
          c.dartColor (ω.firstDart hcyc.not_nil) := by
      rw [firstDart_append_of_not_nil_left hAnil,
        firstDart_append_of_not_nil_left hVUnil]
      simp [VU, firstDart_takeUntil hu hVUnil, firstDart_proof]
    have hlast' :
        c.dartColor (ω'.lastDart hcyc'.not_nil) =
          c.dartColor (ω.lastDart hcyc.not_nil) := by
      rw [lastDart_append_of_not_nil_right hWVnil, lastDart_dropUntil hw hWVnil,
        lastDart_dropUntil hu hUVnil]
      try simp [lastDart_proof]
    have hn' :
        c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
          c.dartColor (ω'.lastDart hcyc'.not_nil) := by
      rw [hfirst', hlast']; exact hnocusp
    have hinterUV := internalCuspCount_take_drop (p := UV) c hw hWUnil hWVnil
    let n1 := internalCuspCount VU c
    let n2 := internalCuspCount UW c
    let n3 := internalCuspCount WV c
    let bω := seamCusp c UW WV hWUnil hWVnil
    let b' := seamCusp c q WV hqnil hWVnil
    have hωint : internalCuspCount ω c = n1 + 1 + n2 + bω + n3 := by
      have h1 : internalCuspCount ω c =
          internalCuspCount VU c + internalCuspCount UV c + 1 := by
        simpa [VU, UV, hseamU] using hinterω
      have h2 : internalCuspCount UV c = n2 + n3 + bω := hinterUV
      omega
    have hω'int : internalCuspCount ω' c = n1 + b' + n3 := by
      have hAq := internalCuspCount_append (p := VU) (q := q) c hVUnil hqnil
      have hse0 : seamCusp c VU q hVUnil hqnil = 0 :=
        (seamCusp_eq_zero_iff c hVUnil hqnil).2
          (fun hcol => hqfirst (hcusp.1 ▸ hcol.symm))
      have hrest := internalCuspCount_append (p := VU.append q) (q := WV)
        c hAnil hWVnil
      have hseb : seamCusp c (VU.append q) WV hAnil hWVnil = b' := by
        simp only [b', seamCusp]
        rw [lastDart_append_of_not_nil_right hqnil]
      simp [ω', hrest, hAq, hse0, hq0, hseb]
      omega
    rw [hωint0]
    have hω'c := closedCuspCount_eq_internal_of_nocusp c hcyc'.not_nil hn'
    by_cases hlt : n1 + b' + n3 < n1 + 1 + n2 + bω + n3
    · refine Or.inr ⟨ω', hcyc', hn', ?_⟩
      rw [hω'c, hωint, hω'int]; exact hlt
    · have hb'le : b' ≤ 1 := seamCusp_le_one c hqnil hWVnil
      have hbωle : bω ≤ 1 := seamCusp_le_one c hWUnil hWVnil
      have hn2 : n2 = 0 := by omega
      have hbω : bω = 0 := by omega
      have hb' : b' = 1 := by omega
      have hUWrev : UW.reverse.IsPath := hUW.reverse
      have hUWrevnil : ¬ UW.reverse.Nil := not_nil_reverse hWUnil
      have hDdisj : ∀ x ∈ UW.reverse.support.tail, x = u ∨ x ∉ q.support := by
        intro x hx
        by_cases hxu : x = u
        · exact Or.inl hxu
        · right
          intro hxq
          have hxUW : x ∈ UW.support := by
            simpa [Walk.support_reverse] using List.mem_of_mem_tail hx
          have hxω := mem_support_of_mem_dropUntil hu
            (mem_support_of_mem_takeUntil hw hxUW)
          rw [Walk.mem_support_iff] at hxq
          rcases hxq with rfl | hxqt
          · exact hxu rfl
          · have : x = w := hinter x hxqt hxω
            subst this
            exact not_mem_support_tail_of_isPath hUWrev hx
      have h3d : 3 ≤ q.length + UW.reverse.length := by
        refine le_of_not_gt fun hlt => ?_
        have hUWpos : 1 ≤ UW.length :=
          Nat.succ_le_of_lt (Walk.not_nil_iff_lt_length.1 hWUnil)
        have hUW1 : UW.length = 1 := by simp [Walk.length_reverse] at hlt; omega
        have hq1 : q.length = 1 := by simp [Walk.length_reverse] at hlt; omega
        have hse := dartColor_length_one_same c hqnil hWUnil hq1 hUW1
        have hfirstUW : c.dartColor (UW.firstDart hWUnil) = α := by
          rw [firstDart_takeUntil hw hWUnil]; exact hcusp.2
        exact hqfirst (hse.trans hfirstUW)
      have hcycd : (q.append UW.reverse).IsCycle :=
        isCycle_append_of_paths hq hUWrev hqnil hUWrevnil hDdisj h3d
      have hnocuspd :
          c.dartColor ((q.append UW.reverse).firstDart hcycd.not_nil) ≠
            c.dartColor ((q.append UW.reverse).lastDart hcycd.not_nil) := by
        rw [firstDart_append_of_not_nil_left hqnil,
          lastDart_append_of_not_nil_right hUWrevnil,
          lastDart_reverse hWUnil hUWrevnil, EdgeColoring.dartColor_symm,
          firstDart_takeUntil hw hWUnil]
        exact fun hcol => hqfirst (hcol.trans hcusp.2)
      have hinterd : internalCuspCount (q.append UW.reverse) c = 0 := by
        rw [internalCuspCount_append c hqnil hUWrevnil, hq0,
          internalCuspCount_reverse]
        have hse0 : seamCusp c q UW.reverse hqnil hUWrevnil = 0 := by
          rw [seamCusp_eq_zero_iff]
          rw [firstDart_reverse hWUnil hUWrevnil, EdgeColoring.dartColor_symm, hqlast]
          have hb'1 := (seamCusp_eq_one_iff c hqnil hWVnil).1 hb'
          have hbω0 := (seamCusp_eq_zero_iff c hWUnil hWVnil).1 hbω
          rw [hqlast] at hb'1
          exact fun hcol => hbω0 (hcol.symm.trans hb'1)
        omega
      refine Or.inl ⟨u, q.append UW.reverse, ?_⟩
      exact (isProperlyColored_iff_isCycle_closedCuspCount_eq_zero c).2
        ⟨hcycd, (closedCuspCount_eq_zero_iff c hcycd.not_nil).2 ⟨hinterd, hnocuspd⟩⟩

end Yeo
end Nikoghosyan
