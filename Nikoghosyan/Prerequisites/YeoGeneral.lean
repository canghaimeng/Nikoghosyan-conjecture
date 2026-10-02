/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.YeoCusp

/-!
General (unoriented) FSCD Lemma 6, first-cusp extraction, nonsplitting
growth (Proposition 7), and unrestricted-color `yeo_separator`.

Preserves the checked oriented body in `YeoCusp`. Ordinary symmetric edge
colors; no `Fintype C`. Source: Di Guardia–Laurent–Tortora de Falco–Vaux
Auclair, FSCD 2025, Lemma 6 / Proposition 7 / Theorems 16–17.
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

lemma mem_support_reverse_iff {u v x : V} {p : G.Walk u v} :
    x ∈ p.reverse.support ↔ x ∈ p.support := by
  simp [Walk.support_reverse]

lemma cusp_at_reverse {v u : V} {ω : G.Walk v v} {α : C}
    (c : EdgeColoring G C) (hcyc : ω.IsCycle)
    (hu : u ∈ ω.support) (hne : u ≠ v)
    (hcusp :
      c.dartColor ((ω.takeUntil u hu).lastDart (Walk.not_nil_of_ne hne.symm)) = α ∧
        c.dartColor ((ω.dropUntil u hu).firstDart (Walk.not_nil_of_ne hne)) = α) :
    c.dartColor
        ((ω.reverse.takeUntil u (by simp [Walk.support_reverse, hu])).lastDart
          (Walk.not_nil_of_ne hne.symm)) = α ∧
      c.dartColor
        ((ω.reverse.dropUntil u (by simp [Walk.support_reverse, hu])).firstDart
          (Walk.not_nil_of_ne hne)) = α := by
  have huR : u ∈ ω.reverse.support := by simp [Walk.support_reverse, hu]
  have htake := takeUntil_reverse_eq (ω := ω) hcyc hu hne
  have hdrop := dropUntil_reverse_eq (ω := ω) hcyc hu hne
  have hUVnil : ¬ (ω.dropUntil u hu).Nil := Walk.not_nil_of_ne hne
  have hVUnil : ¬ (ω.takeUntil u hu).Nil := Walk.not_nil_of_ne hne.symm
  have hUVrev : ¬ (ω.dropUntil u hu).reverse.Nil := not_nil_reverse hUVnil
  have hVUrev : ¬ (ω.takeUntil u hu).reverse.Nil := not_nil_reverse hVUnil
  constructor
  · have hcol :
        c.dartColor ((ω.dropUntil u hu).reverse.lastDart hUVrev) = α := by
      rw [lastDart_reverse hUVnil hUVrev, EdgeColoring.dartColor_symm]
      exact hcusp.2
    convert hcol
  · have hcol :
        c.dartColor ((ω.takeUntil u hu).reverse.firstDart hVUrev) = α := by
      rw [firstDart_reverse hVUnil hVUrev, EdgeColoring.dartColor_symm]
      exact hcusp.1
    convert hcol

lemma or_min_of_eq_count {v : V} {ω ωor : G.Walk v v} (c : EdgeColoring G C)
    (hcount : closedCuspCount ωor c = closedCuspCount ω c)
    (h : HasProperlyColoredCycle c ∨
      ∃ (ω' : G.Walk v v) (hcyc' : ω'.IsCycle),
        c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
            c.dartColor (ω'.lastDart hcyc'.not_nil) ∧
          closedCuspCount ω' c < closedCuspCount ωor c) :
    HasProperlyColoredCycle c ∨
      ∃ (ω' : G.Walk v v) (hcyc' : ω'.IsCycle),
        c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
            c.dartColor (ω'.lastDart hcyc'.not_nil) ∧
          closedCuspCount ω' c < closedCuspCount ω c := by
  rcases h with h | ⟨ω', hcyc', hn', hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨ω', hcyc', hn', hcount ▸ hlt⟩

lemma mem_takeUntil_of_mem_support_not_dropUntil {v u x : V} {ω : G.Walk v v}
    (hu : u ∈ ω.support) (hx : x ∈ ω.support)
    (hxD : x ∉ (ω.dropUntil u hu).support) :
    x ∈ (ω.takeUntil u hu).support := by
  have hx' : x ∈ ((ω.takeUntil u hu).append (ω.dropUntil u hu)).support := by
    simpa [Walk.take_spec ω hu] using hx
  rw [Walk.mem_support_append_iff] at hx'
  exact hx'.resolve_right hxD

lemma firstDart_takeUntil_color {u v w : V} {q : G.Walk u v} {α : C}
    (c : EdgeColoring G C) (hw : w ∈ q.support)
    (hnil : ¬ (q.takeUntil w hw).Nil)
    (hqnil : ¬ q.Nil)
    (hqfirst : c.dartColor (q.firstDart hqnil) ≠ α) :
    c.dartColor ((q.takeUntil w hw).firstDart hnil) ≠ α := by
  rw [firstDart_takeUntil hw hnil, firstDart_proof]
  exact hqfirst

/-- General FSCD Lemma 6: the detour may reenter anywhere on the old cycle.
First reentry, interior avoidance, and orientation are derived, then the
checked oriented body is applied. -/
theorem cusp_minimization {v u w : V} {α : C}
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
    (hw : w ∈ ω.support) :
    HasProperlyColoredCycle c ∨
      ∃ (ω' : G.Walk v v) (hcyc' : ω'.IsCycle),
        c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
            c.dartColor (ω'.lastDart hcyc'.not_nil) ∧
          closedCuspCount ω' c < closedCuspCount ω c := by
  have hne_uw : u ≠ w := mt (Walk.IsPath.nil_iff_eq hq).2 hqnil
  obtain ⟨x, hx, hxS, hnil, hxtail, hinter⟩ :=
    first_reentry_spec (q := q) hq hqnil hne_uw (S := ω.support) hw
  set q' := q.takeUntil x hx
  have hq' : q'.IsPath := hq.takeUntil hx
  have hq'0 : internalCuspCount q' c = 0 := internalCuspCount_takeUntil c hx hq0
  have hq'first : c.dartColor (q'.firstDart hnil) ≠ α :=
    firstDart_takeUntil_color c hx hnil hqnil hqfirst
  set β : C := c.dartColor (q'.lastDart hnil)
  have hinterω : ∀ y ∈ q'.support.tail, y ∈ ω.support → y = x := hinter
  have hne_xu : x ≠ u := by
    intro hxu
    subst hxu
    exact not_mem_support_tail_of_isPath hq hxtail
  have hcountR : closedCuspCount ω.reverse c = closedCuspCount ω c :=
    closedCuspCount_reverse ω c
  by_cases hxv : x = v
  · subst x
    rcases startColor_ne_or_reverse (ω := ω) c hcyc.not_nil hnocusp β with hstart | hstartR
    · have hwUV : v ∈ (ω.dropUntil u hu).support := Walk.end_mem_support _
      exact cusp_minimization_oriented (w := v) (β := β) ω c hcyc hnocusp hu hne_uv
        hcusp hq' hnil hq'0 hq'first rfl hwUV hinterω (fun _ => hstart.symm)
    · have hcycR : ω.reverse.IsCycle := hcyc.reverse
      have hnocuspR := nocusp_reverse (ω := ω) c hcyc.not_nil hnocusp
      have huR : u ∈ ω.reverse.support := by simp [Walk.support_reverse, hu]
      have hcuspR := cusp_at_reverse (ω := ω) (α := α) c hcyc hu hne_uv hcusp
      have hwUV : v ∈ (ω.reverse.dropUntil u huR).support := Walk.end_mem_support _
      have hinterR : ∀ y ∈ q'.support.tail, y ∈ ω.reverse.support → y = v := by
        intro y hy hyR
        exact hinterω y hy (mem_support_reverse_iff.1 hyR)
      refine or_min_of_eq_count (ωor := ω.reverse) c hcountR ?_
      exact cusp_minimization_oriented (w := v) (β := β) ω.reverse c hcycR hnocuspR
        huR hne_uv hcuspR hq' hnil hq'0 hq'first rfl hwUV hinterR (fun _ => hstartR.symm)
  · have hinterω' : ∀ y ∈ q'.support.tail, y ∈ ω.support → y = x := hinterω
    by_cases hxUV : x ∈ (ω.dropUntil u hu).support
    · refine cusp_minimization_oriented (w := x) (β := β) ω c hcyc hnocusp hu hne_uv
        hcusp hq' hnil hq'0 hq'first rfl hxUV hinterω' ?_
      intro hxeq
      exact (hxv hxeq).elim
    · have hxVU : x ∈ (ω.takeUntil u hu).support :=
        mem_takeUntil_of_mem_support_not_dropUntil hu hxS hxUV
      have hcycR : ω.reverse.IsCycle := hcyc.reverse
      have hnocuspR := nocusp_reverse (ω := ω) c hcyc.not_nil hnocusp
      have huR : u ∈ ω.reverse.support := by simp [Walk.support_reverse, hu]
      have hcuspR := cusp_at_reverse (ω := ω) (α := α) c hcyc hu hne_uv hcusp
      have hwUV : x ∈ (ω.reverse.dropUntil u huR).support := by
        have hdrop := dropUntil_reverse_eq (ω := ω) hcyc hu hne_uv
        simpa [hdrop, Walk.support_reverse] using hxVU
      have hinterR : ∀ y ∈ q'.support.tail, y ∈ ω.reverse.support → y = x := by
        intro y hy hyR
        exact hinterω' y hy (mem_support_reverse_iff.1 hyR)
      refine or_min_of_eq_count (ωor := ω.reverse) c hcountR ?_
      refine cusp_minimization_oriented (w := x) (β := β) ω.reverse c hcycR hnocuspR
        huR hne_uv hcuspR hq' hnil hq'0 hq'first rfl hwUV hinterR ?_
      intro hxeq
      exact (hxv hxeq).elim

lemma darts_takeUntil_getElem {u v w : V} {p : G.Walk u v}
    (hw : w ∈ p.support) {n : ℕ} (hn : n < (p.takeUntil w hw).length) :
    (p.takeUntil w hw).darts[n]'(by simpa [Walk.length_darts] using hn) =
      p.darts[n]'(by
        have := Walk.length_takeUntil_le_length p hw
        simpa [Walk.length_darts] using lt_of_lt_of_le hn this) := by
  have hpref := Walk.darts_takeUntil_prefix_darts p hw
  exact List.IsPrefix.getElem hpref (by simpa [Walk.length_darts] using hn)

lemma length_take_drop {u v w : V} (p : G.Walk u v) (hw : w ∈ p.support) :
    (p.takeUntil w hw).length + (p.dropUntil w hw).length = p.length := by
  rw [← Walk.length_append]
  exact congrArg Walk.length (Walk.take_spec p hw)

lemma zip_pair_eq {u v : V} {p : G.Walk u v} {j : ℕ}
    (hj : j + 1 < p.darts.length) :
    (p.darts.zip p.darts.tail)[j]'(by
        have := Walk.length_darts p
        simp [List.length_zip, List.length_tail, this]; omega) =
      (p.darts[j]'(Nat.lt_of_succ_lt hj), p.darts[j + 1]'hj) := by
  have hL := Walk.length_darts p
  have hz :
      (p.darts.zip p.darts.tail)[j]'(by
          simp [List.length_zip, List.length_tail, hL]; omega) =
        (p.darts[j]'(Nat.lt_of_succ_lt hj),
          p.darts.tail[j]'(by simp [List.length_tail, hL]; omega)) := by
    rw [List.getElem_zip]
  have htail :
      p.darts.tail[j]'(by simp [List.length_tail, hL]; omega) =
        p.darts[j + 1]'hj :=
    getElem_tail_eq p.darts j hj
  rw [hz, htail]

/-- A genuine no-wrap-cusp cycle of positive closed count has a first internal
equal-color dart pair. The `v`-to-`u` prefix is simple, nonnil and internally
cusp-free, and both cycle darts at `u` have that first cusp color. -/
theorem exists_first_internal_cusp {v : V} {ω : G.Walk v v}
    (c : EdgeColoring G C) (hcyc : ω.IsCycle)
    (hnocusp : c.dartColor (ω.firstDart hcyc.not_nil) ≠
      c.dartColor (ω.lastDart hcyc.not_nil))
    (hpos : 0 < closedCuspCount ω c) :
    ∃ (u : V) (hu : u ∈ ω.support) (hne : u ≠ v) (α : C),
      ¬ (ω.takeUntil u hu).Nil ∧
        internalCuspCount (ω.takeUntil u hu) c = 0 ∧
          c.dartColor ((ω.takeUntil u hu).firstDart (Walk.not_nil_of_ne hne.symm)) =
            c.dartColor (ω.firstDart hcyc.not_nil) ∧
            c.dartColor ((ω.takeUntil u hu).lastDart (Walk.not_nil_of_ne hne.symm)) = α ∧
              c.dartColor ((ω.dropUntil u hu).firstDart (Walk.not_nil_of_ne hne)) = α ∧
                α ∈ c.usedColors := by
  have hinterpos : 0 < internalCuspCount ω c := by
    rwa [closedCuspCount_eq_internal_of_nocusp c hcyc.not_nil hnocusp] at hpos
  let pred : G.Dart × G.Dart → Bool :=
    fun p => decide (c.dartColor p.1 = c.dartColor p.2)
  have hex : ∃ pair ∈ ω.darts.zip ω.darts.tail, pred pair = true := by
    have hne : ¬ ((ω.darts.zip ω.darts.tail).filter
        (fun p => c.dartColor p.1 = c.dartColor p.2)).length = 0 :=
      Nat.pos_iff_ne_zero.mp hinterpos
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hne
    push Not at hne
    obtain ⟨pair, hp, hcol⟩ := hne
    exact ⟨pair, hp, by simp [pred, hcol]⟩
  have hi : (ω.darts.zip ω.darts.tail).findIdx pred <
      (ω.darts.zip ω.darts.tail).length :=
    List.findIdx_lt_length_of_exists hex
  set i := (ω.darts.zip ω.darts.tail).findIdx pred
  have hlenω : 3 ≤ ω.length := hcyc.three_le_length
  have hzip_len : (ω.darts.zip ω.darts.tail).length = ω.length - 1 := by
    simp [List.length_zip, Walk.length_darts, List.length_tail]
  have hi_lt : i + 1 < ω.length := by
    have : i < ω.length - 1 := by
      simpa [hzip_len] using hi
    omega
  have hi_le : i + 1 ≤ ω.length := Nat.le_of_lt hi_lt
  have hpair :
      c.dartColor (ω.darts[i]'(by simp [Walk.length_darts]; omega)) =
        c.dartColor (ω.darts[i + 1]'(by simp [Walk.length_darts]; omega)) := by
    have hget := List.findIdx_getElem (xs := ω.darts.zip ω.darts.tail) (w := hi)
    have hz := zip_pair_eq (p := ω) (hj := by simp [Walk.length_darts]; omega)
    simpa [pred, hz, i] using of_decide_eq_true hget
  set u := ω.getVert (i + 1)
  have hu : u ∈ ω.support := Walk.getVert_mem_support ω (i + 1)
  have hne : u ≠ v := by
    intro heq
    have := (hcyc.getVert_endpoint_iff (i := i + 1) hi_le).1 heq
    omega
  have hidx : ω.support.idxOf u = i + 1 := by
    have hltS : i + 1 < ω.support.length := by
      simp [Walk.length_support]; omega
    have hgetS : ω.support[i + 1]'hltS = u :=
      Walk.support_getElem_eq_getVert ω hltS
    have huω : u ∈ ω.support := hu
    refine Nat.le_antisymm ?_ ?_
    · have hlen_take : i + 1 < (ω.support.take (i + 2)).length := by
        simp [List.length_take]; omega
      have hget_take : (ω.support.take (i + 2))[i + 1]'hlen_take = u := by
        rw [List.getElem_take, hgetS]
      have hmem_take : u ∈ ω.support.take (i + 2) := hget_take ▸ List.getElem_mem _
      exact Nat.lt_succ_iff.mp ((List.mem_take_iff_idxOf_lt huω).1 hmem_take)
    · by_contra hlt'
      have : ω.support.idxOf u < i + 1 := Nat.not_le.mp hlt'
      have hmem := (List.mem_take_iff_idxOf_lt huω).2 this
      obtain ⟨j, hj, hjget⟩ := List.mem_iff_getElem.1 hmem
      have hj_lt : j < i + 1 := by
        have : (ω.support.take (i + 1)).length = i + 1 := by
          simp [List.length_take, Walk.length_support]; omega
        simpa [this] using hj
      have hjS : j < ω.support.length := lt_trans hj_lt hltS
      have hju : ω.support[j]'hjS = u := by
        rwa [List.getElem_take] at hjget
      have hjle : j ≤ ω.length := by
        simp [Walk.length_support] at hjS; omega
      have hgetj : ω.getVert j = u := by
        rw [Walk.getVert_eq_support_getElem ω hjle, hju]
      have hj_eq : j = i + 1 :=
        hcyc.getVert_injOn' (by simp; omega) (by simp; omega) hgetj
      omega
  have hlen : (ω.takeUntil u hu).length = i + 1 := by
    rw [Walk.length_takeUntil, hidx]
  have hVUnil : ¬ (ω.takeUntil u hu).Nil := Walk.not_nil_of_ne hne.symm
  have hUVnil : ¬ (ω.dropUntil u hu).Nil := Walk.not_nil_of_ne hne
  have h0 : internalCuspCount (ω.takeUntil u hu) c = 0 := by
    rw [← isAlternating_iff_internalCuspCount_eq_zero]
    intro j hj
    have hj_lt : j < i := by
      simp [Walk.length_darts, hlen] at hj
      omega
    have hdj := darts_takeUntil_getElem (p := ω) hu
      (n := j) (by simp [Walk.length_darts, hlen] at hj ⊢; omega)
    have hdj1 := darts_takeUntil_getElem (p := ω) hu
      (n := j + 1) (by simp [Walk.length_darts, hlen] at hj ⊢; omega)
    have hfalse := List.not_of_lt_findIdx (p := pred)
      (xs := ω.darts.zip ω.darts.tail) hj_lt
    have hz := zip_pair_eq (p := ω) (hj := by simp [Walk.length_darts]; omega)
    rw [hdj, hdj1]
    have : pred ((ω.darts.zip ω.darts.tail)[j]'(by
        simp [List.length_zip, List.length_tail, Walk.length_darts]; omega)) = false :=
      hfalse
    simpa [pred, hz] using of_decide_eq_false this
  let αdef := c.dartColor (ω.darts[i]'(by simp [Walk.length_darts]; omega))
  refine ⟨u, hu, hne, αdef, hVUnil, h0, ?_, ?_, ?_,
    c.mem_usedColors_dartColor (ω.darts[i]'(by simp [Walk.length_darts]; omega))⟩
  · rw [firstDart_takeUntil hu (Walk.not_nil_of_ne hne.symm)]
  · apply c.dartColor_eq_of_edge
    have hpen : (ω.takeUntil u hu).penultimate = ω.getVert i := by
      simp [Walk.penultimate, hlen]
      exact Walk.getVert_takeUntil hu (by omega)
    simp [Walk.edge_lastDart, hpen, Walk.darts_getElem_eq_getVert]
    simp [u, Walk.getVert_length_takeUntil]
  · trans c.dartColor (ω.darts[i + 1]'(by simp [Walk.length_darts]; omega))
    · apply c.dartColor_eq_of_edge
      have hsnd : (ω.dropUntil u hu).snd = ω.getVert (i + 2) := by
        have hlt : ¬ i + 2 < (ω.takeUntil u hu).length := by omega
        have hget := Walk.getVert_append (ω.takeUntil u hu) (ω.dropUntil u hu) (i + 2)
        simp [hlt, hlen, Walk.take_spec] at hget
        simpa [Walk.snd] using hget.symm
      simp [Walk.edge_firstDart, hsnd, Walk.darts_getElem_eq_getVert]
      simp [u]
    · exact hpair.symm

lemma exists_nocusp_cycle_of_not_splitting (c : EdgeColoring G C) {v : V}
    (h : ¬ SplittingVertex c v) :
    ∃ (ω : G.Walk v v) (hcyc : ω.IsCycle),
      c.dartColor (ω.firstDart hcyc.not_nil) ≠
        c.dartColor (ω.lastDart hcyc.not_nil) := by
  have hcs : ¬ CycleSplittingVertex c v := by
    rwa [splittingVertex_iff_cycleSplittingVertex] at h
  have : ∃ (u : V) (w : G.Walk u u) (hcyc : w.IsCycle) (hv : v ∈ w.support),
      c.dartColor ((w.rotate v hv).firstDart (hcyc.rotate hv).not_nil) ≠
        c.dartColor ((w.rotate v hv).lastDart (hcyc.rotate hv).not_nil) := by
    by_contra hnone
    refine hcs ?_
    intro u w hcyc hv
    by_contra hne
    exact hnone ⟨u, w, hcyc, hv, hne⟩
  obtain ⟨_, w, hcyc, hv, hne⟩ := this
  exact ⟨w.rotate v hv, hcyc.rotate hv, hne⟩

lemma exists_min_nocusp_cycle (c : EdgeColoring G C) {v : V}
    (h : ∃ (ω : G.Walk v v) (hcyc : ω.IsCycle),
      c.dartColor (ω.firstDart hcyc.not_nil) ≠
        c.dartColor (ω.lastDart hcyc.not_nil)) :
    ∃ (ω : G.Walk v v) (hcyc : ω.IsCycle),
      c.dartColor (ω.firstDart hcyc.not_nil) ≠
          c.dartColor (ω.lastDart hcyc.not_nil) ∧
        ∀ (ω' : G.Walk v v) (hcyc' : ω'.IsCycle),
          c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
              c.dartColor (ω'.lastDart hcyc'.not_nil) →
            closedCuspCount ω c ≤ closedCuspCount ω' c := by
  let P : ℕ → Prop := fun n =>
    ∃ (ω : G.Walk v v) (hcyc : ω.IsCycle),
      c.dartColor (ω.firstDart hcyc.not_nil) ≠
          c.dartColor (ω.lastDart hcyc.not_nil) ∧
        closedCuspCount ω c = n
  have hP : ∃ n, P n := by
    obtain ⟨ω, hcyc, hn⟩ := h
    exact ⟨closedCuspCount ω c, ω, hcyc, hn, rfl⟩
  obtain ⟨ω, hcyc, hnocusp, hcount⟩ := Nat.find_spec hP
  refine ⟨ω, hcyc, hnocusp, ?_⟩
  intro ω' hcyc' hnocusp'
  have hnotlt : ¬ closedCuspCount ω' c < Nat.find hP := by
    intro hlt
    exact Nat.find_min hP hlt ⟨ω', hcyc', hnocusp', rfl⟩
  rw [hcount]
  exact Nat.le_of_not_gt hnotlt

lemma closedCuspCount_pos_of_noprop {v : V} {ω : G.Walk v v}
    (c : EdgeColoring G C) (hcyc : ω.IsCycle)
    (hnocusp : c.dartColor (ω.firstDart hcyc.not_nil) ≠
      c.dartColor (ω.lastDart hcyc.not_nil))
    (hnoprop : ¬ HasProperlyColoredCycle c) :
    0 < closedCuspCount ω c := by
  by_contra hle
  have h0 : closedCuspCount ω c = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hle)
  exact hnoprop ⟨v, ω,
    (isProperlyColored_iff_isCycle_closedCuspCount_eq_zero c).2 ⟨hcyc, h0⟩⟩

/-- FSCD Proposition 7: a nonsplitting vertex, in the absence of properly
colored genuine cycles, admits a strict `◁`-successor. -/
theorem exists_strict_of_nonsplitting (c : EdgeColoring G C) (v : V) (α : C)
    (hnoprop : ¬ HasProperlyColoredCycle c)
    (hns : ¬ SplittingVertex c v) :
    ∃ (u : V) (β : C), StrictCuspFreeReach c v u α β ∧ β ∈ c.usedColors := by
  obtain ⟨ω0, hcyc0, hn0⟩ := exists_nocusp_cycle_of_not_splitting c hns
  obtain ⟨ω1, hcyc1, hn1, hmin⟩ :=
    exists_min_nocusp_cycle c ⟨ω0, hcyc0, hn0⟩
  have growth (ω : G.Walk v v) (hcyc : ω.IsCycle)
      (hnocusp : c.dartColor (ω.firstDart hcyc.not_nil) ≠
        c.dartColor (ω.lastDart hcyc.not_nil))
      (hstart : c.dartColor (ω.firstDart hcyc.not_nil) ≠ α)
      (hminω : ∀ (ω' : G.Walk v v) (hcyc' : ω'.IsCycle),
        c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
            c.dartColor (ω'.lastDart hcyc'.not_nil) →
          closedCuspCount ω c ≤ closedCuspCount ω' c) :
      ∃ (u : V) (β : C), StrictCuspFreeReach c v u α β ∧ β ∈ c.usedColors := by
    have hpos := closedCuspCount_pos_of_noprop c hcyc hnocusp hnoprop
    obtain ⟨u, hu, hne, β, hVUnil, h0, hfirst, hlast, hdrop, hβused⟩ :=
      exists_first_internal_cusp c hcyc hnocusp hpos
    have hpfirst :
        c.dartColor ((ω.takeUntil u hu).firstDart hVUnil) ≠ α := by
      rw [hfirst]; exact hstart
    refine ⟨u, β,
      ⟨ω.takeUntil u hu, hcyc.isPath_takeUntil hu, hVUnil, h0, hpfirst, hlast, ?_⟩,
      hβused⟩
    intro w q hq hqnil hq0 hqfirst hw
    have hwω : w ∈ ω.support := mem_support_of_mem_takeUntil hu hw
    have halt := cusp_minimization (v := v) (u := u) (w := w) (α := β) ω c
      hcyc hnocusp hu hne ⟨hlast, hdrop⟩ hq hqnil hq0 hqfirst hwω
    rcases halt with hprop | ⟨ω', hcyc', hn', hlt⟩
    · exact hnoprop hprop
    · exact (not_le_of_gt hlt) (hminω ω' hcyc' hn')
  rcases startColor_ne_or_reverse (ω := ω1) c hcyc1.not_nil hn1 α with hα | hαR
  · exact growth ω1 hcyc1 hn1 hα hmin
  · have hcycR : ω1.reverse.IsCycle := hcyc1.reverse
    have hnR := nocusp_reverse (ω := ω1) c hcyc1.not_nil hn1
    have hminR : ∀ (ω' : G.Walk v v) (hcyc' : ω'.IsCycle),
        c.dartColor (ω'.firstDart hcyc'.not_nil) ≠
            c.dartColor (ω'.lastDart hcyc'.not_nil) →
          closedCuspCount ω1.reverse c ≤ closedCuspCount ω' c := by
      intro ω' hcyc' hn'
      simpa [closedCuspCount_reverse] using hmin ω' hcyc' hn'
    exact growth ω1.reverse hcycR hnR hαR hminR

/-- Yeo's separator theorem for ordinary symmetric colorings of a nonempty
finite simple graph, with an unrestricted palette. The only hypothesis is
the absence of a properly colored genuine simple cycle. -/
theorem yeo_separator (c : EdgeColoring G C) [Nonempty V]
    (h : ¬ HasProperlyColoredCycle c) :
    ∃ v : V, SplittingVertex c v := by
  rcases c.usedColors.eq_empty_or_nonempty with hempty | hne
  · exact yeo_separator_of_usedColors_empty c hempty
  · obtain ⟨m, hmax⟩ := exists_usedLt_maximal c hne
    refine ⟨m.1, ?_⟩
    by_contra hns
    obtain ⟨u, β, hstrict, hβ⟩ :=
      exists_strict_of_nonsplitting c m.1 m.2.1 h hns
    exact hmax (u, ⟨β, hβ⟩) hstrict

end Yeo
end Nikoghosyan
