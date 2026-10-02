/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Mathlib.Data.Finset.Max
import Nikoghosyan.Prerequisites.Yeo

/-!
Cusp-count calculus and the FSCD vertex-color strict order.

Closed order milestone: `internalCuspCount = 0` iff `IsAlternating`, the
append seam formula, reverse invariance, the strict append of an ordinary
`↱`-step after a `◁`-step, transitivity of `usedLt`, and a `usedLt`-maximal
used pair when `usedColors` is nonempty.

Source: Di Guardia–Laurent–Tortora de Falco–Vaux Auclair, FSCD 2025,
Lemmas 4–5.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Function SimpleGraph

namespace List

variable {α : Type*}

/-- Consecutive pairs of a concatenation of two nonempty lists are the
consecutive pairs of each list together with the single seam pair. -/
theorem zip_tail_append :
    ∀ (l₁ l₂ : List α) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
      (l₁ ++ l₂).zip (l₁ ++ l₂).tail =
        l₁.zip l₁.tail ++ [(l₁.getLast h₁, l₂.head h₂)] ++ l₂.zip l₂.tail
  | [], _, h₁, _ => (h₁ rfl).elim
  | _ :: _, [], _, h₂ => (h₂ rfl).elim
  | [x], y :: ys, _, _ => by simp
  | x :: x' :: xs, l₂, h₁, h₂ => by
      have ih := zip_tail_append (x' :: xs) l₂ (cons_ne_nil _ _) h₂
      calc
        (x :: x' :: xs ++ l₂).zip (x :: x' :: xs ++ l₂).tail
            = (x :: (x' :: xs ++ l₂)).zip (x' :: xs ++ l₂) := by simp
        _ = (x, x') :: (x' :: xs ++ l₂).zip (x' :: xs ++ l₂).tail := by
            simp [zip_cons_cons]
        _ = (x, x') ::
              ((x' :: xs).zip (x' :: xs).tail ++
                [((x' :: xs).getLast (cons_ne_nil _ _), l₂.head h₂)] ++
                  l₂.zip l₂.tail) := by
            rw [ih]
        _ = (x :: x' :: xs).zip (x' :: xs) ++
              [((x :: x' :: xs).getLast h₁, l₂.head h₂)] ++
                l₂.zip l₂.tail := by
            simp [zip_cons_cons, getLast_cons]

theorem mem_zip_tail_append_left {l₁ l₂ : List α} {a : α × α}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (ha : a ∈ l₁.zip l₁.tail) :
    a ∈ (l₁ ++ l₂).zip (l₁ ++ l₂).tail := by
  rw [zip_tail_append l₁ l₂ h₁ h₂]
  simp [ha]

theorem mem_zip_tail_append_right {l₁ l₂ : List α} {a : α × α}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (ha : a ∈ l₂.zip l₂.tail) :
    a ∈ (l₁ ++ l₂).zip (l₁ ++ l₂).tail := by
  rw [zip_tail_append l₁ l₂ h₁ h₂]
  simp [ha]

theorem zip_tail_subset_of_prefix {l m : List α} (h : l <+: m) :
    l.zip l.tail ⊆ m.zip m.tail := by
  obtain ⟨t, rfl⟩ := h
  intro a ha
  match l, t with
  | [], _ => simp at ha
  | _ :: _, [] => simpa using ha
  | x :: xs, y :: ys =>
    exact mem_zip_tail_append_left (cons_ne_nil _ _) (cons_ne_nil _ _) ha

theorem zip_tail_subset_of_suffix {l m : List α} (h : l <:+ m) :
    l.zip l.tail ⊆ m.zip m.tail := by
  obtain ⟨t, rfl⟩ := h
  intro a ha
  match t, l with
  | [], _ => simpa using ha
  | _ :: _, [] => simp at ha
  | y :: ys, x :: xs =>
    exact mem_zip_tail_append_right (cons_ne_nil _ _) (cons_ne_nil _ _) ha

theorem zip_tail_reverse :
    ∀ l : List α,
      l.reverse.zip l.reverse.tail = (l.zip l.tail).reverse.map Prod.swap
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
      have ih := zip_tail_reverse (b :: l)
      have hrev : (b :: l).reverse ≠ [] := by simp
      have ha : [a] ≠ [] := cons_ne_nil _ _
      rw [reverse_cons, zip_tail_append (b :: l).reverse [a] hrev ha, ih]
      simp [zip_cons_cons, reverse_cons, map_append, Prod.swap]

theorem zip_tail_map {β : Type*} (f : α → β) :
    ∀ l : List α,
      (l.map f).zip (l.map f).tail = (l.zip l.tail).map (Prod.map f f)
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
      have ih := zip_tail_map f (b :: l)
      simpa [zip_cons_cons, Prod.map] using
        congrArg (fun t => (f a, f b) :: t) ih

theorem head_eq_of_eq {l₁ l₂ : List α} (h : l₁ = l₂) {h₁ : l₁ ≠ []} {h₂ : l₂ ≠ []} :
    l₁.head h₁ = l₂.head h₂ := by
  subst h
  rfl

theorem getLast_eq_of_eq {l₁ l₂ : List α} (h : l₁ = l₂) {h₁ : l₁ ≠ []} {h₂ : l₂ ≠ []} :
    l₁.getLast h₁ = l₂.getLast h₂ := by
  subst h
  rfl

end List

namespace Nikoghosyan
namespace Yeo

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [DecidableEq C]
variable {G : SimpleGraph V}

lemma isPath_append {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ x ∈ q.support.tail, x ∉ p.support) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  refine List.Nodup.append hp.support_nodup hq.support_nodup.tail ?_
  intro x hxP hxQ
  exact hdisj x hxQ hxP

lemma not_nil_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hq : ¬ q.Nil) : ¬ (p.append q).Nil := by
  cases q with
  | nil => exact (hq Walk.nil_nil).elim
  | cons h q' =>
    cases p <;> simp

lemma firstDart_append_of_not_nil_left {u v w : V} {p : G.Walk u v}
    {q : G.Walk v w} (hp : ¬ p.Nil) (h : ¬ (p.append q).Nil) :
    (p.append q).firstDart h = p.firstDart hp := by
  apply Dart.ext
  cases p with
  | nil => exact (hp Walk.nil_nil).elim
  | cons hadj p' =>
    simp [Walk.firstDart]

lemma penultimate_append_of_not_nil_right {u v w : V} {p : G.Walk u v}
    {q : G.Walk v w} (hq : ¬ q.Nil) :
    (p.append q).penultimate = q.penultimate := by
  have hqpos : 0 < q.length := Walk.not_nil_iff_lt_length.1 hq
  simp [Walk.penultimate, Walk.getVert_append, Walk.length_append]
  split_ifs with hlt
  · omega
  · congr 1
    omega

lemma lastDart_append_of_not_nil_right {u v w : V} {p : G.Walk u v}
    {q : G.Walk v w} (hq : ¬ q.Nil) (h : ¬ (p.append q).Nil) :
    (p.append q).lastDart h = q.lastDart hq := by
  apply Dart.ext
  simp [Walk.lastDart, penultimate_append_of_not_nil_right hq]

lemma darts_ne_nil {u v : V} {p : G.Walk u v} (h : ¬ p.Nil) : p.darts ≠ [] :=
  Walk.darts_eq_nil.not.mpr h

lemma firstDart_proof {u v : V} {p : G.Walk u v} (h h' : ¬ p.Nil) :
    p.firstDart h = p.firstDart h' := by
  apply Dart.ext
  rfl

lemma lastDart_proof {u v : V} {p : G.Walk u v} (h h' : ¬ p.Nil) :
    p.lastDart h = p.lastDart h' := by
  apply Dart.ext
  rfl

lemma length_zip_tail {α : Type*} (l : List α) :
    (l.zip l.tail).length = l.length - 1 := by
  cases l <;> simp [List.length_zip]

lemma getElem_tail_eq {α : Type*} (l : List α) (i : ℕ)
    (hi : i + 1 < l.length) :
    l.tail[i]'(by simp [List.length_tail]; omega) = l[i + 1]'hi := by
  cases l with
  | nil => simp at hi
  | cons a as => rfl

lemma getElem_mem_zip_tail {α : Type*} (l : List α) (i : ℕ)
    (hi : i + 1 < l.length) :
    (l[i]'(Nat.lt_of_succ_lt hi), l[i + 1]'hi) ∈ l.zip l.tail := by
  have hlen : i < (l.zip l.tail).length := by
    rw [length_zip_tail]
    omega
  have hget : (l.zip l.tail)[i] = (l[i]'(Nat.lt_of_succ_lt hi), l[i + 1]'hi) := by
    rw [List.getElem_zip]
    congr 1
    exact getElem_tail_eq l i hi
  exact hget ▸ List.getElem_mem _

lemma isAlternating_iff_internalCuspCount_eq_zero {u v : V}
    (w : G.Walk u v) (c : EdgeColoring G C) :
    IsAlternating w c ↔ internalCuspCount w c = 0 := by
  constructor
  · intro halt
    unfold internalCuspCount IsAlternating at *
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
    have hlen : i + 1 < w.darts.length := by
      have : i < w.darts.length - 1 := by
        simpa [length_zip_tail] using hi
      omega
    have hpair :
        (w.darts.zip w.darts.tail)[i] =
          (w.darts[i]'(Nat.lt_of_succ_lt hlen), w.darts[i + 1]'hlen) := by
      rw [List.getElem_zip]
      congr 1
      exact getElem_tail_eq w.darts i hlen
    have := halt i hlen
    simpa [hpair] using this
  · intro h0 i hi
    unfold internalCuspCount at h0
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
    have := h0 _ (getElem_mem_zip_tail w.darts i hi)
    simpa using this

lemma internalCuspCount_eq_zero_of_darts_prefix {u v u' v' : V}
    {p : G.Walk u v} {q : G.Walk u' v'} (c : EdgeColoring G C)
    (h : p.darts <+: q.darts) (hq : internalCuspCount q c = 0) :
    internalCuspCount p c = 0 := by
  unfold internalCuspCount at *
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hq ⊢
  intro pair hp
  exact hq pair (List.zip_tail_subset_of_prefix h hp)

lemma internalCuspCount_eq_zero_of_darts_suffix {u v u' v' : V}
    {p : G.Walk u v} {q : G.Walk u' v'} (c : EdgeColoring G C)
    (h : p.darts <:+ q.darts) (hq : internalCuspCount q c = 0) :
    internalCuspCount p c = 0 := by
  unfold internalCuspCount at *
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hq ⊢
  intro pair hp
  exact hq pair (List.zip_tail_subset_of_suffix h hp)

lemma internalCuspCount_takeUntil {u v w : V} {p : G.Walk u v}
    (c : EdgeColoring G C) (hw : w ∈ p.support)
    (hp : internalCuspCount p c = 0) :
    internalCuspCount (p.takeUntil w hw) c = 0 :=
  internalCuspCount_eq_zero_of_darts_prefix c
    (Walk.darts_takeUntil_prefix_darts p hw) hp

lemma internalCuspCount_dropUntil {u v w : V} {p : G.Walk u v}
    (c : EdgeColoring G C) (hw : w ∈ p.support)
    (hp : internalCuspCount p c = 0) :
    internalCuspCount (p.dropUntil w hw) c = 0 :=
  internalCuspCount_eq_zero_of_darts_suffix c
    (Walk.darts_dropUntil_suffix_darts p hw) hp

lemma firstDart_of_darts_prefix {u v u' v' : V} {p : G.Walk u v}
    {q : G.Walk u' v'} (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (h : p.darts <+: q.darts) :
    p.firstDart hp = q.firstDart hq := by
  rw [Walk.firstDart_eq_head_darts, Walk.firstDart_eq_head_darts]
  obtain ⟨t, ht⟩ := h
  have hp' := darts_ne_nil hp
  have hq' := darts_ne_nil hq
  have : q.darts.head hq' = (p.darts ++ t).head (by simp [hp']) :=
    List.head_eq_of_eq ht.symm
  rw [this, List.head_append_of_ne_nil hp']

lemma not_nil_of_not_nil_takeUntil {u v w : V} {p : G.Walk u v}
    {hw : w ∈ p.support} (h : ¬ (p.takeUntil w hw).Nil) : ¬ p.Nil := by
  intro hp
  cases p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst w
    exact h (by simp)
  | cons _ _ =>
    exact (Walk.not_nil_cons hp).elim

lemma firstDart_takeUntil {u v w : V} {p : G.Walk u v}
    (hw : w ∈ p.support) (h : ¬ (p.takeUntil w hw).Nil) :
    (p.takeUntil w hw).firstDart h =
      p.firstDart (not_nil_of_not_nil_takeUntil h) :=
  firstDart_of_darts_prefix h _ (Walk.darts_takeUntil_prefix_darts p hw)

lemma lastDart_of_darts_suffix {u v u' v' : V} {p : G.Walk u v}
    {q : G.Walk u' v'} (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (h : p.darts <:+ q.darts) :
    p.lastDart hp = q.lastDart hq := by
  rw [Walk.lastDart_eq_getLast_darts, Walk.lastDart_eq_getLast_darts]
  obtain ⟨t, ht⟩ := h
  have hp' := darts_ne_nil hp
  have hq' := darts_ne_nil hq
  have : q.darts.getLast hq' = (t ++ p.darts).getLast (by simp [hp']) :=
    List.getLast_eq_of_eq ht.symm
  rw [this, List.getLast_append_of_ne_nil (l := t) (by simp [hp']) hp']

lemma not_nil_of_not_nil_dropUntil {u v w : V} {p : G.Walk u v}
    {hw : w ∈ p.support} (h : ¬ (p.dropUntil w hw).Nil) : ¬ p.Nil := by
  intro hp
  cases p with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst w
    exact h (by simp)
  | cons _ _ =>
    exact (Walk.not_nil_cons hp).elim

lemma lastDart_dropUntil {u v w : V} {p : G.Walk u v}
    (hw : w ∈ p.support) (h : ¬ (p.dropUntil w hw).Nil) :
    (p.dropUntil w hw).lastDart h =
      p.lastDart (not_nil_of_not_nil_dropUntil h) :=
  lastDart_of_darts_suffix h _ (Walk.darts_dropUntil_suffix_darts p hw)

/-- Seam indicator: 1 when the last dart of `p` and the first dart of `q`
have the same color. -/
def seamCusp (c : EdgeColoring G C) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hp : ¬ p.Nil) (hq : ¬ q.Nil) : ℕ :=
  if c.dartColor (p.lastDart hp) = c.dartColor (q.firstDart hq) then 1 else 0

theorem internalCuspCount_append {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (c : EdgeColoring G C) (hp : ¬ p.Nil) (hq : ¬ q.Nil) :
    internalCuspCount (p.append q) c =
      internalCuspCount p c + internalCuspCount q c + seamCusp c p q hp hq := by
  unfold internalCuspCount
  have hzip :
      (p.append q).darts.zip (p.append q).darts.tail =
        p.darts.zip p.darts.tail ++
          [(p.lastDart hp, q.firstDart hq)] ++
            q.darts.zip q.darts.tail := by
    simp only [Walk.darts_append]
    rw [List.zip_tail_append p.darts q.darts (darts_ne_nil hp) (darts_ne_nil hq),
      Walk.lastDart_eq_getLast_darts, Walk.firstDart_eq_head_darts]
  have hseam :
      ([(p.lastDart hp, q.firstDart hq)].filter
          (fun r => c.dartColor r.1 = c.dartColor r.2)).length =
        seamCusp c p q hp hq := by
    unfold seamCusp
    by_cases hcol : c.dartColor (p.lastDart hp) = c.dartColor (q.firstDart hq)
    · simp [hcol]
    · simp [hcol]
  rw [hzip, List.filter_append, List.filter_append, List.length_append,
    List.length_append, hseam]
  omega

lemma internalCuspCount_append_eq_zero {u v w : V} {p : G.Walk u v}
    {q : G.Walk v w} (c : EdgeColoring G C) (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hp0 : internalCuspCount p c = 0) (hq0 : internalCuspCount q c = 0)
    (hseam : c.dartColor (p.lastDart hp) ≠ c.dartColor (q.firstDart hq)) :
    internalCuspCount (p.append q) c = 0 := by
  rw [internalCuspCount_append c hp hq]
  unfold seamCusp
  simp [hp0, hq0, hseam]

lemma not_nil_reverse {u v : V} {p : G.Walk u v} (h : ¬ p.Nil) :
    ¬ p.reverse.Nil := by
  rw [Walk.nil_reverse]
  exact h

lemma firstDart_reverse {u v : V} {p : G.Walk u v} (h : ¬ p.Nil)
    (hrev : ¬ p.reverse.Nil) :
    p.reverse.firstDart hrev = (p.lastDart h).symm := by
  rw [Walk.firstDart_eq_head_darts, Walk.lastDart_eq_getLast_darts]
  have hp' := darts_ne_nil h
  have hmap : (p.darts.map Dart.symm).reverse ≠ [] := by simp [hp']
  refine (List.head_eq_of_eq (Walk.darts_reverse p) (h₂ := hmap)).trans ?_
  simp [List.head_reverse, List.getLast_map]

lemma lastDart_reverse {u v : V} {p : G.Walk u v} (h : ¬ p.Nil)
    (hrev : ¬ p.reverse.Nil) :
    p.reverse.lastDart hrev = (p.firstDart h).symm := by
  rw [Walk.lastDart_eq_getLast_darts, Walk.firstDart_eq_head_darts]
  have hp' := darts_ne_nil h
  have hmap : (p.darts.map Dart.symm).reverse ≠ [] := by simp [hp']
  refine (List.getLast_eq_of_eq (Walk.darts_reverse p) (h₂ := hmap)).trans ?_
  simp [List.getLast_reverse, List.head_map]

theorem internalCuspCount_reverse {u v : V} (p : G.Walk u v)
    (c : EdgeColoring G C) :
    internalCuspCount p.reverse c = internalCuspCount p c := by
  unfold internalCuspCount
  rw [Walk.darts_reverse, List.zip_tail_reverse, List.zip_tail_map,
    List.map_reverse, List.map_map, List.filter_reverse, List.filter_map,
    List.length_reverse, List.length_map]
  congr 1
  refine List.filter_congr ?_
  intro q _hq
  simp [EdgeColoring.dartColor_symm, eq_comm, Function.comp, Prod.map]

theorem closedCuspCount_reverse {u : V} (p : G.Walk u u) (c : EdgeColoring G C) :
    closedCuspCount p.reverse c = closedCuspCount p c := by
  unfold closedCuspCount
  rw [internalCuspCount_reverse]
  by_cases hnil : p.Nil
  · have : p.reverse.Nil := Walk.nil_reverse.2 hnil
    simp [hnil, this]
  · have hrev : ¬ p.reverse.Nil := not_nil_reverse hnil
    simp [hnil, hrev, firstDart_reverse hnil hrev, lastDart_reverse hnil hrev,
      EdgeColoring.dartColor_symm, eq_comm]

lemma not_mem_support_tail_of_isPath {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) : u ∉ p.support.tail := by
  cases p with
  | nil => simp
  | cons h q =>
    rw [Walk.isPath_def, Walk.support_cons, List.nodup_cons] at hp
    exact hp.1

lemma not_nil_takeUntil_of_mem_tail {u v w : V} {p : G.Walk u v}
    (hp : p.IsPath) (hw : w ∈ p.support.tail) :
    ¬ (p.takeUntil w (List.mem_of_mem_tail hw)).Nil := by
  intro hnil
  have : u = w := (Walk.nil_takeUntil p _).1 hnil
  subst this
  exact not_mem_support_tail_of_isPath hp hw

lemma support_tail_disjoint_of_strict {c : EdgeColoring G C} {v u w : V}
    {β : C} {p : G.Walk v u} (_hp : p.IsPath) (_hpnil : ¬ p.Nil)
    (hstrict : ∀ {x : V} (r : G.Walk u x) (_hr : r.IsPath) (hrnil : ¬ r.Nil),
      internalCuspCount r c = 0 →
        c.dartColor (r.firstDart hrnil) ≠ β →
          x ∉ p.support)
    {q : G.Walk u w} (hq : q.IsPath) (hqnil : ¬ q.Nil)
    (hq0 : internalCuspCount q c = 0)
    (hqfirst : c.dartColor (q.firstDart hqnil) ≠ β) :
    ∀ x ∈ q.support.tail, x ∉ p.support := by
  intro x hx
  have hxmem : x ∈ q.support := List.mem_of_mem_tail hx
  have hqxnil : ¬ (q.takeUntil x hxmem).Nil :=
    not_nil_takeUntil_of_mem_tail hq hx
  have hqx0 : internalCuspCount (q.takeUntil x hxmem) c = 0 :=
    internalCuspCount_takeUntil c hxmem hq0
  have hqxfirst :
      c.dartColor ((q.takeUntil x hxmem).firstDart hqxnil) ≠ β := by
    rw [firstDart_takeUntil hxmem hqxnil, firstDart_proof]
    exact hqfirst
  exact hstrict (q.takeUntil x hxmem) (hq.takeUntil hxmem) hqxnil hqx0 hqxfirst

lemma append_of_strict_ordinary {c : EdgeColoring G C} {v u w : V}
    {α β τ : C} {p : G.Walk v u} (hp : p.IsPath) (hpnil : ¬ p.Nil)
    (hp0 : internalCuspCount p c = 0)
    (hpfirst : c.dartColor (p.firstDart hpnil) ≠ α)
    (hplast : c.dartColor (p.lastDart hpnil) = β)
    (hstrict : ∀ {x : V} (r : G.Walk u x) (_hr : r.IsPath) (hrnil : ¬ r.Nil),
      internalCuspCount r c = 0 →
        c.dartColor (r.firstDart hrnil) ≠ β →
          x ∉ p.support)
    {q : G.Walk u w} (hq : q.IsPath) (hqnil : ¬ q.Nil)
    (hq0 : internalCuspCount q c = 0)
    (hqfirst : c.dartColor (q.firstDart hqnil) ≠ β)
    (hqlast : c.dartColor (q.lastDart hqnil) = τ) :
    (p.append q).IsPath ∧
      ¬ (p.append q).Nil ∧
        internalCuspCount (p.append q) c = 0 ∧
          c.dartColor ((p.append q).firstDart (not_nil_append_right hqnil)) ≠ α ∧
            c.dartColor ((p.append q).lastDart (not_nil_append_right hqnil)) = τ := by
  have hdisj :=
    support_tail_disjoint_of_strict hp hpnil hstrict hq hqnil hq0 hqfirst
  refine ⟨isPath_append hp hq hdisj, not_nil_append_right hqnil, ?_, ?_, ?_⟩
  · refine internalCuspCount_append_eq_zero c hpnil hqnil hp0 hq0 ?_
    exact Ne.symm (hplast ▸ hqfirst)
  · rw [firstDart_append_of_not_nil_left hpnil]
    exact hpfirst
  · rw [lastDart_append_of_not_nil_right hqnil]
    exact hqlast

lemma CuspFreeReach.append_of_strict {c : EdgeColoring G C} {v u w : V}
    {α β τ : C} (hp : StrictCuspFreeReach c v u α β)
    (hq : CuspFreeReach c u w β τ) :
    CuspFreeReach c v w α τ := by
  obtain ⟨p, hpPath, hpnil, hp0, hpfirst, hplast, hpstrict⟩ := hp
  obtain ⟨q, hqPath, hqnil, hq0, hqfirst, hqlast⟩ := hq
  obtain ⟨hpath, hnil, h0, hfirst, hlast⟩ :=
    append_of_strict_ordinary hpPath hpnil hp0 hpfirst hplast hpstrict
      hqPath hqnil hq0 hqfirst hqlast
  exact ⟨p.append q, hpath, hnil, h0, hfirst, hlast⟩

theorem StrictCuspFreeReach.trans {c : EdgeColoring G C} {v u w : V}
    {α β τ : C} (hp : StrictCuspFreeReach c v u α β)
    (hq : StrictCuspFreeReach c u w β τ) :
    StrictCuspFreeReach c v w α τ := by
  obtain ⟨p, hpPath, hpnil, hp0, hpfirst, hplast, hpstrict⟩ := hp
  obtain ⟨q, hqPath, hqnil, hq0, hqfirst, hqlast, hqstrict⟩ := hq
  obtain ⟨hpath, hnil, h0, hfirst, hlast⟩ :=
    append_of_strict_ordinary hpPath hpnil hp0 hpfirst hplast hpstrict
      hqPath hqnil hq0 hqfirst hqlast
  refine ⟨p.append q, hpath, hnil, h0, hfirst, hlast, ?_⟩
  intro z r hrPath hrnil hr0 hrfirst hz
  rw [Walk.mem_support_append_iff] at hz
  obtain ⟨qrPath, qrNil, qr0, qrFirst, _⟩ :=
    append_of_strict_ordinary hqPath hqnil hq0 hqfirst hqlast hqstrict
      hrPath hrnil hr0 hrfirst rfl
  have hz_not_p : z ∉ p.support :=
    hpstrict (q.append r) qrPath qrNil qr0 qrFirst
  have hz_not_q : z ∉ q.support :=
    hqstrict r hrPath hrnil hr0 hrfirst
  exact hz.elim hz_not_p hz_not_q

theorem usedLt_trans (c : EdgeColoring G C) {x y z : UsedPair c}
    (hxy : usedLt c x y) (hyz : usedLt c y z) : usedLt c x z :=
  StrictCuspFreeReach.trans hxy hyz

/-- A nonempty finite used-pair carrier admits a `◁`-maximal element.
The successor-count is minimized: a successor would strictly decrease it. -/
theorem exists_usedLt_maximal (c : EdgeColoring G C) [Nonempty V]
    (hne : c.usedColors.Nonempty) :
    ∃ m : UsedPair c, ∀ a, ¬ usedLt c m a := by
  haveI : Nonempty (UsedPair c) := UsedPair.nonempty c hne
  obtain ⟨m, -, hm⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (UsedPair c))
      (fun x =>
        (Finset.univ : Finset (UsedPair c)).card -
          (Finset.univ.filter (fun y => usedLt c x y)).card)
      Finset.univ_nonempty
  refine ⟨m, ?_⟩
  intro a hma
  have hss :
      (Finset.univ.filter (fun y => usedLt c a y)) ⊂
        (Finset.univ.filter (fun y => usedLt c m y)) := by
    rw [Finset.ssubset_def]
    constructor
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact usedLt_trans c hma hy
    · intro hsub
      have ha : a ∈ Finset.univ.filter (fun y => usedLt c m y) := by
        simp [hma]
      have : a ∈ Finset.univ.filter (fun y => usedLt c a y) := hsub ha
      simp [usedLt_irrefl c a] at this
  have hlt :
      (Finset.univ.filter (fun y => usedLt c a y)).card <
        (Finset.univ.filter (fun y => usedLt c m y)).card :=
    Finset.card_lt_card hss
  have hle := hm a (Finset.mem_univ a)
  have : (Finset.univ : Finset (UsedPair c)).card -
        (Finset.univ.filter (fun y => usedLt c m y)).card <
      (Finset.univ : Finset (UsedPair c)).card -
        (Finset.univ.filter (fun y => usedLt c a y)).card := by
    have hltU :
        (Finset.univ.filter (fun y => usedLt c a y)).card <
          (Finset.univ : Finset (UsedPair c)).card :=
      lt_of_lt_of_le hlt (Finset.card_le_univ _)
    exact Nat.sub_lt_sub_left hltU hlt
  exact (not_le_of_gt this) hle

end Yeo
end Nikoghosyan
