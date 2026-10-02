/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Prerequisites.YeoDefs

/-!
Cycle-to-component splitting equivalence for unrestricted edge colorings.
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

/-- Lift a walk of `G - v` to an original-edge walk of `G`. -/
def liftDeleteWalk {v : V} {x y : {w : V // w ≠ v}}
    (p : (deleteGraph G v).Walk x y) : G.Walk x.1 y.1 :=
  p.map (Embedding.induce (G := G) (deleteSet v)).toHom

lemma liftDeleteWalk_isPath {v : V} {x y : {w : V // w ≠ v}}
    {p : (deleteGraph G v).Walk x y} (hp : p.IsPath) :
    (liftDeleteWalk p).IsPath :=
  hp.map (Embedding.induce (G := G) (deleteSet v)).injective

lemma not_mem_support_liftDeleteWalk {v : V} {x y : {w : V // w ≠ v}}
    (p : (deleteGraph G v).Walk x y) : v ∉ (liftDeleteWalk p).support := by
  intro hv
  change v ∈
      (p.map (Embedding.induce (G := G) (deleteSet v)).toHom).support at hv
  rw [Walk.support_map, List.mem_map] at hv
  obtain ⟨z, _, hz⟩ := hv
  exact z.property hz

/-- The simple cycle `v — x — (G-v path) — y — v`. -/
def cycleThroughVertex {v : V} {x y : {w : V // w ≠ v}}
    (hx : G.Adj v x.1) (hy : G.Adj v y.1)
    (p : G.Walk x.1 y.1) : G.Walk v v :=
  Walk.cons hx (p.concat hy.symm)

lemma not_nil_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    ¬ (p.concat h).Nil := by
  cases p <;> simp [Walk.concat]

lemma penultimate_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).penultimate = v := by
  simp [Walk.penultimate, Walk.concat_eq_append, Walk.getVert_append']

lemma cycleThroughVertex_isCycle {v : V} {x y : {w : V // w ≠ v}}
    (hx : G.Adj v x.1) (hy : G.Adj v y.1)
    {p : G.Walk x.1 y.1} (hp : p.IsPath) (hv : v ∉ p.support) (hne : x.1 ≠ y.1) :
    (cycleThroughVertex hx hy p).IsCycle := by
  rw [cycleThroughVertex, Walk.cons_isCycle_iff]
  refine ⟨hp.concat hv hy.symm, ?_⟩
  intro he
  rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
  rcases he with hp' | heq
  · exact hv (p.fst_mem_support_of_mem_edges hp')
  · rcases (Sym2.eq_iff).1 heq with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact x.property h2
    · exact hne h2

lemma cycleThroughVertex_firstDart {v : V} {x y : {w : V // w ≠ v}}
    (hx : G.Adj v x.1) (hy : G.Adj v y.1) (p : G.Walk x.1 y.1)
    (h : ¬ (cycleThroughVertex hx hy p).Nil) :
    (cycleThroughVertex hx hy p).firstDart h = ⟨(v, x.1), hx⟩ := by
  apply Dart.ext
  simp [Walk.firstDart, cycleThroughVertex]

lemma cycleThroughVertex_lastDart {v : V} {x y : {w : V // w ≠ v}}
    (hx : G.Adj v x.1) (hy : G.Adj v y.1) (p : G.Walk x.1 y.1)
    (h : ¬ (cycleThroughVertex hx hy p).Nil) :
    (cycleThroughVertex hx hy p).lastDart h = ⟨(y.1, v), hy.symm⟩ := by
  have hq : ¬ (p.concat hy.symm).Nil := not_nil_concat p hy.symm
  have hpen : (cycleThroughVertex hx hy p).penultimate = y.1 := by
    rw [cycleThroughVertex, Walk.penultimate_cons_of_not_nil hx _ hq, penultimate_concat]
  apply Dart.ext
  simp [Walk.lastDart, hpen]

/-- Unequal colors from `v` into one `G - v` component give a simple cycle
through `v` whose two incident edges at `v` have those unequal colors. -/
theorem exists_cycle_of_bichromatic_component (c : EdgeColoring G C) (v : V)
    (x y : {w : V // w ≠ v}) (hx : G.Adj v x.1) (hy : G.Adj v y.1)
    (hreach : (deleteGraph G v).Reachable x y)
    (hcol : c.color hx ≠ c.color hy) :
    ∃ (w : G.Walk v v) (hcyc : w.IsCycle),
      c.dartColor (w.firstDart hcyc.not_nil) = c.color hx ∧
      c.dartColor (w.lastDart hcyc.not_nil) = c.color hy := by
  have hne : x.1 ≠ y.1 := by
    intro hxy
    have : x = y := Subtype.ext hxy
    subst this
    exact hcol (c.color_proof hx hy)
  obtain ⟨p0, hp0, _⟩ := hreach.exists_path_of_dist
  have hp : (liftDeleteWalk p0).IsPath := liftDeleteWalk_isPath hp0
  have hv : v ∉ (liftDeleteWalk p0).support := not_mem_support_liftDeleteWalk p0
  refine ⟨cycleThroughVertex hx hy (liftDeleteWalk p0),
    cycleThroughVertex_isCycle hx hy hp hv hne, ?_⟩
  constructor
  · rw [cycleThroughVertex_firstDart]
    rfl
  · rw [cycleThroughVertex_lastDart]
    exact (c.color_symm hy).symm

lemma not_mem_dropLast_end {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hnil : ¬ p.Nil) : v ∉ p.dropLast.support := by
  intro hv
  have happ : p.dropLast.support ++ [v] = p.support :=
    Walk.support_dropLast_concat hnil
  have hnodup : p.support.Nodup := hp.support_nodup
  have hcount : List.count v p.support =
      List.count v p.dropLast.support + 1 := by
    rw [← happ, List.count_append]
    simp
  have : List.count v p.support ≤ 1 :=
    (List.nodup_iff_count_le_one.1 hnodup) v
  have : 0 < List.count v p.dropLast.support := List.count_pos_iff.2 hv
  omega

/-- The two neighbours of `v` on a genuine cycle through `v` are reachable
in `G - v` along the remainder of the cycle. -/
theorem reachable_in_delete_of_cycle {v : V} {w : G.Walk v v}
    (hcyc : w.IsCycle) :
    ∃ (x y : {z : V // z ≠ v}),
      G.Adj v x.1 ∧ G.Adj v y.1 ∧
        x.1 = w.snd ∧ y.1 = w.penultimate ∧
          (deleteGraph G v).Reachable x y := by
  match w, hcyc with
  | .cons (v := x0) h p, hcyc =>
    have hp : p.IsPath := ((Walk.cons_isCycle_iff p h).1 hcyc).1
    have hlen : 2 ≤ p.length := by
      have : 3 ≤ (Walk.cons h p).length := hcyc.three_le_length
      simp at this
      omega
    have hpnil : ¬ p.Nil := Walk.not_nil_iff_lt_length.2 (by omega)
    have hxne : x0 ≠ v := h.ne.symm
    have hpen_eq : (Walk.cons h p).penultimate = p.penultimate :=
      Walk.penultimate_cons_of_not_nil h p hpnil
    have hyne : p.penultimate ≠ v := (p.adj_penultimate hpnil).ne
    refine ⟨⟨x0, hxne⟩, ⟨p.penultimate, hyne⟩, h, (p.adj_penultimate hpnil).symm,
      by simp, hpen_eq.symm, ?_⟩
    have hv : v ∉ p.dropLast.support := not_mem_dropLast_end hp hpnil
    have hmem : ∀ z ∈ p.dropLast.support, z ∈ deleteSet v := by
      intro z hz heq
      exact hv (heq ▸ hz)
    let qind := (p.dropLast).induce (deleteSet v) hmem
    exact qind.reachable

/-- Unequal incident colors at `v` on a genuine cycle through `v` give two
neighbours of `v` in one `G - v` component with those unequal colors. -/
theorem exists_bichromatic_component_of_cycle (c : EdgeColoring G C) {v : V}
    (w : G.Walk v v) (hcyc : w.IsCycle)
    (hcol : c.dartColor (w.firstDart hcyc.not_nil) ≠
      c.dartColor (w.lastDart hcyc.not_nil)) :
    ∃ (x y : {z : V // z ≠ v}) (hx : G.Adj v x.1) (hy : G.Adj v y.1),
      (deleteGraph G v).Reachable x y ∧ c.color hx ≠ c.color hy := by
  obtain ⟨x, y, hx, hy, hxeq, hyeq, hreach⟩ := reachable_in_delete_of_cycle hcyc
  refine ⟨x, y, hx, hy, hreach, ?_⟩
  have hfirst : c.dartColor (w.firstDart hcyc.not_nil) = c.color hx := by
    simp only [Walk.firstDart, EdgeColoring.dartColor, hxeq]
  have hlast : c.dartColor (w.lastDart hcyc.not_nil) = c.color hy := by
    simp only [Walk.lastDart, EdgeColoring.dartColor, hyeq]
    exact (c.color_symm _).trans (c.color_proof _ _)
  exact fun h => hcol (hfirst.trans (h.trans hlast.symm))

/-- Cycle form of splitting is equivalent to monochromatic attachment into
every component of `G - v`. -/
theorem splittingVertex_iff_cycleSplittingVertex (c : EdgeColoring G C) (v : V) :
    SplittingVertex c v ↔ CycleSplittingVertex c v := by
  constructor
  · intro hsplit u w hcyc hv
    by_contra hne
    obtain ⟨x, y, hx, hy, hreach, hcol⟩ :=
      exists_bichromatic_component_of_cycle (c := c)
        (w := w.rotate v hv) (hcyc := hcyc.rotate hv) (hcol := hne)
    exact hcol (hsplit x y hx hy hreach)
  · intro hcycle x y hx hy hreach
    by_contra hcol
    obtain ⟨w, hcyc, hfirst, hlast⟩ :=
      exists_cycle_of_bichromatic_component c v x y hx hy hreach hcol
    have hv : v ∈ w.support := Walk.start_mem_support w
    have hrot : w.rotate v hv = w := by
      simp [Walk.rotate, Walk.takeUntil_first, Walk.dropUntil_first]
    have hagree := hcycle w hcyc hv
    simp [hrot] at hagree
    rw [hfirst, hlast] at hagree
    exact hcol hagree

end Yeo
end Nikoghosyan

