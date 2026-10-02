/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProtectedRestoration

/-!
# Strict protected-path existence by graph-general strong induction

Manuscript `prof:thm:protected`. Given a genuine original cycle on `U`, a
nonempty `A ⊆ U`, canonical `IsCograph G (U \ A)` and strict slack
`p(U \ A) < |A|`, there is a spanning original `A`–`A` path protected at
the prescribed cycle. The inductive hypothesis quantifies over every
graph on the fixed finite vertex type, because internal-edge suppression
changes the host graph.

No OneTough, host-cofree, terminal-spectrum, callback, desired-path or
boundary-count hypothesis is placed on the final signature.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath
open Nikoghosyan.GraphCycle

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Opened-cycle support and the A–A neighbour base -/

lemma openAt_support (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).support = c.support := by
  have hnn := c.rotateTo_not_nil hu
  have hcons := (c.rotateTo hu).walk.cons_tail_eq hnn
  have hsup : (c.rotateTo hu).walk.support =
      (c.rotateTo hu).start :: (c.rotateTo hu).walk.tail.support := by
    rw [← hcons]; simp [Walk.support_cons]
  have hwalk : (c.openAt hu).walk = (c.rotateTo hu).walk.tail := rfl
  ext x
  constructor
  · intro hx
    have hxL : x ∈ (c.openAt hu).walk.support :=
      (mem_walk_support (p := c.openAt hu)).1 hx
    have hxT : x ∈ (c.rotateTo hu).walk.support.tail :=
      (Walk.support_tail_of_not_nil (c.rotateTo hu).walk hnn) ▸ hxL
    have hxR : x ∈ (c.rotateTo hu).walk.support := List.mem_of_mem_tail hxT
    have : x ∈ (c.rotateTo hu).support := List.mem_toFinset.2 hxR
    simpa [c.support_rotateTo hu] using this
  · intro hx
    have hx0 : x ∈ (c.rotateTo hu).support := by
      simpa [c.support_rotateTo hu] using hx
    have hxW : x ∈ (c.rotateTo hu).walk.support := List.mem_toFinset.1 hx0
    have hxL : x ∈ (c.rotateTo hu).start :: (c.rotateTo hu).walk.tail.support := by
      simpa [hsup] using hxW
    rcases List.mem_cons.1 hxL with h | h
    · have hxu : x = u := h.trans (start_rotateTo c hu)
      simpa [hxu, c.openAt_finish hu] using (c.openAt hu).finish_mem_support
    · exact (mem_walk_support (p := c.openAt hu)).2 (hwalk ▸ h)

lemma ProtectedAt_openAt (c : GraphCycle G) {u : V} (hu : u ∈ c.support)
    {A : Finset V} : (c.openAt hu).ProtectedAt c A := by
  intro e he
  have heE : e ∈ (c.openAt hu).edges := (mem_AIncident_iff.1 he).1
  have : e ∈ c.edges := by
    rw [c.edges_eq_insert_openAt hu]
    exact mem_insert_of_mem heE
  simpa [GraphCycle.edges] using this

lemma opened_reverse_start (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).reverse.start = u := by
  simp [GraphPath.reverse, c.openAt_finish hu]

lemma opened_reverse_finish (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).reverse.finish = c.succAt hu := by
  simp [GraphPath.reverse, c.openAt_start hu]

lemma opened_reverse_support (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).reverse.support = c.support := by
  simpa [GraphPath.support_reverse] using openAt_support c hu

lemma opened_reverse_close (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    G.Adj (c.openAt hu).reverse.finish (c.openAt hu).reverse.start := by
  simpa [opened_reverse_finish c hu, opened_reverse_start c hu] using
    (c.adj_succAt hu).symm

lemma opened_reverse_edges (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).reverse.edges ∪ {s((c.openAt hu).reverse.finish,
      (c.openAt hu).reverse.start)} = c.walk.edges.toFinset := by
  have hedges : (c.openAt hu).reverse.edges = (c.openAt hu).edges :=
    (c.openAt hu).edges_reverse
  have hclose : s((c.openAt hu).reverse.finish, (c.openAt hu).reverse.start) =
      s(u, c.succAt hu) := by
    simp [opened_reverse_finish c hu, opened_reverse_start c hu, Sym2.eq_swap]
  rw [hedges, hclose]
  simpa [GraphCycle.edges, union_comm, singleton_union] using
    (c.edges_eq_insert_openAt hu).symm

lemma ProtectedAt_opened_reverse (c : GraphCycle G) {u : V} (hu : u ∈ c.support)
    {A : Finset V} : (c.openAt hu).reverse.ProtectedAt c A :=
  (ProtectedAt_reverse (c.openAt hu) c A).2 (ProtectedAt_openAt c hu)

lemma mem_support_penultimate_rotateTo (c : GraphCycle G) {u : V}
    (hu : u ∈ c.support) :
    (c.rotateTo hu).walk.penultimate ∈ (c.rotateTo hu).support := by
  have hnn : ¬ (c.rotateTo hu).walk.Nil := (c.rotateTo hu).isCycle.not_nil
  have hpos : 0 < (c.rotateTo hu).walk.length :=
    Walk.not_nil_iff_lt_length.1 hnn
  have : (c.rotateTo hu).walk.getVert ((c.rotateTo hu).walk.length - 1) ∈
      (c.rotateTo hu).walk.support :=
    Walk.getVert_mem_support _ _
  simpa [GraphCycle.support, Walk.penultimate] using this

lemma cycle_takeUntil_length_eq (c : GraphCycle G) {i : ℕ}
    (hi : i < c.walk.length) :
    (c.walk.takeUntil (c.walk.getVert i)
        (Walk.getVert_mem_support c.walk i)).length = i := by
  set u := c.walk.getVert i
  set p := c.walk.takeUntil u (Walk.getVert_mem_support c.walk i)
  have hi' : i ≤ c.walk.length := hi.le
  have hpu : c.walk.getVert p.length = u :=
    Walk.getVert_length_takeUntil (p := c.walk)
      (Walk.getVert_mem_support c.walk i)
  have hne : p.length ≠ c.walk.length := by
    intro heq
    have huStart : u = c.start := by
      simpa [heq, Walk.getVert_length] using hpu.symm
    have hi0 : i = 0 := by
      have := (c.isCycle.getVert_endpoint_iff hi').1 huStart
      omega
    have hp0 : p.length = 0 := by
      subst hi0
      simp [p, u, Walk.getVert_zero, Walk.takeUntil_first]
    have h3 := c.three_le_length
    omega
  have hplt : p.length < c.walk.length := lt_of_le_of_ne
    (Walk.length_takeUntil_le_length c.walk
      (Walk.getVert_mem_support c.walk i)) hne
  have hp_le : p.length ≤ c.walk.length - 1 := Nat.le_pred_of_lt hplt
  have hi_le : i ≤ c.walk.length - 1 := Nat.le_pred_of_lt hi
  exact c.isCycle.getVert_injOn' hp_le hi_le (hpu.trans rfl)

lemma cycle_idxOf_getVert (c : GraphCycle G) {i : ℕ} (hi : i < c.walk.length) :
    c.walk.support.idxOf (c.walk.getVert i) = i := by
  have := cycle_takeUntil_length_eq c hi
  simpa [Walk.length_takeUntil] using this

/-- The successor of the predecessor of `u` along the rotated cycle is `u`. -/
lemma succAt_penultimate_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.rotateTo hu).succAt (mem_support_penultimate_rotateTo c hu) = u := by
  set c0 := c.rotateTo hu
  set b := c0.walk.penultimate
  have hb : b ∈ c0.support := mem_support_penultimate_rotateTo c hu
  have hst : c0.start = u := start_rotateTo c hu
  have h3 : 3 ≤ c0.walk.length := c0.three_le_length
  have hlt : c0.walk.length - 1 < c0.walk.length := by omega
  have hbW : b ∈ c0.walk.support := by simpa [GraphCycle.support] using hb
  have hidx : c0.walk.support.idxOf b = c0.walk.length - 1 := by
    simpa [b, Walk.penultimate] using cycle_idxOf_getVert c0 hlt
  have hdropLen : (c0.walk.dropUntil b hbW).length = 1 := by
    rw [Walk.length_dropUntil, hidx]
    omega
  have hsnd : (c0.rotateTo hb).walk.getVert 1 =
      (c0.walk.dropUntil b hbW).getVert 1 := by
    simp only [GraphCycle.rotateTo, Walk.rotate]
    rw [Walk.getVert_append']
    have : 1 ≤ (c0.walk.dropUntil b hbW).length := by omega
    simp [this]
  have hfinDrop : (c0.walk.dropUntil b hbW).getVert
      (c0.walk.dropUntil b hbW).length = u := by
    simp [Walk.getVert_length, hst]
  have hdrop1 : (c0.walk.dropUntil b hbW).getVert 1 = u := by
    simpa [hdropLen] using hfinDrop
  rw [GraphCycle.succAt]
  exact hsnd.trans hdrop1

lemma exists_protectedAt_of_succAt_mem_A {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U) {a : V} (haA : a ∈ A)
    (hu : a ∈ c.support) (hsucc : c.succAt hu ∈ A) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧ p.ProtectedAt c A := by
  refine ⟨c.openAt hu, ?_, ?_, ?_, c.openAt_start_ne_finish hu,
    ProtectedAt_openAt c hu⟩
  · simpa [openAt_support c hu] using hc
  · simpa [c.openAt_start hu] using hsucc
  · simpa [c.openAt_finish hu] using haA

lemma exists_protectedAt_of_pred_mem_A {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U) {a : V} (haA : a ∈ A)
    (hu : a ∈ c.support)
    (hpred : (c.openAt hu).walk.penultimate ∈ A) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧ p.ProtectedAt c A := by
  set c0 := c.rotateTo hu
  set b := c0.walk.penultimate
  have hb : b ∈ c0.support := mem_support_penultimate_rotateTo c hu
  have hbA : b ∈ A := by
    have : b = (c.openAt hu).walk.penultimate := c.penultimate_rotateTo hu
    simpa [this] using hpred
  have hst : c0.succAt hb = a := by
    have := succAt_penultimate_rotateTo c hu
    simpa [c0] using this
  have hP0 : (c0.openAt hb).ProtectedAt c0 A := ProtectedAt_openAt c0 hb
  have hedges : c0.walk.edges.toFinset = c.walk.edges.toFinset := by
    simpa [GraphCycle.edges] using c.edges_rotateTo_eq hu
  refine ⟨c0.openAt hb, ?_, ?_, ?_, c0.openAt_start_ne_finish hb,
    ProtectedAt.of_cycle_edges_eq hedges hP0⟩
  · rw [openAt_support c0 hb, c.support_rotateTo hu, hc]
  · simpa [c0.openAt_start hb, hst] using haA
  · simpa [c0.openAt_finish hb] using hbA

lemma exists_protectedAt_of_cycle_neighbour_A {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U) {a : V} (haA : a ∈ A)
    (hu : a ∈ c.support)
    (hn : c.succAt hu ∈ A ∨ (c.openAt hu).walk.penultimate ∈ A) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧ p.ProtectedAt c A := by
  rcases hn with h | h
  · exact exists_protectedAt_of_succAt_mem_A c hc haA hu h
  · exact exists_protectedAt_of_pred_mem_A c hc haA hu h

/-! ### Original-cycle boundary endpoints in `X` -/

lemma cycle_boundary_eq_ax {U0 : Finset V} {e : Sym2 V} {a x : V}
    (hstr : endsStraddle e U0) (hae : a ∈ e) (haU : a ∉ U0)
    (hxe : x ∈ e) (hxU : x ∈ U0) : e = s(a, x) := by
  refine Sym2.inductionOn e (fun u v hstr hae haU hxe hxU => ?_) hstr hae haU hxe hxU
  rcases (Sym2.mem_iff.mp hae) with rfl | rfl
  · rcases (Sym2.mem_iff.mp hxe) with rfl | rfl
    · exact (haU hxU).elim
    · rfl
  · rcases (Sym2.mem_iff.mp hxe) with rfl | rfl
    · simp [Sym2.eq_swap]
    · exact (haU hxU).elim

lemma cycle_boundary_U0_end_mem_X {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hU0 : U0 ⊆ U \ A)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    {e : Sym2 V} (he : e ∈ c.boundaryEdges U0) {x : V}
    (hxe : x ∈ e) (hxU : x ∈ U0) : x ∈ X := by
  obtain ⟨Q, hQ, hxQ, hsU0, hQsup⟩ :=
    leftover_U0_run_of_mem (U := U) (A := A) (U0 := U0) hp hU0 hnocross hstay hxU
  have hsX : Q.start ∈ X := hstartX Q hQ hsU0
  have hfX : Q.finish ∈ X := hfinX Q hQ hsU0
  obtain ⟨heC, hstr⟩ := GraphCycle.mem_boundaryEdges_iff.1 he
  obtain ⟨a, haA, hae⟩ :=
    boundary_outside_end_mem_A (c := c) hc hU0 hnocross he
  have haU : a ∉ U0 := disjoint_left.1 (disjoint_A_U0 hU0) haA
  have heq : e = s(a, x) := cycle_boundary_eq_ax hstr hae haU hxe hxU
  have haQ : a ∉ Q.support := fun hmem =>
    (mem_sdiff.1 (hU0 (hQsup hmem))).2 haA
  by_cases heP : s(a, x) ∈ p.edges
  · have hends := leftover_endpoint_of_leaving_edge (A := A) hQ heP hxQ haQ
    rcases hends with h | h
    · simpa [h] using hsX
    · simpa [h] using hfX
  · have hmem : s(a, x) ∈ p.edges ∪ {s(p.finish, p.start)} := by
      simpa [hedges, GraphCycle.edges, heq] using heC
    have hclose : s(a, x) = s(p.finish, p.start) :=
      mem_singleton.1 ((mem_union.1 hmem).resolve_left heP)
    have hxfin : x = p.finish := by
      have hsU : p.start ∉ U0 := disjoint_left.1 (disjoint_A_U0 hU0) hs
      rcases (Sym2.eq_iff.mp hclose) with ⟨_, hx'⟩ | ⟨_, hx'⟩
      · exact (hsU (by simpa [hx'] using hxU)).elim
      · exact hx'
    have : Q.finish = p.finish :=
      leftover_finish_eq_of_mem (A := A) hQ (by simpa [hxfin] using hxQ)
    simpa [hxfin, this] using hfX

lemma path_boundary_outside_end_mem_A {U A U0 Y : Finset V}
    {G' : SimpleGraph V} (hLE : G' ≤ G)
    (_hA : A ⊆ U) (hU0 : U0 ⊆ U \ A) (_hY : Y ⊆ U0)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    {p' : GraphPath G'} (hp' : p'.support = U)
    {e : Sym2 V} (he : e ∈ p'.boundaryEdges U0) :
    ∃ a ∈ A, a ∈ e := by
  obtain ⟨heP, hstr⟩ := GraphPath.mem_boundaryEdges_iff.1 he
  obtain ⟨x, hxe, hxU, huniq⟩ := existsUnique_U0_end hstr
  refine Sym2.inductionOn e (fun u v heP hstr hxe hxU huniq => ?_) heP hstr hxe hxU huniq
  have hadj' : G'.Adj u v := by
    simpa [SimpleGraph.mem_edgeSet] using p'.edges_subset_edgeSet _ heP
  have hadj : G.Adj u v := hLE hadj'
  have huP : u ∈ p'.support := mem_support_of_mem_edge heP (by simp)
  have hvP : v ∈ p'.support := mem_support_of_mem_edge heP (by simp)
  have huU : u ∈ U := by simpa [hp'] using huP
  have hvU : v ∈ U := by simpa [hp'] using hvP
  rcases (show u = x ∨ v = x from by
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl) with rfl | rfl
  · have hvU0 : v ∉ U0 := fun hvU0 =>
      (endsStraddle_iff.1 hstr) (propext ⟨fun _ => hvU0, fun _ => hxU⟩)
    by_cases hvA : v ∈ A
    · exact ⟨v, hvA, by simp⟩
    · have hvK : v ∈ (U \ A) \ U0 := mem_sdiff.2 ⟨mem_sdiff.2 ⟨hvU, hvA⟩, hvU0⟩
      exact (hnocross u hxU v hvK hadj).elim
  · have huU0 : u ∉ U0 := fun huU0 =>
      (endsStraddle_iff.1 hstr) (propext ⟨fun _ => hxU, fun _ => huU0⟩)
    by_cases huA : u ∈ A
    · exact ⟨u, huA, by simp⟩
    · have huK : u ∈ (U \ A) \ U0 := mem_sdiff.2 ⟨mem_sdiff.2 ⟨huU, huA⟩, huU0⟩
      exact (hnocross v hxU u huK hadj.symm).elim

lemma path_boundary_mem_cycle_boundary {U A U0 Y : Finset V}
    {G' : SimpleGraph V} (hLE : G' ≤ G)
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hU0 : U0 ⊆ U \ A) (hY : Y ⊆ U0)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    {p' : GraphPath G'} {c' : GraphCycle G'}
    (hp' : p'.support = U)
    (hP : p'.ProtectedAt c' A) (hedges' : c'.edges = c.edges)
    {e : Sym2 V} (he : e ∈ p'.boundaryEdges U0) :
    e ∈ c.boundaryEdges U0 := by
  obtain ⟨heP, hstr⟩ := GraphPath.mem_boundaryEdges_iff.1 he
  obtain ⟨a, haA, hae⟩ :=
    path_boundary_outside_end_mem_A (G := G) hLE hA hU0 hY hnocross hp' he
  have heA : e ∈ p'.AIncident A := mem_AIncident_iff.2 ⟨heP, a, haA, hae⟩
  have heC' : e ∈ c'.edges := by
    simpa [GraphCycle.edges] using hP heA
  exact GraphCycle.mem_boundaryEdges_iff.2 ⟨by simpa [hedges'] using heC', hstr⟩

lemma boundaryEdges_reverse (p : GraphPath G) (U0 : Finset V) :
    p.reverse.boundaryEdges U0 = p.boundaryEdges U0 := by
  simp [GraphPath.boundaryEdges, p.edges_reverse]

lemma ProtectedAt_ofLE_edges {G G' : SimpleGraph V} (hLE : G' ≤ G)
    {p : GraphPath G'} {c : GraphCycle G} {c' : GraphCycle G'} {A : Finset V}
    (hedges : c'.edges = c.edges) (hP : p.ProtectedAt c' A) :
    (p.ofLE hLE).ProtectedAt c A := by
  intro e he
  have he' : e ∈ p.AIncident A := by
    simpa [AIncident, GraphPath.ofLE_edges] using he
  change e ∈ c.edges
  have heC' : e ∈ c'.edges := hP he'
  exact hedges ▸ heC'

/-! ### Original-A restoration from an `A ∪ Y`-ended inductive path -/

/-- One prefix rotation of a `G'`-path that starts in `Y`, using the
derived four-edge cycle bound and the complete-join chord in `G'`. -/
lemma exists_one_return_rotate {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hU0 : U0 ⊆ U \ A) (hX : X ⊆ U0) (hY : Y ⊆ U0)
    (hdisjXY : Disjoint X Y)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    {p' : GraphPath (suppressInternal G (A ∪ Y))}
    {c' : GraphCycle (suppressInternal G (A ∪ Y))}
    (hp' : p'.support = U) (hc' : c'.support = U)
    (hP : p'.ProtectedAt c' A) (hedges' : c'.edges = c.edges)
    (hsY : p'.start ∈ Y) :
    ∃ q : GraphPath (suppressInternal G (A ∪ Y)),
      q.support = U ∧ q.start ∈ A ∧ q.finish = p'.finish ∧
        q.start ≠ q.finish ∧ q.ProtectedAt c' A := by
  let G' := suppressInternal G (A ∪ Y)
  have hLE : G' ≤ G := suppressInternal_le G (A ∪ Y)
  have hdisjAY : Disjoint A Y := disjoint_A_of_saving_child hU0 hY
  have h3 : 3 ≤ (p'.boundaryEdges U0).card :=
    three_le_path_boundary_of_start_Y (G := G) (G' := G') c hc hA hU0 hY
      hnocross hdisjAY hp' hc' hP hedges' hsY h4
  have h2 : 2 ≤ (p'.boundaryEdges U0).card := le_trans (by decide : (2 : ℕ) ≤ 3) h3
  have hsU0 : p'.start ∈ U0 := hY hsY
  have hAout : Disjoint A U0 := disjoint_A_U0 hU0
  have hjoin' : ∀ y ∈ Y, ∀ z ∈ X, G'.Adj y z := fun y hy z hx =>
    completeJoin_adj_suppressInternal (U := U) (A := A) (U0 := U0) (X := X)
      (Y := Y) hU0 hX hdisjXY hjoin hy hx
  have henterX : ∀ i, i < p'.walk.length → p'.walk.getVert i ∉ U0 →
      p'.walk.getVert (i + 1) ∈ U0 → p'.walk.getVert (i + 1) ∈ X := by
    intro i hi h0 h1
    have he : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈ p'.edges :=
      p'.crossingEdge_mem_edges hi
    have hbd : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈
        p'.boundaryEdges U0 :=
      GraphPath.mem_boundaryEdges_iff.2 ⟨he, endsStraddle_of_outside_inside h0 h1⟩
    have heC : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈
        c.boundaryEdges U0 :=
      path_boundary_mem_cycle_boundary (G := G) hLE c hc hA hU0 hY hnocross
        hp' hP hedges' hbd
    exact cycle_boundary_U0_end_mem_X (Y := Y) c hc hU0 hp hs hedges hnocross
      hstay hstartX hfinX heC (by simp) h1
  have henterA : ∀ i, i < p'.walk.length → p'.walk.getVert i ∉ U0 →
      p'.walk.getVert (i + 1) ∈ U0 → p'.walk.getVert i ∈ A := by
    intro i hi h0 h1
    have he : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈ p'.edges :=
      p'.crossingEdge_mem_edges hi
    have hbd : s(p'.walk.getVert i, p'.walk.getVert (i + 1)) ∈
        p'.boundaryEdges U0 :=
      GraphPath.mem_boundaryEdges_iff.2 ⟨he, endsStraddle_of_outside_inside h0 h1⟩
    obtain ⟨a, haA, hae⟩ :=
      path_boundary_outside_end_mem_A (G := G) hLE hA hU0 hY hnocross hp' hbd
    have hxU : p'.walk.getVert (i + 1) ∈ U0 := h1
    have haU : a ∉ U0 := disjoint_left.1 hAout haA
    have heq := cycle_boundary_eq_ax
      (endsStraddle_of_outside_inside (U0 := U0) h0 h1) hae haU
      (by simp) hxU
    rcases (Sym2.eq_iff.mp heq) with ⟨rfl, _⟩ | ⟨hvu, _⟩
    · exact haA
    · exact (h0 (by simpa [hvu] using hxU)).elim
  obtain ⟨i, F, hyx, hi, h0, h1, haA, hxX, hst, hsup, hProt⟩ :=
    exists_returnRotate (p := p') (U0 := U0) hsU0 h2 (A := A) (X := X) (Y := Y)
      (c := c') hjoin' hsY hP hAout hY hX henterX henterA
  have hne : (F.rotate hyx).start ≠ (F.rotate hyx).finish :=
    F.rotate_start_ne_finish hyx
  refine ⟨F.rotate hyx, by simpa [hsup] using hp', ?_, ?_, hne, hProt⟩
  · simpa [hst] using haA
  · simpa [F.rotate_finish hyx]

/-- Restore original-`A` ends of an inductive `A ∪ Y`-ended `G'`-path by
at most two prefix rotations. -/
lemma exists_restore_originalA_ends {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hU0 : U0 ⊆ U \ A) (hX : X ⊆ U0) (hY : Y ⊆ U0)
    (hdisjXY : Disjoint X Y) (hYne : Y.Nonempty)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    {p' : GraphPath (suppressInternal G (A ∪ Y))}
    {c' : GraphCycle (suppressInternal G (A ∪ Y))}
    (hp' : p'.support = U) (hc' : c'.support = U)
    (hs' : p'.start ∈ A ∪ Y) (hf' : p'.finish ∈ A ∪ Y)
    (hne' : p'.start ≠ p'.finish)
    (hP' : p'.ProtectedAt c' (A ∪ Y))
    (hedges' : c'.edges = c.edges) :
    ∃ q : GraphPath (suppressInternal G (A ∪ Y)),
      q.support = U ∧ q.start ∈ A ∧ q.finish ∈ A ∧
        q.start ≠ q.finish ∧ q.ProtectedAt c' A := by
  have hsub : A ⊆ A ∪ Y := subset_union_left
  have hP : p'.ProtectedAt c' A := hP'.mono_set hsub
  have hdisjAY : Disjoint A Y := disjoint_A_of_saving_child hU0 hY
  by_cases hboth : p'.start ∈ A ∧ p'.finish ∈ A
  · exact ⟨p', hp', hboth.1, hboth.2, hne', hP⟩
  have hYend : p'.start ∈ Y ∨ p'.finish ∈ Y := by
    have hst : p'.start ∈ A ∨ p'.start ∈ Y := mem_union.1 hs'
    have hfn : p'.finish ∈ A ∨ p'.finish ∈ Y := mem_union.1 hf'
    rcases hst with hstA | hstY
    · rcases hfn with hfnA | hfnY
      · exact (hboth ⟨hstA, hfnA⟩).elim
      · exact Or.inr hfnY
    · exact Or.inl hstY
  -- Orient so the path starts in `Y`.
  let q0 : GraphPath (suppressInternal G (A ∪ Y)) :=
    if h : p'.start ∈ Y then p' else p'.reverse
  have hq0sup : q0.support = U := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h] using hp'
    · simpa [q0, h, GraphPath.support_reverse] using hp'
  have hq0stY : q0.start ∈ Y := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h]
    · have hfY : p'.finish ∈ Y := hYend.resolve_left h
      simpa [q0, h, GraphPath.reverse] using hfY
  have hq0P : q0.ProtectedAt c' A := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h] using hP
    · simpa [q0, h, ProtectedAt_reverse] using hP
  have hq0fin_mem : q0.finish ∈ A ∪ Y := by
    by_cases h : p'.start ∈ Y
    · simpa [q0, h] using hf'
    · simpa [q0, h, GraphPath.reverse] using hs'
  obtain ⟨q1, hq1sup, hq1st, hq1fin, hq1ne, hq1P⟩ :=
    exists_one_return_rotate (Y := Y) c hc hA hU0 hX hY hdisjXY hjoin hnocross
      hp hs hedges hstay hstartX hfinX h4 hq0sup hc' hq0P hedges' hq0stY
  by_cases hfA : q1.finish ∈ A
  · exact ⟨q1, hq1sup, hq1st, hfA, hq1ne, hq1P⟩
  have hfY : q1.finish ∈ Y := by
    have : q1.finish ∈ A ∪ Y := by simpa [hq1fin] using hq0fin_mem
    exact (mem_union.1 this).resolve_left hfA
  -- Reverse the current path and restore the remaining `Y`-end.
  let qR := q1.reverse
  have hRsup : qR.support = U := by simpa [qR, GraphPath.support_reverse] using hq1sup
  have hRstY : qR.start ∈ Y := by simpa [qR, GraphPath.reverse] using hfY
  have hRP : qR.ProtectedAt c' A :=
    (ProtectedAt_reverse q1 c' A).2 hq1P
  obtain ⟨q2, hq2sup, hq2st, hq2fin, hq2ne, hq2P⟩ :=
    exists_one_return_rotate (Y := Y) c hc hA hU0 hX hY hdisjXY hjoin hnocross
      hp hs hedges hstay hstartX hfinX h4 hRsup hc' hRP hedges' hRstY
  refine ⟨q2, hq2sup, hq2st, ?_, hq2ne, hq2P⟩
  simpa [hq2fin, qR, GraphPath.reverse] using hq1st

lemma exists_lift_restored {U A U0 X Y : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hU0 : U0 ⊆ U \ A) (hX : X ⊆ U0) (hY : Y ⊆ U0)
    (hdisjXY : Disjoint X Y) (hYne : Y.Nonempty)
    (hjoin : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (U \ A) \ U0, ¬ G.Adj a b)
    {p : GraphPath G} (hp : p.support = U) (hs : p.start ∈ A)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset)
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hstartX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.start ∈ X)
    (hfinX : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ X)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    {p' : GraphPath (suppressInternal G (A ∪ Y))}
    {c' : GraphCycle (suppressInternal G (A ∪ Y))}
    (hp' : p'.support = U) (hc' : c'.support = U)
    (hs' : p'.start ∈ A ∪ Y) (hf' : p'.finish ∈ A ∪ Y)
    (hne' : p'.start ≠ p'.finish)
    (hP' : p'.ProtectedAt c' (A ∪ Y))
    (hedges' : c'.edges = c.edges) :
    ∃ q : GraphPath G,
      q.support = U ∧ q.start ∈ A ∧ q.finish ∈ A ∧
        q.start ≠ q.finish ∧ q.ProtectedAt c A := by
  obtain ⟨r, hrsup, hrst, hrfin, hrne, hrP⟩ :=
    exists_restore_originalA_ends (Y := Y) c hc hA hU0 hX hY hdisjXY hYne hjoin
      hnocross hp hs hedges hstay hstartX hfinX h4 hp' hc' hs' hf' hne' hP'
      hedges'
  let hLE := suppressInternal_le G (A ∪ Y)
  refine ⟨r.ofLE hLE, ?_, ?_, ?_, ?_, ProtectedAt_ofLE_edges hLE hedges' hrP⟩
  · simpa [GraphPath.ofLE_support] using hrsup
  · simpa [GraphPath.ofLE_start] using hrst
  · simpa [GraphPath.ofLE_finish] using hrfin
  · simpa [GraphPath.ofLE_start, GraphPath.ofLE_finish] using hrne

lemma InducedP4_suppressInternal {A' : Finset V} {a b c d : V}
    (ha : a ∉ A') (hb : b ∉ A') (hc : c ∉ A') (hd : d ∉ A') :
    InducedP4 (suppressInternal G A') a b c d ↔ InducedP4 G a b c d := by
  constructor
  · intro h
    exact
      { ne_ab := h.ne_ab, ne_ac := h.ne_ac, ne_ad := h.ne_ad, ne_bc := h.ne_bc
        ne_bd := h.ne_bd, ne_cd := h.ne_cd
        adj_ab := (adj_eq_on_carrier G ha hb).1 h.adj_ab
        adj_bc := (adj_eq_on_carrier G hb hc).1 h.adj_bc
        adj_cd := (adj_eq_on_carrier G hc hd).1 h.adj_cd
        not_ac := mt ((adj_eq_on_carrier G ha hc).2) h.not_ac
        not_ad := mt ((adj_eq_on_carrier G ha hd).2) h.not_ad
        not_bd := mt ((adj_eq_on_carrier G hb hd).2) h.not_bd }
  · intro h
    exact
      { ne_ab := h.ne_ab, ne_ac := h.ne_ac, ne_ad := h.ne_ad, ne_bc := h.ne_bc
        ne_bd := h.ne_bd, ne_cd := h.ne_cd
        adj_ab := (adj_eq_on_carrier G ha hb).2 h.adj_ab
        adj_bc := (adj_eq_on_carrier G hb hc).2 h.adj_bc
        adj_cd := (adj_eq_on_carrier G hc hd).2 h.adj_cd
        not_ac := mt ((adj_eq_on_carrier G ha hc).1) h.not_ac
        not_ad := mt ((adj_eq_on_carrier G ha hd).1) h.not_ad
        not_bd := mt ((adj_eq_on_carrier G hb hd).1) h.not_bd }

lemma isCograph_suppressInternal {U A' : Finset V} (hU : Disjoint U A')
    (h : IsCograph G U) : IsCograph (suppressInternal G A') U := by
  intro a b c d ha hb hc hd hp
  exact h ha hb hc hd
    ((InducedP4_suppressInternal (disjoint_left.1 hU ha) (disjoint_left.1 hU hb)
      (disjoint_left.1 hU hc) (disjoint_left.1 hU hd)).1 hp)

lemma finish_mem_of_start_U0 {A U0 S : Finset V} {p : GraphPath G}
    (hstay : ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.support ⊆ U0)
    (hfin : ∀ Q ∈ leftoverPieces A p, Q.finish ∈ U0 → Q.finish ∈ S) :
    ∀ Q ∈ leftoverPieces A p, Q.start ∈ U0 → Q.finish ∈ S :=
  fun Q hQ hs => hfin Q hQ (hstay Q hQ hs Q.finish_mem_support)

lemma exists_protectedAt_reorder {U A : Finset V} {c : GraphCycle G}
    {q : GraphPath G}
    (h : q.support = U ∧ q.ProtectedAt c A ∧ q.start ∈ A ∧ q.finish ∈ A ∧
      q.start ≠ q.finish) :
    q.support = U ∧ q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish ∧
      q.ProtectedAt c A :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h.2.1⟩

/-! ### Graph-general strong induction -/

/-- Strict protected spanning `A`–`A` path from a genuine original cycle,
canonical remainder cograph, and `p(U \ A) < |A|`. The induction is on
`|(U \ A)|` and quantifies over every graph on the fixed finite vertex
type. -/
theorem exists_protectedAt_of_strict {U A : Finset V}
    {G : SimpleGraph V} (c : GraphCycle G)
    (hc : c.support = U) (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : IsCograph G (U \ A))
    (hstrict : pathCoverNumber G (U \ A) < A.card) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧ p.ProtectedAt c A := by
  let motive : ℕ → Prop := fun n =>
    ∀ (G : SimpleGraph V) (U A : Finset V) (c : GraphCycle G),
      (U \ A).card = n →
        c.support = U → A ⊆ U → A.Nonempty →
          IsCograph G (U \ A) →
            pathCoverNumber G (U \ A) < A.card →
              ∃ p : GraphPath G,
                p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
                  p.start ≠ p.finish ∧ p.ProtectedAt c A
  refine Nat.strongRecOn (motive := motive) (U \ A).card ?_ G U A c rfl hc hA
    hAne hK hstrict
  intro n ih Gind Uind Aind cind hcard hcind hAind hAneind hKind hstrictind
  by_cases hAA : ∃ a ∈ Aind, ∃ hu : a ∈ cind.support,
      cind.succAt hu ∈ Aind ∨ (cind.openAt hu).walk.penultimate ∈ Aind
  · obtain ⟨a, haA, hu, hneigh⟩ := hAA
    exact exists_protectedAt_of_cycle_neighbour_A cind hcind haA hu hneigh
  have hnoAA : ∀ a ∈ Aind, ∀ hu : a ∈ cind.support,
      cind.succAt hu ∉ Aind ∧ (cind.openAt hu).walk.penultimate ∉ Aind := by
    intro a haA hu
    constructor
    · intro h
      exact hAA ⟨a, haA, hu, Or.inl h⟩
    · intro h
      exact hAA ⟨a, haA, hu, Or.inr h⟩
  obtain ⟨a, haA⟩ := hAneind
  have hu : a ∈ cind.support := by simpa [hcind] using hAind haA
  have hsuccA : cind.succAt hu ∉ Aind := (hnoAA a haA hu).1
  let p := (cind.openAt hu).reverse
  have hp : p.support = Uind := by
    simpa [p, opened_reverse_support cind hu] using hcind
  have hs : p.start ∈ Aind := by simpa [p, opened_reverse_start cind hu] using haA
  have hf : p.finish ∉ Aind := by
    simpa [p, opened_reverse_finish cind hu] using hsuccA
  have hclose : Gind.Adj p.finish p.start := opened_reverse_close cind hu
  have hedges : p.edges ∪ {s(p.finish, p.start)} = cind.walk.edges.toFinset :=
    opened_reverse_edges cind hu
  have hno : NoConsecutive Aind p :=
    NoConsecutive_of_no_AA_cycle (c := cind) hcind hAind hedges hnoAA
  obtain ⟨U0, pcU0, hU0, hU0ne, hconn, hU0cog, hnocross, hpaths, hq0, _, hU0card,
      hstay⟩ :=
    exists_saving_component (c := cind) hcind hAind ⟨a, haA⟩ hKind hstrictind
      hp hs hf hno
  obtain ⟨X, Y, hX, hY, hXne, hYne, hdisjXY, hcover, hjoin, _, _⟩ :=
    exists_complete_join_of_saving hU0cog hconn hU0card
  have h2 : 2 ≤
      (List.filter (fun Q => Q.start ∈ U0) (leftoverPieces Aind p)).length := by
    simpa [PathCover.card, hpaths] using hq0
  obtain ⟨Q0, _, hQ0, _, hs0, _, _⟩ := exists_two_leftover_in h2
  by_cases hAdjS : ∃ Q ∈ leftoverPieces Aind p, ∃ R ∈ leftoverPieces Aind p,
      Q.start ≠ R.start ∧ Gind.Adj Q.start R.start
  · obtain ⟨Q, hQ, R, hR, hneQR, hadj⟩ := hAdjS
    obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
      exists_protectedAt_of_adj_leftover_starts (c := cind) hcind hp hs hclose
        hedges hQ hR hneQR hadj
    exact ⟨q, hsup, hst, hfin, hne, hProt⟩
  by_cases hAdjF : ∃ Q ∈ leftoverPieces Aind p, ∃ R ∈ leftoverPieces Aind p,
      Q.finish ≠ R.finish ∧ Gind.Adj Q.finish R.finish
  · obtain ⟨Q, hQ, R, hR, hneQR, hadj⟩ := hAdjF
    obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
      exists_protectedAt_of_adj_leftover_ends (c := cind) hcind hp hs hclose
        hedges hQ hR hneQR hadj
    exact ⟨q, hsup, hst, hfin, hne, hProt⟩
  have hIndS : ∀ Q ∈ leftoverPieces Aind p, ∀ R ∈ leftoverPieces Aind p,
      Q.start ∈ U0 → R.start ∈ U0 → Q.start ≠ R.start → ¬ Gind.Adj Q.start R.start :=
    fun Q hQ R hR _ _ hne hadj => hAdjS ⟨Q, hQ, R, hR, hne, hadj⟩
  have hIndF : ∀ Q ∈ leftoverPieces Aind p, ∀ R ∈ leftoverPieces Aind p,
      Q.finish ∈ U0 → R.finish ∈ U0 → Q.finish ≠ R.finish →
        ¬ Gind.Adj Q.finish R.finish :=
    fun Q hQ R hR _ _ hne hadj => hAdjF ⟨Q, hQ, R, hR, hne, hadj⟩
  have hstartSide := leftover_starts_in_one_join_side (A := Aind) (U0 := U0)
    (X := X) (Y := Y) hjoin hcover hIndS hQ0 hs0
  have hf0 : Q0.finish ∈ U0 := hstay Q0 hQ0 hs0 Q0.finish_mem_support
  have hfinSide := leftover_finishes_in_one_join_side (A := Aind) (U0 := U0)
    (X := X) (Y := Y) hjoin hcover hIndF hQ0 hf0
  rcases hstartSide with hstartX | hstartY
  · have hstartX' := hstartX
    rcases hfinSide with hfinX0 | hfinY0
    · have hfinX := finish_mem_of_start_U0 hstay hfinX0
      by_cases hYY : ∃ Q ∈ leftoverPieces Aind p, Q.start ∈ U0 ∧
          ∃ u ∈ Y, ∃ v ∈ Y, s(u, v) ∈ Q.edges
      · obtain ⟨Q, hQ, hQs, u, huY, v, hvY, huvQ⟩ := hYY
        have hadjuv : Gind.Adj u v := by
          simpa [SimpleGraph.mem_edgeSet] using Q.edges_subset_edgeSet _ huvQ
        obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
          exists_protectedAt_of_join_insert_YY_of_saving (c := cind) hcind hU0
            hjoin hcover hp hs hclose hedges hstay h2 hfinX hstartX' hQ hQs
            huY hvY hadjuv huvQ
        exact ⟨q, hsup, hst, hfin, hne, hProt⟩
      · have hnoYY : ∀ Q ∈ leftoverPieces Aind p, Q.start ∈ U0 →
            ∀ u ∈ Y, ∀ v ∈ Y, s(u, v) ∉ Q.edges := by
          intro Q hQ hsU u hu v hv he
          exact hYY ⟨Q, hQ, hsU, u, hu, v, hv, he⟩
        have hsurv :=
          cycle_edges_mem_suppressInternal_noYY (c := cind) hcind hU0 hY hdisjXY
            hp hs hedges hnoAA hnocross hstay hstartX' hfinX hnoYY
        let G' := suppressInternal Gind (Aind ∪ Y)
        let c' := cind.transferEdges hsurv
        have hc' : c'.support = Uind :=
          (GraphCycle.transferEdges_support cind hsurv).trans hcind
        have hedges' : c'.edges = cind.edges :=
          GraphCycle.transferEdges_edges cind hsurv
        have hA'sub : Aind ∪ Y ⊆ Uind := by
          intro x hx
          rcases mem_union.1 hx with h | h
          · exact hAind h
          · exact (mem_sdiff.1 (hU0 (hY h))).1
        have hAne' : (Aind ∪ Y).Nonempty := ⟨a, mem_union.2 (Or.inl haA)⟩
        have hK' : IsCograph G' (Uind \ (Aind ∪ Y)) :=
          isCograph_suppressInternal (Finset.disjoint_sdiff).symm
            (isCograph_sdiff_union_Y (U := Uind) (A := Aind) (Y := Y) hKind)
        have hpnum' : pathCoverNumber G' (Uind \ (Aind ∪ Y)) < (Aind ∪ Y).card := by
          have hEq := pathCoverNumber_carrier (G := Gind) Uind (Aind ∪ Y)
          have hltY := pathCoverNumber_lt_of_delete_Y (U := Uind) (A := Aind)
            (U0 := U0) (Y := Y) hU0 hY hstrictind
          exact hEq ▸ hltY
        have hlt : (Uind \ (Aind ∪ Y)).card < n := by
          have hsubY : Y ⊆ Uind \ Aind := hY.trans hU0
          have hEq : Uind \ (Aind ∪ Y) = (Uind \ Aind) \ Y :=
            (sdiff_sdiff_eq_sdiff_union Uind Aind Y).symm
          rw [hEq, card_sdiff_of_subset hsubY]
          have hpos : 0 < Y.card := card_pos.2 hYne
          have hle : Y.card ≤ (Uind \ Aind).card := card_le_card hsubY
          omega
        obtain ⟨q', hq'sup, hq'st, hq'fin, hq'ne, hq'P⟩ :=
          ih (Uind \ (Aind ∪ Y)).card hlt G' Uind (Aind ∪ Y) c' rfl hc' hA'sub
            hAne' hK' hpnum'
        have h4 : 4 ≤ (cind.boundaryEdges U0).card :=
          four_le_card_cycle_boundary_U0 (c := cind) hcind hU0 hp hs hedges hstay h2
        exact exists_lift_restored (Y := Y) cind hcind hAind hU0 hX hY hdisjXY
          hYne hjoin hnocross hp hs hedges hstay hstartX' hfinX h4 hq'sup hc'
          hq'st hq'fin hq'ne hq'P hedges'
    · have hfinY := finish_mem_of_start_U0 hstay hfinY0
      obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
        exists_protectedAt_of_join_insert_XZ_of_saving (c := cind) hcind hU0 hjoin
          hcover hp hs hclose hedges hstay h2 hstartX' hfinY
      exact ⟨q, hsup, hst, hfin, hne, hProt⟩
  · have hstartY' := hstartY
    rcases hfinSide with hfinX0 | hfinY0
    · have hfinX := finish_mem_of_start_U0 hstay hfinX0
      obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
        exists_protectedAt_of_join_insert_YX_of_saving (c := cind) hcind hU0 hjoin
          hcover hp hs hclose hedges hstay h2 hstartY' hfinX
      exact ⟨q, hsup, hst, hfin, hne, hProt⟩
    · have hfinY := finish_mem_of_start_U0 hstay hfinY0
      by_cases hXX : ∃ Q ∈ leftoverPieces Aind p, Q.start ∈ U0 ∧
          ∃ u ∈ X, ∃ v ∈ X, s(u, v) ∈ Q.edges
      · obtain ⟨Q, hQ, hQs, u, huX, v, hvX, huvQ⟩ := hXX
        have hadjuv : Gind.Adj u v := by
          simpa [SimpleGraph.mem_edgeSet] using Q.edges_subset_edgeSet _ huvQ
        obtain ⟨q, hsup, hProt, hst, hfin, hne⟩ :=
          exists_protectedAt_of_join_insert_XX_of_saving (c := cind) hcind hU0
            hjoin hcover hp hs hclose hedges hstay h2 hfinY hstartY' hQ hQs
            huX hvX hadjuv huvQ
        exact ⟨q, hsup, hst, hfin, hne, hProt⟩
      · have hnoXX : ∀ Q ∈ leftoverPieces Aind p, Q.start ∈ U0 →
            ∀ u ∈ X, ∀ v ∈ X, s(u, v) ∉ Q.edges := by
          intro Q hQ hsU u hu v hv he
          exact hXX ⟨Q, hQ, hsU, u, hu, v, hv, he⟩
        have hjoinYX : Gind.IsCompleteBetween (Y : Set V) (X : Set V) :=
          fun {y} hy {x} hx => (hjoin hx hy).symm
        have hdisjYX : Disjoint Y X := hdisjXY.symm
        have hsurv :=
          cycle_edges_mem_suppressInternal_noYY (c := cind) hcind hU0 hX hdisjYX
            hp hs hedges hnoAA hnocross hstay hstartY' hfinY hnoXX
        let G' := suppressInternal Gind (Aind ∪ X)
        let c' := cind.transferEdges hsurv
        have hc' : c'.support = Uind :=
          (GraphCycle.transferEdges_support cind hsurv).trans hcind
        have hedges' : c'.edges = cind.edges :=
          GraphCycle.transferEdges_edges cind hsurv
        have hA'sub : Aind ∪ X ⊆ Uind := by
          intro x hx
          rcases mem_union.1 hx with h | h
          · exact hAind h
          · exact (mem_sdiff.1 (hU0 (hX h))).1
        have hAne' : (Aind ∪ X).Nonempty := ⟨a, mem_union.2 (Or.inl haA)⟩
        have hK' : IsCograph G' (Uind \ (Aind ∪ X)) :=
          isCograph_suppressInternal (Finset.disjoint_sdiff).symm
            (isCograph_sdiff_union_Y (U := Uind) (A := Aind) (Y := X) hKind)
        have hpnum' : pathCoverNumber G' (Uind \ (Aind ∪ X)) < (Aind ∪ X).card := by
          have hEq := pathCoverNumber_carrier (G := Gind) Uind (Aind ∪ X)
          have hltX := pathCoverNumber_lt_of_delete_Y (U := Uind) (A := Aind)
            (U0 := U0) (Y := X) hU0 hX hstrictind
          exact hEq ▸ hltX
        have hlt : (Uind \ (Aind ∪ X)).card < n := by
          have hsubX : X ⊆ Uind \ Aind := hX.trans hU0
          have hEq : Uind \ (Aind ∪ X) = (Uind \ Aind) \ X :=
            (sdiff_sdiff_eq_sdiff_union Uind Aind X).symm
          rw [hEq, card_sdiff_of_subset hsubX]
          have hpos : 0 < X.card := card_pos.2 hXne
          have hle : X.card ≤ (Uind \ Aind).card := card_le_card hsubX
          omega
        obtain ⟨q', hq'sup, hq'st, hq'fin, hq'ne, hq'P⟩ :=
          ih (Uind \ (Aind ∪ X)).card hlt G' Uind (Aind ∪ X) c' rfl hc' hA'sub
            hAne' hK' hpnum'
        have h4 : 4 ≤ (cind.boundaryEdges U0).card :=
          four_le_card_cycle_boundary_U0 (c := cind) hcind hU0 hp hs hedges hstay h2
        exact exists_lift_restored (X := Y) (Y := X) cind hcind hAind hU0 hY hX
          hdisjYX hXne hjoinYX hnocross hp hs hedges hstay hstartY' hfinY h4
          hq'sup hc' hq'st hq'fin hq'ne hq'P hedges'

/-- Canonical-predicate API for the same protected sufficient theorem. -/
theorem exists_protectedAt_of_strict_of_canonical {U A : Finset V}
    {G : SimpleGraph V} (c : GraphCycle G)
    (hc : c.support = U) (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : Nikoghosyan.IsCograph G (U \ A))
    (hstrict : pathCoverNumber G (U \ A) < A.card) :
    ∃ p : GraphPath G,
      p.support = U ∧ p.start ∈ A ∧ p.finish ∈ A ∧
        p.start ≠ p.finish ∧ p.ProtectedAt c A :=
  exists_protectedAt_of_strict c hc hA hAne (isCograph_iff.2 hK) hstrict

end Cograph
end Nikoghosyan
