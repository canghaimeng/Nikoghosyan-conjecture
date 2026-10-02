/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.HamiltonEndpoints

/-!
# Balanced spanning-path endpoint classes

Manuscript `cog:prop:hamilton-endpoints`, balanced child: a connected
traceable cograph of order at least two is either a critical complete
join, in which case the checked identity `R = D` and the nonempty
extended part-cut apply, or else both join capacities are balanced.
In the balanced case `E(U) = U`, the actual R-incompatible classes
`Q_x = {x} ∪ F(U.erase x)` partition `U`, pairs from distinct classes
are realised by original spanning paths, and `c(U \ P) = |P|` for every
part `P`.

Strong induction is on support cardinality. Extension
`R(U)(x, y) ↔ Eligible(U.erase x) y` is proved, not assumed. Adding a
vertex to a smaller critical remainder uses an original-adjacency
label map to old components, never an unproved monotonicity of
component counts.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma IsCograph.subset {U W : Finset V}
    (hW : IsCograph G W) (hUW : U ⊆ W) : IsCograph G U :=
  fun _ _ _ _ ha hb hc hd => hW (hUW ha) (hUW hb) (hUW hc) (hUW hd)

/-- R-incompatible class of `x` inside `U`, including `x` itself. -/
noncomputable def rNonadjClass (U : Finset V) (x : V) : Finset V :=
  U.filter fun y => ¬ SpanningPathCompatible (G := G) U x y

lemma mem_rNonadjClass_iff {U : Finset V} {x y : V} :
    y ∈ rNonadjClass (G := G) U x ↔
      y ∈ U ∧ ¬ SpanningPathCompatible (G := G) U x y := by
  simp [rNonadjClass]

lemma rNonadjClass_subset (U : Finset V) (x : V) :
    rNonadjClass (G := G) U x ⊆ U :=
  filter_subset _ _

lemma not_SpanningPathCompatible_self (U : Finset V) (x : V) :
    ¬ SpanningPathCompatible (G := G) U x x := fun h => h.1 rfl

lemma mem_rNonadjClass_self {U : Finset V} {x : V} (hx : x ∈ U) :
    x ∈ rNonadjClass (G := G) U x :=
  mem_rNonadjClass_iff.2 ⟨hx, not_SpanningPathCompatible_self (G := G) U x⟩

/-- Paper `Q_x = {x} ∪ F(U − x)`. -/
noncomputable def qxSet (U : Finset V) (x : V) : Finset V :=
  insert x (ineligibleSet G (U.erase x))

lemma mem_qxSet_iff {U : Finset V} {x y : V} :
    y ∈ qxSet (G := G) U x ↔
      y = x ∨ y ∈ ineligibleSet G (U.erase x) := by
  simp [qxSet]

lemma pathCoverNumber_eq_one_of_support {U : Finset V}
    (p : GraphPath G) (hp : p.support = U) :
    pathCoverNumber G U = 1 := by
  have hne : U.Nonempty := by rw [← hp]; exact p.support_nonempty
  let pc : PathCover G U := (PathCover.ofPath p).cast hp
  have hcard : pc.card = 1 := by
    rw [PathCover.cast_card, PathCover.ofPath_card]
  have hle := pathCoverNumber_le (G := G) pc
  have hge := one_le_pathCoverNumber_of_nonempty (G := G) hne
  omega

lemma Eligible_of_support_ends {U : Finset V} (p : GraphPath G)
    (hp : p.support = U) :
    Eligible G U p.start ∧ Eligible G U p.finish := by
  let pc : PathCover G U := (PathCover.ofPath p).cast hp
  have hcard : pc.card = 1 := by
    rw [PathCover.cast_card, PathCover.ofPath_card]
  have hmin : pc.card = pathCoverNumber G U :=
    hcard.trans (pathCoverNumber_eq_one_of_support p hp).symm
  have hmem : p ∈ pc.paths := by
    rw [PathCover.cast_paths, PathCover.ofPath]
    exact List.mem_singleton.2 rfl
  exact Eligible.of_min_cover_endpoint pc hmin hmem

lemma exists_spanning_path_of_eligible_eq_one {U : Finset V} {y : V}
    (hp : pathCoverNumber G U = 1) (hE : Eligible G U y) :
    ∃ p : GraphPath G, p.support = U ∧ (p.start = y ∨ p.finish = y) := by
  obtain ⟨pc, hpc, p, hpmem, hy⟩ := hE
  have hlen : pc.card = 1 := hpc.trans hp
  obtain ⟨q, hq⟩ := PathCover.exists_singleton_of_card_one pc hlen
  have hpq : p = q := by simpa [hq] using hpmem
  subst hpq
  refine ⟨p, ?_, hy.imp Eq.symm Eq.symm⟩
  ext z
  constructor
  · intro hz
    exact pc.support_subset (by simp [hq]) hz
  · intro hzU
    obtain ⟨r, hr, hzr⟩ := (pc.mem_iff z).1 hzU
    have : r = p := by simpa [hq] using hr
    simpa [this] using hzr

/-- Delete an endpoint of a spanning `x`-`y` path; the remainder still
spans the erased support and retains the surviving endpoint `y`. -/
lemma exists_erase_endpoint_path {U : Finset V} {x y : V}
    (p : GraphPath G) (hp : p.support = U) (hxy : x ≠ y)
    (hends : (p.start = x ∧ p.finish = y) ∨ (p.start = y ∧ p.finish = x)) :
    ∃ q : GraphPath G, q.support = U.erase x ∧
      (q.start = y ∨ q.finish = y) := by
  have hnil : ¬ p.walk.Nil := by
    intro h
    have heq := (GraphPath.nil_iff_start_eq_finish p).1 h
    rcases hends with ⟨hs, hf⟩ | ⟨hs, hf⟩
    · exact hxy (hs.symm.trans (heq.trans hf))
    · exact hxy (hf.symm.trans (heq.symm.trans hs))
  rcases hends with ⟨hs, hf⟩ | ⟨hs, hf⟩
  · refine ⟨p.trimStart hnil, ?_, Or.inr ?_⟩
    · simpa [GraphPath.support_trimStart, hs, hp]
    · simp [GraphPath.trimStart, hf]
  · refine ⟨p.trimFinish hnil, ?_, Or.inl ?_⟩
    · simpa [GraphPath.support_trimFinish, hf, hp]
    · simp [GraphPath.trimFinish, hs]

lemma Eligible_erase_of_spanning {U : Finset V} {x y : V}
    (hR : SpanningPathCompatible (G := G) U x y) :
    Eligible G (U.erase x) y := by
  obtain ⟨hxy, p, hp, hends⟩ := hR
  obtain ⟨q, hq, hy⟩ := exists_erase_endpoint_path p hp hxy hends
  have hE := Eligible_of_support_ends q hq
  rcases hy with hs | hf
  · simpa [hs] using hE.1
  · simpa [hf] using hE.2

lemma sdiff_eq_erase_sdiff_erase {U S : Finset V} {x : V} (hxS : x ∈ S) :
    U \ S = U.erase x \ S.erase x := by
  ext z
  simp only [mem_sdiff, mem_erase]
  constructor
  · intro ⟨hzU, hzS⟩
    exact ⟨⟨fun hzx => hzS (hzx ▸ hxS), hzU⟩, fun h => hzS h.2⟩
  · intro ⟨⟨hzx, hzU⟩, hzSe⟩
    refine ⟨hzU, fun hzS => hzSe ⟨hzx, hzS⟩⟩

/-- Generic both-endpoints cut bound: an actual spanning `x`-`y` path and a
set containing both distinct ends leaves at most `|S| − 1` components.
No cograph or toughness hypothesis is used. -/
lemma componentCount_sdiff_le_of_both_endpoints {U S : Finset V} {x y : V}
    (hS : S ⊆ U) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hR : SpanningPathCompatible (G := G) U x y) :
    componentCount G (U \ S) ≤ S.card - 1 := by
  obtain ⟨_, p, hp, hends⟩ := hR
  obtain ⟨q, hq, hyend⟩ := exists_erase_endpoint_path p hp hxy hends
  have hEy : Eligible G (U.erase x) y := by
    have hE := Eligible_of_support_ends q hq
    rcases hyend with hs | hf
    · simpa [hs] using hE.1
    · simpa [hf] using hE.2
  have hpK : pathCoverNumber G (U.erase x) = 1 :=
    pathCoverNumber_eq_one_of_support q hq
  have hEq : U \ S = U.erase x \ S.erase x := sdiff_eq_erase_sdiff_erase hx
  have hsub : S.erase x ⊆ U.erase x := by
    intro z hz
    exact mem_erase.2 ⟨(mem_erase.1 hz).1, hS (mem_of_mem_erase hz)⟩
  have hySe : y ∈ S.erase x := mem_erase.2 ⟨hxy.symm, hy⟩
  have hle :=
    componentCount_sdiff_le_of_eligible (G := G) hsub hySe hEy
  have hcard : (S.erase x).card = S.card - 1 := card_erase_of_mem hx
  have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)
  rw [hEq]
  omega

/-- Attach an original edge at an endpoint of a spanning path of `K`. -/
lemma SpanningPathCompatible_extend {K : Finset V} {x y z : V}
    (hR : SpanningPathCompatible (G := G) K z y)
    (hadj : G.Adj x z) (hx : x ∉ K) :
    SpanningPathCompatible (G := G) (insert x K) x y := by
  obtain ⟨hne, p0, hp0, hends⟩ := hR
  let p : GraphPath G :=
    if h : p0.start = z ∧ p0.finish = y then p0 else p0.reverse
  have hp : p.support = K := by
    by_cases h : p0.start = z ∧ p0.finish = y
    · simpa [p, h] using hp0
    · simpa [p, h, GraphPath.support_reverse] using hp0
  have hzy : p.start = z ∧ p.finish = y := by
    by_cases h : p0.start = z ∧ p0.finish = y
    · simpa [p, h]
    · have h' : p0.start = y ∧ p0.finish = z := by
        rcases hends with h1 | h2
        · exact (h h1).elim
        · exact h2
      have hp' : p = p0.reverse := dif_neg h
      refine ⟨?_, ?_⟩
      · simpa [hp', GraphPath.reverse] using h'.2
      · simpa [hp', GraphPath.reverse] using h'.1
  have hx' : x ∉ p.support := by simpa [hp] using hx
  have hadj' : G.Adj x p.start := by simpa [hzy.1] using hadj
  let r := p.consAdj hadj' hx'
  have hxny : x ≠ y := fun hxy => hx (by
    have : y ∈ p0.support := by
      rcases hends with h1 | h2
      · simpa [h1.2] using p0.finish_mem_support
      · simpa [h2.1] using p0.start_mem_support
    simpa [hxy, hp0] using this)
  refine ⟨hxny, r, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · simpa [r, GraphPath.support_consAdj, hp]
  · simp [r, GraphPath.consAdj, hzy.2]

lemma pathCoverNumber_child_le_succ {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hp : pathCoverNumber G (A ∪ B) = 1) :
    pathCoverNumber G A ≤ B.card + 1 := by
  have h := pathCoverNumber_complete_join_ge_sub hAB
  omega

lemma pathCoverNumber_child_le_of_not_crit {A B : Finset V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hp : pathCoverNumber G (A ∪ B) = 1)
    (hnot : pathCoverNumber G A ≠ B.card + 1) :
    pathCoverNumber G A ≤ B.card := by
  have hle := pathCoverNumber_child_le_succ hAB hp
  omega

/-- Balanced nonempty-cut bound from full eligibility and `p = 1`. -/
lemma componentCount_sdiff_le_card_of_eligible_all {U S : Finset V}
    (hp : pathCoverNumber G U = 1)
    (hE : eligibleSet G U = U)
    (hS : S ⊆ U) (hSne : S.Nonempty) :
    componentCount G (U \ S) ≤ S.card := by
  obtain ⟨x, hxS⟩ := hSne
  have hxE : Eligible G U x := by
    have : x ∈ eligibleSet G U := by simpa [hE] using hS hxS
    exact (mem_eligibleSet_iff (G := G)).1 this |>.2
  have hle := componentCount_sdiff_le_of_eligible (G := G) hS hxS hxE
  have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.2 ⟨x, hxS⟩)
  omega

lemma insert_erase_eq {U : Finset V} {x : V} (hx : x ∈ U) :
    insert x (U.erase x) = U :=
  insert_erase hx

lemma qxSet_sdiff {U : Finset V} {x : V} (hx : x ∈ U) :
    U \ qxSet (G := G) U x = U.erase x \ ineligibleSet G (U.erase x) := by
  ext z
  simp only [mem_sdiff, qxSet, mem_insert]
  constructor
  · intro ⟨hzU, hzQ⟩
    have hzx : z ≠ x := fun h => hzQ (Or.inl h)
    exact ⟨mem_erase.2 ⟨hzx, hzU⟩, fun hF => hzQ (Or.inr hF)⟩
  · intro ⟨hzK, hzF⟩
    exact ⟨(mem_erase.1 hzK).2, fun h => h.elim
      (fun hzx => (mem_erase.1 hzK).1 hzx) hzF⟩

lemma card_qxSet {U : Finset V} {x : V} (hx : x ∈ U) :
    (qxSet (G := G) U x).card = (ineligibleSet G (U.erase x)).card + 1 := by
  have hxF : x ∉ ineligibleSet G (U.erase x) := fun h =>
    (mem_erase.1 ((ineligibleSet_subset (G := G) (U.erase x)) h)).1 rfl
  simp [qxSet, card_insert_of_notMem hxF]

lemma componentCount_sdiff_qxSet_eq {U : Finset V} {x : V}
    (hx : x ∈ U) (hK : IsCograph G (U.erase x))
    (hpK : pathCoverNumber G (U.erase x) = 1) :
    componentCount G (U \ qxSet (G := G) U x) =
      (qxSet (G := G) U x).card := by
  have hcut :=
    componentCount_sdiff_ineligibleSet_eq_of_isCograph (G := G) hK
  have hrew := qxSet_sdiff (G := G) hx
  have hcard := card_qxSet (G := G) hx
  rw [hrew, hcut, hcard, hpK, add_comm]

/-- Original-adjacency label map: if every neighbour of an external
vertex in `Rem` lies in one actual old component, then inserting that
vertex cannot decrease the component count. -/
lemma componentCount_insert_ge_of_neighbors_in_one {Rem W : Finset V} {x : V}
    (hx : x ∉ Rem) (hW : W ⊆ Rem) (hWne : W.Nonempty)
    (hcomp : InOneComponent (G := G) Rem W)
    (hN : ∀ z ∈ Rem, G.Adj x z → z ∈ W) :
    componentCount G Rem ≤ componentCount G (insert x Rem) := by
  obtain ⟨C0, hC0⟩ := exists_component_of_inOneComponent hWne hcomp
  let oldLabel : ((insert x Rem : Finset V) : Set V) →
      (G.induce (Rem : Set V)).ConnectedComponent := fun v =>
    if hvx : v.val = x then C0
    else
      (G.induce (Rem : Set V)).connectedComponentMk
        ⟨v.val, (mem_insert.1 v.property).resolve_left hvx⟩
  have hAdj : ∀ {a b : ((insert x Rem : Finset V) : Set V)},
      (G.induce ((insert x Rem : Finset V) : Set V)).Adj a b →
        oldLabel a = oldLabel b := by
    intro a b hadj
    have hadjG : G.Adj a.val b.val := by simpa [induce_adj] using hadj
    by_cases ha : a.val = x
    · by_cases hb : b.val = x
      · simp [oldLabel, ha, hb]
      · have hbR : b.val ∈ Rem := (mem_insert.1 b.property).resolve_left hb
        have hbW : b.val ∈ W := hN b.val hbR (by simpa [ha] using hadjG)
        obtain ⟨hbU, hbeq⟩ := hC0 b.val hbW
        simp [oldLabel, ha, hb]
        have : (G.induce (Rem : Set V)).connectedComponentMk ⟨b.val, hbU⟩ = C0 := hbeq
        exact this.symm
    · by_cases hb : b.val = x
      · have haR : a.val ∈ Rem := (mem_insert.1 a.property).resolve_left ha
        have haW : a.val ∈ W := hN a.val haR (by simpa [hb] using hadjG.symm)
        obtain ⟨haU, hAeq⟩ := hC0 a.val haW
        simp [oldLabel, ha, hb]
        exact hAeq
      · have haR : a.val ∈ Rem := (mem_insert.1 a.property).resolve_left ha
        have hbR : b.val ∈ Rem := (mem_insert.1 b.property).resolve_left hb
        simp [oldLabel, ha, hb]
        exact Adj.reachable (by simpa [induce_adj] using hadjG)
  have hwalk : ∀ {a b : ((insert x Rem : Finset V) : Set V)}
      (p : (G.induce ((insert x Rem : Finset V) : Set V)).Walk a b),
      oldLabel a = oldLabel b := by
    intro a b p
    induction p with
    | nil => rfl
    | cons hadj q ih => exact (hAdj hadj).trans ih
  have hreach : ∀ {a b : ((insert x Rem : Finset V) : Set V)},
      (G.induce ((insert x Rem : Finset V) : Set V)).Reachable a b →
        oldLabel a = oldLabel b := fun h =>
    hwalk (Classical.choice h)
  let f : (G.induce ((insert x Rem : Finset V) : Set V)).ConnectedComponent →
      (G.induce (Rem : Set V)).ConnectedComponent :=
    ConnectedComponent.lift oldLabel fun a b p _hp => hreach ⟨p⟩
  have hf : Function.Surjective f := by
    intro C
    refine C.ind fun v => ?_
    have hvR : v.val ∈ Rem := v.property
    have hvI : v.val ∈ insert x Rem := mem_insert_of_mem hvR
    refine ⟨(G.induce ((insert x Rem : Finset V) : Set V)).connectedComponentMk
      ⟨v.val, hvI⟩, ?_⟩
    change oldLabel ⟨v.val, hvI⟩ = (G.induce (Rem : Set V)).connectedComponentMk v
    have hvx : v.val ≠ x := fun h => hx (h ▸ hvR)
    simp [oldLabel, hvx]
  haveI : Fintype (G.induce (Rem : Set V)).ConnectedComponent := inferInstance
  haveI : Fintype
      (G.induce ((insert x Rem : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  simpa [componentCount, Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_surjective f hf

/-- Cycle-opening: an original spanning cycle of order at least three
makes every vertex an endpoint of a spanning original path. -/
lemma GraphCycle.exists_spanning_path (c : GraphCycle G) :
    ∃ p : GraphPath G, p.support = c.support ∧ G.Adj p.finish p.start := by
  have hnil : ¬ c.walk.Nil := c.isCycle.not_nil
  obtain ⟨w, hadj, q, hwalk⟩ := (Walk.not_nil_iff.1 hnil)
  have hq : q.IsPath :=
    ((Walk.cons_isCycle_iff q hadj).1 (by simpa [hwalk] using c.isCycle)).1
  let p : GraphPath G := ⟨w, c.start, q, hq⟩
  refine ⟨p, ?_, hadj⟩
  have hstart : c.start ∈ q.support := Walk.end_mem_support q
  simp [p, GraphPath.support, GraphCycle.support, hwalk, Walk.support_cons,
    insert_eq_of_mem (List.mem_toFinset.2 hstart)]

lemma eligible_of_cycle {U : Finset V} {x : V}
    (c : GraphCycle G) (hc : c.support = U) (hx : x ∈ U) :
    Eligible G U x := by
  obtain ⟨r, hr, hadj⟩ := GraphCycle.exists_spanning_path c
  have hrU : r.support = U := hr.trans hc
  have hmin_of (p : GraphPath G) (hp : p.support = U) :
      Eligible G U p.start ∧ Eligible G U p.finish :=
    Eligible_of_support_ends p hp
  by_cases hxs : x = r.start
  · simpa [hxs] using (hmin_of r hrU).1
  by_cases hxf : x = r.finish
  · simpa [hxf] using (hmin_of r hrU).2
  obtain ⟨p, hp, hstart⟩ :=
    exists_spanning_path_start_of_internal (U := U) r hrU hadj hx hxs hxf
  simpa [hstart] using (hmin_of p hp).1

lemma eligibleSet_eq_of_cycle {U : Finset V}
    (c : GraphCycle G) (hc : c.support = U) :
    eligibleSet G U = U := by
  ext x
  constructor
  · intro hx
    exact eligibleSet_subset (G := G) U hx
  · intro hx
    exact (mem_eligibleSet_iff (G := G)).2 ⟨hx, eligible_of_cycle c hc hx⟩

/-- Critical join packaged as actual R/D identity plus nonempty part-cuts. -/
def IsCriticalEndpoints (U : Finset V) : Prop :=
  ∃ (A B : Finset V),
    A.Nonempty ∧ B.Nonempty ∧ A ∪ B = U ∧
      G.IsCompleteBetween (A : Set V) (B : Set V) ∧
        pathCoverNumber G A = B.card + 1 ∧
          IsCograph G A ∧
            eligibleSet G U = eligibleSet G A ∧
              ineligibleSet G U = B ∪ ineligibleSet G A ∧
                (∀ x y, SpanningPathCompatible (G := G) U x y ↔
                  DistinctPathCompatible (G := G) A x y) ∧
                  ∀ x, x ∈ eligibleSet G A →
                    ∃ S, S ⊆ ineligibleSet G U ∧ S.Nonempty ∧
                      componentCount G (U \ S) = S.card + 1 ∧
                        InOneComponent (G := G) (U \ S)
                          ((ineligibleSet G U ∪
                            dNonadjClass (G := G) A x) \ S)

/-- Balanced complete-multipartite R on the whole vertex set, with actual
part-cut equalities. -/
def IsBalancedEndpoints (U : Finset V) : Prop :=
  eligibleSet G U = U ∧
    (∀ x, x ∈ U →
      componentCount G (U \ rNonadjClass (G := G) U x) =
        (rNonadjClass (G := G) U x).card) ∧
      (∀ {x y : V}, x ∈ U → y ∈ U →
        (rNonadjClass (G := G) U x = rNonadjClass (G := G) U y ↔
          y ∈ rNonadjClass (G := G) U x))

def HamiltonEndpointsData (U : Finset V) : Prop :=
  IsCriticalEndpoints (G := G) U ∨ IsBalancedEndpoints (G := G) U

lemma critical_endpoints_of_join {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hcrit : pathCoverNumber G A = B.card + 1)
    (hA : IsCograph G A) :
    IsCriticalEndpoints (G := G) (A ∪ B) := by
  refine ⟨A, B, hAne, hBne, rfl, hAB, hcrit, hA,
    eligibleSet_complete_join_critical hAne hBne hAB hcrit,
    ineligibleSet_complete_join_critical hAne hBne hAB hcrit, ?_, ?_⟩
  · intro x y
    simpa using
      (SpanningPathCompatible_critical_iff (G := G) hAne hBne hAB hcrit
        (x := x) (y := y))
  · intro x hx
    exact exists_critical_partCut hAne hBne hAB hcrit hA hx

lemma spanningPathCompatible_symm {U : Finset V} {x y : V}
    (h : SpanningPathCompatible (G := G) U x y) :
    SpanningPathCompatible (G := G) U y x := by
  obtain ⟨hne, p, hp, hends⟩ := h
  exact ⟨hne.symm, p, hp, hends.symm⟩

lemma isCompleteBetween_symm {A B : Finset V}
    (h : G.IsCompleteBetween (A : Set V) (B : Set V)) :
    G.IsCompleteBetween (B : Set V) (A : Set V) :=
  fun {_} hb {_} ha => (h ha hb).symm

lemma insert_erase_sdiff {U S : Finset V} {x : V}
    (hx : x ∈ U) (hxS : x ∉ S) :
    insert x (U.erase x \ S) = U \ S := by
  ext z
  simp only [mem_insert, mem_sdiff, mem_erase]
  constructor
  · intro h
    rcases h with rfl | ⟨⟨_, hzU⟩, hzS⟩
    · exact ⟨hx, hxS⟩
    · exact ⟨hzU, hzS⟩
  · intro ⟨hzU, hzS⟩
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr ⟨⟨hzx, hzU⟩, hzS⟩

lemma mem_eligibleSet_of_mem_not_ineligible {U : Finset V} {z : V}
    (hzU : z ∈ U) (hzF : z ∉ ineligibleSet G U) :
    z ∈ eligibleSet G U := by
  have : z ∈ eligibleSet G U ∪ ineligibleSet G U := by
    simpa [eligibleSet_union_ineligibleSet] using hzU
  exact (mem_union.1 this).resolve_right hzF

lemma rNonadjClass_eq_qxSet_of_extension {U : Finset V} {x : V}
    (hx : x ∈ U)
    (hiff : ∀ y ∈ U.erase x,
      SpanningPathCompatible (G := G) U x y ↔ Eligible G (U.erase x) y) :
    rNonadjClass (G := G) U x = qxSet (G := G) U x := by
  ext y
  constructor
  · intro hyQ
    have hyU : y ∈ U := rNonadjClass_subset (G := G) U x hyQ
    have hnotR : ¬ SpanningPathCompatible (G := G) U x y :=
      (mem_rNonadjClass_iff.1 hyQ).2
    by_cases hyx : y = x
    · simp [qxSet, hyx]
    · have hyK : y ∈ U.erase x := mem_erase.2 ⟨hyx, hyU⟩
      have hnotE : ¬ Eligible G (U.erase x) y := fun hE => hnotR ((hiff y hyK).2 hE)
      exact mem_qxSet_iff.2 (Or.inr ((mem_ineligibleSet_iff (G := G)).2
        ⟨hyK, hnotE⟩))
  · intro hyQ
    rcases mem_qxSet_iff.1 hyQ with rfl | hyF
    · exact mem_rNonadjClass_self hx
    · have hyK : y ∈ U.erase x := ineligibleSet_subset (G := G) (U.erase x) hyF
      have hnotE : ¬ Eligible G (U.erase x) y :=
        (mem_ineligibleSet_iff (G := G)).1 hyF |>.2
      have hnotR : ¬ SpanningPathCompatible (G := G) U x y := fun hR =>
        hnotE ((hiff y hyK).1 hR)
      exact mem_rNonadjClass_iff.2 ⟨(mem_erase.1 hyK).2, hnotR⟩

/-- Sufficiency of the extension equivalence: an eligible vertex of `K`
that is not R-adjacent to the deleted vertex yields a toughness
contradiction from the inductive certificate of `K`. -/
lemma false_of_eligible_not_extend {U : Finset V} {x y : V}
    (hx : x ∈ U)
    (hEy : Eligible G (U.erase x) y)
    (hnot : ¬ SpanningPathCompatible (G := G) U x y)
    (hKdata : HamiltonEndpointsData (G := G) (U.erase x))
    (hpK : pathCoverNumber G (U.erase x) = 1)
    (hEall : eligibleSet G U = U)
    (hpU : pathCoverNumber G U = 1) :
    False := by
  set K := U.erase x
  have hyK : y ∈ K := Eligible.mem (G := G) hEy
  have hxK : x ∉ K := notMem_erase x U
  have hUK : insert x K = U := insert_erase hx
  rcases hKdata with hcrit | hbal
  · obtain ⟨A, B, hAne, hBne, hunion, hAB, hcritAB, hA, hEeq, hFeq, hRiff, hpart⟩ :=
      hcrit
    have hyE : y ∈ eligibleSet G A := by
      have : y ∈ eligibleSet G K := (mem_eligibleSet_iff (G := G)).2 ⟨hyK, hEy⟩
      rwa [← hEeq]
    let P := dNonadjClass (G := G) A y
    have hyP : y ∈ P := mem_dNonadjClass_self hyE
    have hN : ∀ z ∈ K, G.Adj x z → z ∈ ineligibleSet G K ∪ P := by
      intro z hzK hadj
      by_cases hzF : z ∈ ineligibleSet G K
      · exact mem_union.2 (Or.inl hzF)
      · have hzE : z ∈ eligibleSet G K :=
          mem_eligibleSet_of_mem_not_ineligible hzK hzF
        by_cases hzP : z ∈ P
        · exact mem_union.2 (Or.inr hzP)
        · have hzEA : z ∈ eligibleSet G A := by rwa [hEeq] at hzE
          have hD : DistinctPathCompatible (G := G) A y z := by
            by_contra hnotD
            exact hzP (mem_dNonadjClass_iff.2 ⟨hzEA, hnotD⟩)
          have hRKyz : SpanningPathCompatible (G := G) K y z :=
            (hRiff y z).2 hD
          have hRU : SpanningPathCompatible (G := G) (insert x K) x y :=
            SpanningPathCompatible_extend (spanningPathCompatible_symm hRKyz) hadj hxK
          exact (hnot (by simpa [hUK] using hRU)).elim
    obtain ⟨S, hSsub, hSne, hScut, hScomp⟩ := hpart y hyE
    have hSF : S ⊆ ineligibleSet G K := hSsub
    have hxS : x ∉ S := fun h => hxK (ineligibleSet_subset (G := G) K (hSF h))
    have hWU :
        ((ineligibleSet G K ∪ P) \ S) ⊆ K \ S := by
      intro z hz
      have hzKP : z ∈ ineligibleSet G K ∪ P := (mem_sdiff.1 hz).1
      have hzS : z ∉ S := (mem_sdiff.1 hz).2
      have hzK : z ∈ K := by
        rcases mem_union.1 hzKP with hzF | hzP'
        · exact ineligibleSet_subset (G := G) K hzF
        · have hsub : eligibleSet G A ⊆ K := by
            simpa [hEeq] using eligibleSet_subset (G := G) K
          exact hsub (dNonadjClass_subset_eligible (G := G) A y hzP')
      exact mem_sdiff.2 ⟨hzK, hzS⟩
    have hWne : ((ineligibleSet G K ∪ P) \ S).Nonempty := by
      refine ⟨y, mem_sdiff.2 ⟨mem_union.2 (Or.inr hyP), ?_⟩⟩
      intro hyS
      have hyF := hSF hyS
      have hyE' : y ∈ eligibleSet G K := (mem_eligibleSet_iff (G := G)).2 ⟨hyK, hEy⟩
      exact (disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) K)
        hyE') hyF
    have hNRem : ∀ z ∈ K \ S, G.Adj x z → z ∈ (ineligibleSet G K ∪ P) \ S := by
      intro z hzRem hadj
      have hzK : z ∈ K := (mem_sdiff.1 hzRem).1
      have hzS : z ∉ S := (mem_sdiff.1 hzRem).2
      have hzFP := hN z hzK hadj
      exact mem_sdiff.2 ⟨hzFP, hzS⟩
    have hge :=
      componentCount_insert_ge_of_neighbors_in_one (Rem := K \ S)
        (W := (ineligibleSet G K ∪ P) \ S) (x := x)
        (fun h => hxK (mem_sdiff.1 h).1) hWU hWne hScomp hNRem
    have hinsert : insert x (K \ S) = U \ S :=
      insert_erase_sdiff hx hxS
    have hge' : S.card + 1 ≤ componentCount G (U \ S) := by
      simpa [hScut, hinsert] using hge
    have hSsubU : S ⊆ U :=
      (hSF.trans (ineligibleSet_subset (G := G) K)).trans (erase_subset x U)
    have hle :=
      componentCount_sdiff_le_card_of_eligible_all hpU hEall hSsubU hSne
    omega
  · obtain ⟨hEK, hcutK, _hclass⟩ := hbal
    have hF : ineligibleSet G K = ∅ := by
      ext z
      constructor
      · intro hz
        have hzK : z ∈ K := ineligibleSet_subset (G := G) K hz
        have hzE : z ∈ eligibleSet G K := by simpa [hEK] using hzK
        exact (disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) K)
          hzE hz).elim
      · intro hz
        exact (notMem_empty z hz).elim
    let P := rNonadjClass (G := G) K y
    have hyP : y ∈ P := mem_rNonadjClass_self hyK
    have hN : ∀ z ∈ K, G.Adj x z → z ∈ P := by
      intro z hzK hadj
      by_cases hzP : z ∈ P
      · exact hzP
      · have hRKyz : SpanningPathCompatible (G := G) K y z := by
          by_contra hnotR
          exact hzP (mem_rNonadjClass_iff.2 ⟨hzK, hnotR⟩)
        have hRU : SpanningPathCompatible (G := G) (insert x K) x y :=
          SpanningPathCompatible_extend (spanningPathCompatible_symm hRKyz) hadj hxK
        exact (hnot (by simpa [hUK] using hRU)).elim
    have hxP : x ∉ P := fun h => hxK (rNonadjClass_subset (G := G) K y h)
    have hnocross : ∀ a ∈ ({x} : Finset V), ∀ b ∈ K \ P, ¬ G.Adj a b := by
      intro a ha b hb hadj
      have : a = x := mem_singleton.1 ha
      subst this
      have hbK : b ∈ K := (mem_sdiff.1 hb).1
      have hbP : b ∉ P := (mem_sdiff.1 hb).2
      exact hbP (hN b hbK hadj)
    have hdisj : Disjoint ({x} : Finset V) (K \ P) := by
      rw [disjoint_singleton_left]
      intro h
      exact hxK (mem_sdiff.1 h).1
    have hunion : ({x} : Finset V) ∪ (K \ P) = U \ P := by
      have : P ⊆ K := rNonadjClass_subset (G := G) K y
      have hxS : x ∉ P := hxP
      simpa [singleton_union] using insert_erase_sdiff (S := P) hx hxS
    have hadd :=
      componentCount_union_of_no_cross (A := ({x} : Finset V)) (B := K \ P)
        hdisj hnocross
    have hPx : componentCount G ({x} : Finset V) = 1 :=
      componentCount_singleton (G := G) x
    have hPK : componentCount G (K \ P) = P.card := hcutK y hyK
    have hPsub : P ⊆ U :=
      (rNonadjClass_subset (G := G) K y).trans (erase_subset x U)
    have hPne : P.Nonempty := ⟨y, hyP⟩
    have hle :=
      componentCount_sdiff_le_card_of_eligible_all hpU hEall hPsub hPne
    have : componentCount G (U \ P) = P.card + 1 := by
      rw [← hunion, hadd, hPx, hPK, add_comm]
    omega

lemma extension_iff_of_IH {U : Finset V} {x y : V}
    (hx : x ∈ U) (hy : y ∈ U.erase x)
    (hKdata : HamiltonEndpointsData (G := G) (U.erase x))
    (hpK : pathCoverNumber G (U.erase x) = 1)
    (hEall : eligibleSet G U = U)
    (hpU : pathCoverNumber G U = 1) :
    SpanningPathCompatible (G := G) U x y ↔ Eligible G (U.erase x) y := by
  constructor
  · exact fun hR => Eligible_erase_of_spanning hR
  · intro hEy
    by_contra hnot
    exact false_of_eligible_not_extend hx hEy hnot hKdata hpK hEall hpU

lemma class_coincidence_of_qx {U : Finset V}
    (hEall : eligibleSet G U = U)
    (hpU : pathCoverNumber G U = 1)
    (hcut : ∀ x ∈ U,
      componentCount G (U \ rNonadjClass (G := G) U x) =
        (rNonadjClass (G := G) U x).card) :
    ∀ {x y : V}, x ∈ U → y ∈ U →
      (rNonadjClass (G := G) U x = rNonadjClass (G := G) U y ↔
        y ∈ rNonadjClass (G := G) U x) := by
  intro x y hx hy
  constructor
  · intro heq
    simpa [heq] using mem_rNonadjClass_self hy
  · intro hyQ
    have hsub : rNonadjClass (G := G) U x ⊆ rNonadjClass (G := G) U y := by
      intro z hz
      by_cases hzy : z = y
      · simpa [hzy] using mem_rNonadjClass_self hy
      · have hne : y ≠ z := fun h => hzy h.symm
        have hRfalse : ¬ SpanningPathCompatible (G := G) U y z := by
          intro hR
          have hle :=
            componentCount_sdiff_le_of_both_endpoints
              (rNonadjClass_subset (G := G) U x)
              hyQ hz hne hR
          have heq := hcut x hx
          have hpos : 1 ≤ (rNonadjClass (G := G) U x).card :=
            Nat.succ_le_of_lt (card_pos.2 ⟨y, hyQ⟩)
          omega
        exact mem_rNonadjClass_iff.2
          ⟨rNonadjClass_subset (G := G) U x hz, hRfalse⟩
    have hxQy : x ∈ rNonadjClass (G := G) U y := hsub (mem_rNonadjClass_self hx)
    have hsub' : rNonadjClass (G := G) U y ⊆ rNonadjClass (G := G) U x := by
      intro z hz
      by_cases hzx : z = x
      · simpa [hzx] using mem_rNonadjClass_self hx
      · have hRfalse : ¬ SpanningPathCompatible (G := G) U x z := by
          intro hR
          have hle :=
            componentCount_sdiff_le_of_both_endpoints
              (rNonadjClass_subset (G := G) U y)
              hxQy hz (Ne.symm hzx) hR
          have heq := hcut y hy
          have hpos : 1 ≤ (rNonadjClass (G := G) U y).card :=
            Nat.succ_le_of_lt (card_pos.2 ⟨x, hxQy⟩)
          omega
        exact mem_rNonadjClass_iff.2
          ⟨rNonadjClass_subset (G := G) U y hz, hRfalse⟩
    exact subset_antisymm hsub hsub'

lemma support_eq_pair_of_card_two {U : Finset V} (p : GraphPath G)
    (hp : p.support = U) (h2 : U.card = 2) (hne : p.start ≠ p.finish) :
    p.support = {p.start, p.finish} := by
  have hsub : ({p.start, p.finish} : Finset V) ⊆ p.support :=
    insert_subset_iff.2 ⟨p.start_mem_support, singleton_subset_iff.2 p.finish_mem_support⟩
  have hpair : ({p.start, p.finish} : Finset V).card = 2 := by
    rw [card_insert_of_notMem (by simp [hne])]
    simp
  have hsc : p.support.card = 2 := by simpa [hp] using h2
  exact (eq_of_subset_of_card_le hsub (by omega)).symm

lemma balanced_endpoints_of_card_two {U : Finset V}
    (hU : IsCograph G U)
    (hconn : (G.induce (U : Set V)).Connected)
    (hp : pathCoverNumber G U = 1)
    (h2 : U.card = 2) :
    IsBalancedEndpoints (G := G) U := by
  have h2le : 2 ≤ U.card := by omega
  obtain ⟨A, B, hAU, hBU, hAne, hBne, _, hcover, hAB, hAcard, hBcard⟩ :=
    exists_complete_join_on hU hconn h2le
  have hApos : 1 ≤ A.card := card_pos.2 hAne
  have hBpos : 1 ≤ B.card := card_pos.2 hBne
  have hA1 : A.card = 1 := by omega
  have hB1 : B.card = 1 := by omega
  have hpA : pathCoverNumber G A ≤ B.card :=
    (pathCoverNumber_le_card (G := G) A).trans (by omega)
  have hpB : pathCoverNumber G B ≤ A.card :=
    (pathCoverNumber_le_card (G := G) B).trans (by omega)
  have hE : eligibleSet G (A ∪ B) = A ∪ B :=
    eligibleSet_complete_join_balanced hAne hBne hAB hpA hpB
  have hEU : eligibleSet G U = U := by simpa [hcover] using hE
  obtain ⟨p, hpU, hs, hf⟩ :=
    exists_complete_join_spanning_path hAne hBne hAB hpA hpB
  have hsupU : p.support = U := by simpa [hcover] using hpU
  have hsf : p.start ≠ p.finish := by
    intro heq
    have hnil : p.walk.Nil := (GraphPath.nil_iff_start_eq_finish p).2 heq
    have hs1 : p.support = {p.start} := GraphPath.support_eq_singleton_of_nil p hnil
    have : U.card = 1 := by
      rw [← hsupU, hs1, card_singleton]
    omega
  have hRAB : SpanningPathCompatible (G := G) U p.start p.finish :=
    ⟨hsf, p, hsupU, Or.inl ⟨rfl, rfl⟩⟩
  have hpairEnds : p.support = {p.start, p.finish} :=
    support_eq_pair_of_card_two p hsupU h2 hsf
  have hpair : ∀ {u v : V}, u ∈ U → v ∈ U → u ≠ v →
      SpanningPathCompatible (G := G) U u v := by
    intro u v hu hv hne
    have hu' : u = p.start ∨ u = p.finish := by
      have : u ∈ p.support := by simpa [hsupU] using hu
      have : u ∈ ({p.start, p.finish} : Finset V) := by simpa [hpairEnds] using this
      simpa [mem_insert, mem_singleton] using this
    have hv' : v = p.start ∨ v = p.finish := by
      have : v ∈ p.support := by simpa [hsupU] using hv
      have : v ∈ ({p.start, p.finish} : Finset V) := by simpa [hpairEnds] using this
      simpa [mem_insert, mem_singleton] using this
    rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact (hne (hu'.trans hv'.symm)).elim
    · simpa [hu', hv'] using hRAB
    · simpa [hu', hv'] using spanningPathCompatible_symm hRAB
    · exact (hne (hu'.trans hv'.symm)).elim
  refine ⟨hEU, ?_, ?_⟩
  · intro x hx
    have hQ : rNonadjClass (G := G) U x = {x} := by
      ext z
      constructor
      · intro hz
        have hzU : z ∈ U := rNonadjClass_subset (G := G) U x hz
        by_cases hzx : z = x
        · simp [hzx]
        · have hR := hpair hx hzU (fun h => hzx h.symm)
          exact ((mem_rNonadjClass_iff.1 hz).2 hR).elim
      · intro hz
        have : z = x := mem_singleton.1 hz
        simpa [this] using mem_rNonadjClass_self hx
    have hrem : U \ {x} = U.erase x := sdiff_singleton_eq_erase x U
    have hK : (U.erase x).card = 1 := by
      have := card_erase_of_mem hx
      omega
    obtain ⟨w, hw⟩ := card_eq_one.1 hK
    rw [hQ, hrem, hw, componentCount_singleton, card_singleton]
  · intro x y hx hy
    constructor
    · intro heq
      simpa [heq] using mem_rNonadjClass_self hy
    · intro hyQ
      have hQx : rNonadjClass (G := G) U x = {x} := by
        ext z
        constructor
        · intro hz
          have hzU : z ∈ U := rNonadjClass_subset (G := G) U x hz
          by_cases hzx : z = x
          · simp [hzx]
          · exact ((mem_rNonadjClass_iff.1 hz).2 (hpair hx hzU (fun h => hzx h.symm))).elim
        · intro hz
          simpa [mem_singleton.1 hz] using mem_rNonadjClass_self hx
      have : y = x := by
        have : y ∈ ({x} : Finset V) := by simpa [hQx] using hyQ
        exact mem_singleton.1 this
      subst this
      rfl

/-- Strong induction on support order: every connected traceable cograph of
order at least two carries a critical or balanced actual R-certificate. -/
lemma hamilton_endpoints_of_card (n : ℕ) :
    ∀ (U : Finset V), U.card = n →
      2 ≤ U.card →
      IsCograph G U →
      (G.induce (U : Set V)).Connected →
      pathCoverNumber G U = 1 →
      HamiltonEndpointsData (G := G) U := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U hcard h2 hcog hconn hpU
    obtain ⟨A, B, hAU, hBU, hAne, hBne, hdisj, hcover, hAB, hAcard, hBcard⟩ :=
      exists_complete_join_on hcog hconn h2
    have hpAB : pathCoverNumber G (A ∪ B) = 1 := by simpa [hcover] using hpU
    have hpA_le := pathCoverNumber_child_le_succ hAB hpAB
    have hpB_le :=
      pathCoverNumber_child_le_succ (isCompleteBetween_symm hAB)
        (by simpa [union_comm] using hpAB)
    by_cases hAcrit : pathCoverNumber G A = B.card + 1
    · have hA : IsCograph G A := hcog.subset hAU
      have hcert := critical_endpoints_of_join hAne hBne hAB hAcrit hA
      exact Or.inl (hcover ▸ hcert)
    · by_cases hBcrit : pathCoverNumber G B = A.card + 1
      · have hB : IsCograph G B := hcog.subset hBU
        have hcert :=
          critical_endpoints_of_join hBne hAne (isCompleteBetween_symm hAB)
            hBcrit hB
        exact Or.inl (by simpa [union_comm, hcover] using hcert)
      · have hpA : pathCoverNumber G A ≤ B.card := by omega
        have hpB : pathCoverNumber G B ≤ A.card := by omega
        have hEAB :=
          eligibleSet_complete_join_balanced hAne hBne hAB hpA hpB
        have hEall : eligibleSet G U = U := by simpa [hcover] using hEAB
        by_cases h3 : 3 ≤ U.card
        · have hcut : ∀ x ∈ U,
              componentCount G (U \ rNonadjClass (G := G) U x) =
                (rNonadjClass (G := G) U x).card := by
            intro x hx
            have hxE : Eligible G U x :=
              ((mem_eligibleSet_iff (G := G)).1 (by simpa [hEall] using hx)).2
            set K := U.erase x
            have hKcard : K.card = U.card - 1 := card_erase_of_mem hx
            have hK2 : 2 ≤ K.card := by omega
            have hKlt : K.card < n := by omega
            have hKcog : IsCograph G K :=
              hcog.subset (erase_subset x U)
            have hpKle : pathCoverNumber G K ≤ pathCoverNumber G U :=
              pathCoverNumber_erase_le_of_eligible (G := G) hxE
            have hKne : K.Nonempty := card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hK2)
            have hpKge := one_le_pathCoverNumber_of_nonempty (G := G) hKne
            have hpK : pathCoverNumber G K = 1 := by omega
            obtain ⟨pK, hpKsup⟩ :=
              exists_spanning_path_of_pathCoverNumber_eq_one (G := G) hpK
            have hKconn := connected_of_spanning_path pK hpKsup
            have hKdata :=
              ih K.card hKlt K rfl hK2 hKcog hKconn hpK
            have hiff : ∀ y ∈ K,
                SpanningPathCompatible (G := G) U x y ↔ Eligible G K y :=
              fun y hy =>
                extension_iff_of_IH (U := U) hx hy hKdata hpK hEall hpU
            have hQ : rNonadjClass (G := G) U x = qxSet (G := G) U x :=
              rNonadjClass_eq_qxSet_of_extension hx hiff
            have hKcog' : IsCograph G (U.erase x) := hKcog
            have hqx :=
              componentCount_sdiff_qxSet_eq (G := G) hx hKcog' hpK
            simpa [hQ] using hqx
          refine Or.inr ⟨hEall, hcut,
            class_coincidence_of_qx hEall hpU hcut⟩
        · have hcard2 : U.card = 2 := by omega
          exact Or.inr (balanced_endpoints_of_card_two hcog hconn hpU hcard2)

lemma hamilton_endpoints_of_traceable_cograph {U : Finset V}
    (h2 : 2 ≤ U.card)
    (hcog : IsCograph G U)
    (hconn : (G.induce (U : Set V)).Connected)
    (hpU : pathCoverNumber G U = 1) :
    HamiltonEndpointsData (G := G) U :=
  hamilton_endpoints_of_card U.card U rfl h2 hcog hconn hpU

lemma hamilton_endpoints_of_traceable_cograph_canonical {U : Finset V}
    (h2 : 2 ≤ U.card)
    (hcog : Nikoghosyan.IsCograph G U)
    (hconn : (G.induce (U : Set V)).Connected)
    (hpU : pathCoverNumber G U = 1) :
    HamiltonEndpointsData (G := G) U :=
  hamilton_endpoints_of_traceable_cograph h2 (isCograph_iff.2 hcog) hconn hpU

lemma spanning_iff_distinct_classes_of_balanced {U : Finset V}
    (h : IsBalancedEndpoints (G := G) U) {x y : V}
    (hx : x ∈ U) (hy : y ∈ U) :
    SpanningPathCompatible (G := G) U x y ↔
      rNonadjClass (G := G) U x ≠ rNonadjClass (G := G) U y := by
  obtain ⟨_, _, hclass⟩ := h
  constructor
  · intro hR heq
    have hyQ : y ∈ rNonadjClass (G := G) U x := by
      simpa [heq] using mem_rNonadjClass_self hy
    exact (mem_rNonadjClass_iff.1 hyQ).2 hR
  · intro hneQ
    by_contra hnot
    have hyQ : y ∈ rNonadjClass (G := G) U x :=
      mem_rNonadjClass_iff.2 ⟨hy, hnot⟩
    exact hneQ ((hclass hx hy).2 hyQ)

/-- Specialization to an actual Hamiltonian cograph block of order at least
three: opening the original spanning cycle makes every vertex eligible, so
the block is balanced rather than critical, and the actual R classes cover
`U` with class equality capturing incompatibility. -/
lemma hamiltonian_cograph_port {U : Finset V}
    (hcog : IsCograph G U) (c : GraphCycle G) (hc : c.support = U) :
    eligibleSet G U = U ∧
      IsBalancedEndpoints (G := G) U ∧
        (∀ (x y : V), x ∈ U → y ∈ U → x ≠ y →
          (SpanningPathCompatible (G := G) U x y ↔
            rNonadjClass (G := G) U x ≠ rNonadjClass (G := G) U y)) := by
  have h3 : 3 ≤ U.card := by
    simpa [hc] using c.three_le_card_support
  have h2 : 2 ≤ U.card := le_trans (by decide : (2 : ℕ) ≤ 3) h3
  obtain ⟨p, hp, hadj⟩ := GraphCycle.exists_spanning_path c
  have hpUsup : p.support = U := hp.trans hc
  have hpU : pathCoverNumber G U = 1 :=
    pathCoverNumber_eq_one_of_support p hpUsup
  have hconn := connected_of_spanning_path p hpUsup
  have hE : eligibleSet G U = U := eligibleSet_eq_of_cycle c hc
  have hdata :=
    hamilton_endpoints_of_traceable_cograph h2 hcog hconn hpU
  have hbal : IsBalancedEndpoints (G := G) U := by
    rcases hdata with hcrit | hbal
    · obtain ⟨A, B, hAne, hBne, hunion, hAB, hcritAB, _, hEeq, hFeq, _, _⟩ :=
        hcrit
      have hEU : eligibleSet G U = eligibleSet G A := by simpa [hunion] using hEeq
      have hF : ineligibleSet G U = B ∪ ineligibleSet G A := by
        simpa [hunion] using hFeq
      have hBne' : (ineligibleSet G U).Nonempty := by
        refine hBne.mono ?_
        intro z hz
        simpa [hF] using mem_union.2 (Or.inl hz)
      have : eligibleSet G U ≠ U := by
        intro hEq
        have : ineligibleSet G U = ∅ := by
          ext z
          constructor
          · intro hz
            have hzU : z ∈ U := ineligibleSet_subset (G := G) U hz
            have hzE : z ∈ eligibleSet G U := by simpa [hEq] using hzU
            exact (disjoint_left.1 (disjoint_eligibleSet_ineligibleSet (G := G) U)
              hzE hz).elim
          · intro hz
            exact (notMem_empty z hz).elim
        exact hBne'.ne_empty this
      exact (this hE).elim
    · exact hbal
  exact ⟨hE, hbal, fun (x y : V) (hx : x ∈ U) (hy : y ∈ U) (_ : x ≠ y) =>
    spanning_iff_distinct_classes_of_balanced (x := x) (y := y) hbal hx hy⟩

lemma hamiltonian_cograph_port_canonical {U : Finset V}
    (hcog : Nikoghosyan.IsCograph G U) (c : GraphCycle G) (hc : c.support = U) :
    eligibleSet G U = U ∧
      IsBalancedEndpoints (G := G) U ∧
        (∀ (x y : V), x ∈ U → y ∈ U → x ≠ y →
          (SpanningPathCompatible (G := G) U x y ↔
            rNonadjClass (G := G) U x ≠ rNonadjClass (G := G) U y)) :=
  hamiltonian_cograph_port (isCograph_iff.2 hcog) c hc

lemma spanningPath_of_distinct_classes {U : Finset V} {x y : V}
    (h : IsBalancedEndpoints (G := G) U)
    (hx : x ∈ U) (hy : y ∈ U)
    (hne : rNonadjClass (G := G) U x ≠ rNonadjClass (G := G) U y) :
    SpanningPathCompatible (G := G) U x y := by
  obtain ⟨_, _, hclass⟩ := h
  by_contra hnot
  have hyQ : y ∈ rNonadjClass (G := G) U x :=
    mem_rNonadjClass_iff.2 ⟨hy, hnot⟩
  exact hne ((hclass hx hy).2 hyQ)

lemma partCut_of_balanced {U : Finset V} {x : V}
    (h : IsBalancedEndpoints (G := G) U) (hx : x ∈ U) :
    componentCount G (U \ rNonadjClass (G := G) U x) =
      (rNonadjClass (G := G) U x).card :=
  h.2.1 x hx

end Cograph
end Nikoghosyan

