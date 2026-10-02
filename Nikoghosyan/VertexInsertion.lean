/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.TraceableExtension
import Nikoghosyan.CycleInsertion

/-!
Original one-vertex insertion: strict path-cover obstruction.

On a host `J = insert x H` that is 1-tough on that support, with `H` the
support of an actual original cycle and `x ∉ H`, the actual profile
`A = H.filter (G.Adj x)` is nonempty by original connectivity of `J`.
The cycle bound gives `p(H \ A) ≤ |A|`. Equality would produce a tight
container `S ⊆ H` of `A` by the checked canonical-container theorem on
the cograph remainder `H \ A`. Then `x` has no original neighbour in
`H \ S`, so the remainder identity `J \ S = (H \ S) ∪ {x}` is a no-cross
union and `c(J \ S) = |S| + 1 ≥ 2`, contradicting `OneToughOn G J`.

Hence `p(H \ A) < |A|`. No terminal cover, strict profile, protected
path, or inherited induced toughness is assumed. The elementary cycle
splice from an actual `A`-ended spanning path of `H` is recorded, but
existence of that path remains open.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

lemma componentCount_eq_one_of_OneToughOn {J : Finset V}
    (h : OneToughOn G J) (hJ : J.Nonempty) :
    componentCount G J = 1 := by
  haveI : Nonempty (J : Set V) := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  haveI : Nonempty (G.induce (J : Set V)).ConnectedComponent := inferInstance
  have hpos : 0 < componentCount G J := Nat.card_pos
  have hle : componentCount G J ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ componentCount G J := Nat.succ_le_of_lt (lt_of_not_ge hlt)
    have hbound := h ∅ (empty_subset J) (by simpa using h2)
    have : componentCount G J ≤ 0 := by simpa using hbound
    omega
  omega

/-- Isolated insertion: no original edge from `x` into `U` adds one
component. -/
lemma componentCount_insert_of_no_cross {U : Finset V} {x : V}
    (hx : x ∉ U) (hnocross : ∀ u ∈ U, ¬ G.Adj x u) :
    componentCount G (insert x U) = componentCount G U + 1 := by
  have hdisj : Disjoint U {x} := disjoint_singleton_right.2 hx
  have hnc : ∀ a ∈ U, ∀ b ∈ ({x} : Finset V), ¬ G.Adj a b := by
    intro a ha b hb hadj
    have hb' : b = x := mem_singleton.mp hb
    subst hb'
    exact hnocross a ha hadj.symm
  have hunion : insert x U = U ∪ {x} := by
    rw [insert_eq, union_comm]
  rw [hunion, Cograph.componentCount_union_of_no_cross (G := G) hdisj hnc,
    componentCount_singleton]

lemma insert_sdiff_eq_union_singleton {H S : Finset V} {x : V}
    (hx : x ∉ H) (hS : S ⊆ H) :
    insert x H \ S = (H \ S) ∪ {x} := by
  have hxS : x ∉ S := fun h => hx (hS h)
  rw [insert_sdiff_of_notMem (s := H) hxS, insert_eq, union_comm]

lemma not_adj_sdiff_of_rowProfile_subset {H S : Finset V} {x : V}
    (hAS : rowProfile (G := G) H x ⊆ S) :
    ∀ y ∈ H \ S, ¬ G.Adj x y := by
  intro y hy hadj
  have hyH : y ∈ H := (mem_sdiff.1 hy).1
  have hyA : y ∈ rowProfile (G := G) H x :=
    (mem_rowProfile_iff (G := G)).2 ⟨hyH, hadj⟩
  exact (mem_sdiff.1 hy).2 (hAS hyA)

lemma componentCount_host_remainder_eq_add_one {H S : Finset V} {x : V}
    (hx : x ∉ H) (hS : S ⊆ H)
    (hnocross : ∀ y ∈ H \ S, ¬ G.Adj x y) :
    componentCount G (insert x H \ S) = componentCount G (H \ S) + 1 := by
  have hrem := insert_sdiff_eq_union_singleton (H := H) (S := S) hx hS
  have hdisj : Disjoint (H \ S) {x} := by
    refine disjoint_singleton_right.2 ?_
    intro hxS
    exact hx (mem_sdiff.1 hxS).1
  have hnc : ∀ a ∈ H \ S, ∀ b ∈ ({x} : Finset V), ¬ G.Adj a b := by
    intro a ha b hb hadj
    have hb' : b = x := mem_singleton.mp hb
    subst hb'
    exact hnocross a ha hadj.symm
  rw [hrem, Cograph.componentCount_union_of_no_cross (G := G) hdisj hnc,
    componentCount_singleton]

/-- Connectivity of `J = insert x H` forces the actual profile nonempty:
an empty profile would make `x` isolated from the cycle support, so
`c(J) = 2`. -/
lemma rowProfile_nonempty_of_oneToughOn_cycle (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support)) :
    (rowProfile (G := G) c.support x).Nonempty := by
  by_contra hA
  have hAempty : rowProfile (G := G) c.support x = ∅ :=
    not_nonempty_iff_eq_empty.1 hA
  have hnocross : ∀ u ∈ c.support, ¬ G.Adj x u := by
    intro u hu hadj
    have : u ∈ rowProfile (G := G) c.support x :=
      (mem_rowProfile_iff (G := G)).2 ⟨hu, hadj⟩
    rw [hAempty] at this
    exact (notMem_empty u this)
  have hcount := componentCount_insert_of_no_cross hx hnocross
  have hH : componentCount G c.support = 1 := componentCount_cycle_eq_one c
  have hJne : (insert x c.support).Nonempty := ⟨x, mem_insert_self _ _⟩
  have h1 := componentCount_eq_one_of_OneToughOn hJ hJne
  omega

/-- A tight container of the actual profile contradicts `OneToughOn` on
`insert x H`: the remainder is a no-cross union with the isolated vertex
`x`, so the component count increases by one. -/
lemma not_tight_container_of_oneToughOn_cycle (c : GraphCycle G) {x : V}
    {S : Finset V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support))
    (hS : S ⊆ c.support)
    (hAS : rowProfile (G := G) c.support x ⊆ S) :
    componentCount G (c.support \ S) ≠ S.card := by
  intro heq
  have hAne := rowProfile_nonempty_of_oneToughOn_cycle c hx hJ
  have hSne : S.Nonempty := hAne.mono hAS
  have hnocross := not_adj_sdiff_of_rowProfile_subset (G := G) hAS
  have hcount :=
    componentCount_host_remainder_eq_add_one hx hS hnocross
  have h2 : 2 ≤ componentCount G (insert x c.support \ S) := by
    have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.2 hSne)
    omega
  have hTsub : S ⊆ insert x c.support := hS.trans (subset_insert x c.support)
  have hle := hJ S hTsub h2
  omega

theorem noTightContainer_of_oneToughOn_cycle (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support)) :
    NoTightContainer G c.support (rowProfile (G := G) c.support x) := by
  intro S hS heq hAS
  exact not_tight_container_of_oneToughOn_cycle c hx hJ hS hAS heq

/-- 1-toughness of `J` forbids a unique original neighbour in `H`: the
singleton profile would be a tight container of size one whose remainder
is a no-cross union of a nonempty path with the isolated vertex `x`. -/
lemma two_le_card_rowProfile_of_oneToughOn_cycle (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support)) :
    2 ≤ (rowProfile (G := G) c.support x).card := by
  have hAne := rowProfile_nonempty_of_oneToughOn_cycle c hx hJ
  have hpos : 1 ≤ (rowProfile (G := G) c.support x).card :=
    Nat.succ_le_of_lt (card_pos.2 hAne)
  by_contra hlt
  have h1 : (rowProfile (G := G) c.support x).card = 1 := by omega
  obtain ⟨w, hwA⟩ := card_eq_one.1 h1
  have hAS : rowProfile (G := G) c.support x ⊆ {w} := by
    intro y hy
    simpa [hwA] using hy
  have hwAmem : w ∈ rowProfile (G := G) c.support x := by
    rw [hwA]
    exact mem_singleton_self w
  have hwH : w ∈ c.support := ((mem_rowProfile_iff (G := G)).1 hwAmem).1
  have hS : ({w} : Finset V) ⊆ c.support := singleton_subset_iff.2 hwH
  have hwcard : ({w} : Finset V).card = 1 := card_singleton w
  have hcycle := componentCount_cycle_sdiff_le c hS (singleton_nonempty w)
  have hremne : (c.support \ {w}).Nonempty := by
    rw [sdiff_nonempty]
    intro hsub
    have : c.support.card ≤ ({w} : Finset V).card := card_le_card hsub
    have h3 := c.three_le_card_support
    omega
  haveI : Nonempty ((c.support \ {w} : Finset V) : Set V) :=
    ⟨⟨hremne.choose, hremne.choose_spec⟩⟩
  haveI : Nonempty
      (G.induce ((c.support \ {w} : Finset V) : Set V)).ConnectedComponent :=
    inferInstance
  have hpos' : 0 < componentCount G (c.support \ {w}) := Nat.card_pos
  have heq : componentCount G (c.support \ {w}) = 1 := by omega
  exact not_tight_container_of_oneToughOn_cycle c hx hJ hS hAS heq

/-- Manuscript one-vertex strict-cut obstruction, generic support form.
The remainder `H \ A` is supplied as an actual cograph; this is the
canonical antineighbourhood input and is not an extra graph hypothesis
beyond the host forbidden-subgraph condition used to produce it. -/
theorem strict_pathCover_of_oneToughOn_cycle (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support))
    (hK : IsCograph G (c.support \ rowProfile (G := G) c.support x)) :
    pathCoverNumber G (c.support \ rowProfile (G := G) c.support x) <
      (rowProfile (G := G) c.support x).card := by
  set H := c.support
  set A := rowProfile (G := G) c.support x
  have hAne := rowProfile_nonempty_of_oneToughOn_cycle c hx hJ
  have hAsub : A ⊆ H := rowProfile_subset (G := G) H x
  have hle : pathCoverNumber G (H \ A) ≤ A.card :=
    Cograph.pathCoverNumber_sdiff_le_card_of_cycle c rfl hAsub hAne
  by_contra hnot
  have hSat : Cograph.Saturated (G := G) H A :=
    le_antisymm hle (le_of_not_gt hnot)
  have hiff :=
    Cograph.canonical_saturated_container_of_canonical (G := G) c rfl hAsub hAne hK
  obtain ⟨S, hT, hAS⟩ := hiff.2 hSat
  exact not_tight_container_of_oneToughOn_cycle c hx hJ hT.1 hAS hT.2

lemma isCograph_sdiff_rowProfile_insert (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hOn : ∀ ⦃a b c' d y : V⦄,
      a ∈ insert x c.support →
        b ∈ insert x c.support →
          c' ∈ insert x c.support →
            d ∈ insert x c.support →
              y ∈ insert x c.support →
      InducedP4 G a b c' d →
      y ≠ a → y ≠ b → y ≠ c' → y ≠ d →
        G.Adj y a ∨ G.Adj y b ∨ G.Adj y c' ∨ G.Adj y d) :
    IsCograph G (c.support \ rowProfile (G := G) c.support x) := by
  have hdisj : Disjoint c.support ({x} : Finset V) :=
    disjoint_singleton_right.2 hx
  refine isCograph_sdiff_rowProfile (H := c.support) (R := {x}) hdisj
    (mem_singleton_self x) ?_
  intro a b c' d y ha hb hc hd hy hp hya hyb hyc hyd
  have hconv : c.support ∪ {x} = insert x c.support := by
    rw [insert_eq, union_comm]
  rw [hconv] at ha hb hc hd hy
  exact hOn ha hb hc hd hy hp hya hyb hyc hyd

theorem strict_pathCover_of_oneToughOn_cycle_of_host
    (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support))
    (hOn : ∀ ⦃a b c' d y : V⦄,
      a ∈ insert x c.support →
        b ∈ insert x c.support →
          c' ∈ insert x c.support →
            d ∈ insert x c.support →
              y ∈ insert x c.support →
      InducedP4 G a b c' d →
      y ≠ a → y ≠ b → y ≠ c' → y ≠ d →
        G.Adj y a ∨ G.Adj y b ∨ G.Adj y c' ∨ G.Adj y d) :
    pathCoverNumber G (c.support \ rowProfile (G := G) c.support x) <
      (rowProfile (G := G) c.support x).card :=
  strict_pathCover_of_oneToughOn_cycle c hx hJ
    (isCograph_sdiff_rowProfile_insert c hx hOn)

theorem strict_pathCover_of_oneToughOn_cycle_of_NoInducedP4UnionP1
    (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support))
    (hG : NoInducedP4UnionP1 G) :
    pathCoverNumber G (c.support \ rowProfile (G := G) c.support x) <
      (rowProfile (G := G) c.support x).card :=
  strict_pathCover_of_oneToughOn_cycle_of_host c hx hJ
    (fun _ _ _ _ _ _ _ _ _ _ hp hya hyb hyc hyd =>
      hG hp hya hyb hyc hyd)

/-- Host specialization: an original 1-tough graph with a genuine cycle
spanning `univ.erase x`. -/
theorem strict_pathCover_of_oneTough_erase (hG : OneTough G)
    (c : GraphCycle G) {x : V} (hc : c.support = univ.erase x)
    (hK : IsCograph G (c.support \ rowProfile (G := G) c.support x)) :
    pathCoverNumber G (c.support \ rowProfile (G := G) c.support x) <
      (rowProfile (G := G) c.support x).card := by
  have hx : x ∉ c.support := by simp [hc]
  have hJ : OneToughOn G (insert x c.support) := by
    have : insert x c.support = univ := by simp [hc]
    rw [this]
    exact OneToughOn.univ_iff.2 hG
  exact strict_pathCover_of_oneToughOn_cycle c hx hJ hK

lemma sdiff_rowProfile_eq_antineighbors {x : V}
    (H : Finset V) (hH : H = univ.erase x) :
    H \ rowProfile (G := G) H x = antineighbors G x := by
  ext y
  constructor
  · intro hy
    have hyH : y ∈ H := (mem_sdiff.1 hy).1
    have hyA : y ∉ rowProfile (G := G) H x := (mem_sdiff.1 hy).2
    have hyx : y ≠ x := by
      intro h
      subst h
      simp [hH] at hyH
    have hnadj : ¬ G.Adj x y := by
      intro hadj
      exact hyA ((mem_rowProfile_iff (G := G)).2 ⟨hyH, hadj⟩)
    exact mem_filter.2 ⟨mem_univ _, ⟨hyx, hnadj⟩⟩
  · intro hy
    have hy' := mem_filter.1 hy
    have hyx : y ≠ x := hy'.2.1
    have hnadj : ¬ G.Adj x y := hy'.2.2
    have hyH : y ∈ H := by
      simp [hH, hyx]
    refine mem_sdiff.2 ⟨hyH, ?_⟩
    intro hyA
    exact hnadj ((mem_rowProfile_iff (G := G)).1 hyA).2

theorem strict_pathCover_of_oneTough_erase_of_NoInducedP4UnionP1
    (hG : OneTough G) (hNP : NoInducedP4UnionP1 G)
    (c : GraphCycle G) {x : V} (hc : c.support = univ.erase x) :
    pathCoverNumber G (c.support \ rowProfile (G := G) c.support x) <
      (rowProfile (G := G) c.support x).card := by
  have hK : IsCograph G (c.support \ rowProfile (G := G) c.support x) := by
    rw [sdiff_rowProfile_eq_antineighbors c.support hc]
    exact NoInducedP4UnionP1.isCograph_antineighbors (G := G) hNP x
  exact strict_pathCover_of_oneTough_erase hG c hc hK

/-- Actual cycle splice through two distinct original neighbours of `x`
that are the endpoints of an `H`-spanning path. Existence of that path
is an input, not a conclusion of the strict-cut theorem. -/
theorem exists_inserted_cycle_of_profile_ends (p : GraphPath G)
    (c : GraphCycle G) {x : V}
    (hp : p.support = c.support) (hx : x ∉ c.support)
    (hs : p.start ∈ rowProfile (G := G) c.support x)
    (hf : p.finish ∈ rowProfile (G := G) c.support x)
    (hne : p.start ≠ p.finish) :
    ∃ γ : GraphCycle G,
      γ.support = insert x c.support ∧ 3 ≤ γ.support.card := by
  have hs' : G.Adj x p.start := ((mem_rowProfile_iff (G := G)).1 hs).2
  have hf' : G.Adj p.finish x :=
    ((mem_rowProfile_iff (G := G)).1 hf).2.symm
  have hx' : x ∉ p.support := by simpa [hp] using hx
  obtain ⟨γ, hsupp, h3, _⟩ := exists_graphCycle_insert p hs' hf' hx' hne
  refine ⟨γ, ?_, h3⟩
  simpa [hp] using hsupp

end Nikoghosyan
