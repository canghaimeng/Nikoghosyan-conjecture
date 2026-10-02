/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.Profiles
import Nikoghosyan.Cograph.Decomposition
import Nikoghosyan.Cograph.DistinctPath
import Nikoghosyan.Cograph.PathCoverUnion

/-!
# Distinct-path release of a Hamiltonian attachment

Manuscript `abs:lem:distinct-release`. An original Hamiltonian block `D`
is attached to an old cograph carrier `L` with `p(L)=p(L ∪ D)`. A vertex
released from `F(L)` into `E(L ∪ D)` is `D`-adjacent in the union to at
least one end of any old distinct-path pair of `L`. The argument is
strong induction on `|L ∪ D|` along an actual cotree split of the union;
no `L`–`D` edge hypothesis, OneTough, or protected/spectrum certificate
is used. Traceable (non-Hamiltonian) attachments are not treated.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma two_le_pathCoverNumber_of_DistinctPathCompatible {U : Finset V} {x y : V}
    (h : DistinctPathCompatible (G := G) U x y) :
    2 ≤ pathCoverNumber G U := by
  by_contra hle
  have : pathCoverNumber G U ≤ 1 := by omega
  exact not_DistinctPathCompatible_of_le_one this h

lemma isCompleteBetween_mono {A A' B B' : Finset V}
    (h : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    G.IsCompleteBetween (A' : Set V) (B' : Set V) :=
  fun {_} ha {_} hb => h (hA ha) (hB hb)

lemma isCograph_canonical_subset {U W : Finset V}
    (hW : Nikoghosyan.IsCograph G W) (hUW : U ⊆ W) :
    Nikoghosyan.IsCograph G U :=
  isCograph_iff.1 ((isCograph_iff.2 hW).subset hUW)

lemma pathCoverNumber_union_le_of_disjoint {A B : Finset V}
    (hdisj : Disjoint A B) :
    pathCoverNumber G (A ∪ B) ≤
      pathCoverNumber G A + pathCoverNumber G B := by
  obtain ⟨pcA, hA⟩ := exists_min_pathCover (G := G) A
  obtain ⟨pcB, hB⟩ := exists_min_pathCover (G := G) B
  have hle := pathCoverNumber_le (G := G) (PathCover.unionDisjoint hdisj pcA pcB)
  have hcard := PathCover.unionDisjoint_card hdisj pcA pcB
  omega

lemma GraphCycle.support_subset_of_no_cross {A B : Finset V}
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (c : GraphCycle G) (hsupp : c.support ⊆ A ∪ B) :
    c.support ⊆ A ∨ c.support ⊆ B := by
  have hstart : c.start ∈ A ∪ B := hsupp c.start_mem_support
  have hwalk : ∀ y ∈ c.walk.support, y ∈ (A : Set V) ∨ y ∈ (B : Set V) := by
    intro y hy
    have : y ∈ c.support := by simpa [GraphCycle.support] using hy
    simpa [mem_union] using hsupp this
  rcases mem_union.mp hstart with hA | hB
  · refine Or.inl ?_
    intro x hx
    have hxW : x ∈ c.walk.support := by simpa [GraphCycle.support] using hx
    exact walk_support_subset_of_no_cross
      (A := (A : Set V)) (B := (B : Set V))
      (fun a ha b hb => hnocross a ha b hb) c.walk hA hwalk x hxW
  · refine Or.inr ?_
    intro x hx
    have hxW : x ∈ c.walk.support := by simpa [GraphCycle.support] using hx
    exact walk_support_subset_of_no_cross'
      (A := (A : Set V)) (B := (B : Set V))
      (fun a ha b hb => hnocross a ha b hb) c.walk hB hwalk x hxW

lemma supportUnion_eq_carrier {U : Finset V} (pc : PathCover G U) :
    supportUnion pc.paths = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := (mem_supportUnion_iff (l := pc.paths) (x := x)).1 hx
    exact (pc.mem_iff x).2 ⟨p, hp, hxp⟩
  · intro hx
    obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hx
    exact (mem_supportUnion_iff (l := pc.paths) (x := x)).2 ⟨p, hp, hxp⟩

lemma filter_unionDisjoint_left {A B : Finset V}
    (hdisj : Disjoint A B)
    (pcA : PathCover G A) (pcB : PathCover G B) :
    (PathCover.unionDisjoint hdisj pcA pcB).paths.filter
        (fun p => decide (p.start ∈ A)) = pcA.paths := by
  have hA : pcA.paths.filter (fun p => decide (p.start ∈ A)) = pcA.paths :=
    List.filter_eq_self.2 fun p hp =>
      decide_eq_true (pcA.support_subset hp p.start_mem_support)
  have hB : pcB.paths.filter (fun p => decide (p.start ∈ A)) = [] := by
    refine List.filter_eq_nil_iff.2 ?_
    intro p hp hdec
    have hpB : p.start ∈ B := pcB.support_subset hp p.start_mem_support
    exact (Finset.disjoint_left.1 hdisj (of_decide_eq_true hdec) hpB).elim
  simp [PathCover.unionDisjoint, List.filter_append, hA, hB]

lemma eligibleSet_unionDisjoint_left {A B : Finset V}
    (hdisj : Disjoint A B)
    (hAcog : Nikoghosyan.IsCograph G (A ∪ B))
    (pcA : PathCover G A) (pcB : PathCover G B)
    (hmin : (PathCover.unionDisjoint hdisj pcA pcB).card =
      pathCoverNumber G (A ∪ B)) :
    eligibleSet G A = eligibleSet G (A ∪ B) ∩ A := by
  let pc := PathCover.unionDisjoint hdisj pcA pcB
  have hP :
      supportUnion (pc.paths.filter (fun p => decide (p.start ∈ A))) = A := by
    rw [filter_unionDisjoint_left hdisj pcA pcB, supportUnion_eq_carrier pcA]
  have hrest :=
    restriction_eq_of_min_cover_of_canonical hAcog pc hmin
      (fun p => decide (p.start ∈ A))
  simpa [hP] using hrest.2.1

/-- If a Hamiltonian attachment meets the nondominant child of a saturated
complete join, the released ineligible vertex of `L` cannot lie in `E(J)`. -/
lemma false_of_cycle_meets_nondominant {L D X Y : Finset V} {h : V}
    (c : GraphCycle G)
    (hLD : Disjoint L D) (hc : c.support = D)
    (hcover : X ∪ Y = L ∪ D)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hdom : Y.card < pathCoverNumber G X)
    (hXcog : Nikoghosyan.IsCograph G X)
    (_hLcog : Nikoghosyan.IsCograph G L)
    (hp : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hq : 2 ≤ pathCoverNumber G (L ∪ D))
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hDY : (D ∩ Y).Nonempty) : False := by
  have hdisjXY := disjoint_of_completeBetween hXY
  have hJeq : pathCoverNumber G (X ∪ Y) = pathCoverNumber G (L ∪ D) := by
    rw [hcover]
  have hpX : pathCoverNumber G X =
      pathCoverNumber G (L ∪ D) + Y.card := by
    have := pathCoverNumber_add_card_of_dominant hXne hYne hXY hdom
    omega
  let LX := L ∩ X
  let LY := L ∩ Y
  let DX := D ∩ X
  let DY := D ∩ Y
  have hXsplit : LX ∪ DX = X := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzL | hzD
      · exact (mem_inter.1 hzL).2
      · exact (mem_inter.1 hzD).2
    · intro hzX
      have hzJ : z ∈ L ∪ D := by
        rw [← hcover]
        exact mem_union.2 (Or.inl hzX)
      rcases mem_union.1 hzJ with hzL | hzD
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzD, hzX⟩))
  have hYsplit : LY ∪ DY = Y := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzL | hzD
      · exact (mem_inter.1 hzL).2
      · exact (mem_inter.1 hzD).2
    · intro hzY
      have hzJ : z ∈ L ∪ D := by
        rw [← hcover]
        exact mem_union.2 (Or.inr hzY)
      rcases mem_union.1 hzJ with hzL | hzD
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzY⟩))
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzD, hzY⟩))
  have hdisjLXDX : Disjoint LX DX :=
    disjoint_of_subset_left (inter_subset_left (s₂ := X))
      (disjoint_of_subset_right (inter_subset_left (s₂ := X)) hLD)
  have hdisjLYDY : Disjoint LY DY :=
    disjoint_of_subset_left (inter_subset_left (s₂ := Y))
      (disjoint_of_subset_right (inter_subset_left (s₂ := Y)) hLD)
  have hLXsdiff : LX = L \ LY := by
    ext z
    constructor
    · intro hz
      exact mem_sdiff.2 ⟨(mem_inter.1 hz).1, fun hzLY =>
        Finset.disjoint_left.1 hdisjXY (mem_inter.1 hz).2 (mem_inter.1 hzLY).2⟩
    · intro hz
      have hzL : z ∈ L := (mem_sdiff.1 hz).1
      have hznotLY : z ∉ LY := (mem_sdiff.1 hz).2
      have hzX : z ∈ X := by
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inl hzL)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact hzX
        · exact (hznotLY (mem_inter.2 ⟨hzL, hzY⟩)).elim
      exact mem_inter.2 ⟨hzL, hzX⟩
  have hDXsdiff : DX = D \ DY := by
    ext z
    constructor
    · intro hz
      exact mem_sdiff.2 ⟨(mem_inter.1 hz).1, fun hzDY =>
        Finset.disjoint_left.1 hdisjXY (mem_inter.1 hz).2 (mem_inter.1 hzDY).2⟩
    · intro hz
      have hzD : z ∈ D := (mem_sdiff.1 hz).1
      have hznotDY : z ∉ DY := (mem_sdiff.1 hz).2
      have hzX : z ∈ X := by
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inr hzD)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact hzX
        · exact (hznotDY (mem_inter.2 ⟨hzD, hzY⟩)).elim
      exact mem_inter.2 ⟨hzD, hzX⟩
  have hpXle :=
    pathCoverNumber_union_le_of_disjoint (G := G) (A := LX) (B := DX) hdisjLXDX
  have hpXle' : pathCoverNumber G X ≤ pathCoverNumber G LX + pathCoverNumber G DX := by
    simpa [hXsplit] using hpXle
  have hLYsub : LY ⊆ L := inter_subset_left
  have hpLX : pathCoverNumber G LX ≤ pathCoverNumber G L + LY.card := by
    simpa [hLXsdiff] using pathCoverNumber_sdiff_le (G := G) L LY hLYsub
  have hDYsub : DY ⊆ D := inter_subset_left
  have hpDX : pathCoverNumber G DX ≤ DY.card := by
    have hdel :=
      pathCoverNumber_sdiff_le_card_of_cycle (U := D) (A := DY) c hc hDYsub hDY
    simpa [hDXsdiff] using hdel
  have hYcard : Y.card = LY.card + DY.card := by
    have := card_union_of_disjoint hdisjLYDY
    simpa [hYsplit] using this
  have hqL : pathCoverNumber G L = pathCoverNumber G (L ∪ D) := hp
  have hchain :
      pathCoverNumber G X ≤ pathCoverNumber G (L ∪ D) + Y.card := by
    omega
  have hpLXeq : pathCoverNumber G LX = pathCoverNumber G L + LY.card := by omega
  have hEjoin := eligibleSet_complete_join_dominant hXne hYne hXY hdom
  have hEJ : eligibleSet G (L ∪ D) = eligibleSet G X := by
    simpa [hcover] using hEjoin
  have hhX : h ∈ X := (eligibleSet_subset (G := G) X) (by
    have : h ∈ eligibleSet G X := by simpa [hEJ] using hhE
    exact this)
  have hhL : h ∈ L := (ineligibleSet_subset (G := G) L) hhF
  have hhLX : h ∈ LX := mem_inter.2 ⟨hhL, hhX⟩
  obtain ⟨pcLX, hpcLX⟩ := exists_min_pathCover (G := G) LX
  obtain ⟨pcDX, hpcDX⟩ := exists_min_pathCover (G := G) DX
  let pcX := PathCover.unionDisjoint hdisjLXDX pcLX pcDX
  have hminX : pcX.card = pathCoverNumber G X := by
    have hsum := PathCover.unionDisjoint_card (G := G) hdisjLXDX pcLX pcDX
    have hpcX : pcX.card = pcLX.card + pcDX.card := hsum
    have heq : pathCoverNumber G LX + pathCoverNumber G DX = pathCoverNumber G X := by
      have hle := hpXle'
      omega
    omega
  have hErest :=
    eligibleSet_unionDisjoint_left hdisjLXDX (by simpa [hXsplit] using hXcog)
      pcLX pcDX (by simpa [hXsplit] using hminX)
  have hhELX : h ∈ eligibleSet G LX := by
    have hhEX : h ∈ eligibleSet G X := by simpa [hEJ] using hhE
    have hErest' : eligibleSet G LX = eligibleSet G X ∩ LX := by
      simpa [hXsplit] using hErest
    have : h ∈ eligibleSet G X ∩ LX := mem_inter.2 ⟨hhEX, hhLX⟩
    simpa [hErest'] using this
  by_cases hLYne : LY.Nonempty
  · have hLXne : LX.Nonempty := ⟨h, hhLX⟩
    have hLXY : G.IsCompleteBetween (LX : Set V) (LY : Set V) :=
      isCompleteBetween_mono hXY inter_subset_right inter_subset_right
    have hLXdom : LY.card < pathCoverNumber G LX := by omega
    have hEL := eligibleSet_complete_join_dominant hLXne hLYne hLXY hLXdom
    have hLsplit : LX ∪ LY = L := by
      ext z
      constructor
      · intro hz
        rcases mem_union.1 hz with hzX | hzY
        · exact (mem_inter.1 hzX).1
        · exact (mem_inter.1 hzY).1
      · intro hzL
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inl hzL)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
        · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hzL, hzY⟩))
    have : h ∈ eligibleSet G L := by
      have : eligibleSet G L = eligibleSet G LX := by simpa [hLsplit] using hEL
      simpa [this] using hhELX
    exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2
      ((mem_eligibleSet_iff (G := G)).1 this).2
  · have hLYempty : LY = ∅ := not_nonempty_iff_eq_empty.1 hLYne
    have hLeq : LX = L := by
      have : L ∩ Y = ∅ := hLYempty
      ext z
      constructor
      · intro hz
        exact (mem_inter.1 hz).1
      · intro hzL
        refine mem_inter.2 ⟨hzL, ?_⟩
        have hzJ : z ∈ X ∪ Y := by
          rw [hcover]
          exact mem_union.2 (Or.inl hzL)
        rcases mem_union.1 hzJ with hzX | hzY
        · exact hzX
        · have hzLY : z ∈ LY := mem_inter.2 ⟨hzL, hzY⟩
          have : z ∈ (∅ : Finset V) := by simpa [hLYempty] using hzLY
          exact (notMem_empty z this).elim
    have : h ∈ eligibleSet G L := by simpa [hLeq] using hhELX
    exact (mem_ineligibleSet_iff (G := G)).1 hhF |>.2
      ((mem_eligibleSet_iff (G := G)).1 this).2

lemma union_inter_eq_of_cycle_subset_left {L D X Y : Finset V}
    (hcover : X ∪ Y = L ∪ D) (_hLD : Disjoint L D)
    (hXY : Disjoint X Y) (hDX : D ⊆ X) :
    (L ∩ X) ∪ D = X ∧ Y ⊆ L ∧ Disjoint (L ∩ X) Y := by
  have hYsub : Y ⊆ L := by
    intro y hy
    have hyJ : y ∈ L ∪ D := by
      rw [← hcover]
      exact mem_union.2 (Or.inr hy)
    rcases mem_union.1 hyJ with hyL | hyD
    · exact hyL
    · exact (Finset.disjoint_left.1 hXY (hDX hyD) hy).elim
  have hdisj : Disjoint (L ∩ X) Y :=
    disjoint_of_subset_left inter_subset_right hXY
  refine ⟨?_, hYsub, hdisj⟩
  ext z
  constructor
  · intro hz
    rcases mem_union.1 hz with hzL | hzD
    · exact (mem_inter.1 hzL).2
    · exact hDX hzD
  · intro hzX
    by_cases hzD : z ∈ D
    · exact mem_union.2 (Or.inr hzD)
    · have hzJ : z ∈ L ∪ D := by
        rw [← hcover]
        exact mem_union.2 (Or.inl hzX)
      have hzL : z ∈ L := by
        rcases mem_union.1 hzJ with hL | hD
        · exact hL
        · exact (hzD hD).elim
      exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))

/-- After the cycle is forced into the dominant child, the restricted
instance on that child inherits every hypothesis of distinct-release. -/
lemma restrict_hyps_of_dominant_cycle_subset {L D X Y : Finset V} {h u v : V}
    (c : GraphCycle G)
    (hLD : Disjoint L D) (hc : c.support = D)
    (hcover : X ∪ Y = L ∪ D)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (hdom : Y.card < pathCoverNumber G X)
    (hJcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hLcog : Nikoghosyan.IsCograph G L)
    (hp : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hq : 2 ≤ pathCoverNumber G (L ∪ D))
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hDuv : DistinctPathCompatible (G := G) L u v)
    (hDX : D ⊆ X) :
    Disjoint (L ∩ X) D ∧
      (L ∩ X) ∪ D = X ∧
      Nikoghosyan.IsCograph G X ∧
      Nikoghosyan.IsCograph G (L ∩ X) ∧
      pathCoverNumber G (L ∩ X) = pathCoverNumber G X ∧
      h ∈ ineligibleSet G (L ∩ X) ∧
      h ∈ eligibleSet G X ∧
      DistinctPathCompatible (G := G) (L ∩ X) u v ∧
      2 ≤ pathCoverNumber G X ∧
      Y ⊆ L ∧
      Y.card < pathCoverNumber G (L ∩ X) := by
  have hdisjXY := disjoint_of_completeBetween hXY
  obtain ⟨hXeq, hYsub, hdisjLXY⟩ :=
    union_inter_eq_of_cycle_subset_left hcover hLD hdisjXY hDX
  have hXcan : Nikoghosyan.IsCograph G X :=
    isCograph_canonical_subset hJcog (by
      intro x hx
      rw [← hcover]
      exact mem_union.2 (Or.inl hx))
  have hLXcan : Nikoghosyan.IsCograph G (L ∩ X) :=
    isCograph_canonical_subset hLcog inter_subset_left
  have hdisjLXD : Disjoint (L ∩ X) D :=
    disjoint_of_subset_left inter_subset_left hLD
  have hLXne : (L ∩ X).Nonempty := by
    have hpX : pathCoverNumber G X =
        pathCoverNumber G (L ∪ D) + Y.card := by
      have := pathCoverNumber_add_card_of_dominant hXne hYne hXY hdom
      have hJ : pathCoverNumber G (X ∪ Y) = pathCoverNumber G (L ∪ D) := by
        rw [hcover]
      omega
    have hpD : pathCoverNumber G D = 1 := pathCoverNumber_eq_one_of_cycle c hc
    by_contra hempty
    have hLXempty : L ∩ X = ∅ := not_nonempty_iff_eq_empty.1 hempty
    have hXeqD : X = D := by
      have : (∅ : Finset V) ∪ D = X := by simpa [hLXempty] using hXeq
      simpa using this.symm
    have hpX1 : pathCoverNumber G X = 1 := by simpa [hXeqD] using hpD
    omega
  have hLXY :
      G.IsCompleteBetween (L ∩ X : Finset V) (Y : Set V) :=
    isCompleteBetween_mono (A := X) (A' := L ∩ X) (B := Y) (B' := Y)
      hXY inter_subset_right (fun _ hy => hy)
  have hpXadd : pathCoverNumber G X =
      pathCoverNumber G (L ∪ D) + Y.card := by
    have := pathCoverNumber_add_card_of_dominant hXne hYne hXY hdom
    have hJ : pathCoverNumber G (X ∪ Y) = pathCoverNumber G (L ∪ D) := by
      rw [hcover]
    omega
  have hpD : pathCoverNumber G D = 1 := pathCoverNumber_eq_one_of_cycle c hc
  have hpXle : pathCoverNumber G X ≤
      pathCoverNumber G (L ∩ X) + 1 := by
    have hle : pathCoverNumber G ((L ∩ X) ∪ D) ≤
        pathCoverNumber G (L ∩ X) + pathCoverNumber G D :=
      pathCoverNumber_union_le_of_disjoint hdisjLXD
    simpa [hXeq, hpD] using hle
  have hpLXge : pathCoverNumber G (L ∪ D) + Y.card - 1 ≤
      pathCoverNumber G (L ∩ X) := by omega
  have hpLXgt : Y.card < pathCoverNumber G (L ∩ X) := by omega
  have hLsplit : (L ∩ X) ∪ Y = L := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzX | hzY
      · exact (mem_inter.1 hzX).1
      · exact hYsub hzY
    · intro hzL
      have hzJ : z ∈ X ∪ Y := by
        rw [hcover]
        exact mem_union.2 (Or.inl hzL)
      rcases mem_union.1 hzJ with hzX | hzY
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzX⟩))
      · exact mem_union.2 (Or.inr hzY)
  have hpLsub :=
    pathCoverNumber_eq_sub_of_dominant hLXne hYne hLXY hpLXgt
  have hpLX : pathCoverNumber G (L ∩ X) = pathCoverNumber G X := by
    have hL : pathCoverNumber G ((L ∩ X) ∪ Y) = pathCoverNumber G L := by
      rw [hLsplit]
    omega
  have hqL : 2 ≤ pathCoverNumber G L := by omega
  have hEL := eligibleSet_complete_join_dominant hLXne hYne hLXY hpLXgt
  have hFL := ineligibleSet_complete_join_dominant hLXne hYne hLXY hpLXgt
  have hEJ := eligibleSet_complete_join_dominant hXne hYne hXY hdom
  have hEJrw : eligibleSet G (L ∪ D) = eligibleSet G X := by
    simpa [hcover] using hEJ
  have hhEX : h ∈ eligibleSet G X := by simpa [hEJrw] using hhE
  have hhFLX : h ∈ ineligibleSet G (L ∩ X) := by
    have hFrw : ineligibleSet G L = Y ∪ ineligibleSet G (L ∩ X) := by
      simpa [hLsplit] using hFL
    have hhF' : h ∈ Y ∪ ineligibleSet G (L ∩ X) := by simpa [hFrw] using hhF
    rcases mem_union.1 hhF' with hhY | hhLX
    · have hhX : h ∈ X := (eligibleSet_subset (G := G) X) hhEX
      exact (Finset.disjoint_left.1 hdisjXY hhX hhY).elim
    · exact hhLX
  have hErw : eligibleSet G L = eligibleSet G (L ∩ X) := by
    simpa [hLsplit] using hEL
  have hqX : 2 ≤ pathCoverNumber G X := by omega
  have hDuvLX : DistinctPathCompatible (G := G) (L ∩ X) u v := by
    have hUV : DistinctPathCompatible (G := G) ((L ∩ X) ∪ Y) u v := by
      simpa [hLsplit] using hDuv
    exact DistinctPathCompatible_of_dominant hLXne hYne hLXY hpLXgt hUV
  exact ⟨hdisjLXD, hXeq, hXcan, hLXcan, hpLX, hhFLX, hhEX, hDuvLX, hqX, hYsub,
    hpLXgt⟩

lemma DistinctPathCompatible_union_comm {A B : Finset V} {x y : V} :
    DistinctPathCompatible (G := G) (A ∪ B) x y ↔
      DistinctPathCompatible (G := G) (B ∪ A) x y := by
  constructor
  · intro h
    have : A ∪ B = B ∪ A := union_comm _ _
    simpa [this] using h
  · intro h
    have : B ∪ A = A ∪ B := union_comm _ _
    simpa [this] using h

lemma eligibleSet_union_comm (A B : Finset V) :
    eligibleSet G (A ∪ B) = eligibleSet G (B ∪ A) := by
  simp [union_comm]

lemma pathCoverNumber_union_comm (A B : Finset V) :
    pathCoverNumber G (A ∪ B) = pathCoverNumber G (B ∪ A) := by
  simp [union_comm]

lemma distinct_release_disconnected_side
    (n : ℕ)
    (ih : ∀ m < n, ∀ (L D : Finset V) (h u v : V) (c : GraphCycle G),
      (L ∪ D).card = m →
      Disjoint L D →
      c.support = D →
      Nikoghosyan.IsCograph G (L ∪ D) →
      Nikoghosyan.IsCograph G L →
      pathCoverNumber G L = pathCoverNumber G (L ∪ D) →
      h ∈ ineligibleSet G L →
      h ∈ eligibleSet G (L ∪ D) →
      DistinctPathCompatible (G := G) L u v →
      DistinctPathCompatible (G := G) (L ∪ D) h u ∨
        DistinctPathCompatible (G := G) (L ∪ D) h v)
    {L D A B : Finset V} {h u v : V} {c : GraphCycle G}
    (_hcard : (L ∪ D).card = n)
    (hLD : Disjoint L D)
    (hc : c.support = D)
    (hJcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hLcog : Nikoghosyan.IsCograph G L)
    (hp : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hDuv : DistinctPathCompatible (G := G) L u v)
    (hAU : A ⊆ L ∪ D)
    (hdisjAB : Disjoint A B)
    (hcover : A ∪ B = L ∪ D)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hAcard : A.card < n)
    (hDA : D ⊆ A) :
    DistinctPathCompatible (G := G) (L ∪ D) h u ∨
      DistinctPathCompatible (G := G) (L ∪ D) h v := by
  have hAJcard : A.card < n := hAcard
  have hXeq : (L ∩ A) ∪ D = A :=
    (union_inter_eq_of_cycle_subset_left
      (X := A) (Y := B) hcover hLD hdisjAB hDA).1
  have hYsub : B ⊆ L :=
    (union_inter_eq_of_cycle_subset_left
      (X := A) (Y := B) hcover hLD hdisjAB hDA).2.1
  have hdisjLXB : Disjoint (L ∩ A) B :=
    disjoint_of_subset_left inter_subset_right hdisjAB
  have hnocrossLB : ∀ a ∈ L ∩ A, ∀ b ∈ B, ¬ G.Adj a b :=
    fun a ha b hb => hnocross a (inter_subset_right ha) b hb
  have hLsplit : (L ∩ A) ∪ B = L := by
    ext z
    constructor
    · intro hz
      rcases mem_union.1 hz with hzA | hzB
      · exact (mem_inter.1 hzA).1
      · exact hYsub hzB
    · intro hzL
      have hzJ : z ∈ L ∪ D := mem_union.2 (Or.inl hzL)
      have hzAB : z ∈ A ∪ B := by rwa [← hcover] at hzJ
      rcases mem_union.1 hzAB with hzA | hzB
      · exact mem_union.2 (Or.inl (mem_inter.2 ⟨hzL, hzA⟩))
      · exact mem_union.2 (Or.inr hzB)
  have hpaddJ := pathCoverNumber_disjoint_union hdisjAB hnocross
  have hpaddL := pathCoverNumber_disjoint_union hdisjLXB hnocrossLB
  have hpA : pathCoverNumber G (L ∩ A) = pathCoverNumber G A := by
    have hJp : pathCoverNumber G (L ∪ D) =
        pathCoverNumber G A + pathCoverNumber G B := by
      simpa [hcover] using hpaddJ
    have hLp : pathCoverNumber G L =
        pathCoverNumber G (L ∩ A) + pathCoverNumber G B := by
      simpa [hLsplit] using hpaddL
    omega
  have hEJ := eligibleSet_disjoint_union hdisjAB hnocross
  have hFL := ineligibleSet_disjoint_union hdisjLXB hnocrossLB
  have hhA : h ∈ A := by
    have hhE' : h ∈ eligibleSet G A ∪ eligibleSet G B := by
      have : eligibleSet G (L ∪ D) = eligibleSet G A ∪ eligibleSet G B := by
        simpa [hcover] using hEJ
      simpa [this] using hhE
    rcases mem_union.1 hhE' with hhA | hhB
    · exact (eligibleSet_subset (G := G) A) hhA
    · have hhBmem : h ∈ B := (eligibleSet_subset (G := G) B) hhB
      have hFrw : ineligibleSet G L =
          ineligibleSet G (L ∩ A) ∪ ineligibleSet G B := by
        simpa [hLsplit] using hFL
      have : h ∈ ineligibleSet G (L ∩ A) ∪ ineligibleSet G B := by
        simpa [hFrw] using hhF
      rcases mem_union.1 this with hLA | hhFB
      · have : h ∈ L ∩ A := ineligibleSet_subset (G := G) (L ∩ A) hLA
        exact (Finset.disjoint_left.1 hdisjLXB this hhBmem).elim
      · have hnotE : ¬ Eligible G B h := (mem_ineligibleSet_iff (G := G)).1 hhFB |>.2
        have hE : Eligible G B h := (mem_eligibleSet_iff (G := G)).1 hhB |>.2
        exact (hnotE hE).elim
  have hhFLA : h ∈ ineligibleSet G (L ∩ A) := by
    have hFrw : ineligibleSet G L =
        ineligibleSet G (L ∩ A) ∪ ineligibleSet G B := by
      simpa [hLsplit] using hFL
    have : h ∈ ineligibleSet G (L ∩ A) ∪ ineligibleSet G B := by
      simpa [hFrw] using hhF
    rcases mem_union.1 this with hLA | hB
    · exact hLA
    · have hhB : h ∈ B := ineligibleSet_subset (G := G) B hB
      exact (Finset.disjoint_left.1 hdisjAB hhA hhB).elim
  have hhEA : h ∈ eligibleSet G A := by
    have hhE' : h ∈ eligibleSet G A ∪ eligibleSet G B := by
      have : eligibleSet G (L ∪ D) = eligibleSet G A ∪ eligibleSet G B := by
        simpa [hcover] using hEJ
      simpa [this] using hhE
    rcases mem_union.1 hhE' with hhA' | hhB
    · exact hhA'
    · have hhBmem : h ∈ B := (eligibleSet_subset (G := G) B) hhB
      exact (Finset.disjoint_left.1 hdisjAB hhA hhBmem).elim
  have hEhA : Eligible G A h := (mem_eligibleSet_iff (G := G)).1 hhEA |>.2
  have huE : Eligible G L u := DistinctPathCompatible.eligible_left hDuv
  have hvE : Eligible G L v := DistinctPathCompatible.eligible_right hDuv
  have huL : u ∈ L := Eligible.mem (G := G) huE
  have hvL : v ∈ L := Eligible.mem (G := G) hvE
  by_cases huB : u ∈ B
  · have huEB : Eligible G B u := by
      have hE : Eligible G ((L ∩ A) ∪ B) u := by simpa [hLsplit] using huE
      rcases (eligible_disjoint_union_iff hdisjLXB hnocrossLB).1 hE with hA | hB
      · exact (Finset.disjoint_left.1 hdisjLXB hA.mem huB).elim
      · exact hB
    refine Or.inl ?_
    have hDcross := DistinctPathCompatible_union_cross hdisjAB hnocross hEhA huEB
    simpa [hcover] using hDcross
  · by_cases hvB : v ∈ B
    · have hvEB : Eligible G B v := by
        have hE : Eligible G ((L ∩ A) ∪ B) v := by simpa [hLsplit] using hvE
        rcases (eligible_disjoint_union_iff hdisjLXB hnocrossLB).1 hE with hA | hB
        · exact (Finset.disjoint_left.1 hdisjLXB hA.mem hvB).elim
        · exact hB
      refine Or.inr ?_
      have hDcross := DistinctPathCompatible_union_cross hdisjAB hnocross hEhA hvEB
      simpa [hcover] using hDcross
    · have huA : u ∈ A := by
        have hzJ : u ∈ L ∪ D := mem_union.2 (Or.inl huL)
        have : u ∈ A ∪ B := by rwa [← hcover] at hzJ
        rcases mem_union.1 this with hA | hB
        · exact hA
        · exact (huB hB).elim
      have hvA : v ∈ A := by
        have hzJ : v ∈ L ∪ D := mem_union.2 (Or.inl hvL)
        have : v ∈ A ∪ B := by rwa [← hcover] at hzJ
        rcases mem_union.1 this with hA | hB
        · exact hA
        · exact (hvB hB).elim
      have huLA : u ∈ L ∩ A := mem_inter.2 ⟨huL, huA⟩
      have hvLA : v ∈ L ∩ A := mem_inter.2 ⟨hvL, hvA⟩
      have hDuvA : DistinctPathCompatible (G := G) (L ∩ A) u v :=
        DistinctPathCompatible_union_of_left hdisjLXB hnocrossLB huLA hvLA
          (by simpa [hLsplit] using hDuv)
      have hdisjLXD : Disjoint (L ∩ A) D :=
        disjoint_of_subset_left inter_subset_left hLD
      have hIH :=
        ih A.card hAJcard (L ∩ A) D h u v c (by simpa [hXeq]) hdisjLXD hc
          (isCograph_canonical_subset hJcog (by simpa [hXeq] using hAU))
          (isCograph_canonical_subset hLcog inter_subset_left)
          (by simpa [hXeq] using hpA) hhFLA
          (by simpa [hXeq] using hhEA) hDuvA
      rcases hIH with hhu | hhv
      · exact Or.inl (by
          have hhuA : DistinctPathCompatible (G := G) A h u := by
            simpa [hXeq] using hhu
          have := DistinctPathCompatible_union_left hdisjAB hnocross hhuA
          simpa [hcover] using this)
      · exact Or.inr (by
          have hhvA : DistinctPathCompatible (G := G) A h v := by
            simpa [hXeq] using hhv
          have := DistinctPathCompatible_union_left hdisjAB hnocross hhvA
          simpa [hcover] using this)

/-- Strong induction on `|L ∪ D|`. -/
lemma distinct_release_of_card (n : ℕ) :
    ∀ (L D : Finset V) (h u v : V) (c : GraphCycle G),
      (L ∪ D).card = n →
      Disjoint L D →
      c.support = D →
      Nikoghosyan.IsCograph G (L ∪ D) →
      Nikoghosyan.IsCograph G L →
      pathCoverNumber G L = pathCoverNumber G (L ∪ D) →
      h ∈ ineligibleSet G L →
      h ∈ eligibleSet G (L ∪ D) →
      DistinctPathCompatible (G := G) L u v →
      DistinctPathCompatible (G := G) (L ∪ D) h u ∨
        DistinctPathCompatible (G := G) (L ∪ D) h v := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro L D h u v c hcard hLD hc hJcog hLcog hp hhF hhE hDuv
    set J := L ∪ D
    have hqL : 2 ≤ pathCoverNumber G L :=
      two_le_pathCoverNumber_of_DistinctPathCompatible hDuv
    have hqJ : 2 ≤ pathCoverNumber G J := by omega
    have hJ3 : 3 ≤ J.card :=
      (GraphCycle.three_le_card_support c).trans (card_le_card (by
        simpa [J, hc] using (subset_union_right : D ⊆ L ∪ D)))
    have hJ2 : 2 ≤ J.card := le_trans (by decide : (2 : ℕ) ≤ 3) hJ3
    have hJne : J.Nonempty := card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hJ2)
    have hDsub : D ⊆ J := by simp [J]
    by_cases hconn : (G.induce (J : Set V)).Connected
    · obtain ⟨A, B, hAU, hBU, hAne, hBne, hdisjAB, hcoverAB, hAB, hAcard, hBcard⟩ :=
        exists_complete_join_on (isCograph_iff.2 hJcog) hconn hJ2
      have hcover : A ∪ B = J := hcoverAB
      by_cases hAdom : B.card < pathCoverNumber G A
      · have hAJcard : A.card < n := by simpa [hcard] using hAcard
        by_cases hDmeetsB : (D ∩ B).Nonempty
        · exact (false_of_cycle_meets_nondominant
            (L := L) (D := D) (X := A) (Y := B) (h := h) c hLD hc
            (by simpa [J] using hcover) hAne hBne hAB hAdom
            (isCograph_canonical_subset hJcog hAU) hLcog hp
            (by simpa [J] using hqJ) hhF (by simpa [J] using hhE) hDmeetsB).elim
        · have hDB : D ∩ B = ∅ := not_nonempty_iff_eq_empty.1 hDmeetsB
          have hDA : D ⊆ A := by
            intro x hx
            have hxJ : x ∈ A ∪ B := by
              rw [hcover]; exact hDsub hx
            rcases mem_union.1 hxJ with hxA | hxB
            · exact hxA
            · have : x ∈ D ∩ B := mem_inter.2 ⟨hx, hxB⟩
              simpa [hDB] using this
          obtain ⟨hdisjLXD, hXeq, hXcan, hLXcan, hpLX, hhFLX, hhEX, hDuvLX, hqX,
              hYsub, hLXdom⟩ :=
            restrict_hyps_of_dominant_cycle_subset (X := A) (Y := B) c hLD hc
              (by simpa [J] using hcover) hAne hBne hAB hAdom hJcog hLcog hp
              (by simpa [J] using hqJ) hhF (by simpa [J] using hhE) hDuv hDA
          have hIH :=
            ih A.card hAJcard (L ∩ A) D h u v c (by simpa [hXeq]) hdisjLXD hc
              (by simpa [hXeq] using hXcan) hLXcan (by simpa [hXeq] using hpLX)
              hhFLX (by simpa [hXeq] using hhEX) hDuvLX
          have hqAB : 2 ≤ pathCoverNumber G (A ∪ B) := by simpa [hcover, J] using hqJ
          rcases hIH with hhu | hhv
          · exact Or.inl (by
              have hhuA : DistinctPathCompatible (G := G) A h u := by
                simpa [hXeq] using hhu
              have : DistinctPathCompatible (G := G) (A ∪ B) h u :=
                (DistinctPathCompatible_complete_join_dominant_iff
                  (x := h) (y := u) hAne hBne hAB hAdom hqAB).2 hhuA
              simpa [hcover, J] using this)
          · exact Or.inr (by
              have hhvA : DistinctPathCompatible (G := G) A h v := by
                simpa [hXeq] using hhv
              have : DistinctPathCompatible (G := G) (A ∪ B) h v :=
                (DistinctPathCompatible_complete_join_dominant_iff
                  (x := h) (y := v) hAne hBne hAB hAdom hqAB).2 hhvA
              simpa [hcover, J] using this)
      · by_cases hBdom : A.card < pathCoverNumber G B
        · have hBA : G.IsCompleteBetween (B : Set V) (A : Set V) :=
            isCompleteBetween_symm hAB
          have hBJcard : B.card < n := by simpa [hcard] using hBcard
          by_cases hDmeetsA : (D ∩ A).Nonempty
          · exact (false_of_cycle_meets_nondominant
              (L := L) (D := D) (X := B) (Y := A) (h := h) c hLD hc
              (by simpa [J, union_comm] using hcover) hBne hAne hBA hBdom
              (isCograph_canonical_subset hJcog hBU) hLcog hp
              (by simpa [J] using hqJ) hhF (by simpa [J] using hhE) hDmeetsA).elim
          · have hDA : D ∩ A = ∅ := not_nonempty_iff_eq_empty.1 hDmeetsA
            have hDB : D ⊆ B := by
              intro x hx
              have hxJ : x ∈ A ∪ B := by
                rw [hcover]; exact hDsub hx
              rcases mem_union.1 hxJ with hxA | hxB
              · have : x ∈ D ∩ A := mem_inter.2 ⟨hx, hxA⟩
                simpa [hDA] using this
              · exact hxB
            obtain ⟨hdisjLXD, hXeq, hXcan, hLXcan, hpLX, hhFLX, hhEX, hDuvLX, hqX,
                hYsub, hLXdom⟩ :=
              restrict_hyps_of_dominant_cycle_subset (X := B) (Y := A) c hLD hc
                (by simpa [J, union_comm] using hcover) hBne hAne hBA hBdom hJcog
                hLcog hp (by simpa [J] using hqJ) hhF (by simpa [J] using hhE)
                hDuv hDB
            have hIH :=
              ih B.card hBJcard (L ∩ B) D h u v c (by simpa [hXeq]) hdisjLXD hc
                (by simpa [hXeq] using hXcan) hLXcan (by simpa [hXeq] using hpLX)
                hhFLX (by simpa [hXeq] using hhEX) hDuvLX
            have hqBA : 2 ≤ pathCoverNumber G (B ∪ A) := by
              simpa [union_comm, hcover, J] using hqJ
            rcases hIH with hhu | hhv
            · exact Or.inl (by
                have hhuB : DistinctPathCompatible (G := G) B h u := by
                  simpa [hXeq] using hhu
                have : DistinctPathCompatible (G := G) (B ∪ A) h u :=
                  (DistinctPathCompatible_complete_join_dominant_iff
                    (x := h) (y := u) hBne hAne hBA hBdom hqBA).2 hhuB
                simpa [union_comm, hcover, J] using this)
            · exact Or.inr (by
                have hhvB : DistinctPathCompatible (G := G) B h v := by
                  simpa [hXeq] using hhv
                have : DistinctPathCompatible (G := G) (B ∪ A) h v :=
                  (DistinctPathCompatible_complete_join_dominant_iff
                    (x := h) (y := v) hBne hAne hBA hBdom hqBA).2 hhvB
                simpa [union_comm, hcover, J] using this)
        · have hpA : pathCoverNumber G A ≤ B.card := Nat.le_of_not_gt hAdom
          have hpB : pathCoverNumber G B ≤ A.card := Nat.le_of_not_gt hBdom
          have hpAB := pathCoverNumber_complete_join hAne hBne hAB
          have hp1 : pathCoverNumber G (A ∪ B) = 1 := by
            simp [hpAB, Nat.sub_eq_zero_of_le hpA, Nat.sub_eq_zero_of_le hpB]
          have : pathCoverNumber G J = 1 := by simpa [hcover, J] using hp1
          omega
    · obtain ⟨A, B, hAU, hBU, hAne, hBne, hdisjAB, hcoverAB, hnocross, hAcard, hBcard⟩ :=
        exists_disjoint_union_on (by simpa [J] using hconn) hJne
      have hcover : A ∪ B = J := hcoverAB
      have hDside := GraphCycle.support_subset_of_no_cross hnocross c (by
        simpa [hc, hcover, J] using hDsub)
      have hDside' : D ⊆ A ∨ D ⊆ B := by simpa [hc] using hDside
      rcases hDside' with hDA | hDB
      · exact distinct_release_disconnected_side n ih hcard hLD hc hJcog hLcog hp
          hhF hhE hDuv hAU hdisjAB (by simpa [J] using hcover) hnocross
          (by simpa [hcard] using hAcard) hDA
      · exact distinct_release_disconnected_side n ih hcard hLD hc hJcog hLcog hp
          hhF hhE hDuv hBU hdisjAB.symm (by simpa [union_comm, J] using hcover)
          (fun b hb a ha hab => hnocross a ha b hb hab.symm)
          (by simpa [hcard] using hBcard) hDB

theorem distinct_release {L D : Finset V} {h u v : V}
    (c : GraphCycle G)
    (hLD : Disjoint L D)
    (hc : c.support = D)
    (hJcog : Nikoghosyan.IsCograph G (L ∪ D))
    (hLcog : Nikoghosyan.IsCograph G L)
    (hp : pathCoverNumber G L = pathCoverNumber G (L ∪ D))
    (hhF : h ∈ ineligibleSet G L)
    (hhE : h ∈ eligibleSet G (L ∪ D))
    (hDuv : DistinctPathCompatible (G := G) L u v) :
    DistinctPathCompatible (G := G) (L ∪ D) h u ∨
      DistinctPathCompatible (G := G) (L ∪ D) h v :=
  distinct_release_of_card (L ∪ D).card L D h u v c rfl hLD hc hJcog hLcog hp
    hhF hhE hDuv

end Cograph
end Nikoghosyan
