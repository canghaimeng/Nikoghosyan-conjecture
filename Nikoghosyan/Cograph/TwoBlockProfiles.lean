/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Cograph.ProfileEndpoints
import Nikoghosyan.FactorAssembly
import Nikoghosyan.CycleSwitches
import Nikoghosyan.TraceableExtension

/-!
Arbitrary-pair nonmerge profile dichotomy, without pair toughness.

Manuscript `prof:prop:two-block` is a spanning two-cycle host theorem and
is not applied here. Given two actual disjoint original cycles `cH`, `cD`
with noncograph host support `H = cH.support`, the original
induced-`(P₄ ∪ P₁)`-free pattern, and no original cycle spanning
`H ∪ D`, every actual `D`-row into `H` is nonempty with cograph
remainder, and either

* every row is strict: `p(H \ row) < |row|`, or
* every row is saturated and they share one common proper canonical
  tight container `S`, which contains every actual `H`–`D` attachment.

No `OneTough` hypothesis on `H ∪ D`, no whole-host Hamiltonicity, and no
inherited induced-pair toughness is used. Rows may overlap.

A globally minimum original-edge `CycleFactor` supplies the no-union-cycle
hypothesis by group replacement (`not_exists_merge_of_min`). The spanning
pair specialisation `H ∪ D = univ` with original `OneTough` eliminates the
saturated branch by a host cut; it does not construct a Hamilton cycle.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ### Cycle indexing along `succAt` -/

lemma getVert_mem_cycle_support (c : GraphCycle G) (i : ℕ) :
    c.walk.getVert i ∈ c.support :=
  List.mem_toFinset.2 (Walk.getVert_mem_support c.walk i)

lemma cycle_length_pos (c : GraphCycle G) : 0 < c.walk.length :=
  lt_of_lt_of_le (by decide : (0 : ℕ) < 3) c.three_le_length

lemma exists_getVert_lt_length_of_mem_support (c : GraphCycle G) {x : V}
    (hx : x ∈ c.support) :
    ∃ i, i < c.walk.length ∧ c.walk.getVert i = x := by
  have hxW : x ∈ c.walk.support := GraphCycle.mem_walk_support_of_mem hx
  obtain ⟨i, hiEq, hiLe⟩ := (Walk.mem_support_iff_exists_getVert).1 hxW
  rcases eq_or_lt_of_le hiLe with rfl | hlt
  · refine ⟨0, cycle_length_pos c, ?_⟩
    have hxstart : x = c.start := by
      simpa [Walk.getVert_length] using hiEq.symm
    simpa [Walk.getVert_zero] using hxstart.symm
  · exact ⟨i, hlt, hiEq⟩

lemma takeUntil_length_eq_getVert_index (c : GraphCycle G) {i : ℕ}
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

lemma idxOf_getVert_eq (c : GraphCycle G) {i : ℕ}
    (hi : i < c.walk.length) :
    c.walk.support.idxOf (c.walk.getVert i) = i := by
  have hlen := takeUntil_length_eq_getVert_index c hi
  simpa [Walk.length_takeUntil] using hlen

lemma getVert_copy {u u' v v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (n : ℕ) :
    (p.copy hu hv).getVert n = p.getVert n := by
  subst hu
  subst hv
  rfl

lemma dropUntil_getVert_succ (c : GraphCycle G) {i : ℕ}
    (hi : i < c.walk.length) :
    (c.walk.dropUntil (c.walk.getVert i)
        (Walk.getVert_mem_support c.walk i)).getVert 1 =
      c.walk.getVert (i + 1) := by
  set u := c.walk.getVert i
  have huW : u ∈ c.walk.support := Walk.getVert_mem_support c.walk i
  have hidx := idxOf_getVert_eq c hi
  rw [Walk.dropUntil_eq_drop c.walk huW, getVert_copy, Walk.drop_getVert, hidx]

/-- Opening `c` at `getVert i` exposes the next cycle vertex as `succAt`. -/
lemma succAt_eq_getVert_succ (c : GraphCycle G) {i : ℕ}
    (hi : i < c.walk.length) :
    c.succAt (getVert_mem_cycle_support c i) = c.walk.getVert (i + 1) := by
  set u := c.walk.getVert i
  set hu := getVert_mem_cycle_support c i
  have huW : u ∈ c.walk.support := Walk.getVert_mem_support c.walk i
  have hidx := idxOf_getVert_eq c hi
  have hdrop_len :
      (c.walk.dropUntil u huW).length = c.walk.length - i := by
    rw [Walk.length_dropUntil, hidx]
  have hstart : (c.rotateTo hu).start = u := c.start_rotateTo hu
  -- Unfold `rotate` on the original walk, then transport along `start = u`.
  have hrot :
      (c.walk.rotate u (GraphCycle.mem_walk_support_of_mem hu)).getVert 1 =
        ((c.walk.dropUntil u huW).append (c.walk.takeUntil u huW)).getVert 1 :=
    rfl
  have hsucc : c.succAt hu =
      (c.walk.rotate u (GraphCycle.mem_walk_support_of_mem hu)).getVert 1 :=
    rfl
  rw [hsucc, hrot, Walk.getVert_append]
  split_ifs with hlt
  · exact dropUntil_getVert_succ c hi
  · have h1 : (c.walk.dropUntil u huW).length = 1 := by omega
    have hi1 : i + 1 = c.walk.length := by omega
    have hL : (c.walk.takeUntil u huW).getVert
        (1 - (c.walk.dropUntil u huW).length) = c.start := by
      simp [h1, Walk.getVert_zero]
    have hrhs : c.walk.getVert (i + 1) = c.start := by
      simpa [hi1] using Walk.getVert_length c.walk
    simpa [h1] using hL.trans hrhs.symm

/-! ### Opening a cycle at a prescribed successor dart -/

lemma exists_path_open_succ (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    ∃ p : GraphPath G,
      p.support = c.support ∧
        p.start = c.succAt hu ∧
          p.finish = u := by
  obtain ⟨w, rest, hadj, hw, hcons, hpath⟩ := c.rotateTo_eq_cons hu
  have hfin : (c.rotateTo hu).start = u := c.start_rotateTo hu
  let p : GraphPath G := ⟨w, (c.rotateTo hu).start, rest, hpath⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · have huRest : (c.rotateTo hu).start ∈ rest.support :=
      Walk.end_mem_support rest
    have hrot : p.support = (c.rotateTo hu).support := by
      simp [p, GraphPath.support, GraphCycle.support, hcons, Walk.support_cons,
        insert_eq_of_mem (List.mem_toFinset.2 huRest)]
    simpa [hrot, GraphCycle.support_rotateTo]
  · simpa [p] using hw
  · simpa [p, hfin]

lemma three_le_union_card (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support) :
    3 ≤ (cH.support ∪ cD.support).card := by
  have hH := cH.three_le_card_support
  have hD := cD.three_le_card_support
  have hcup :
      (cH.support ∪ cD.support).card = cH.support.card + cD.support.card :=
    card_union_of_disjoint hdisj
  omega

/-! ### Nonempty rows and cograph remainders -/

lemma exists_inducedP4_of_not_isCograph {U : Finset V}
    (h : ¬ IsCograph G U) :
    ∃ a b c d : V, a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ d ∈ U ∧ InducedP4 G a b c d := by
  unfold IsCograph at h
  push Not at h
  exact h

lemma ne_of_mem_disjoint {A B : Finset V} {x y : V}
    (hdisj : Disjoint A B) (hx : x ∈ A) (hy : y ∈ B) : x ≠ y := by
  intro h
  subst h
  exact disjoint_left.1 hdisj hx hy

/-- A missing `D`-row into a noncograph host `H` yields an induced
`P₄ ∪ P₁` with the outside `D`-vertex. -/
lemma rowProfile_nonempty_of_not_cograph
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hH : ¬ IsCograph G cH.support)
    (hpat : NoInducedP4UnionP1 G) {v : V}
    (hv : v ∈ cD.support) :
    (rowProfile (G := G) cH.support v).Nonempty := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hp⟩ :=
    exists_inducedP4_of_not_isCograph hH
  by_contra hempty
  have hAempty : rowProfile (G := G) cH.support v = ∅ :=
    not_nonempty_iff_eq_empty.1 hempty
  have hnone : ∀ x ∈ cH.support, ¬ G.Adj v x := by
    intro x hx hadj
    have hxA : x ∈ rowProfile (G := G) cH.support v :=
      (mem_rowProfile_iff (G := G)).2 ⟨hx, hadj⟩
    simpa [hAempty] using hxA
  have hva := ne_of_mem_disjoint hdisj ha hv
  have hvb := ne_of_mem_disjoint hdisj hb hv
  have hvc := ne_of_mem_disjoint hdisj hc hv
  have hvd := ne_of_mem_disjoint hdisj hd hv
  have hdom := hpat hp hva.symm hvb.symm hvc.symm hvd.symm
  rcases hdom with h1 | h2 | h3 | h4
  · exact hnone a ha h1
  · exact hnone b hb h2
  · exact hnone c hc h3
  · exact hnone d hd h4

lemma isCograph_sdiff_rowProfile_of_pair
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hpat : NoInducedP4UnionP1 G) {v : V}
    (hv : v ∈ cD.support) :
    IsCograph G (cH.support \ rowProfile (G := G) cH.support v) :=
  isCograph_sdiff_rowProfile (H := cH.support) (R := cD.support) hdisj hv
    (fun _ _ _ _ _ _ _ _ _ _ hp hxa hxb hxc hxd =>
      hpat hp hxa hxb hxc hxd)

lemma pathCoverNumber_row_le
    (cH : GraphCycle G) {v : V}
    (hAne : (rowProfile (G := G) cH.support v).Nonempty) :
    pathCoverNumber G
        (cH.support \ rowProfile (G := G) cH.support v) ≤
      (rowProfile (G := G) cH.support v).card :=
  Cograph.pathCoverNumber_sdiff_le_card_of_cycle (G := G) cH rfl
    (rowProfile_subset (G := G) cH.support v) hAne

lemma strict_of_not_saturated
    (cH : GraphCycle G) {v : V}
    (hAne : (rowProfile (G := G) cH.support v).Nonempty)
    (hnot : ¬ Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support v)) :
    pathCoverNumber G
        (cH.support \ rowProfile (G := G) cH.support v) <
      (rowProfile (G := G) cH.support v).card := by
  have hle := pathCoverNumber_row_le cH hAne
  exact Nat.lt_of_le_of_ne hle (by
    intro heq
    exact hnot heq)

/-! ### Consecutive rows cannot span `H` under a no-union-cycle hypothesis -/

lemma not_spanningPathCompatible_of_no_union_cycle
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ cD.support)
    {u : V} (hu : u ∈ cD.support)
    {a b : V}
    (ha : a ∈ rowProfile (G := G) cH.support u)
    (hb : b ∈ rowProfile (G := G) cH.support (cD.succAt hu)) :
    ¬ SpanningPathCompatible (G := G) cH.support a b := by
  intro hR
  obtain ⟨hne, p, hp, hends⟩ := hR
  obtain ⟨q, hq, qst, qfin⟩ := exists_path_open_succ cD hu
  have ha' := (mem_rowProfile_iff (G := G)).1 ha
  have hb' := (mem_rowProfile_iff (G := G)).1 hb
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact hdisj
  have h3 : 3 ≤ (p.support ∪ q.support).card := by
    rw [hp, hq]
    exact three_le_union_card cH cD hdisj
  let p' : GraphPath G :=
    if hdir : p.start = a ∧ p.finish = b then p else p.reverse
  have hp' : p'.support = cH.support := by
    dsimp [p']
    split_ifs
    · exact hp
    · simpa [GraphPath.support_reverse] using hp
  have hp'start : p'.start = a := by
    dsimp [p']
    split_ifs with hdir
    · exact hdir.1
    · have : p.start = b ∧ p.finish = a := by
        rcases hends with h | h
        · exact (hdir h).elim
        · exact h
      simpa [GraphPath.reverse] using this.2
  have hp'finish : p'.finish = b := by
    dsimp [p']
    split_ifs with hdir
    · exact hdir.2
    · have : p.start = b ∧ p.finish = a := by
        rcases hends with h | h
        · exact (hdir h).elim
        · exact h
      simpa [GraphPath.reverse] using this.1
  have hd' : Disjoint p'.support q.support := by
    rw [hp', hq]
    exact hdisj
  have hfwd : G.Adj p'.finish q.start := by
    rw [hp'finish, qst]
    exact hb'.2.symm
  have hback : G.Adj q.finish p'.start := by
    rw [qfin, hp'start]
    exact ha'.2
  have h3' : 3 ≤ (p'.support ∪ q.support).card := by
    rw [hp', hq]
    exact three_le_union_card cH cD hdisj
  have hspan :
      (GraphPath.assembleTwo p' q hd' hfwd hback h3').support =
        cH.support ∪ cD.support := by
    simp [GraphPath.support_assembleTwo, hp', hq]
  exact hnoC _ hspan

lemma no_spanning_of_succAt
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ cD.support)
    {u : V} (hu : u ∈ cD.support) :
    ∀ a ∈ rowProfile (G := G) cH.support u,
      ∀ b ∈ rowProfile (G := G) cH.support (cD.succAt hu),
        ¬ SpanningPathCompatible (G := G) cH.support a b :=
  fun a ha b hb =>
    not_spanningPathCompatible_of_no_union_cycle cH cD hdisj hnoC hu ha hb

/-! ### Adjacent-row incompatibility along `succAt` -/

lemma adjacent_rows_incompatible
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hH : ¬ IsCograph G cH.support)
    (hpat : NoInducedP4UnionP1 G)
    (hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ cD.support)
    {u : V} (hu : u ∈ cD.support)
    (hSat : Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support u) ∨
      Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support (cD.succAt hu))) :
    Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support u) ∧
      Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support (cD.succAt hu)) ∧
      Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support u) =
        Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support (cD.succAt hu)) := by
  set A := rowProfile (G := G) cH.support u
  set B := rowProfile (G := G) cH.support (cD.succAt hu)
  have hAne := rowProfile_nonempty_of_not_cograph cH cD hdisj hH hpat hu
  have hBne :=
    rowProfile_nonempty_of_not_cograph cH cD hdisj hH hpat
      (cD.succAt_mem_support hu)
  have hKA := isCograph_sdiff_rowProfile_of_pair cH cD hdisj hpat hu
  have hKB := isCograph_sdiff_rowProfile_of_pair cH cD hdisj hpat
    (cD.succAt_mem_support hu)
  have hno := no_spanning_of_succAt cH cD hdisj hnoC hu
  have hinc :=
    Cograph.incompatible_saturated_profiles (G := G) cH rfl
      (rowProfile_subset (G := G) cH.support u) hAne hKA
      (rowProfile_subset (G := G) cH.support (cD.succAt hu)) hBne hKB
      hSat hno
  exact ⟨hinc.2.1, hinc.2.2.1, hinc.2.2.2⟩

lemma saturated_getVert_of_start
    (cH c0 : GraphCycle G)
    (hdisj : Disjoint cH.support c0.support)
    (hH : ¬ IsCograph G cH.support)
    (hpat : NoInducedP4UnionP1 G)
    (hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ c0.support)
    (hSat0 : Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support c0.start))
    (i : ℕ) (hi : i ≤ c0.walk.length) :
    Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support (c0.walk.getVert i)) ∧
      Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support (c0.walk.getVert i)) =
        Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support c0.start) := by
  induction i with
  | zero =>
    simpa only [Walk.getVert_zero] using
      (And.intro hSat0 (rfl :
        Cograph.canonicalContainer (G := G) cH.support
            (rowProfile (G := G) cH.support c0.start) =
          Cograph.canonicalContainer (G := G) cH.support
            (rowProfile (G := G) cH.support c0.start)))
  | succ i ih =>
    have hi0 : i ≤ c0.walk.length := Nat.le_of_succ_le hi
    have hi0lt : i < c0.walk.length := Nat.lt_of_succ_le hi
    obtain ⟨hSati, hconti⟩ := ih hi0
    have hu_i : c0.walk.getVert i ∈ c0.support :=
      getVert_mem_cycle_support c0 i
    have hinc :=
      adjacent_rows_incompatible cH c0 hdisj hH hpat hnoC hu_i (Or.inl hSati)
    have hsucc := succAt_eq_getVert_succ c0 hi0lt
    refine ⟨?_, ?_⟩
    · simpa [hsucc] using hinc.2.1
    · simpa [hsucc, hconti] using hinc.2.2.symm.trans hconti

/-! ### Generic pair dichotomy -/

/-- Common proper canonical tight container of a saturated gate, after
propagation around `cD`. -/
lemma exists_common_canonical_container
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hH : ¬ IsCograph G cH.support)
    (hpat : NoInducedP4UnionP1 G)
    (hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ cD.support)
    {u : V} (hu : u ∈ cD.support)
    (hSat0 : Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support u)) :
    ∃ S : Finset V,
      Cograph.Tight (G := G) cH.support S ∧
        S ⊂ cH.support ∧
          (∀ v ∈ cD.support,
            Cograph.Saturated (G := G) cH.support
                (rowProfile (G := G) cH.support v) ∧
              Cograph.canonicalContainer (G := G) cH.support
                  (rowProfile (G := G) cH.support v) = S ∧
                rowProfile (G := G) cH.support v ⊆ S) ∧
            (∀ x ∈ cH.support, ∀ y ∈ cD.support, G.Adj x y → x ∈ S) := by
  set A0 := rowProfile (G := G) cH.support u
  have hA0ne := rowProfile_nonempty_of_not_cograph cH cD hdisj hH hpat hu
  have hK0 := isCograph_sdiff_rowProfile_of_pair cH cD hdisj hpat hu
  have hspec :=
    Cograph.canonical_saturated_container_spec_of_canonical (G := G)
      (rowProfile_subset (G := G) cH.support u) hA0ne hK0 hSat0
  set S := Cograph.canonicalContainer (G := G) cH.support A0
  let c0 := cD.rotateTo hu
  have hdisj0 : Disjoint cH.support c0.support := by
    simpa [c0, GraphCycle.support_rotateTo] using hdisj
  have hnoC0 : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ c0.support := by
    simpa [c0, GraphCycle.support_rotateTo] using hnoC
  have hSat00 : Cograph.Saturated (G := G) cH.support
      (rowProfile (G := G) cH.support c0.start) := by
    simpa [c0, GraphCycle.start_rotateTo] using hSat0
  refine ⟨S, hspec.1, hspec.2.1, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, hvi⟩ := exists_getVert_lt_length_of_mem_support (x := v)
      (cD.rotateTo hu) (by simpa [GraphCycle.support_rotateTo] using hv)
    have hiLe : i ≤ (cD.rotateTo hu).walk.length := hi.le
    have hprop :=
      saturated_getVert_of_start cH c0 hdisj0 hH hpat hnoC0 hSat00 i hiLe
    have hSatv : Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support v) := by
      simpa [c0, hvi] using hprop.1
    have hcont : Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support v) = S := by
      have heq := hprop.2
      change Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support ((cD.rotateTo hu).walk.getVert i)) =
        Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support (cD.rotateTo hu).start) at heq
      rw [hvi, GraphCycle.start_rotateTo] at heq
      exact heq
    refine ⟨hSatv, hcont, ?_⟩
    intro x hx
    have hxS : x ∈ Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support v) :=
      Cograph.mem_canonicalContainer_of_mem_A hx
    simpa [hcont] using hxS
  · intro x hx y hy hadj
    have hxA : x ∈ rowProfile (G := G) cH.support y :=
      (mem_rowProfile_iff (G := G)).2 ⟨hx, hadj.symm⟩
    obtain ⟨i, hi, hvi⟩ := exists_getVert_lt_length_of_mem_support (x := y)
      (cD.rotateTo hu) (by simpa [GraphCycle.support_rotateTo] using hy)
    have hiLe : i ≤ (cD.rotateTo hu).walk.length := hi.le
    have hprop :=
      saturated_getVert_of_start cH c0 hdisj0 hH hpat hnoC0 hSat00 i hiLe
    have hcont : Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support y) = S := by
      have heq := hprop.2
      change Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support ((cD.rotateTo hu).walk.getVert i)) =
        Cograph.canonicalContainer (G := G) cH.support
          (rowProfile (G := G) cH.support (cD.rotateTo hu).start) at heq
      rw [hvi, GraphCycle.start_rotateTo] at heq
      exact heq
    have hxS : x ∈ Cograph.canonicalContainer (G := G) cH.support
        (rowProfile (G := G) cH.support y) :=
      Cograph.mem_canonicalContainer_of_mem_A hxA
    simpa [hcont] using hxS

/-- Generic arbitrary-pair profile dichotomy: either every `D`-row into
the noncograph host is strict, or every row is saturated and they share
one common proper canonical tight container containing all attachments.
No pair-toughness or spanning-pair premise is used. -/
theorem pair_profile_dichotomy
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hH : ¬ IsCograph G cH.support)
    (hpat : NoInducedP4UnionP1 G)
    (hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ cD.support) :
    (∀ v ∈ cD.support,
        (rowProfile (G := G) cH.support v).Nonempty ∧
          IsCograph G
              (cH.support \ rowProfile (G := G) cH.support v) ∧
            pathCoverNumber G
                (cH.support \ rowProfile (G := G) cH.support v) <
              (rowProfile (G := G) cH.support v).card) ∨
      ∃ S : Finset V,
        Cograph.Tight (G := G) cH.support S ∧
          S ⊂ cH.support ∧
            (∀ v ∈ cD.support,
              (rowProfile (G := G) cH.support v).Nonempty ∧
                IsCograph G
                    (cH.support \ rowProfile (G := G) cH.support v) ∧
                  Cograph.Saturated (G := G) cH.support
                    (rowProfile (G := G) cH.support v) ∧
                    Cograph.canonicalContainer (G := G) cH.support
                        (rowProfile (G := G) cH.support v) = S ∧
                      rowProfile (G := G) cH.support v ⊆ S) ∧
              (∀ x ∈ cH.support, ∀ y ∈ cD.support, G.Adj x y → x ∈ S) := by
  have hrow : ∀ v ∈ cD.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        IsCograph G (cH.support \ rowProfile (G := G) cH.support v) :=
    fun v hv =>
      ⟨rowProfile_nonempty_of_not_cograph cH cD hdisj hH hpat hv,
        isCograph_sdiff_rowProfile_of_pair cH cD hdisj hpat hv⟩
  by_cases hsome :
      ∃ v ∈ cD.support,
        Cograph.Saturated (G := G) cH.support
          (rowProfile (G := G) cH.support v)
  · obtain ⟨u, hu, hSatu⟩ := hsome
    obtain ⟨S, hT, hproper, hrows, hatt⟩ :=
      exists_common_canonical_container cH cD hdisj hH hpat hnoC hu hSatu
    refine Or.inr ⟨S, hT, hproper, ?_, hatt⟩
    intro v hv
    obtain ⟨hSatv, hcont, hsub⟩ := hrows v hv
    exact ⟨(hrow v hv).1, (hrow v hv).2, hSatv, hcont, hsub⟩
  · refine Or.inl ?_
    intro v hv
    have hnot : ¬ Cograph.Saturated (G := G) cH.support
        (rowProfile (G := G) cH.support v) := fun hSat => hsome ⟨v, hv, hSat⟩
    exact ⟨(hrow v hv).1, (hrow v hv).2,
      strict_of_not_saturated cH (hrow v hv).1 hnot⟩

/-! ### Minimum-factor derivation of the no-union-cycle hypothesis -/

lemma not_exists_union_cycle_of_min (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {i j : Fin F.card} (hij : i ≠ j)
    (C : GraphCycle G)
    (hspan : C.support =
      (F.getCycle i).support ∪ (F.getCycle j).support) : False := by
  have h2 : 2 ≤ ({i, j} : Finset (Fin F.card)).card := by
    simp [card_pair hij]
  have hsel := F.selectedSupport_pair (i := i) (j := j)
  exact F.not_exists_merge_of_min hmin {i, j} h2 C (hspan.trans hsel.symm)

/-- Scope-safe replacement used by `prop:normal-form`: on a globally
minimum original-edge factor, any distinct pair with noncograph host
block obeys the generic dichotomy. The no-union-cycle input is derived
from group replacement, never from ambient non-Hamiltonicity. -/
theorem pair_profile_dichotomy_of_min (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hpat : NoInducedP4UnionP1 G)
    {i j : Fin F.card} (hij : i ≠ j)
    (hH : ¬ IsCograph G (F.getCycle i).support) :
    (∀ v ∈ (F.getCycle j).support,
        (rowProfile (G := G) (F.getCycle i).support v).Nonempty ∧
          IsCograph G
              ((F.getCycle i).support \
                rowProfile (G := G) (F.getCycle i).support v) ∧
            pathCoverNumber G
                ((F.getCycle i).support \
                  rowProfile (G := G) (F.getCycle i).support v) <
              (rowProfile (G := G) (F.getCycle i).support v).card) ∨
      ∃ S : Finset V,
        Cograph.Tight (G := G) (F.getCycle i).support S ∧
          S ⊂ (F.getCycle i).support ∧
            (∀ v ∈ (F.getCycle j).support,
              (rowProfile (G := G) (F.getCycle i).support v).Nonempty ∧
                IsCograph G
                    ((F.getCycle i).support \
                      rowProfile (G := G) (F.getCycle i).support v) ∧
                  Cograph.Saturated (G := G) (F.getCycle i).support
                    (rowProfile (G := G) (F.getCycle i).support v) ∧
                    Cograph.canonicalContainer (G := G)
                        (F.getCycle i).support
                        (rowProfile (G := G) (F.getCycle i).support v) =
                      S ∧
                      rowProfile (G := G) (F.getCycle i).support v ⊆ S) ∧
              (∀ x ∈ (F.getCycle i).support, ∀ y ∈ (F.getCycle j).support,
                G.Adj x y → x ∈ S) :=
  pair_profile_dichotomy (F.getCycle i) (F.getCycle j)
    (F.disjoint_getCycle hij) hH hpat
    (fun C hC => not_exists_union_cycle_of_min F hmin hij C hC)

/-! ### Spanning-pair specialisation: original toughness kills the gate -/

lemma univ_sdiff_eq_union_of_spanning {H D S : Finset V}
    (hHD : H ∪ D = univ) (hS : S ⊆ H) (hdisj : Disjoint H D) :
    univ \ S = (H \ S) ∪ D := by
  have hDS : Disjoint D S := hdisj.symm.mono_right hS
  have hD : D \ S = D := sdiff_eq_self_iff_disjoint.2 hDS
  calc
    univ \ S = (H ∪ D) \ S := by rw [hHD]
    _ = (H \ S) ∪ (D \ S) := union_sdiff_distrib _ _ _
    _ = (H \ S) ∪ D := by rw [hD]

lemma componentCount_host_delete_eq_add_one
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    {S : Finset V} (hS : S ⊆ cH.support)
    (hnocross : ∀ x ∈ cH.support \ S, ∀ y ∈ cD.support, ¬ G.Adj x y) :
    componentCount G ((cH.support \ S) ∪ cD.support) =
      componentCount G (cH.support \ S) + 1 := by
  have hdisj' : Disjoint (cH.support \ S) cD.support :=
    hdisj.mono_left sdiff_subset
  have hnc : ∀ a ∈ cH.support \ S, ∀ b ∈ cD.support, ¬ G.Adj a b :=
    hnocross
  rw [Cograph.componentCount_union_of_no_cross (G := G) hdisj' hnc,
    componentCount_cycle_eq_one cD]

/-- On a spanning two-cycle host, a common proper tight container of every
`D`-row contradicts original `OneTough`. This counting identity is not
asserted when further factor blocks remain. -/
theorem not_common_container_of_spanning_oneTough
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hHD : cH.support ∪ cD.support = univ)
    (hT : OneTough G)
    {S : Finset V}
    (hS : S ⊆ cH.support)
    (hTight : componentCount G (cH.support \ S) = S.card)
    (hproper : S ⊂ cH.support)
    (hrows : ∀ v ∈ cD.support, rowProfile (G := G) cH.support v ⊆ S) :
    False := by
  have hnocross : ∀ x ∈ cH.support \ S, ∀ y ∈ cD.support, ¬ G.Adj x y := by
    intro x hx y hy hadj
    have hxS : x ∈ S := hrows y hy
      ((mem_rowProfile_iff (G := G)).2 ⟨(mem_sdiff.1 hx).1, hadj.symm⟩)
    exact (mem_sdiff.1 hx).2 hxS
  have hrem := univ_sdiff_eq_union_of_spanning hHD hS hdisj
  have hcount :=
    componentCount_host_delete_eq_add_one cH cD hdisj hS hnocross
  have hSne : S.Nonempty := by
    by_contra hempty
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hempty
    simp [hSempty, componentCount_cycle_eq_one cH] at hTight
  have h2 : 2 ≤ componentCount G (univ \ S) := by
    have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.2 hSne)
    simpa [hrem, hcount, hTight] using Nat.succ_le_succ hpos
  have hle := hT S (by simpa [hrem] using h2)
  have hEq : componentCount G (univ \ S) = S.card + 1 := by
    simpa [hrem, hcount, hTight]
  omega

/-- Spanning two-cycle specialisation: original `OneTough` forces every
`D`-row to be strict. Traceable-extension toughness of the union then
follows the checked prefix-free argument. Hamiltonian insertion of the
pair remains an explicit pending prerequisite. -/
theorem all_rows_strict_of_spanning_oneTough
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hH : ¬ IsCograph G cH.support)
    (hpat : NoInducedP4UnionP1 G)
    (hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ cD.support)
    (hHD : cH.support ∪ cD.support = univ)
    (hT : OneTough G) :
    ∀ v ∈ cD.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        IsCograph G
            (cH.support \ rowProfile (G := G) cH.support v) ∧
          pathCoverNumber G
              (cH.support \ rowProfile (G := G) cH.support v) <
            (rowProfile (G := G) cH.support v).card := by
  rcases pair_profile_dichotomy cH cD hdisj hH hpat hnoC with hstrict | hsat
  · exact hstrict
  · obtain ⟨S, hTgt, hproper, hrows, _hatt⟩ := hsat
    have hsub : ∀ v ∈ cD.support,
        rowProfile (G := G) cH.support v ⊆ S :=
      fun v hv => (hrows v hv).2.2.2.2
    exact (not_common_container_of_spanning_oneTough cH cD hdisj hHD hT
      hTgt.1 hTgt.2 hproper hsub).elim

theorem oneToughOn_of_all_rows_strict
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hpat : NoInducedP4UnionP1 G)
    (hstrict : ∀ v ∈ cD.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        pathCoverNumber G
            (cH.support \ rowProfile (G := G) cH.support v) <
          (rowProfile (G := G) cH.support v).card) :
    OneToughOn G (cH.support ∪ cD.support) := by
  obtain ⟨r, hr, _⟩ := exists_path_open_succ cD cD.start_mem_support
  have hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        NoTightContainer G cH.support
          (rowProfile (G := G) cH.support v) := by
    intro v hv
    have hvD : v ∈ cD.support := by simpa [hr] using hv
    have hAne := (hstrict v hvD).1
    have hlt := (hstrict v hvD).2
    refine ⟨hAne, ?_⟩
    exact (noTightContainer_iff_strict_pathCover_of_host cH r
      (by simpa [hr] using hdisj) (by simpa [hr] using hvD) hAne hpat).2 hlt
  simpa [hr] using
    oneToughOn_of_traceable_extension cH r (by simpa [hr] using hdisj) hrow

/-- Strict rows transfer to any actual traceable subset of the second block.
Toughness is derived from the initial cycle and inherited rows. -/
theorem oneToughOn_of_traceable_subset_of_strict_rows
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hpat : NoInducedP4UnionP1 G)
    (hstrict : ∀ v ∈ cD.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        pathCoverNumber G
            (cH.support \ rowProfile (G := G) cH.support v) <
          (rowProfile (G := G) cH.support v).card)
    (r : GraphPath G) (hR : r.support ⊆ cD.support) :
    OneToughOn G (cH.support ∪ r.support) := by
  have hd : Disjoint cH.support r.support := hdisj.mono_right hR
  apply oneToughOn_of_traceable_extension cH r hd
  intro v hv
  obtain ⟨hAne, hlt⟩ := hstrict v (hR hv)
  exact ⟨hAne,
    (noTightContainer_iff_strict_pathCover_of_host cH r hd hv hAne hpat).2 hlt⟩

/-- Manuscript `prof:prop:two-block`, on a SPANNING two-cycle host.
The generic arbitrary-pair dichotomy remains a separate theorem. -/
theorem strict_profiles_of_spanning_two_cycles
    (cH cD : GraphCycle G)
    (hdisj : Disjoint cH.support cD.support)
    (hHD : cH.support ∪ cD.support = univ)
    (hH : ¬ IsCograph G cH.support)
    (hpat : NoInducedP4UnionP1 G) (hT : OneTough G)
    (hNonHam : ¬ G.IsHamiltonian) :
    (∀ v ∈ cD.support,
      (rowProfile (G := G) cH.support v).Nonempty ∧
        IsCograph G (cH.support \ rowProfile (G := G) cH.support v) ∧
          pathCoverNumber G
              (cH.support \ rowProfile (G := G) cH.support v) <
            (rowProfile (G := G) cH.support v).card) ∧
      ∀ r : GraphPath G, r.support ⊆ cD.support →
        OneToughOn G (cH.support ∪ r.support) := by
  have hord : 3 ≤ Fintype.card V := cH.three_le_card_support.trans
    (by simpa using card_le_card (subset_univ cH.support))
  have hnoC : ∀ C : GraphCycle G,
      C.support ≠ cH.support ∪ cD.support := by
    intro C hC
    exact hNonHam ((isHamiltonian_iff_exists_spanning_graphCycle hord).2
      ⟨C, hC.trans hHD⟩)
  have hs := all_rows_strict_of_spanning_oneTough cH cD hdisj hH hpat hnoC hHD hT
  refine ⟨hs, ?_⟩
  intro r hR
  exact oneToughOn_of_traceable_subset_of_strict_rows cH cD hdisj hpat
    (fun v hv => ⟨(hs v hv).1, (hs v hv).2.2⟩) r hR

end Nikoghosyan
