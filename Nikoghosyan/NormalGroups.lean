/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.NormalForm

/-!
# Manuscript `prop:normal-form` (canonical groups)

Remaining clauses on a globally minimum original-edge cycle factor of a
1-tough cofree non-Hamiltonian host of order at least three:

* distinct-gate satellites are anticomplete, via an actual three-block
  original cycle and group replacement;
* there are at least two canonical gate groups, via the original host
  tight cut at the common gate;
* each whole group (including inter-satellite original edges) is a
  cograph, via an anticomplete vertex from another group and the
  forbidden pattern.

Spanning-only `prof:prop:two-block` is not used on a proper core/satellite
pair. Pair toughness of arbitrary satellites is not inherited.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Three-block original assembly -/

lemma GraphPath.supportUnion_triple (p q r : GraphPath G) :
    GraphPath.supportUnion [p, q, r] =
      p.support ∪ (q.support ∪ r.support) := by
  simp [GraphPath.supportUnion_cons, GraphPath.supportUnion_nil]

lemma GraphPath.exists_assemble_three (p q r : GraphPath G)
    (hdpq : Disjoint p.support q.support)
    (hdpr : Disjoint p.support r.support)
    (hdqr : Disjoint q.support r.support)
    (h1 : G.Adj p.finish q.start)
    (h2 : G.Adj q.finish r.start)
    (h3e : G.Adj r.finish p.start)
    (hcard : 3 ≤ (p.support ∪ (q.support ∪ r.support)).card) :
    ∃ C : GraphCycle G,
      C.support = p.support ∪ (q.support ∪ r.support) := by
  let ps : List (GraphPath G) := [p, q, r]
  have h2len : 2 ≤ ps.length := by simp [ps]
  have hne : ps ≠ [] := by intro h; simp [ps] at h
  have hdisj : ps.Pairwise fun a b => Disjoint a.support b.support := by
    refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, by simp⟩⟩
    · intro b hb
      simp [ps] at hb
      rcases hb with rfl | rfl
      · exact hdpq
      · exact hdpr
    · intro b hb
      simp [ps] at hb
      subst hb
      exact hdqr
  have hedges : ∀ i (hi : i + 1 < ps.length),
      G.Adj (ps.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (ps.get ⟨i + 1, hi⟩).start := by
    intro i hi
    have hi' : i + 1 < 3 := by simpa [ps] using hi
    have h01 : i = 0 ∨ i = 1 := by omega
    rcases h01 with rfl | rfl
    · simpa [ps] using h1
    · simpa [ps] using h2
  have hclose : G.Adj (ps.getLast hne).finish (ps.head hne).start := by
    simpa [ps] using h3e
  have h3 : 3 ≤ (GraphPath.supportUnion ps).card := by
    simpa [ps, GraphPath.supportUnion_triple] using hcard
  refine ⟨GraphPath.assembleCycle ps h2len hdisj hedges hclose h3, ?_⟩
  simpa [ps, GraphPath.support_assembleCycle, GraphPath.supportUnion_triple]

lemma card_selected_triple {F : CycleFactor G} {i j k : Fin F.card}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i, j, k} : Finset (Fin F.card)).card = 3 := by
  have hi : i ∉ ({j, k} : Finset (Fin F.card)) := by simp [hij, hik]
  have hjmem : j ∉ ({k} : Finset (Fin F.card)) := by simp [hjk]
  rw [card_insert_of_notMem hi, card_insert_of_notMem hjmem, card_singleton]

lemma CycleFactor.selectedSupport_triple (F : CycleFactor G)
    {i j k : Fin F.card} :
    F.selectedSupport {i, j, k} =
      (F.getCycle i).support ∪
        ((F.getCycle j).support ∪ (F.getCycle k).support) := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hx
    have ht' : t = i ∨ t = j ∨ t = k := by simpa using ht
    rcases ht' with rfl | rfl | rfl
    · exact mem_union.2 (Or.inl hxt)
    · exact mem_union.2 (Or.inr (mem_union.2 (Or.inl hxt)))
    · exact mem_union.2 (Or.inr (mem_union.2 (Or.inr hxt)))
  · intro hx
    rw [mem_selectedSupport]
    rcases mem_union.1 hx with h | h
    · exact ⟨i, by simp, h⟩
    · rcases mem_union.1 h with h' | h'
      · exact ⟨j, by simp, h'⟩
      · exact ⟨k, by simp, h'⟩

/-! ### Deterministic satellite gate from `cycle.start` -/

/-- Canonical gate of satellite `j` into the noncograph core, taken from
the actual `cycle.start` row. Every other row of the same satellite equals
this gate by the common-gate theorem. -/
noncomputable def satelliteGate
    (_hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (_hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core j : Fin F.card} (_hcore : ¬ IsCograph G (F.getCycle core).support)
    (_hj : j ≠ core) : Finset V :=
  Cograph.canonicalContainer (G := G) (F.getCycle core).support
    (rowProfile (G := G) (F.getCycle core).support (F.getCycle j).start)

lemma satelliteGate_spec
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core j : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    (hj : j ≠ core) :
    let S := satelliteGate hpat F hmin hcore hj
    Cograph.Tight (G := G) (F.getCycle core).support S ∧
      S ⊂ (F.getCycle core).support ∧
        S.Nonempty ∧
          (∀ v ∈ (F.getCycle j).support,
            (rowProfile (G := G) (F.getCycle core).support v).Nonempty ∧
              IsCograph G
                  ((F.getCycle core).support \
                    rowProfile (G := G) (F.getCycle core).support v) ∧
                Cograph.Saturated (G := G) (F.getCycle core).support
                  (rowProfile (G := G) (F.getCycle core).support v) ∧
                  Cograph.canonicalContainer (G := G)
                      (F.getCycle core).support
                      (rowProfile (G := G) (F.getCycle core).support v) =
                    S ∧
                    rowProfile (G := G) (F.getCycle core).support v ⊆ S) ∧
            (∀ x ∈ (F.getCycle core).support, ∀ y ∈ (F.getCycle j).support,
              G.Adj x y → x ∈ S) := by
  obtain ⟨S, hT, hproper, hrows, hatt⟩ :=
    satellite_saturated_common_gate_of_min hpat F hmin hj.symm hcore
  have hstart := hrows (F.getCycle j).start (F.getCycle j).start_mem_support
  have hgate : satelliteGate hpat F hmin hcore hj = S := hstart.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hgate] using hT
  · simpa [hgate] using hproper
  · have hA := hstart.1
    have hsub := hstart.2.2.2.2
    have hSne : S.Nonempty := hA.mono hsub
    simpa [hgate] using hSne
  · intro v hv
    simpa [hgate] using hrows v hv
  · simpa [hgate] using hatt

/-! ### Distinct-gate anticompleteness via a three-block original cycle -/

lemma exists_core_spanning_of_distinct_gates
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core j k : Fin F.card}
    (hcore : ¬ IsCograph G (F.getCycle core).support)
    (hj : j ≠ core) (hk : k ≠ core) (_hjk : j ≠ k)
    (hgate : satelliteGate hpat F hmin hcore hj ≠
      satelliteGate hpat F hmin hcore hk)
    {u' v' : V}
    (hu' : u' ∈ (F.getCycle j).support)
    (hv' : v' ∈ (F.getCycle k).support) :
    ∃ p : GraphPath G,
      p.support = (F.getCycle core).support ∧
        p.start ∈ rowProfile (G := G) (F.getCycle core).support u' ∧
          p.finish ∈ rowProfile (G := G) (F.getCycle core).support v' := by
  set cH := F.getCycle core
  set A := rowProfile (G := G) cH.support u'
  set B := rowProfile (G := G) cH.support v'
  have hjS := satelliteGate_spec hpat F hmin hcore hj
  have hkS := satelliteGate_spec hpat F hmin hcore hk
  obtain ⟨hAne, hKA, hSatA, hcontA, _⟩ := hjS.2.2.2.1 u' hu'
  obtain ⟨hBne, hKB, hSatB, hcontB, _⟩ := hkS.2.2.2.1 v' hv'
  have hU : cH.support = cH.support := rfl
  have hAsub := rowProfile_subset (G := G) cH.support u'
  have hBsub := rowProfile_subset (G := G) cH.support v'
  have hdiff : Cograph.canonicalContainer (G := G) cH.support A ≠
      Cograph.canonicalContainer (G := G) cH.support B := by
    intro heq
    apply hgate
    calc
      satelliteGate hpat F hmin hcore hj =
          Cograph.canonicalContainer (G := G) cH.support A := hcontA.symm
      _ = Cograph.canonicalContainer (G := G) cH.support B := heq
      _ = satelliteGate hpat F hmin hcore hk := hcontB
  have hsome :
      ∃ a ∈ A, ∃ b ∈ B, SpanningPathCompatible (G := G) cH.support a b := by
    by_contra hnone
    have hinc :=
      Cograph.incompatible_saturated_profiles (G := G) cH hU hAsub hAne hKA
        hBsub hBne hKB (Or.inl hSatA) (by
          intro a ha b hb hR
          exact hnone ⟨a, ha, b, hb, hR⟩)
    exact hdiff hinc.2.2.2
  obtain ⟨a, ha, b, hb, hne, p, hp, hends⟩ := hsome
  rcases hends with hdir | hdir
  · exact ⟨p, hp, by simpa [hdir.1] using ha, by simpa [hdir.2] using hb⟩
  · refine ⟨p.reverse, by simpa [GraphPath.support_reverse] using hp, ?_, ?_⟩
    · simpa [GraphPath.reverse, hdir.2] using ha
    · simpa [GraphPath.reverse, hdir.1] using hb

/-- Distinct-gate satellites are anticomplete: an original cross edge would
open both satellites, realise a core spanning path between the successor
rows, and assemble an original cycle on the three supports, contradicting
global minimum-factor replacement. -/
theorem distinct_gate_satellites_anticomplete
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core j k : Fin F.card}
    (hcore : ¬ IsCograph G (F.getCycle core).support)
    (hj : j ≠ core) (hk : k ≠ core) (hjk : j ≠ k)
    (hgate : satelliteGate hpat F hmin hcore hj ≠
      satelliteGate hpat F hmin hcore hk)
    {u v : V}
    (hu : u ∈ (F.getCycle j).support)
    (hv : v ∈ (F.getCycle k).support) :
    ¬ G.Adj u v := by
  intro hadj
  set cH := F.getCycle core
  set cJ := F.getCycle j
  set cK := F.getCycle k
  obtain ⟨qJ, hqJ, hqJst, hqJfin⟩ := exists_path_open_succ cJ hu
  obtain ⟨qK, hqK, hqKst, hqKfin⟩ := exists_path_open_succ cK hv
  have hu' : cJ.succAt hu ∈ cJ.support := cJ.succAt_mem_support hu
  have hv' : cK.succAt hv ∈ cK.support := cK.succAt_mem_support hv
  obtain ⟨p, hp, ha, hb⟩ :=
    exists_core_spanning_of_distinct_gates hpat F hmin hcore hk hj hjk.symm
      (Ne.symm hgate) hv' hu'
  have hdpq : Disjoint qJ.support qK.reverse.support := by
    simpa [hqJ, hqK, GraphPath.support_reverse] using F.disjoint_getCycle hjk
  have hdpr : Disjoint qJ.support p.support := by
    simpa [hqJ, hp] using F.disjoint_getCycle hj
  have hdqr : Disjoint qK.reverse.support p.support := by
    simpa [hqK, GraphPath.support_reverse, hp] using F.disjoint_getCycle hk
  have h1 : G.Adj qJ.finish qK.reverse.start := by
    simpa [hqJfin, GraphPath.reverse, hqKfin] using hadj
  have h2 : G.Adj qK.reverse.finish p.start := by
    have : p.start ∈ rowProfile (G := G) cH.support (cK.succAt hv) := ha
    have hmem := (mem_rowProfile_iff (G := G)).1 this
    simpa [GraphPath.reverse, hqKst] using hmem.2
  have h3e : G.Adj p.finish qJ.start := by
    have : p.finish ∈ rowProfile (G := G) cH.support (cJ.succAt hu) := hb
    have hmem := (mem_rowProfile_iff (G := G)).1 this
    simpa [hqJst] using hmem.2.symm
  have hcard : 3 ≤ (qJ.support ∪ (qK.reverse.support ∪ p.support)).card := by
    have hj3 := cJ.three_le_card_support
    have hk3 := cK.three_le_card_support
    have hh3 := cH.three_le_card_support
    have hJ : qJ.support.card = cJ.support.card := by rw [hqJ]
    have hK : qK.reverse.support.card = cK.support.card := by
      simpa [GraphPath.support_reverse] using congrArg Finset.card hqK
    have hH : p.support.card = cH.support.card := by rw [hp]
    have hKP : Disjoint qK.reverse.support p.support := hdqr
    have hKPcard : (qK.reverse.support ∪ p.support).card =
        qK.reverse.support.card + p.support.card :=
      card_union_of_disjoint hKP
    have hdisj' : Disjoint qJ.support (qK.reverse.support ∪ p.support) :=
      disjoint_union_right.2 ⟨hdpq, hdpr⟩
    have hU : (qJ.support ∪ (qK.reverse.support ∪ p.support)).card =
        qJ.support.card + (qK.reverse.support ∪ p.support).card :=
      card_union_of_disjoint hdisj'
    omega
  obtain ⟨C, hC⟩ :=
    GraphPath.exists_assemble_three qJ qK.reverse p hdpq hdpr hdqr h1 h2 h3e hcard
  have hspan : C.support = F.selectedSupport ({core, j, k} : Finset (Fin F.card)) := by
    have hsel := F.selectedSupport_triple (i := core) (j := j) (k := k)
    calc
      C.support = qJ.support ∪ (qK.reverse.support ∪ p.support) := hC
      _ = cJ.support ∪ (cK.support ∪ cH.support) := by
        simp [hqJ, hqK, GraphPath.support_reverse, hp, cH]
      _ = cH.support ∪ (cJ.support ∪ cK.support) := by
        ac_rfl
      _ = F.selectedSupport {core, j, k} := by
        simpa [cH, cJ, cK] using hsel.symm
  have h2s : 2 ≤ ({core, j, k} : Finset (Fin F.card)).card := by
    have h3c := card_selected_triple (F := F) hj.symm hk.symm hjk
    omega
  exact F.not_exists_merge_of_min hmin {core, j, k} h2s C hspan

/-! ### At least two groups, via the original host tight cut -/

lemma CycleFactor.selectedSupport_erase_core (F : CycleFactor G)
    (core : Fin F.card) :
    F.selectedSupport (univ.erase core) = univ \ (F.getCycle core).support := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, hxj⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hx
    have hj' : j ≠ core := (mem_erase.1 hj).1
    exact mem_sdiff.2 ⟨mem_univ x, disjoint_left.1 (F.disjoint_getCycle hj') hxj⟩
  · intro hx
    have hxU : x ∈ (univ : Finset V) := mem_univ x
    have hxcore : x ∉ (F.getCycle core).support := (mem_sdiff.1 hx).2
    obtain ⟨c, hc, hxc⟩ := F.mem_iff x
    obtain ⟨n, hn⟩ := List.get_of_mem hc
    let t : Fin F.card := ⟨n.1, by simpa [CycleFactor.card] using n.2⟩
    have hx' : x ∈ (F.getCycle t).support := by
      have hget : F.getCycle t = c := by
        simpa [CycleFactor.getCycle, t] using hn
      simpa [hget] using hxc
    have ht : t ≠ core := by
      intro heq
      have : x ∈ (F.getCycle core).support := by simpa [heq] using hx'
      exact hxcore this
    exact (CycleFactor.mem_selectedSupport (F := F)).2 ⟨t, mem_erase.2 ⟨ht, mem_univ t⟩, hx'⟩

lemma one_le_componentCount_of_nonempty {U : Finset V} (hU : U.Nonempty) :
    1 ≤ componentCount G U := by
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (G.induce (U : Set V)).ConnectedComponent :=
    ⟨(G.induce (U : Set V)).connectedComponentMk ⟨x, hx⟩⟩
  exact Nat.succ_le_iff.2 Nat.card_pos

/-- If every satellite of the unique noncograph core shared one common
gate `S`, the original cut `G − S` would have at least `|S| + 1`
components, contradicting `OneTough`. The satellite union need not be
connected. -/
theorem exists_distinct_gate_satellite
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian)
    {core : Fin F.card}
    (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    ∃ (k : Fin F.card) (hk : k ≠ core),
      k ≠ j ∧
        satelliteGate hpat F hmin hcore hk ≠
          satelliteGate hpat F hmin hcore hj := by
  by_contra hnone
  have hnone' : ∀ (k : Fin F.card) (hk : k ≠ core),
      k = j ∨
        satelliteGate hpat F hmin hcore hk =
          satelliteGate hpat F hmin hcore hj := by
    intro k hk
    have h := not_exists.1 (not_exists.1 hnone k) hk
    rw [not_and, Classical.not_not] at h
    by_cases hkj : k = j
    · exact Or.inl hkj
    · exact Or.inr (h hkj)
  have h3 := three_le_card_of_min_nonHamiltonian hT hord hpat F hmin hNonHam
  have hjS := satelliteGate_spec hpat F hmin hcore hj
  set S := satelliteGate hpat F hmin hcore hj
  have hTgt : Cograph.Tight (G := G) (F.getCycle core).support S := hjS.1
  have hproper : S ⊂ (F.getCycle core).support := hjS.2.1
  have hSne : S.Nonempty := hjS.2.2.1
  have hatt : ∀ t : Fin F.card, t ≠ core →
      ∀ x ∈ (F.getCycle core).support, ∀ y ∈ (F.getCycle t).support,
        G.Adj x y → x ∈ S := by
    intro t ht
    have hteq : satelliteGate hpat F hmin hcore ht = S := by
      rcases hnone' t ht with rfl | heq
      · rfl
      · exact heq
    have hspec := satelliteGate_spec hpat F hmin hcore ht
    simpa [hteq] using hspec.2.2.2.2
  set H := (F.getCycle core).support
  set D := F.selectedSupport (univ.erase core)
  have hDH : D = univ \ H := F.selectedSupport_erase_core core
  have hSsub : S ⊆ H := hTgt.1
  have hdisj : Disjoint (H \ S) D := by
    have : Disjoint H D := by
      rw [hDH]
      exact disjoint_left.2 fun x hxH hxD => (mem_sdiff.1 hxD).2 hxH
    exact this.mono_left sdiff_subset
  have hnocross : ∀ a ∈ H \ S, ∀ b ∈ D, ¬ G.Adj a b := by
    intro a ha b hb hadj
    obtain ⟨t, ht, hbt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hb
    have ht' : t ≠ core := (mem_erase.1 ht).1
    have haH : a ∈ H := (mem_sdiff.1 ha).1
    have haS : a ∈ S := hatt t ht' a haH b hbt hadj
    exact (mem_sdiff.1 ha).2 haS
  have hrem : univ \ S = (H \ S) ∪ D := by
    have hDS : Disjoint D S := by
      have : Disjoint D H := by
        rw [hDH]
        exact disjoint_left.2 fun x hxD hxH => (mem_sdiff.1 hxD).2 hxH
      exact this.mono_right hSsub
    have hD : D \ S = D := sdiff_eq_self_iff_disjoint.2 hDS
    calc
      univ \ S = (H ∪ D) \ S := by
        have : H ∪ D = univ := by
          ext x
          constructor
          · intro; exact mem_univ x
          · intro _
            by_cases hxH : x ∈ H
            · exact mem_union.2 (Or.inl hxH)
            · exact mem_union.2 (Or.inr (by
                simpa [hDH] using mem_sdiff.2 ⟨mem_univ x, hxH⟩))
        rw [this]
      _ = (H \ S) ∪ (D \ S) := union_sdiff_distrib _ _ _
      _ = (H \ S) ∪ D := by rw [hD]
  have hcount :
      componentCount G ((H \ S) ∪ D) =
        componentCount G (H \ S) + componentCount G D :=
    Cograph.componentCount_union_of_no_cross (G := G) hdisj hnocross
  have hTight : componentCount G (H \ S) = S.card := hTgt.2
  have hDne : D.Nonempty := by
    have : 1 ≤ F.card := F.one_le_card hord
    have h2 : 2 ≤ F.card := by omega
    have hex : (univ.erase core).Nonempty := by
      have : 1 ≤ (univ.erase core).card := by
        have : (univ.erase core).card = F.card - 1 := by
          simp [card_erase_of_mem (mem_univ core), card_univ, Fintype.card_fin]
        omega
      exact card_pos.1 this
    obtain ⟨t, ht⟩ := hex
    exact ⟨(F.getCycle t).start, (CycleFactor.mem_selectedSupport (F := F)).2
      ⟨t, ht, (F.getCycle t).start_mem_support⟩⟩
  have hDpos : 1 ≤ componentCount G D :=
    one_le_componentCount_of_nonempty hDne
  have hEq : componentCount G (univ \ S) =
      S.card + componentCount G D := by
    rw [hrem, hcount, hTight]
  have h2c : 2 ≤ componentCount G (univ \ S) := by
    have hpos : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.2 hSne)
    have : S.card + 1 ≤ S.card + componentCount G D :=
      Nat.add_le_add_left hDpos _
    omega
  have hle : componentCount G (univ \ S) ≤ S.card := hT S h2c
  omega

/-! ### Own group / foreign remainder callers -/

noncomputable def ownSatellites
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) : Finset (Fin F.card) :=
  univ.filter fun t =>
    if ht : t = core then False
    else satelliteGate hpat F hmin hcore ht =
      satelliteGate hpat F hmin hcore hj

noncomputable def foreignSatellites
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) : Finset (Fin F.card) :=
  univ.filter fun t =>
    if ht : t = core then False
    else satelliteGate hpat F hmin hcore ht ≠
      satelliteGate hpat F hmin hcore hj

lemma mem_ownSatellites
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j t : Fin F.card} (hj : j ≠ core) :
    t ∈ ownSatellites hpat F hmin hcore hj ↔
      ∃ ht : t ≠ core,
        satelliteGate hpat F hmin hcore ht =
          satelliteGate hpat F hmin hcore hj := by
  constructor
  · intro htO
    have hif := (mem_filter.mp htO).2
    have ht : t ≠ core := by
      intro hc
      simp [hc] at hif
    refine ⟨ht, ?_⟩
    simpa [dif_neg ht] using hif
  · intro ⟨ht, heq⟩
    refine mem_filter.2 ⟨mem_univ t, ?_⟩
    simpa [dif_neg ht] using heq

lemma mem_foreignSatellites
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j t : Fin F.card} (hj : j ≠ core) :
    t ∈ foreignSatellites hpat F hmin hcore hj ↔
      ∃ ht : t ≠ core,
        satelliteGate hpat F hmin hcore ht ≠
          satelliteGate hpat F hmin hcore hj := by
  constructor
  · intro htO
    have hif := (mem_filter.mp htO).2
    have ht : t ≠ core := by
      intro hc
      simp [hc] at hif
    refine ⟨ht, ?_⟩
    simpa [dif_neg ht] using hif
  · intro ⟨ht, hne⟩
    refine mem_filter.2 ⟨mem_univ t, ?_⟩
    simpa [dif_neg ht] using hne

lemma self_mem_ownSatellites
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    j ∈ ownSatellites hpat F hmin hcore hj :=
  (mem_ownSatellites hpat F hmin hcore hj (t := j)).2 ⟨hj, rfl⟩

lemma core_not_mem_ownSatellites
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    core ∉ ownSatellites hpat F hmin hcore hj := by
  intro h
  obtain ⟨hc, _⟩ := (mem_ownSatellites hpat F hmin hcore hj (t := core)).1 h
  exact hc rfl

lemma ownSatellites_nonempty
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    (ownSatellites hpat F hmin hcore hj).Nonempty :=
  ⟨j, self_mem_ownSatellites hpat F hmin hcore hj⟩

lemma foreignSatellites_nonempty_of_distinct
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian)
    {core : Fin F.card}
    (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    (foreignSatellites hpat F hmin hcore hj).Nonempty := by
  obtain ⟨k, hk, _hkj, hgate⟩ :=
    exists_distinct_gate_satellite hT hord hpat F hmin hNonHam hcore hj
  exact ⟨k, (mem_foreignSatellites hpat F hmin hcore hj (t := k)).2 ⟨hk, hgate⟩⟩

lemma disjoint_own_foreign
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    Disjoint (ownSatellites hpat F hmin hcore hj)
      (foreignSatellites hpat F hmin hcore hj) := by
  refine disjoint_left.2 ?_
  intro t htO htF
  obtain ⟨ht, heq⟩ := (mem_ownSatellites hpat F hmin hcore hj (t := t)).1 htO
  obtain ⟨_, hne⟩ := (mem_foreignSatellites hpat F hmin hcore hj (t := t)).1 htF
  exact hne heq

lemma disjoint_core_own_support
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    Disjoint (F.getCycle core).support
      (F.selectedSupport (ownSatellites hpat F hmin hcore hj)) := by
  refine disjoint_left.2 ?_
  intro x hxH hxB
  obtain ⟨t, ht, hxt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hxB
  obtain ⟨htc, _⟩ := (mem_ownSatellites hpat F hmin hcore hj (t := t)).1 ht
  exact disjoint_left.1 (F.disjoint_getCycle htc.symm) hxH hxt

lemma disjoint_core_foreign_support
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    Disjoint (F.getCycle core).support
      (F.selectedSupport (foreignSatellites hpat F hmin hcore hj)) := by
  refine disjoint_left.2 ?_
  intro x hxH hxR
  obtain ⟨t, ht, hxt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hxR
  obtain ⟨htc, _⟩ := (mem_foreignSatellites hpat F hmin hcore hj (t := t)).1 ht
  exact disjoint_left.1 (F.disjoint_getCycle htc.symm) hxH hxt

lemma disjoint_own_foreign_support
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    Disjoint (F.selectedSupport (ownSatellites hpat F hmin hcore hj))
      (F.selectedSupport (foreignSatellites hpat F hmin hcore hj)) := by
  refine disjoint_left.2 ?_
  intro x hxB hxR
  obtain ⟨t, ht, hxt⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hxB
  obtain ⟨s, hs, hxs⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hxR
  obtain ⟨htc, _⟩ := (mem_ownSatellites hpat F hmin hcore hj (t := t)).1 ht
  obtain ⟨hsc, _⟩ := (mem_foreignSatellites hpat F hmin hcore hj (t := s)).1 hs
  have hts : t ≠ s := by
    intro heq
    subst heq
    exact disjoint_left.1 (disjoint_own_foreign hpat F hmin hcore hj) ht hs
  exact disjoint_left.1 (F.disjoint_getCycle hts) hxt hxs

lemma own_foreign_partition_univ
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    (F.getCycle core).support ∪
        F.selectedSupport (ownSatellites hpat F hmin hcore hj) ∪
          F.selectedSupport (foreignSatellites hpat F hmin hcore hj) =
      univ := by
  ext x
  constructor
  · intro; exact mem_univ x
  · intro _
    obtain ⟨c, hc, hxc⟩ := F.mem_iff x
    obtain ⟨n, hn⟩ := List.get_of_mem hc
    let t' : Fin F.card := ⟨n.1, by simpa [CycleFactor.card] using n.2⟩
    have hx' : x ∈ (F.getCycle t').support := by
      have hget : F.getCycle t' = c := by
        simpa [CycleFactor.getCycle, t'] using hn
      simpa [hget] using hxc
    by_cases htcore : t' = core
    · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (by simpa [htcore] using hx'))))
    · by_cases hgate :
          satelliteGate hpat F hmin hcore htcore =
            satelliteGate hpat F hmin hcore hj
      · refine mem_union.2 (Or.inl (mem_union.2 (Or.inr ?_)))
        exact (CycleFactor.mem_selectedSupport (F := F)).2
          ⟨t', (mem_ownSatellites hpat F hmin hcore hj).2 ⟨htcore, hgate⟩, hx'⟩
      · refine mem_union.2 (Or.inr ?_)
        exact (CycleFactor.mem_selectedSupport (F := F)).2
          ⟨t', (mem_foreignSatellites hpat F hmin hcore hj).2 ⟨htcore, hgate⟩, hx'⟩

lemma own_anticomplete_foreign
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {core : Fin F.card} (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core)
    {u v : V}
    (hu : u ∈ F.selectedSupport (ownSatellites hpat F hmin hcore hj))
    (hv : v ∈ F.selectedSupport (foreignSatellites hpat F hmin hcore hj)) :
    ¬ G.Adj u v := by
  obtain ⟨t, ht, hut⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hu
  obtain ⟨s, hs, hvs⟩ := (CycleFactor.mem_selectedSupport (F := F)).1 hv
  obtain ⟨htc, heq⟩ := (mem_ownSatellites hpat F hmin hcore hj (t := t)).1 ht
  obtain ⟨hsc, hne⟩ := (mem_foreignSatellites hpat F hmin hcore hj (t := s)).1 hs
  have hts : t ≠ s := by
    intro h
    subst h
    exact hne heq
  have hgate : satelliteGate hpat F hmin hcore htc ≠
      satelliteGate hpat F hmin hcore hsc := by
    simpa [heq] using hne.symm
  exact distinct_gate_satellites_anticomplete hpat F hmin hcore htc hsc hts
    hgate hut hvs

/-- A whole own group is a cograph: a vertex of a different-gate satellite
is anticomplete to the entire group, so an induced P4 in the group would
be an induced P4 union P1. Inter-satellite original edges inside the group
are retained. -/
theorem own_group_isCograph
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian)
    {core : Fin F.card}
    (hcore : ¬ IsCograph G (F.getCycle core).support)
    {j : Fin F.card} (hj : j ≠ core) :
    IsCograph G (F.selectedSupport (ownSatellites hpat F hmin hcore hj)) := by
  intro a b c d ha hb hc hd hp
  obtain ⟨k, hk⟩ :=
    foreignSatellites_nonempty_of_distinct hT hord hpat F hmin hNonHam hcore hj
  let x := (F.getCycle k).start
  have hxR : x ∈ F.selectedSupport (foreignSatellites hpat F hmin hcore hj) :=
    (CycleFactor.mem_selectedSupport (F := F)).2 ⟨k, hk, (F.getCycle k).start_mem_support⟩
  have hdisjBR := disjoint_own_foreign_support hpat F hmin hcore hj
  have hxne : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; subst h; exact disjoint_left.1 hdisjBR ha hxR
    · intro h; subst h; exact disjoint_left.1 hdisjBR hb hxR
    · intro h; subst h; exact disjoint_left.1 hdisjBR hc hxR
    · intro h; subst h; exact disjoint_left.1 hdisjBR hd hxR
  have hno : ¬ G.Adj x a ∧ ¬ G.Adj x b ∧ ¬ G.Adj x c ∧ ¬ G.Adj x d := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hxa
      exact own_anticomplete_foreign (u := a) (v := x) hpat F hmin hcore hj ha hxR
        (SimpleGraph.Adj.symm hxa)
    · intro hxb
      exact own_anticomplete_foreign (u := b) (v := x) hpat F hmin hcore hj hb hxR
        (SimpleGraph.Adj.symm hxb)
    · intro hxc
      exact own_anticomplete_foreign (u := c) (v := x) hpat F hmin hcore hj hc hxR
        (SimpleGraph.Adj.symm hxc)
    · intro hxd
      exact own_anticomplete_foreign (u := d) (v := x) hpat F hmin hcore hj hd hxR
        (SimpleGraph.Adj.symm hxd)
  have hpat' := hpat hp hxne.1 hxne.2.1 hxne.2.2.1 hxne.2.2.2
  rcases hpat' with h | h | h | h
  · exact hno.1 h
  · exact hno.2.1 h
  · exact hno.2.2.1 h
  · exact hno.2.2.2 h

/-- Bundled canonical normal form consumed by extended-cut / locality
callers. Fields record original factor-index provenance; none assumes the
final host-cut contradiction as an input. -/
structure CanonicalNormalForm (F : CycleFactor G) where
  core : Fin F.card
  hCoreNoncog : ¬ IsCograph G (F.getCycle core).support
  hSatCog : ∀ j : Fin F.card, j ≠ core →
    IsCograph G (F.getCycle j).support
  hThree : 3 ≤ F.card
  gateOf : ∀ j : Fin F.card, j ≠ core → Finset V
  hGateTight : ∀ j hj, Cograph.Tight (G := G) (F.getCycle core).support (gateOf j hj)
  hGateProper : ∀ j hj, gateOf j hj ⊂ (F.getCycle core).support
  hGateNonempty : ∀ j hj, (gateOf j hj).Nonempty
  hGateRows : ∀ j hj, ∀ v ∈ (F.getCycle j).support,
    (rowProfile (G := G) (F.getCycle core).support v).Nonempty ∧
      IsCograph G ((F.getCycle core).support \
        rowProfile (G := G) (F.getCycle core).support v) ∧
      Cograph.Saturated (G := G) (F.getCycle core).support
        (rowProfile (G := G) (F.getCycle core).support v) ∧
      Cograph.canonicalContainer (G := G) (F.getCycle core).support
          (rowProfile (G := G) (F.getCycle core).support v) =
        gateOf j hj ∧
      rowProfile (G := G) (F.getCycle core).support v ⊆ gateOf j hj
  hGateAttach : ∀ j hj, ∀ x ∈ (F.getCycle core).support,
    ∀ y ∈ (F.getCycle j).support, G.Adj x y → x ∈ gateOf j hj
  own : ∀ j : Fin F.card, j ≠ core → Finset (Fin F.card)
  foreign : ∀ j : Fin F.card, j ≠ core → Finset (Fin F.card)
  hOwnMem : ∀ j hj t, t ∈ own j hj ↔
    ∃ ht : t ≠ core, gateOf t ht = gateOf j hj
  hForeignMem : ∀ j hj t, t ∈ foreign j hj ↔
    ∃ ht : t ≠ core, gateOf t ht ≠ gateOf j hj
  hOwnNe : ∀ j hj, (own j hj).Nonempty
  hForeignNe : ∀ j hj, (foreign j hj).Nonempty
  hDisjHB : ∀ j hj, Disjoint (F.getCycle core).support
    (F.selectedSupport (own j hj))
  hDisjHR : ∀ j hj, Disjoint (F.getCycle core).support
    (F.selectedSupport (foreign j hj))
  hDisjBR : ∀ j hj, Disjoint (F.selectedSupport (own j hj))
    (F.selectedSupport (foreign j hj))
  hPartition : ∀ j hj,
    (F.getCycle core).support ∪ F.selectedSupport (own j hj) ∪
      F.selectedSupport (foreign j hj) = univ
  hAnticompleteBR : ∀ j hj {u v : V},
    u ∈ F.selectedSupport (own j hj) →
      v ∈ F.selectedSupport (foreign j hj) → ¬ G.Adj u v
  hOwnCograph : ∀ j hj, IsCograph G (F.selectedSupport (own j hj))

theorem exists_canonical_normal_form
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpat : NoInducedP4UnionP1 G)
    (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (hNonHam : ¬ G.IsHamiltonian) :
    Nonempty (CanonicalNormalForm F) := by
  obtain ⟨core, hcore, huniq⟩ :=
    existsUnique_noncograph_block_of_min hT hord hpat F hmin hNonHam
  refine ⟨{
    core := core
    hCoreNoncog := hcore
    hSatCog := fun j hj => by
      by_contra hnc
      exact hj (huniq j hnc)
    hThree := three_le_card_of_min_nonHamiltonian hT hord hpat F hmin hNonHam
    gateOf := fun j hj => satelliteGate hpat F hmin hcore hj
    hGateTight := fun j hj => (satelliteGate_spec hpat F hmin hcore hj).1
    hGateProper := fun j hj => (satelliteGate_spec hpat F hmin hcore hj).2.1
    hGateNonempty := fun j hj => (satelliteGate_spec hpat F hmin hcore hj).2.2.1
    hGateRows := fun j hj => (satelliteGate_spec hpat F hmin hcore hj).2.2.2.1
    hGateAttach := fun j hj => (satelliteGate_spec hpat F hmin hcore hj).2.2.2.2
    own := fun j hj => ownSatellites hpat F hmin hcore hj
    foreign := fun j hj => foreignSatellites hpat F hmin hcore hj
    hOwnMem := fun j hj t => mem_ownSatellites hpat F hmin hcore hj
    hForeignMem := fun j hj t => mem_foreignSatellites hpat F hmin hcore hj
    hOwnNe := fun j hj => ownSatellites_nonempty hpat F hmin hcore hj
    hForeignNe := fun j hj =>
      foreignSatellites_nonempty_of_distinct hT hord hpat F hmin hNonHam hcore hj
    hDisjHB := fun j hj => disjoint_core_own_support hpat F hmin hcore hj
    hDisjHR := fun j hj => disjoint_core_foreign_support hpat F hmin hcore hj
    hDisjBR := fun j hj => disjoint_own_foreign_support hpat F hmin hcore hj
    hPartition := fun j hj => own_foreign_partition_univ hpat F hmin hcore hj
    hAnticompleteBR := fun j hj _u _v hu hv =>
      own_anticomplete_foreign hpat F hmin hcore hj hu hv
    hOwnCograph := fun j hj =>
      own_group_isCograph hT hord hpat F hmin hNonHam hcore hj
  }⟩

end Nikoghosyan
