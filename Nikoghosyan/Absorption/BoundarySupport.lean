/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.ProtectedInduction
import Nikoghosyan.Cograph.HamiltonBalanced
import Nikoghosyan.Cograph.SaturatedJoin
import Nikoghosyan.Cograph.Profiles
import Nikoghosyan.NoncographUnion

/-!
# Independent OLD/NEW boundary-support prefix for strict absorption

Reusable kernel-checked helpers for manuscript `abs:thm:strict-absorption`.
OLD support is the prescribed cycle `cH` on `H`. NEW support is a path
on `H ∪ D` after inserting a disjoint genuine cycle on `D`. Incidence,
switch-through-`D`, saving-component selection, and the weak three-bound
do not require the path support to equal the cycle support.

This module does not prove `exists_strict_absorption`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

namespace Nikoghosyan
namespace GraphPath

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Internal `A`-vertices that also lie on the prescribed cycle have the
same two incident walk-edges on a protected path. The path need not span
the cycle support. -/
theorem incidentEdges_eq_cycle_of_internal_protected_weak
    (p : GraphPath G) (c : GraphCycle G) {A : Finset V}
    (hP : p.ProtectedAt c A) {v : V}
    (hvA : v ∈ A) (hvP : v ∈ p.support) (hvC : v ∈ c.support)
    (hs : v ≠ p.start) (hf : v ≠ p.finish) :
    p.incidentEdges v = c.incidentEdges v := by
  have h2p : (p.incidentEdges v).card = 2 :=
    p.incidentEdges_card_internal hvP hs hf
  have h2c : (c.incidentEdges v).card = 2 := c.incidentEdges_card hvC
  have hsub : p.incidentEdges v ⊆ c.incidentEdges v :=
    hP.incidentEdges_subset_cycle hvA
  exact eq_of_subset_of_card_le hsub (by omega)

/-- Splice adds only the unordered seam, which meets `A` at neither end. -/
lemma splice_AIncident (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) {A : Finset V}
    (hp : p.finish ∉ A) (hq : q.start ∉ A) :
    (p.splice q h hd).AIncident A = p.AIncident A ∪ q.AIncident A := by
  ext e
  simp only [mem_AIncident_iff, edges_splice p q h hd, mem_union, mem_singleton]
  constructor
  · rintro ⟨hmem, ⟨b, hbA, hbe⟩⟩
    rcases hmem with (h | h) | rfl
    · exact Or.inl ⟨h, ⟨b, hbA, hbe⟩⟩
    · exact Or.inr ⟨h, ⟨b, hbA, hbe⟩⟩
    · rcases Sym2.mem_iff.mp hbe with hb | hb
      · exact (hp (hb ▸ hbA)).elim
      · exact (hq (hb ▸ hbA)).elim
  · rintro (⟨he, hA⟩ | ⟨he, hA⟩)
    · exact ⟨Or.inl (Or.inl he), hA⟩
    · exact ⟨Or.inl (Or.inr he), hA⟩

lemma AIncident_eq_empty_of_disjoint_support' {A : Finset V}
    (q : GraphPath G) (hd : Disjoint q.support A) :
    q.AIncident A = ∅ :=
  AIncident_eq_empty_of_disjoint_support q hd

/-- Join two whole cycle pieces through a disjoint original block `r`
whose ends are adjacent to the two split vertices. The result spans
`p.support ∪ r.support`. -/
lemma pieceAfter_support_subset (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) :
    (pieceAfter p hu hclose hne hv).support ⊆ p.support := by
  intro x hx
  have : x ∈ (pieceBefore p hu hclose hne hv hnv).support ∪
      (pieceAfter p hu hclose hne hv).support := mem_union.2 (Or.inr hx)
  rwa [support_pieces_union p hu hclose hne hv hnv] at this

lemma pieceBefore_support_subset (p : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) :
    (pieceBefore p hu hclose hne hv hnv).support ⊆ p.support := by
  intro x hx
  have : x ∈ (pieceBefore p hu hclose hne hv hnv).support ∪
      (pieceAfter p hu hclose hne hv).support := mem_union.2 (Or.inl hx)
  rwa [support_pieces_union p hu hclose hne hv hnv] at this

lemma disjoint_r_pieceAfter (p r : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) (hd : Disjoint r.support p.support) :
    Disjoint r.support (pieceAfter p hu hclose hne hv).support :=
  Disjoint.mono_right (pieceAfter_support_subset p hu hclose hne hv hnv) hd

lemma disjoint_pieceBefore_mid (p r : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) (hd : Disjoint r.support p.support)
    (hfv : G.Adj r.finish v) :
    Disjoint (pieceBefore p hu hclose hne hv hnv).support
      (r.splice (pieceAfter p hu hclose hne hv) hfv
        (disjoint_r_pieceAfter p r hu hclose hne hv hnv hd)).support := by
  have hdAfter := disjoint_r_pieceAfter p r hu hclose hne hv hnv hd
  have hdisjPieces := disjoint_pieces p hu hclose hne hv hnv
  have hdB : Disjoint (pieceBefore p hu hclose hne hv hnv).support r.support :=
    Disjoint.mono_left (pieceBefore_support_subset p hu hclose hne hv hnv)
      (Disjoint.symm hd)
  rw [GraphPath.support_splice r (pieceAfter p hu hclose hne hv) hfv hdAfter]
  exact disjoint_union_right.2 ⟨hdB, hdisjPieces⟩

/-- Join two whole cycle pieces through a disjoint original block `r`. -/
noncomputable def switchOpenStartsThrough (p r : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) (hd : Disjoint r.support p.support)
    (hsu : G.Adj u r.start) (hfv : G.Adj r.finish v) : GraphPath G :=
  switchStarts (pieceBefore p hu hclose hne hv hnv)
    (r.splice (pieceAfter p hu hclose hne hv) hfv
      (disjoint_r_pieceAfter p r hu hclose hne hv hnv hd))
    (by
      change G.Adj (pieceBefore p hu hclose hne hv hnv).start r.start
      simpa [pieceBefore_start p hu hclose hne hv hnv] using hsu)
    (disjoint_pieceBefore_mid p r hu hclose hne hv hnv hd hfv)

lemma switchOpenStartsThrough_support (p r : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) (hd : Disjoint r.support p.support)
    (hsu : G.Adj u r.start) (hfv : G.Adj r.finish v) :
    (switchOpenStartsThrough p r hu hclose hne hv hnv hd hsu hfv).support =
      p.support ∪ r.support := by
  unfold switchOpenStartsThrough
  rw [switchStarts_support,
    GraphPath.support_splice r (pieceAfter p hu hclose hne hv)
      hfv (disjoint_r_pieceAfter p r hu hclose hne hv hnv hd)]
  rw [union_comm r.support, ← union_assoc,
    support_pieces_union p hu hclose hne hv hnv]

lemma switchOpenStartsThrough_ProtectedAt (p r : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) (hd : Disjoint r.support p.support)
    (hsu : G.Adj u r.start) (hfv : G.Adj r.finish v)
    {A : Finset V} (huA : u ∉ A) (hvA : v ∉ A)
    (hrA : Disjoint r.support A)
    {c : GraphCycle G}
    (hedges : p.edges ∪ {s(p.finish, p.start)} = c.walk.edges.toFinset) :
    (switchOpenStartsThrough p r hu hclose hne hv hnv hd hsu hfv).ProtectedAt c A := by
  let pb := pieceBefore p hu hclose hne hv hnv
  let pa := pieceAfter p hu hclose hne hv
  have hdAfter := disjoint_r_pieceAfter p r hu hclose hne hv hnv hd
  have hdBefore := disjoint_pieceBefore_mid p r hu hclose hne hv hnv hd hfv
  have hsu' : G.Adj pb.start
      (r.splice pa hfv hdAfter).start := by
    have hst : pb.start = u := pieceBefore_start p hu hclose hne hv hnv
    have hsp : (r.splice pa hfv hdAfter).start = r.start := rfl
    simpa [hst, hsp] using hsu
  have hrFinA : r.finish ∉ A := disjoint_left.1 hrA r.finish_mem_support
  have hpaStA : pa.start ∉ A := by
    have : pa.start = v := pieceAfter_start p hu hclose hne hv
    simpa [this] using hvA
  have hmidA : (r.splice pa hfv hdAfter).start ∉ A :=
    disjoint_left.1 hrA r.start_mem_support
  have hpbStA : pb.start ∉ A := by
    have : pb.start = u := pieceBefore_start p hu hclose hne hv hnv
    simpa [this] using huA
  intro e he
  have hAI := switchStarts_AIncident pb (r.splice pa hfv hdAfter)
    hsu' hdBefore hpbStA hmidA
  have he' : e ∈ pb.AIncident A ∪ (r.splice pa hfv hdAfter).AIncident A := by
    change e ∈
        (switchStarts pb (r.splice pa hfv hdAfter) hsu' hdBefore).AIncident A
      at he
    simpa [hAI] using he
  have hmidAI := splice_AIncident r pa hfv hdAfter hrFinA hpaStA
  have hrAI : r.AIncident A = ∅ :=
    AIncident_eq_empty_of_disjoint_support r hrA
  have hsub := pieces_edges_subset_open p hu hclose hne hv hnv
  have hopen := openAtStart_edges_subset_cycle p hu hclose hne hedges
  rcases mem_union.1 he' with h | h
  · exact hopen (hsub.1 (mem_AIncident_iff.1 h).1)
  · have : e ∈ r.AIncident A ∪ pa.AIncident A := by
      simpa [hmidAI] using h
    rcases mem_union.1 this with hr | hpa
    · exact (notMem_empty e (by simpa [hrAI] using hr)).elim
    · exact hopen (hsub.2 (mem_AIncident_iff.1 hpa).1)

lemma switchOpenStartsThrough_start (p r : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) (hd : Disjoint r.support p.support)
    (hsu : G.Adj u r.start) (hfv : G.Adj r.finish v) :
    (switchOpenStartsThrough p r hu hclose hne hv hnv hd hsu hfv).start =
      ((openAtStart p hu hclose hne).takeUntil hv).walk.penultimate := by
  simp [switchOpenStartsThrough, switchStarts_start, pieceBefore_finish]

lemma switchOpenStartsThrough_finish (p r : GraphPath G) {u v : V}
    (hu : u ∈ p.support) (hclose : G.Adj p.finish p.start)
    (hne : u ≠ p.start) (hv : v ∈ (openAtStart p hu hclose hne).support)
    (hnv : v ≠ u) (hd : Disjoint r.support p.support)
    (hsu : G.Adj u r.start) (hfv : G.Adj r.finish v) :
    (switchOpenStartsThrough p r hu hclose hne hv hnv hd hsu hfv).finish =
      (p.takeUntil hu).walk.penultimate := by
  unfold switchOpenStartsThrough
  rw [switchStarts_finish]
  exact pieceAfter_finish p hu hclose hne hv

end GraphPath

namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath
open Nikoghosyan.GraphCycle

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma connected_of_cycle (c : GraphCycle G) :
    (G.induce (c.support : Set V)).Connected := by
  refine (SimpleGraph.connected_iff (G.induce (c.support : Set V))).2 ?_
  refine ⟨fun x y =>
    reachable_of_componentCount_eq_one (G := G)
      (componentCount_cycle_eq_one c) x.2 y.2, ?_⟩
  exact ⟨⟨c.start, c.start_mem_support⟩⟩

/-- Forget the induced-subgraph subtype of a walk. -/
def walkOfInduce {s : Set V} {x y : s} (w : (G.induce s).Walk x y) :
    G.Walk x.1 y.1 :=
  w.map (Embedding.induce s).toHom

lemma walkOfInduce_support_subset {s : Set V} {x y : s}
    (w : (G.induce s).Walk x y) :
    ∀ z ∈ (walkOfInduce w).support, z ∈ s := by
  intro z hz
  have hmap :=
    Walk.support_map (f := (Embedding.induce (s := s) (G := G)).toHom) w
  have hz' : z ∈ w.support.map (Embedding.induce (s := s) (G := G)).toHom :=
    hmap ▸ hz
  obtain ⟨z', _, rfl⟩ := List.mem_map.1 hz'
  exact z'.2

/-- A connected induced `D ⊆ A ∪ B` with no `A`–`B` edge lies wholly in
one side. -/
lemma subset_left_or_right_of_connected {A B D : Finset V}
    (hdisj : Disjoint A B) (hcover : D ⊆ A ∪ B)
    (hnocross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hDconn : (G.induce (D : Set V)).Connected) :
    D ⊆ A ∨ D ⊆ B := by
  by_contra h
  push_neg at h
  obtain ⟨x, hxD, hxA⟩ := not_subset.1 h.1
  obtain ⟨y, hyD, hyB⟩ := not_subset.1 h.2
  have hxB : x ∈ B := (mem_union.1 (hcover hxD)).resolve_left hxA
  have hyA : y ∈ A := (mem_union.1 (hcover hyD)).resolve_right hyB
  have hR : (G.induce (D : Set V)).Reachable ⟨x, hxD⟩ ⟨y, hyD⟩ :=
    hDconn.preconnected _ _
  obtain ⟨w⟩ := hR
  let wG := walkOfInduce w
  have hsupp : ∀ z ∈ wG.support, z ∈ (B : Set V) ∨ z ∈ (A : Set V) := by
    intro z hz
    have hzD : z ∈ (D : Set V) := walkOfInduce_support_subset w z hz
    have hzAB : z ∈ A ∪ B := hcover hzD
    rcases mem_union.1 hzAB with hA | hB
    · exact Or.inr hA
    · exact Or.inl hB
  have hnocrossBA : ∀ b ∈ (B : Set V), ∀ a ∈ (A : Set V), ¬ G.Adj b a :=
    fun b hb a ha hab => hnocross a ha b hb hab.symm
  have hyB' : y ∈ (B : Set V) :=
    walk_support_subset_of_no_cross (A := (B : Set V)) (B := (A : Set V))
      hnocrossBA wG hxB hsupp y (by
        simpa [wG, walkOfInduce] using Walk.end_mem_support wG)
  exact Finset.disjoint_left.1 hdisj hyA hyB'

/-- The induced block containing a connected nonempty `D ⊆ K` that is
anticomplete to the rest of `K`. -/
lemma exists_block_containing {K D : Finset V}
    (hD : D ⊆ K) (hDne : D.Nonempty)
    (hDconn : (G.induce (D : Set V)).Connected) :
    ∃ U : Finset V,
      U ⊆ K ∧ D ⊆ U ∧ U.Nonempty ∧
        (G.induce (U : Set V)).Connected ∧
          (∀ a ∈ U, ∀ b ∈ K \ U, ¬ G.Adj a b) := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (K D : Finset V), K.card = n → D ⊆ K → D.Nonempty →
        (G.induce (D : Set V)).Connected →
          ∃ U : Finset V,
            U ⊆ K ∧ D ⊆ U ∧ U.Nonempty ∧
              (G.induce (U : Set V)).Connected ∧
                (∀ a ∈ U, ∀ b ∈ K \ U, ¬ G.Adj a b))
    K.card ?_ K D rfl hD hDne hDconn
  intro n ih K D hn hDK hDne hDconn
  by_cases hconn : (G.induce (K : Set V)).Connected
  · exact ⟨K, subset_rfl, hDK, hDne.mono hDK, hconn, fun a _ b hb =>
      (notMem_empty b (by simpa using hb)).elim⟩
  · have hKne : K.Nonempty := hDne.mono hDK
    obtain ⟨A, B, hAsub, hBsub, hAne, hBne, hdisj, hcover, hnocross,
        hAcard, hBcard⟩ :=
      exists_disjoint_union_on (G := G) (U := K) hconn hKne
    have hEq : A ∪ B = K := hcover
    have hDsplit : D ⊆ A ∨ D ⊆ B :=
      subset_left_or_right_of_connected hdisj (hDK.trans (hEq.symm.subset))
        hnocross hDconn
    have hltA : A.card < n := by simpa [hn] using hAcard
    have hltB : B.card < n := by simpa [hn] using hBcard
    rcases hDsplit with hDA | hDB
    · obtain ⟨U, hU, hDU, hUne, hUconn, hnc⟩ :=
        ih A.card hltA A D rfl hDA hDne hDconn
      refine ⟨U, hU.trans hAsub, hDU, hUne, hUconn, ?_⟩
      intro a ha b hb
      have hbK : b ∈ (A ∪ B) \ U := by simpa [hEq] using hb
      have hb' : b ∈ A \ U ∨ b ∈ B := by
        have : b ∈ A ∪ B := (mem_sdiff.1 hbK).1
        rcases mem_union.1 this with hA | hB
        · exact Or.inl (mem_sdiff.2 ⟨hA, (mem_sdiff.1 hbK).2⟩)
        · exact Or.inr hB
      rcases hb' with hbA | hbB
      · exact hnc a ha b hbA
      · exact hnocross a (hU ha) b hbB
    · obtain ⟨U, hU, hDU, hUne, hUconn, hnc⟩ :=
        ih B.card hltB B D rfl hDB hDne hDconn
      refine ⟨U, hU.trans hBsub, hDU, hUne, hUconn, ?_⟩
      intro a ha b hb
      have hbK : b ∈ (A ∪ B) \ U := by simpa [hEq] using hb
      have hnocrossBA : ∀ b ∈ B, ∀ a ∈ A, ¬ G.Adj b a :=
        fun b hb a ha hab => hnocross a ha b hb hab.symm
      have hb' : b ∈ B \ U ∨ b ∈ A := by
        have : b ∈ A ∪ B := (mem_sdiff.1 hbK).1
        rcases mem_union.1 this with hA | hB
        · exact Or.inr hA
        · exact Or.inl (mem_sdiff.2 ⟨hB, (mem_sdiff.1 hbK).2⟩)
      rcases hb' with hbB | hbA
      · exact hnc a ha b hbB
      · exact hnocrossBA a (hU ha) b hbA

/-- Retained old `U0` cycle seams on a protected path starting in `Y`.
The path support need not equal the cycle support; extra `D`–`U0` edges
are not counted. -/
lemma three_le_retained_cycle_seams {H A U0 Y : Finset V}
    (c : GraphCycle G) (hc : c.support = H)
    (hA : A ⊆ H) (hU0 : U0 ⊆ H \ A) (hY : Y ⊆ U0)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    (hdisjAY : Disjoint A Y)
    {p : GraphPath G}
    (hAH : A ⊆ p.support)
    (hP : p.ProtectedAt c A)
    (hsY : p.start ∈ Y)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    (h2p : 2 ≤ p.support.card) :
    3 ≤ (c.boundaryEdges U0 ∩ p.edges).card := by
  let S := c.boundaryEdges U0
  change 4 ≤ S.card at h4
  have hmiss : (S \ p.edges).card ≤ 1 := by
    by_cases hfA : p.finish ∈ A
    · have hfC : p.finish ∈ c.support := by simpa [hc] using hA hfA
      have h2c : (c.incidentEdges p.finish).card = 2 := c.incidentEdges_card hfC
      have h1p : (p.incidentEdges p.finish).card = 1 :=
        p.incidentEdges_card_finish h2p
      have hsubI : p.incidentEdges p.finish ⊆ c.incidentEdges p.finish :=
        hP.incidentEdges_subset_cycle hfA
      have hmissF :
          (c.incidentEdges p.finish \ p.incidentEdges p.finish).card ≤ 1 := by
        have : (p.incidentEdges p.finish ∪
            (c.incidentEdges p.finish \ p.incidentEdges p.finish)).card =
            (c.incidentEdges p.finish).card := by
          rw [union_sdiff_of_subset hsubI]
        have hdisj :
            Disjoint (p.incidentEdges p.finish)
              (c.incidentEdges p.finish \ p.incidentEdges p.finish) :=
          disjoint_sdiff
        have := card_union_of_disjoint hdisj
        omega
      have hsubMiss : S \ p.edges ⊆
          c.incidentEdges p.finish \ p.incidentEdges p.finish := by
        intro e he
        have ⟨heS, hneP⟩ := mem_sdiff.1 he
        obtain ⟨a, haA, hae⟩ :=
          boundary_outside_end_mem_A (c := c) hc hU0 hnocross heS
        have haP : a ∈ p.support := hAH haA
        have haC : a ∈ c.support := by simpa [hc] using hA haA
        have hsA : a ≠ p.start := fun h =>
          (disjoint_left.1 hdisjAY (h ▸ haA) hsY)
        have haFin : a = p.finish := by
          by_contra hne
          have heqI :=
            incidentEdges_eq_cycle_of_internal_protected_weak p c hP
              haA haP haC hsA hne
          have heC : e ∈ c.incidentEdges a :=
            (GraphCycle.mem_incidentEdges_iff (c := c) (v := a)).2
              ⟨((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).1,
                hae⟩
          have : e ∈ p.incidentEdges a := by simpa [heqI] using heC
          exact hneP (GraphPath.mem_incidentEdges_iff.1 this).1
        have heC : e ∈ c.incidentEdges p.finish :=
          (GraphCycle.mem_incidentEdges_iff (c := c) (v := p.finish)).2
            ⟨((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).1,
              by simpa [haFin] using hae⟩
        have hnotP : e ∉ p.incidentEdges p.finish := fun hin =>
          hneP (GraphPath.mem_incidentEdges_iff.1 hin).1
        exact mem_sdiff.2 ⟨heC, hnotP⟩
      exact (card_le_card hsubMiss).trans hmissF
    · have hnone : S \ p.edges = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        obtain ⟨heS, hneP⟩ := Finset.mem_sdiff.1 he
        obtain ⟨a, haA, hae⟩ :=
          boundary_outside_end_mem_A (c := c) hc hU0 hnocross heS
        have haP : a ∈ p.support := hAH haA
        have haC : a ∈ c.support := by simpa [hc] using hA haA
        have hsA : a ≠ p.start := fun h =>
          (disjoint_left.1 hdisjAY (h ▸ haA) hsY)
        have hfA' : a ≠ p.finish := fun h => hfA (by simpa [h] using haA)
        have heqI :=
          incidentEdges_eq_cycle_of_internal_protected_weak p c hP
            haA haP haC hsA hfA'
        have heC : e ∈ c.incidentEdges a :=
          (GraphCycle.mem_incidentEdges_iff (c := c) (v := a)).2
            ⟨((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).1,
              hae⟩
        have : e ∈ p.incidentEdges a := by simpa [heqI] using heC
        exact hneP (GraphPath.mem_incidentEdges_iff.1 this).1
      simp [hnone]
  have hinter : 3 ≤ (S ∩ p.edges).card := by
    have hd : Disjoint (S ∩ p.edges) (S \ p.edges) := by
      apply Finset.disjoint_left.2
      intro e heI heD
      exact (Finset.mem_sdiff.1 heD).2 (Finset.mem_inter.1 heI).2
    have hdecomp : S = (S ∩ p.edges) ∪ (S \ p.edges) := by
      ext e
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hcard := congrArg Finset.card hdecomp
    rw [Finset.card_union_of_disjoint hd] at hcard
    omega
  exact hinter

/-- Weak-support three-bound: a protected `H ∪ D` path starting in `Y`
retains at least three of the four original `U0` cycle seams. The path
support need not equal the cycle support. Extra `D`–`U0` edges may make
the `U0`-path-boundary strictly larger than the retained cycle seams. -/
lemma three_le_path_boundary_weak {H A U0 Y : Finset V}
    (c : GraphCycle G) (hc : c.support = H)
    (hA : A ⊆ H) (hU0 : U0 ⊆ H \ A) (hY : Y ⊆ U0)
    (hnocross : ∀ a ∈ U0, ∀ b ∈ (H \ A) \ U0, ¬ G.Adj a b)
    (hdisjAY : Disjoint A Y)
    {p : GraphPath G}
    (hAH : A ⊆ p.support)
    (hP : p.ProtectedAt c A)
    (hsY : p.start ∈ Y)
    (h4 : 4 ≤ (c.boundaryEdges U0).card)
    (h2p : 2 ≤ p.support.card) :
    3 ≤ (p.boundaryEdges U0).card := by
  let S := c.boundaryEdges U0
  have hSsub : S ∩ p.edges ⊆ p.boundaryEdges U0 := by
    intro e he
    have ⟨heS, heP⟩ := mem_inter.1 he
    exact GraphPath.mem_boundaryEdges_iff.2
      ⟨heP, ((GraphCycle.mem_boundaryEdges_iff (c := c) (U0 := U0)).1 heS).2⟩
  have hinter :=
    three_le_retained_cycle_seams (c := c) hc hA hU0 hY hnocross hdisjAY
      hAH hP hsY h4 h2p
  exact le_trans hinter (card_le_card hSsub)

/-- Switch two leftover starts through a disjoint `D`-path. -/
lemma exists_switchThrough_leftover_starts {H A D : Finset V}
    (cH : GraphCycle G) (hcH : cH.support = H)
    (hA : A ⊆ H)
    {p : GraphPath G} (hp : p.support = H) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = cH.walk.edges.toFinset)
    {r : GraphPath G} (hr : r.support = D) (hdisj : Disjoint H D)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.start ≠ R.start)
    (hsu : G.Adj Q.start r.start) (hfv : G.Adj r.finish R.start) :
    ∃ q : GraphPath G,
      q.support = H ∪ D ∧ q.ProtectedAt cH A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hu : Q.start ∈ p.support := leftoverPieces_start_mem hQ
  have hne : Q.start ≠ p.start := leftoverPieces_start_ne hs hQ
  have huA : Q.start ∉ A := leftover_start_not_mem hQ
  have hvA : R.start ∉ A := leftover_start_not_mem hR
  have hvOpen : R.start ∈ (openAtStart p hu hclose hne).support := by
    rw [openAtStart_support p hu hclose hne]
    exact leftoverPieces_start_mem hR
  have hd : Disjoint r.support p.support := by
    simpa [hr, hp] using hdisj.symm
  have hrA : Disjoint r.support A := by
    refine disjoint_left.2 ?_
    intro x hxR hxA
    exact Finset.disjoint_left.1 hdisj (hA hxA) (by simpa [hr] using hxR)
  let q := switchOpenStartsThrough p r hu hclose hne hvOpen hneQR.symm hd hsu hfv
  have hqU : q.support = H ∪ D := by
    simpa [q, hp, hr] using
      switchOpenStartsThrough_support p r hu hclose hne hvOpen hneQR.symm hd hsu hfv
  refine ⟨q, hqU, ?_, ?_, ?_, ?_⟩
  · exact switchOpenStartsThrough_ProtectedAt p r hu hclose hne hvOpen
      hneQR.symm hd hsu hfv huA hvA hrA hedges
  · have hst := switchOpenStartsThrough_start p r hu hclose hne hvOpen
      hneQR.symm hd hsu hfv
    have hpred := leftoverPred_openAtStart_predecessor_mem hs hQ hR hclose hneQR
    simpa [q, hst] using hpred
  · have hfin := switchOpenStartsThrough_finish p r hu hclose hne hvOpen
      hneQR.symm hd hsu hfv
    have hpred := leftoverPred_start_predecessor_mem hs hQ
    simpa [q, hfin] using hpred
  · intro hst
    have hnil : q.walk.Nil := (nil_iff_start_eq_finish q).2 hst
    have hsing : q.support = {q.start} := support_eq_singleton_of_nil q hnil
    have hcard : q.support.card = 1 := by simp [hsing]
    have h3 : 3 ≤ H.card := by simpa [hcH] using cH.three_le_card_support
    have : 3 ≤ q.support.card := by
      have : H ⊆ q.support := by
        intro x hx
        simpa [hqU] using mem_union.2 (Or.inl hx)
      exact h3.trans (card_le_card this)
    omega

/-- Switch a disjoint `D`-path through two prescribed OLD vertices of the
opened `H`-path, given that both incoming predecessors already lie in `A`.
The resulting path has NEW support `H ∪ D` and remains `ProtectedAt` the
OLD cycle. -/
lemma exists_switchThrough_of_preds {H A D : Finset V}
    (cH : GraphCycle G) (hcH : cH.support = H) (hA : A ⊆ H)
    {p : GraphPath G} (hp : p.support = H)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = cH.walk.edges.toFinset)
    {r : GraphPath G} (hr : r.support = D) (hdisj : Disjoint H D)
    {u v : V} (hu : u ∈ p.support) (hne : u ≠ p.start)
    (hv : v ∈ p.support) (hneuv : u ≠ v)
    (hsu : G.Adj u r.start) (hfv : G.Adj r.finish v)
    (huA : u ∉ A) (hvA : v ∉ A)
    (hfinA : (p.takeUntil hu).walk.penultimate ∈ A)
    (hstartA :
      ((openAtStart p hu hclose hne).takeUntil
        (by rw [openAtStart_support p hu hclose hne]; exact hv)).walk.penultimate ∈
          A) :
    ∃ q : GraphPath G,
      q.support = H ∪ D ∧ q.ProtectedAt cH A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hvOpen : v ∈ (openAtStart p hu hclose hne).support := by
    rw [openAtStart_support p hu hclose hne]; exact hv
  have hd : Disjoint r.support p.support := by
    simpa [hr, hp] using hdisj.symm
  have hrA : Disjoint r.support A := by
    refine disjoint_left.2 ?_
    intro x hxR hxA
    exact Finset.disjoint_left.1 hdisj (hA hxA) (by simpa [hr] using hxR)
  let q := switchOpenStartsThrough p r hu hclose hne hvOpen hneuv.symm hd hsu hfv
  have hqU : q.support = H ∪ D := by
    simpa [q, hp, hr] using
      switchOpenStartsThrough_support p r hu hclose hne hvOpen hneuv.symm hd hsu hfv
  refine ⟨q, hqU, ?_, ?_, ?_, ?_⟩
  · exact switchOpenStartsThrough_ProtectedAt p r hu hclose hne hvOpen
      hneuv.symm hd hsu hfv huA hvA hrA hedges
  · have hst := switchOpenStartsThrough_start p r hu hclose hne hvOpen
      hneuv.symm hd hsu hfv
    simpa [q, hst] using hstartA
  · have hfin := switchOpenStartsThrough_finish p r hu hclose hne hvOpen
      hneuv.symm hd hsu hfv
    simpa [q, hfin] using hfinA
  · intro hst
    have hnil : q.walk.Nil := (nil_iff_start_eq_finish q).2 hst
    have hsing : q.support = {q.start} := support_eq_singleton_of_nil q hnil
    have hcard : q.support.card = 1 := by simp [hsing]
    have h3 : 3 ≤ H.card := by simpa [hcH] using cH.three_le_card_support
    have : 3 ≤ q.support.card := by
      have : H ⊆ q.support := by
        intro x hx
        simpa [hqU] using mem_union.2 (Or.inl hx)
      exact h3.trans (card_le_card this)
    omega

/-- Dual of `exists_switchThrough_leftover_starts` at leftover finishes,
obtained by reversing the opened OLD path. -/
lemma exists_switchThrough_leftover_finishes_of_ne_finish {H A D : Finset V}
    (cH : GraphCycle G) (hcH : cH.support = H) (hA : A ⊆ H)
    {p : GraphPath G} (hp : p.support = H) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = cH.walk.edges.toFinset)
    {r : GraphPath G} (hr : r.support = D) (hdisj : Disjoint H D)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.finish ≠ R.finish) (hneFin : Q.finish ≠ p.finish)
    (hsu : G.Adj Q.finish r.start) (hfv : G.Adj r.finish R.finish) :
    ∃ q : GraphPath G,
      q.support = H ∪ D ∧ q.ProtectedAt cH A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  let pr := GraphPath.reverse p
  have hpR : pr.support = H := by
    simpa [pr, GraphPath.support_reverse] using hp
  have hcloseR : G.Adj pr.finish pr.start := by
    change G.Adj p.start p.finish
    exact hclose.symm
  have hedgesR : pr.edges ∪ {s(pr.finish, pr.start)} = cH.walk.edges.toFinset := by
    rw [leftoverPred_reverse_edges p]
    change p.edges ∪ {s(p.start, p.finish)} = _
    rw [show s(p.start, p.finish) = s(p.finish, p.start) from Sym2.eq_swap]
    exact hedges
  have hu : Q.finish ∈ pr.support := by
    simpa [pr, GraphPath.support_reverse] using leftoverPieces_finish_mem hQ
  have hv : R.finish ∈ pr.support := by
    simpa [pr, GraphPath.support_reverse] using leftoverPieces_finish_mem hR
  have hne : Q.finish ≠ pr.start := by
    change Q.finish ≠ p.finish
    exact hneFin
  have huA : Q.finish ∉ A := leftover_finish_not_mem hQ
  have hvA : R.finish ∉ A := leftover_finish_not_mem hR
  have hfinA : (pr.takeUntil hu).walk.penultimate ∈ A := by
    simpa [pr] using leftoverPred_reverse_finish_predecessor_mem hQ hneFin
  have hstartA :
      ((openAtStart pr hu hcloseR hne).takeUntil
        (by rw [openAtStart_support pr hu hcloseR hne]; exact hv)).walk.penultimate ∈
          A :=
    leftoverPred_openAtStart_predecessor_mem_of_pred (A := A) pr hu hv
      hcloseR hne hneQR
      (fun hvs =>
        leftoverPred_reverse_finish_predecessor_mem hR
          (show R.finish ≠ p.finish from hvs))
      (fun _ => by
        change p.start ∈ A
        exact hs)
  exact exists_switchThrough_of_preds (cH := cH) hcH hA hpR hcloseR hedgesR
    hr hdisj hu hne hv hneQR hsu hfv huA hvA hfinA hstartA

lemma exists_switchThrough_leftover_finishes {H A D : Finset V}
    (cH : GraphCycle G) (hcH : cH.support = H) (hA : A ⊆ H)
    {p : GraphPath G} (hp : p.support = H) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = cH.walk.edges.toFinset)
    {r : GraphPath G} (hr : r.support = D) (hdisj : Disjoint H D)
    {Q R : GraphPath G}
    (hQ : Q ∈ leftoverPieces A p) (hR : R ∈ leftoverPieces A p)
    (hneQR : Q.finish ≠ R.finish)
    (hsu : G.Adj Q.finish r.start) (hfv : G.Adj r.finish R.finish) :
    ∃ q : GraphPath G,
      q.support = H ∪ D ∧ q.ProtectedAt cH A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  by_cases hneFin : Q.finish = p.finish
  · have hRfin : R.finish ≠ p.finish := fun h =>
      hneQR (hneFin.trans h.symm)
    let r' := GraphPath.reverse r
    have hr' : r'.support = D := by
      simpa [r', GraphPath.support_reverse] using hr
    have hsu' : G.Adj R.finish r'.start := by
      change G.Adj R.finish r.finish
      exact hfv.symm
    have hfv' : G.Adj r'.finish Q.finish := by
      change G.Adj r.start Q.finish
      exact hsu.symm
    exact exists_switchThrough_leftover_finishes_of_ne_finish (cH := cH) hcH hA
      hp hs hclose hedges hr' hdisj hR hQ hneQR.symm hRfin hsu' hfv'
  · exact exists_switchThrough_leftover_finishes_of_ne_finish (cH := cH) hcH hA
      hp hs hclose hedges hr hdisj hQ hR hneQR hneFin hsu hfv

/-- Restriction of a saturated leftover cover to one OLD run: an eligible
vertex of `H \ A` that lands on that run is locally eligible there. -/
lemma eligible_on_leftover_of_eligible_K0 {H A : Finset V}
    (hK0 : Nikoghosyan.IsCograph G (H \ A))
    {p : GraphPath G} (hp : p.support = H)
    {pc : PathCover G (H \ A)}
    (hmin : pc.card = pathCoverNumber G (H \ A))
    (hpaths : pc.paths = leftoverPieces A p)
    {Q : GraphPath G} (hQ : Q ∈ leftoverPieces A p)
    {u : V} (huE : u ∈ eligibleSet G (H \ A)) (huQ : u ∈ Q.support) :
    Eligible G Q.support u := by
  let P : GraphPath G → Bool := fun q => decide (q.start = Q.start)
  have hPtrue : P Q = true := by simp [P]
  have hfilter : pc.paths.filter P = [Q] := by
    rw [hpaths]
    have hx : Q ∈ (leftoverPieces A p).filter P :=
      List.mem_filter.2 ⟨hQ, hPtrue⟩
    have huniq : ∀ R ∈ (leftoverPieces A p).filter P, R = Q := by
      intro R hR
      obtain ⟨hRmem, hPR⟩ := List.mem_filter.1 hR
      have hst : R.start = Q.start := of_decide_eq_true (by simpa [P] using hPR)
      by_cases hne : R = Q
      · exact hne
      · have hd : Disjoint R.support Q.support :=
          PathCover.pairwise_disjoint_of_mem
            (leftoverPieces_pairwise (B := A) p) hRmem hQ hne
        exact (Finset.disjoint_left.1 hd R.start_mem_support
          (by simpa [hst] using Q.start_mem_support)).elim
    have hnodF : ((leftoverPieces A p).filter P).Nodup :=
      (leftoverPieces_nodup (B := A) p).filter _
    match hf : (leftoverPieces A p).filter P with
    | [] =>
      have : Q ∈ ([] : List (GraphPath G)) := by simpa [hf] using hx
      cases this
    | [z] =>
      have : z = Q := huniq z (by simp [hf])
      simpa [hf, this]
    | z :: w :: rest =>
      have hz : z = Q := huniq z (by simp [hf])
      have hw : w = Q := huniq w (by simp [hf])
      have hnod' : (z :: w :: rest).Nodup := by simpa [hf] using hnodF
      have hzw : z = w := hz.trans hw.symm
      exact False.elim ((List.nodup_cons.1 hnod').1 (by simp [hzw]))
  have hunion : supportUnion (pc.paths.filter P) = Q.support := by
    rw [hfilter]
    simp [supportUnion]
  have hrest :=
    restriction_eq_of_min_cover_of_canonical (U := H \ A) hK0 pc hmin P
  have huL : u ∈ eligibleSet G (supportUnion (pc.paths.filter P)) := by
    have : u ∈ eligibleSet G (H \ A) ∩ supportUnion (pc.paths.filter P) :=
      mem_inter.2 ⟨huE, by
        rw [hunion]; exact huQ⟩
    simpa [hrest.2.1] using this
  have hEl : Eligible G (supportUnion (pc.paths.filter P)) u :=
    ((mem_eligibleSet_iff (G := G)).1 huL).2
  simpa [hunion] using hEl

/-- Reroute one OLD leftover run so a locally eligible vertex becomes the
start of a spanning `H`-path. Protection retains only original `A`-incidence
of `cH`; the unused leftover seam is dropped. NEW `D` is not yet inserted. -/
lemma exists_spanning_H_from_eligible_leftover {H A : Finset V}
    (cH : GraphCycle G) (hcH : cH.support = H)
    {p : GraphPath G} (hp : p.support = H) (hs : p.start ∈ A)
    (hclose : G.Adj p.finish p.start)
    (hedges : p.edges ∪ {s(p.finish, p.start)} = cH.walk.edges.toFinset)
    {Q : GraphPath G} (hQ : Q ∈ leftoverPieces A p)
    {u : V} (huQ : u ∈ Q.support)
    (h2Q : 2 ≤ Q.support.card)
    (hcog : IsCograph G Q.support)
    (huE : Eligible G Q.support u) :
    ∃ p0 : GraphPath G,
      p0.support = H ∧ p0.start = u ∧ p0.finish ∈ A ∧ p0.ProtectedAt cH A := by
  obtain ⟨rC, hrC, hrs, hrf, hadjS, hadjF, hsubE, hseamS, hseamF⟩ :=
    exists_complement_of_leftover_edges (A := A) hs hQ hclose
  have hQsub : Q.support ⊆ p.support := leftoverPieces_support_subset p Q hQ
  have hdisjQC : Disjoint Q.support rC.support := by
    rw [hrC]
    exact disjoint_left.2 fun x hxQ hxR => (mem_sdiff.1 hxR).2 hxQ
  have hQA : Disjoint Q.support A := leftoverPieces_disjoint_B p Q hQ
  rcases exists_compatible_old_end (Q := Q) (b := u) h2Q hcog huE huQ with hToS | hToF
  · obtain ⟨_hne, Qi, hQi, hends⟩ := hToS
    have hnorm :
        ∃ Qi' : GraphPath G,
          Qi'.support = Q.support ∧ Qi'.start = u ∧ Qi'.finish = Q.start := by
      rcases hends with ⟨hs', hf'⟩ | ⟨hs', hf'⟩
      · exact ⟨Qi, hQi, hs', hf'⟩
      · refine ⟨GraphPath.reverse Qi,
          by simpa [GraphPath.support_reverse] using hQi, ?_, ?_⟩
        · change Qi.finish = u; exact hf'
        · change Qi.start = Q.start; exact hs'
    obtain ⟨Qi', hsup', hst', hfin'⟩ := hnorm
    have hstR : (GraphPath.reverse rC).start = rC.finish := rfl
    have hadj : G.Adj Qi'.finish (GraphPath.reverse rC).start := by
      simpa [hfin', hstR] using hadjS.symm
    have hd : Disjoint Qi'.support (GraphPath.reverse rC).support := by
      simpa [hsup', GraphPath.support_reverse] using hdisjQC
    let p0 := Qi'.splice (GraphPath.reverse rC) hadj hd
    have hQsubH : Q.support ⊆ H := by simpa [hp] using hQsub
    have hsup0 : p0.support = H := by
      rw [GraphPath.support_splice, hsup', GraphPath.support_reverse, hrC, hp]
      exact union_sdiff_of_subset hQsubH
    refine ⟨p0, hsup0, ?_, ?_, ?_⟩
    · change Qi'.start = u; exact hst'
    · change (GraphPath.reverse rC).finish ∈ A
      change rC.start ∈ A
      exact hrs
    · intro e he
      obtain ⟨heE, b, hbA, hbe⟩ := mem_AIncident_iff.1 he
      have hse :
          p0.edges =
            Qi'.edges ∪ (GraphPath.reverse rC).edges ∪
              {s(Qi'.finish, (GraphPath.reverse rC).start)} :=
        edges_splice Qi' (GraphPath.reverse rC) hadj hd
      have heE' : e ∈
          Qi'.edges ∪ (GraphPath.reverse rC).edges ∪
            {s(Qi'.finish, (GraphPath.reverse rC).start)} := by
        rwa [hse] at heE
      rcases mem_union.1 heE' with h | hseam
      · rcases mem_union.1 h with hQiE | hrE
        · have hempty : Qi'.AIncident A = ∅ :=
            AIncident_eq_empty_of_disjoint_support Qi' (by simpa [hsup'] using hQA)
          exact (notMem_empty e (by
            have : e ∈ Qi'.AIncident A := mem_AIncident_iff.2 ⟨hQiE, ⟨b, hbA, hbe⟩⟩
            simpa [hempty] using this)).elim
        · have hrE' : e ∈ rC.edges := by
            simpa [GraphPath.edges_reverse] using hrE
          simpa [hedges] using hsubE hrE'
      · have heq : e = s(Q.start, rC.finish) := by
          have := mem_singleton.1 hseam
          simpa [hfin', hstR] using this
        have : e ∈ p.edges ∪ {s(p.finish, p.start)} := by
          simpa [heq, Sym2.eq_swap] using hseamS
        simpa [hedges] using this
  · obtain ⟨_hne, Qi, hQi, hends⟩ := hToF
    have hnorm :
        ∃ Qi' : GraphPath G,
          Qi'.support = Q.support ∧ Qi'.start = u ∧ Qi'.finish = Q.finish := by
      rcases hends with ⟨hs', hf'⟩ | ⟨hs', hf'⟩
      · exact ⟨Qi, hQi, hs', hf'⟩
      · refine ⟨GraphPath.reverse Qi,
          by simpa [GraphPath.support_reverse] using hQi, ?_, ?_⟩
        · change Qi.finish = u; exact hf'
        · change Qi.start = Q.finish; exact hs'
    obtain ⟨Qi', hsup', hst', hfin'⟩ := hnorm
    have hadj : G.Adj Qi'.finish rC.start := by simpa [hfin'] using hadjF
    have hd : Disjoint Qi'.support rC.support := by simpa [hsup'] using hdisjQC
    let p0 := Qi'.splice rC hadj hd
    have hQsubH : Q.support ⊆ H := by simpa [hp] using hQsub
    have hsup0 : p0.support = H := by
      rw [GraphPath.support_splice, hsup', hrC, hp]
      exact union_sdiff_of_subset hQsubH
    refine ⟨p0, hsup0, ?_, ?_, ?_⟩
    · change Qi'.start = u; exact hst'
    · change rC.finish ∈ A; exact hrf
    · intro e he
      obtain ⟨heE, b, hbA, hbe⟩ := mem_AIncident_iff.1 he
      have hse : p0.edges = Qi'.edges ∪ rC.edges ∪ {s(Qi'.finish, rC.start)} :=
        edges_splice Qi' rC hadj hd
      have heE' : e ∈ Qi'.edges ∪ rC.edges ∪ {s(Qi'.finish, rC.start)} := by
        rwa [hse] at heE
      rcases mem_union.1 heE' with h | hseam
      · rcases mem_union.1 h with hQiE | hrE
        · have hempty : Qi'.AIncident A = ∅ :=
            AIncident_eq_empty_of_disjoint_support Qi' (by simpa [hsup'] using hQA)
          exact (notMem_empty e (by
            have : e ∈ Qi'.AIncident A := mem_AIncident_iff.2 ⟨hQiE, ⟨b, hbA, hbe⟩⟩
            simpa [hempty] using this)).elim
        · simpa [hedges] using hsubE hrE
      · have heq : e = s(Q.finish, rC.start) := by
          have := mem_singleton.1 hseam
          simpa [hfin'] using this
        have : e ∈ p.edges ∪ {s(p.finish, p.start)} := by
          simpa [heq] using hseamF
        simpa [hedges] using this

lemma disjoint_trimFinish_takeUntil_dropUntil (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hne : x ≠ p.start) :
    Disjoint
      ((p.takeUntil hx).trimFinish (takeUntil_not_nil_cyclePieces hx hne)).support
      (p.dropUntil hx).support := by
  have hnn := takeUntil_not_nil_cyclePieces hx hne
  have hU := support_takeUntil_union_dropUntil p hx
  have hlen := takeUntil_dropUntil_length_add p hx
  have hcardT := GraphPath.card_support (p.takeUntil hx)
  have hcardD := GraphPath.card_support (p.dropUntil hx)
  have hcardP := GraphPath.card_support p
  have hsum :
      (p.takeUntil hx).support.card + (p.dropUntil hx).support.card =
        p.support.card + 1 := by omega
  have hinter :
      ((p.takeUntil hx).support ∩ (p.dropUntil hx).support).card = 1 := by
    have hcu :=
      card_union_add_card_inter (p.takeUntil hx).support (p.dropUntil hx).support
    have : ((p.takeUntil hx).support ∪ (p.dropUntil hx).support).card =
        p.support.card := by simp [hU]
    omega
  have hxI : x ∈ (p.takeUntil hx).support ∩ (p.dropUntil hx).support :=
    mem_inter.2 ⟨by
        have : (p.takeUntil hx).finish = x := rfl
        simpa [this] using (p.takeUntil hx).finish_mem_support,
      by
        have : (p.dropUntil hx).start = x := rfl
        simpa [this] using (p.dropUntil hx).start_mem_support⟩
  have hinters :
      (p.takeUntil hx).support ∩ (p.dropUntil hx).support = {x} := by
    obtain ⟨w, hw⟩ := card_eq_one.1 hinter
    have : x = w := mem_singleton.1 (by simpa [hw] using hxI)
    simpa [this] using hw
  rw [support_trimFinish (p.takeUntil hx) hnn]
  have hfin : (p.takeUntil hx).finish = x := rfl
  refine disjoint_left.2 ?_
  intro z hz hzD
  have hz' : z ∈ (p.takeUntil hx).support.erase x := by simpa [hfin] using hz
  obtain ⟨hzne, hzT⟩ := mem_erase.1 hz'
  have : z ∈ (p.takeUntil hx).support ∩ (p.dropUntil hx).support :=
    mem_inter.2 ⟨hzT, hzD⟩
  exact hzne (by simpa [hinters] using this)

/-- Insert a disjoint NEW `D`-path across an OLD `A`–`x` dart of an
`H`-path that already starts at an exposed non-`A` vertex. The result
has NEW support `H ∪ D` and both ends in `A`. -/
lemma exists_insert_D_across_A_dart {H A D : Finset V}
    (cH : GraphCycle G) (_hcH : cH.support = H) (hA : A ⊆ H)
    {p0 r : GraphPath G} {a x : V}
    (hp0 : p0.support = H) (huA : p0.start ∉ A) (hfA : p0.finish ∈ A)
    (hP : p0.ProtectedAt cH A)
    (hr : r.support = D) (hdisj : Disjoint H D)
    (hsu : G.Adj p0.start r.start) (hfv : G.Adj r.finish x)
    (haA : a ∈ A) (hx : x ∈ p0.support) (hxA : x ∉ A)
    (hneux : x ≠ p0.start)
    (hpen : (p0.takeUntil hx).walk.penultimate = a) :
    ∃ q : GraphPath G,
      q.support = H ∪ D ∧ q.ProtectedAt cH A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  have hxneS : x ≠ p0.start := hneux
  have hnn := takeUntil_not_nil_cyclePieces hx hxneS
  let pre := (p0.takeUntil hx).trimFinish hnn
  have hpreSt : pre.start = p0.start := trimFinish_start (p0.takeUntil hx) hnn
  have hpreFin : pre.finish = a := hpen
  have hdPR : Disjoint pre.support r.support := by
    rw [hr]
    refine disjoint_left.2 ?_
    intro z hzP hzD
    have hzH : z ∈ H := by
      have hzT : z ∈ (p0.takeUntil hx).support := by
        have := support_trimFinish (p0.takeUntil hx) hnn
        have hfin : (p0.takeUntil hx).finish = x := rfl
        have : z ∈ (p0.takeUntil hx).support.erase x := by
          simpa [this, hfin, pre] using hzP
        exact (mem_erase.1 this).2
      have : z ∈ p0.support := leftoverPred_takeUntil_support_subset p0 hx hzT
      simpa [hp0] using this
    exact Finset.disjoint_left.1 hdisj hzH hzD
  have hrA : Disjoint r.support A :=
    disjoint_left.2 fun z hzR hzA =>
      Finset.disjoint_left.1 hdisj (hA hzA) (by simpa [hr] using hzR)
  have huD : p0.start ∉ r.support := by
    intro h
    have : p0.start ∈ H := by simpa [hp0] using p0.start_mem_support
    exact Finset.disjoint_left.1 hdisj this (by simpa [hr] using h)
  have hxD : x ∉ r.support := by
    intro h
    have : x ∈ H := by simpa [hp0] using hx
    exact Finset.disjoint_left.1 hdisj this (by simpa [hr] using h)
  have hrstartA : r.start ∉ A := disjoint_left.1 hrA r.start_mem_support
  have hrfinA : r.finish ∉ A := disjoint_left.1 hrA r.finish_mem_support
  have hadjUR : G.Adj pre.reverse.finish r.start := by
    have : pre.reverse.finish = pre.start := rfl
    simpa [this, hpreSt] using hsu
  have hdRev : Disjoint pre.reverse.support r.support := by
    simpa [GraphPath.support_reverse] using hdPR
  let q1 := pre.reverse.splice r hadjUR hdRev
  have hdisjSuf : Disjoint q1.support (p0.dropUntil hx).support := by
    rw [GraphPath.support_splice, GraphPath.support_reverse]
    refine disjoint_union_left.2 ⟨?_, ?_⟩
    · simpa [pre] using
        disjoint_trimFinish_takeUntil_dropUntil p0 hx hxneS
    · refine disjoint_left.2 ?_
      intro z hzR hzS
      have hzH : z ∈ H := by
        have hU := support_takeUntil_union_dropUntil p0 hx
        have : z ∈ (p0.takeUntil hx).support ∪ (p0.dropUntil hx).support :=
          mem_union.2 (Or.inr hzS)
        have : z ∈ p0.support := by simpa [hU] using this
        simpa [hp0] using this
      exact Finset.disjoint_left.1 hdisj hzH (by simpa [hr] using hzR)
  have hadjXS : G.Adj q1.finish (p0.dropUntil hx).start := by
    change G.Adj r.finish x
    exact hfv
  let q := q1.splice (p0.dropUntil hx) hadjXS hdisjSuf
  have hqU : q.support = H ∪ D := by
    rw [GraphPath.support_splice, GraphPath.support_splice, GraphPath.support_reverse]
    have hU :=
      support_trimFinish_takeUntil_union_dropUntil p0 hx hxneS
    have hassoc : pre.support ∪ r.support ∪ (p0.dropUntil hx).support =
        (pre.support ∪ (p0.dropUntil hx).support) ∪ r.support := by
      ac_rfl
    rw [hassoc]
    have hHD : pre.support ∪ (p0.dropUntil hx).support = H := by
      simpa [pre, hp0] using hU
    rw [hHD, hr]
  refine ⟨q, hqU, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨heE, b, hbA, hbe⟩ := mem_AIncident_iff.1 he
    have hse :
        q.edges = q1.edges ∪ (p0.dropUntil hx).edges ∪
          {s(q1.finish, (p0.dropUntil hx).start)} :=
      edges_splice q1 (p0.dropUntil hx) hadjXS hdisjSuf
    have heE' : e ∈ q1.edges ∪ (p0.dropUntil hx).edges ∪
        {s(q1.finish, (p0.dropUntil hx).start)} := by
      rwa [hse] at heE
    have hse1 :
        q1.edges = pre.reverse.edges ∪ r.edges ∪
          {s(pre.reverse.finish, r.start)} :=
      edges_splice pre.reverse r hadjUR hdRev
    rcases mem_union.1 heE' with h | hseam
    · rcases mem_union.1 h with hq1E | hD
      · have hq1E' : e ∈ pre.reverse.edges ∪ r.edges ∪
            {s(pre.reverse.finish, r.start)} := by
          rwa [hse1] at hq1E
        rcases mem_union.1 hq1E' with h' | hseam1
        · rcases mem_union.1 h' with hpreE | hrE
          · have hpreE' : e ∈ pre.edges := by
              simpa [GraphPath.edges_reverse] using hpreE
            have hsub : pre.edges ⊆ p0.edges :=
              (edges_trimFinish_subset (p0.takeUntil hx) hnn).trans
                (edges_takeUntil_subset p0 hx)
            exact hP (mem_AIncident_iff.2 ⟨hsub hpreE', ⟨b, hbA, hbe⟩⟩)
          · have : e ∈ r.AIncident A := mem_AIncident_iff.2 ⟨hrE, ⟨b, hbA, hbe⟩⟩
            have hempty : r.AIncident A = ∅ :=
              AIncident_eq_empty_of_disjoint_support r hrA
            exact (notMem_empty e (by simpa [hempty] using this)).elim
        · have heq : e = s(p0.start, r.start) := by
            have h1 := mem_singleton.1 hseam1
            have h2 : pre.reverse.finish = pre.start := rfl
            simpa [h2, hpreSt] using h1
          rcases (show ∃ t, t ∈ e ∧ t ∈ A from ⟨b, hbe, hbA⟩) with ⟨t, hte, htA⟩
          have htends : t = p0.start ∨ t = r.start := by
            have : t ∈ s(p0.start, r.start) := by simpa [heq] using hte
            exact Sym2.mem_iff.1 this
          rcases htends with ht | ht
          · exact (huA (ht ▸ htA)).elim
          · exact (hrstartA (ht ▸ htA)).elim
      · have hsub : (p0.dropUntil hx).edges ⊆ p0.edges :=
          edges_dropUntil_subset p0 hx
        exact hP (mem_AIncident_iff.2 ⟨hsub hD, ⟨b, hbA, hbe⟩⟩)
    · have heq : e = s(r.finish, x) := by
        have h1 := mem_singleton.1 hseam
        have h2 : q1.finish = r.finish := rfl
        have h3 : (p0.dropUntil hx).start = x := rfl
        simpa [h2, h3] using h1
      rcases (show ∃ t, t ∈ e ∧ t ∈ A from ⟨b, hbe, hbA⟩) with ⟨t, hte, htA⟩
      have htends : t = r.finish ∨ t = x := by
        have : t ∈ s(r.finish, x) := by simpa [heq] using hte
        exact Sym2.mem_iff.1 this
      rcases htends with ht | ht
      · exact (hrfinA (ht ▸ htA)).elim
      · exact (hxA (ht ▸ htA)).elim
  · have hstq : q.start = a := by
      change pre.reverse.start = a
      change pre.finish = a
      exact hpreFin
    simpa [hstq] using haA
  · have hfinq : q.finish = p0.finish := rfl
    simpa [hfinq] using hfA
  · intro hst
    have hnil : q.walk.Nil := (nil_iff_start_eq_finish q).2 hst
    have hsing : q.support = {q.start} := support_eq_singleton_of_nil q hnil
    have hcard : q.support.card = 1 := by simp [hsing]
    have h2 : 2 ≤ H.card := by
      have hne : p0.start ≠ p0.finish := fun h => huA (h ▸ hfA)
      have hnnP : ¬ p0.walk.Nil := fun hn =>
        hne ((nil_iff_start_eq_finish p0).1 hn)
      have hpos : 0 < p0.walk.length := Nat.pos_of_ne_zero fun h0 =>
        hnnP (Walk.length_eq_zero_iff.1 h0)
      have hcardp := GraphPath.card_support p0
      have : 2 ≤ p0.support.card := by omega
      simpa [hp0] using this
    have : 2 ≤ q.support.card := by
      have : H ⊆ q.support := by
        intro z hz
        simpa [hqU] using mem_union.2 (Or.inl hz)
      exact h2.trans (card_le_card this)
    omega

/-- Insert a disjoint NEW `D`-path across an actual `PrefixEdgeFactor`
dart `a → x` of an `H`-path that already starts at an exposed non-`A`
vertex. The construction is `pre.reverse.splice r.splice suf`; no
`takeUntil` penultimate identity is required. -/
lemma exists_insert_D_across_factor {H A D : Finset V}
    (cH : GraphCycle G) (_hcH : cH.support = H) (hA : A ⊆ H)
    {p0 r : GraphPath G} {a x : V}
    (hp0 : p0.support = H) (huA : p0.start ∉ A) (hfA : p0.finish ∈ A)
    (hP : p0.ProtectedAt cH A)
    (hr : r.support = D) (hdisj : Disjoint H D)
    (hsu : G.Adj p0.start r.start) (hfv : G.Adj r.finish x)
    (F : PrefixEdgeFactor p0 a x)
    (haA : a ∈ A) (hxA : x ∉ A) :
    ∃ q : GraphPath G,
      q.support = H ∪ D ∧ q.ProtectedAt cH A ∧
        q.start ∈ A ∧ q.finish ∈ A ∧ q.start ≠ q.finish := by
  let pre := F.prefixPath
  let suf := F.suffixPath
  have hpreSt : pre.start = p0.start := rfl
  have hpreFin : pre.finish = a := rfl
  have hsufSt : suf.start = x := rfl
  have haPre : a ≠ p0.start := fun h => huA (h ▸ haA)
  have hpreNN : ¬ pre.walk.Nil := fun hn =>
    haPre ((nil_iff_start_eq_finish pre).1 hn).symm
  have hdPR : Disjoint pre.support r.support := by
    rw [hr]
    refine disjoint_left.2 ?_
    intro z hzP hzD
    have hzH : z ∈ H := by
      have hU := F.support_eq_union
      have hzPS : z ∈ F.prefixPath.support ∪ F.suffixPath.support :=
        mem_union.2 (Or.inl (by simpa [pre] using hzP))
      have hzP0 : z ∈ p0.support := by rwa [hU]
      rwa [hp0] at hzP0
    exact Finset.disjoint_left.1 hdisj hzH hzD
  have hrA : Disjoint r.support A :=
    disjoint_left.2 fun z hzR hzA =>
      Finset.disjoint_left.1 hdisj (hA hzA) (by simpa [hr] using hzR)
  have hrstartA : r.start ∉ A := disjoint_left.1 hrA r.start_mem_support
  have hrfinA : r.finish ∉ A := disjoint_left.1 hrA r.finish_mem_support
  have hadjUR : G.Adj pre.reverse.finish r.start := by
    have : pre.reverse.finish = pre.start := rfl
    simpa [this, hpreSt] using hsu
  have hdRev : Disjoint pre.reverse.support r.support := by
    simpa [GraphPath.support_reverse] using hdPR
  let q1 := pre.reverse.splice r hadjUR hdRev
  have hdisjSuf : Disjoint q1.support suf.support := by
    rw [GraphPath.support_splice, GraphPath.support_reverse]
    refine disjoint_union_left.2 ⟨?_, ?_⟩
    · simpa [pre, suf] using F.disjoint_prefixPath_suffixPath
    · refine disjoint_left.2 ?_
      intro z hzR hzS
      have hzH : z ∈ H := by
        have hU := F.support_eq_union
        have hzPS : z ∈ F.prefixPath.support ∪ F.suffixPath.support :=
          mem_union.2 (Or.inr (by simpa [suf] using hzS))
        have hzP0 : z ∈ p0.support := by rwa [hU]
        rwa [hp0] at hzP0
      exact Finset.disjoint_left.1 hdisj hzH (by simpa [hr] using hzR)
  have hadjXS : G.Adj q1.finish suf.start := by
    change G.Adj r.finish x
    exact hfv
  let q := q1.splice suf hadjXS hdisjSuf
  have hqU : q.support = H ∪ D := by
    rw [GraphPath.support_splice, GraphPath.support_splice, GraphPath.support_reverse]
    have hassoc : pre.support ∪ r.support ∪ suf.support =
        (pre.support ∪ suf.support) ∪ r.support := by
      ac_rfl
    rw [hassoc, hr]
    have hHD : pre.support ∪ suf.support = H := by
      simpa [pre, suf, hp0] using F.support_eq_union.symm
    rw [hHD]
  refine ⟨q, hqU, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨heE, b, hbA, hbe⟩ := mem_AIncident_iff.1 he
    have hse :
        q.edges = q1.edges ∪ suf.edges ∪ {s(q1.finish, suf.start)} :=
      edges_splice q1 suf hadjXS hdisjSuf
    have heE' : e ∈ q1.edges ∪ suf.edges ∪ {s(q1.finish, suf.start)} := by
      rwa [hse] at heE
    have hse1 :
        q1.edges = pre.reverse.edges ∪ r.edges ∪
          {s(pre.reverse.finish, r.start)} :=
      edges_splice pre.reverse r hadjUR hdRev
    have hpreSub : pre.edges ⊆ p0.edges := by
      intro e heP
      have hdecomp := F.edges_toFinset_eq
      have heP' : e ∈ F.preWalk.edges.toFinset := by
        change e ∈ pre.walk.edges.toFinset at heP
        simpa [pre, PrefixEdgeFactor.prefixPath, GraphPath.edges] using heP
      have : e ∈ F.preWalk.edges.toFinset ∪ insert s(a, x) F.sufWalk.edges.toFinset :=
        mem_union.2 (Or.inl heP')
      simpa [hdecomp] using this
    have hsufSub : suf.edges ⊆ p0.edges := by
      intro e heS
      have hdecomp := F.edges_toFinset_eq
      have heS' : e ∈ F.sufWalk.edges.toFinset := by
        change e ∈ suf.walk.edges.toFinset at heS
        simpa [suf, PrefixEdgeFactor.suffixPath, GraphPath.edges] using heS
      have : e ∈ F.preWalk.edges.toFinset ∪ insert s(a, x) F.sufWalk.edges.toFinset :=
        mem_union.2 (Or.inr (mem_insert.2 (Or.inr heS')))
      simpa [hdecomp] using this
    rcases mem_union.1 heE' with h | hseam
    · rcases mem_union.1 h with hq1E | hS
      · have hq1E' : e ∈ pre.reverse.edges ∪ r.edges ∪
            {s(pre.reverse.finish, r.start)} := by
          rwa [hse1] at hq1E
        rcases mem_union.1 hq1E' with h' | hseam1
        · rcases mem_union.1 h' with hpreE | hrE
          · have hpreE' : e ∈ pre.edges := by
              simpa [GraphPath.edges_reverse] using hpreE
            exact hP (mem_AIncident_iff.2 ⟨hpreSub hpreE', ⟨b, hbA, hbe⟩⟩)
          · have : e ∈ r.AIncident A := mem_AIncident_iff.2 ⟨hrE, ⟨b, hbA, hbe⟩⟩
            have hempty : r.AIncident A = ∅ :=
              AIncident_eq_empty_of_disjoint_support r hrA
            exact (notMem_empty e (by simpa [hempty] using this)).elim
        · have heq : e = s(p0.start, r.start) := by
            have h1 := mem_singleton.1 hseam1
            have h2 : pre.reverse.finish = pre.start := rfl
            simpa [h2, hpreSt] using h1
          rcases (show ∃ t, t ∈ e ∧ t ∈ A from ⟨b, hbe, hbA⟩) with ⟨t, hte, htA⟩
          have htends : t = p0.start ∨ t = r.start := by
            have : t ∈ s(p0.start, r.start) := by simpa [heq] using hte
            exact Sym2.mem_iff.1 this
          rcases htends with ht | ht
          · exact (huA (ht ▸ htA)).elim
          · exact (hrstartA (ht ▸ htA)).elim
      · exact hP (mem_AIncident_iff.2 ⟨hsufSub hS, ⟨b, hbA, hbe⟩⟩)
    · have heq : e = s(r.finish, x) := by
        have h1 := mem_singleton.1 hseam
        have h2 : q1.finish = r.finish := rfl
        have h3 : suf.start = x := hsufSt
        simpa [h2, h3] using h1
      rcases (show ∃ t, t ∈ e ∧ t ∈ A from ⟨b, hbe, hbA⟩) with ⟨t, hte, htA⟩
      have htends : t = r.finish ∨ t = x := by
        have : t ∈ s(r.finish, x) := by simpa [heq] using hte
        exact Sym2.mem_iff.1 this
      rcases htends with ht | ht
      · exact (hrfinA (ht ▸ htA)).elim
      · exact (hxA (ht ▸ htA)).elim
  · have hstq : q.start = a := by
      change pre.reverse.start = a
      change pre.finish = a
      exact hpreFin
    simpa [hstq] using haA
  · have hfinq : q.finish = p0.finish := by
      change suf.finish = p0.finish
      rfl
    simpa [hfinq] using hfA
  · intro hst
    have hnil : q.walk.Nil := (nil_iff_start_eq_finish q).2 hst
    have hsing : q.support = {q.start} := support_eq_singleton_of_nil q hnil
    have hcard : q.support.card = 1 := by simp [hsing]
    have h2 : 2 ≤ H.card := by
      have hne : p0.start ≠ p0.finish := fun h => huA (h ▸ hfA)
      have hnnP : ¬ p0.walk.Nil := fun hn =>
        hne ((nil_iff_start_eq_finish p0).1 hn)
      have hpos : 0 < p0.walk.length := Nat.pos_of_ne_zero fun h0 =>
        hnnP (Walk.length_eq_zero_iff.1 h0)
      have hcardp := GraphPath.card_support p0
      have : 2 ≤ p0.support.card := by omega
      simpa [hp0] using this
    have : 2 ≤ q.support.card := by
      have : H ⊆ q.support := by
        intro z hz
        simpa [hqU] using mem_union.2 (Or.inl hz)
      exact h2.trans (card_le_card this)
    omega

end Cograph

end Nikoghosyan
