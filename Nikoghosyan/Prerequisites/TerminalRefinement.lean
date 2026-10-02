/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.Cograph.ProtectedIncidence
import Nikoghosyan.Prerequisites.TerminalAugmentation

/-!
# Fresh-vertex deletion of a supplied augmented AA-path

Given a genuine original-edge simple path `p` of the concrete augmentation
graph whose support is exactly `augCarrier K` and whose two endpoints lie
in `augA` (the old image of `B`), delete the `q` fresh vertices. The
resulting leftover runs form an actual original-edge `B`-ended path cover
of `K` of cardinality exactly `q + 1`.

This is a deletion operation on a supplied path. It does not assert that
such a path exists, and it does not use a protected-path existence
theorem, host 1-toughness, or an augmented OneTough hypothesis.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GraphPath

/-- Independence of `B` in the whole graph forbids a `B`–`B` path edge. -/
lemma NoConsecutive_of_independent {B : Finset V}
    (hInd : Independent (G := G) B) (p : GraphPath G) :
    NoConsecutive B p := by
  intro e he hb
  have hedge : e ∈ G.edgeSet := p.edges_subset_edgeSet e he
  revert hb hedge
  refine Sym2.inductionOn e ?_
  intro u v hb hedge
  have hadj : G.Adj u v := by
    simpa [SimpleGraph.mem_edgeSet] using hedge
  have ⟨hu, hv⟩ := bothEndsIn_iff.1 hb
  exact hInd hu hv hadj

/-- Exact leftover-run count when both path endpoints lie outside `B` and
no path edge is a consecutive `B`–`B` edge. The first-fresh split reduces
to the already checked start-in-`B` / finish-outside-`B` identity on the
drop; no new strong induction is used. -/
lemma leftoverPieces_length_eq_of_ends_not_mem {B : Finset V} {p : GraphPath G}
    (hs : p.start ∉ B) (hf : p.finish ∉ B) (hno : NoConsecutive B p) :
    (leftoverPieces B p).length = (p.support ∩ B).card + 1 := by
  cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
  | none =>
    have hlist : leftoverPieces B p = [p] :=
      leftoverPieces_of_not_mem_start_none hs hfind
    have hemp : p.support ∩ B = ∅ := by
      ext y
      constructor
      · intro hy
        have hyW : y ∈ p.walk.support :=
          (mem_walk_support (p := p)).1 (mem_inter.1 hy).1
        have hnot : ¬ decide (y ∈ B) :=
          (List.find?_eq_none (p := fun x : V => decide (x ∈ B))).1 hfind y hyW
        exact (hnot (decide_eq_true (mem_inter.1 hy).2)).elim
      · intro hy
        exact (notMem_empty y hy).elim
    simp [hlist, hemp]
  | some _ =>
    have hnone :
        p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
      simp [hfind]
    rw [leftoverPieces.eq_def]
    simp only [hs, hnone, dite_false]
    have hfind' := firstB_spec (B := B) (p := p) hnone
    have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
    have hbB : firstB B p hnone ∈ B := (mem_find?_B (B := B) hfind').2
    have hstartD : (p.dropUntil hx).start ∈ B := by
      simpa [dropUntil] using hbB
    have hfinD : (p.dropUntil hx).finish ∉ B := by
      simpa [dropUntil] using hf
    have hnoD : NoConsecutive B (p.dropUntil hx) :=
      NoConsecutive_of_edges_subset (edges_dropUntil_subset p hx) hno
    have hlenD :=
      leftoverPieces_length_eq_of_start_mem_finish_not hstartD hfinD hnoD
    have htakeB :
        (p.takeUntil hx).support ∩ B = {firstB B p hnone} := by
      ext y
      constructor
      · intro hy
        have hy1 := (mem_inter.1 hy).1
        have hy2 := (mem_inter.1 hy).2
        by_cases hEq : y = firstB B p hnone
        · simp [hEq]
        · exact (takeUntil_ne_first_not_mem_B hfind' hx hy1 hEq hy2).elim
      · intro hy
        have : y = firstB B p hnone := mem_singleton.1 hy
        subst this
        exact mem_inter.2 ⟨(p.takeUntil hx).finish_mem_support, hbB⟩
    have hunion := support_takeUntil_union_dropUntil p hx
    have hTD : p.support ∩ B = (p.dropUntil hx).support ∩ B := by
      have h1 :
          p.support ∩ B =
            ((p.takeUntil hx).support ∪ (p.dropUntil hx).support) ∩ B := by
        rw [hunion]
      rw [h1, union_inter_distrib_right, htakeB, singleton_union]
      ext y
      constructor
      · intro hy
        rcases mem_insert.1 hy with rfl | hy'
        · exact mem_inter.2 ⟨(p.dropUntil hx).start_mem_support, hbB⟩
        · exact hy'
      · intro hy
        exact mem_insert.2 (Or.inr hy)
    simp [List.length_cons, hlenD, hTD]

end GraphPath

open GraphPath

variable {B : Finset V} {q : ℕ}

lemma augCarrier_sdiff_fresh (K : Finset V) :
    augCarrier (q := q) K \ augFresh (V := V) (q := q) =
      augOldImage (q := q) K := by
  ext x
  constructor
  · intro hx
    have hxU := (mem_sdiff.1 hx).1
    have hxF := (mem_sdiff.1 hx).2
    rcases mem_union.1 hxU with hxK | hxFr
    · exact hxK
    · exact (hxF hxFr).elim
  · intro hx
    refine mem_sdiff.2 ⟨mem_union.2 (Or.inl hx), ?_⟩
    exact disjoint_left.1 (disjoint_augOldImage_fresh (q := q) K) hx

lemma mem_augA_not_fresh {x : V ⊕ Fin q}
    (hx : x ∈ augA (B := B) (q := q)) :
    x ∉ augFresh (V := V) (q := q) :=
  disjoint_left.1 (disjoint_augOldImage_fresh (q := q) B) hx

lemma leftoverPieces_ends_mem_augA
    {p : GraphPath (augGraph (G := G) B q)}
    (hs : p.start ∈ augA (B := B) (q := q))
    (hf : p.finish ∈ augA (B := B) (q := q))
    {Q : GraphPath (augGraph (G := G) B q)}
    (hQ : Q ∈ leftoverPieces (augFresh (V := V) (q := q)) p) :
    Q.start ∈ augA (B := B) (q := q) ∧
      Q.finish ∈ augA (B := B) (q := q) := by
  obtain ⟨ru, rv, _heq, hruB, hrvB⟩ :=
    leftoverPieces_factor (B := augFresh (V := V) (q := q)) p Q hQ
  constructor
  · by_cases hnil : ru.Nil
    · have hst : Q.start = p.start := (Walk.Nil.eq hnil).symm
      exact hst ▸ hs
    · have hpen : ru.penultimate ∈ augFresh (V := V) (q := q) :=
        hruB.resolve_left hnil
      have hadj :
          (augGraph (G := G) B q).Adj ru.penultimate Q.start :=
        ru.adj_penultimate hnil
      obtain ⟨i, hi⟩ := (mem_augFresh (V := V) (q := q)).1 hpen
      have hadj' : (augGraph (G := G) B q).Adj (.inr i) Q.start := by
        simpa [hi] using hadj
      obtain ⟨a, ha, hxa⟩ :=
        (adj_fresh_iff (G := G) (B := B) (q := q) (i := i) (x := Q.start)).1
          hadj'
      exact (mem_augA (B := B) (q := q)).2 ⟨a, ha, hxa⟩
  · by_cases hnil : rv.Nil
    · have hfin : Q.finish = p.finish := Walk.Nil.eq hnil
      exact hfin ▸ hf
    · have hsnd : rv.snd ∈ augFresh (V := V) (q := q) :=
        hrvB.resolve_left hnil
      have hadj : (augGraph (G := G) B q).Adj Q.finish rv.snd :=
        rv.adj_snd hnil
      obtain ⟨i, hi⟩ := (mem_augFresh (V := V) (q := q)).1 hsnd
      have hadj' : (augGraph (G := G) B q).Adj Q.finish (.inr i) := by
        simpa [hi] using hadj
      have hadj'' : (augGraph (G := G) B q).Adj (.inr i) Q.finish :=
        hadj'.symm
      obtain ⟨a, ha, hxa⟩ :=
        (adj_fresh_iff (G := G) (B := B) (q := q) (i := i) (x := Q.finish)).1
          hadj''
      exact (mem_augA (B := B) (q := q)).2 ⟨a, ha, hxa⟩

lemma leftoverCoverOfPath_fresh_eq_oldImage {K : Finset V}
    {p : GraphPath (augGraph (G := G) B q)}
    (hp : p.support = augCarrier (q := q) K) :
    p.support \ augFresh (V := V) (q := q) = augOldImage (q := q) K := by
  rw [hp, augCarrier_sdiff_fresh]

lemma leftoverCoverOfPath_fresh_card {K : Finset V}
    {p : GraphPath (augGraph (G := G) B q)}
    (hp : p.support = augCarrier (q := q) K)
    (hs : p.start ∈ augA (B := B) (q := q))
    (hf : p.finish ∈ augA (B := B) (q := q)) :
    (leftoverCoverOfPath p (augFresh (V := V) (q := q))).card = q + 1 := by
  have hno :
      NoConsecutive (augFresh (V := V) (q := q)) p :=
    NoConsecutive_of_independent
      (Independent.augFresh (G := G) (B := B) (q := q)) p
  have hlen :=
    leftoverPieces_length_eq_of_ends_not_mem
      (mem_augA_not_fresh (B := B) (q := q) hs)
      (mem_augA_not_fresh (B := B) (q := q) hf) hno
  have hFsub : augFresh (V := V) (q := q) ⊆ p.support := by
    rw [hp]
    exact subset_union_right
  have hinter :
      p.support ∩ augFresh (V := V) (q := q) =
        augFresh (V := V) (q := q) :=
    inter_eq_right.2 hFsub
  rw [leftoverCoverOfPath_card, hlen, hinter, card_augFresh]

lemma leftoverCoverOfPath_fresh_terminal {K : Finset V}
    {p : GraphPath (augGraph (G := G) B q)}
    (hp : p.support = augCarrier (q := q) K)
    (hs : p.start ∈ augA (B := B) (q := q))
    (hf : p.finish ∈ augA (B := B) (q := q)) :
    IsTerminalCover (G := augGraph (G := G) B q)
      (augA (B := B) (q := q))
      ((leftoverCoverOfPath p (augFresh (V := V) (q := q))).cast
        (leftoverCoverOfPath_fresh_eq_oldImage (K := K) hp)) := by
  intro Q hQ
  have hQ' : Q ∈ leftoverPieces (augFresh (V := V) (q := q)) p := by
    rwa [PathCover.cast_paths, leftoverCoverOfPath_paths] at hQ
  exact leftoverPieces_ends_mem_augA (B := B) (q := q) hs hf hQ'

lemma ofAugOldImage_exists_path {U : Finset V}
    (pc : PathCover (augGraph (G := G) B q) (augOldImage (q := q) U))
    {p : GraphPath G}
    (hp : p ∈ (pc.ofAugOldImage (B := B) (q := q)).paths) :
    ∃ qth ∈ pc.paths,
      Sum.inl p.start = qth.start ∧ Sum.inl p.finish = qth.finish := by
  dsimp [PathCover.ofAugOldImage, PathCover.ofCarrierImage_inl,
    PathCover.ofCarrierImage, GraphPath.ofCarrierRange] at hp
  rcases List.mem_map.1 hp with ⟨x, _hx, rfl⟩
  have hrange : ∀ y ∈ x.1.support,
      y ∈ Set.range (Sum.inl : V → V ⊕ Fin q) := by
    intro y hy
    obtain ⟨a, _, rfl⟩ :=
      (mem_augOldImage (q := q)).1 (pc.support_subset x.property hy)
    exact ⟨a, rfl⟩
  haveI : Nonempty V :=
    nonempty_of_mem_range (f := (Embedding.inl : V ↪ V ⊕ Fin q))
      (hrange _ x.1.start_mem_support)
  refine ⟨x.1, x.property, ?_, ?_⟩
  · change Sum.inl (invFun (Sum.inl : V → V ⊕ Fin q) x.1.start) = x.1.start
    exact Function.invFun_eq (hrange _ x.1.start_mem_support)
  · change Sum.inl (invFun (Sum.inl : V → V ⊕ Fin q) x.1.finish) = x.1.finish
    exact Function.invFun_eq (hrange _ x.1.finish_mem_support)

lemma ofAugOldImage_terminal {U : Finset V}
    (pc : PathCover (augGraph (G := G) B q) (augOldImage (q := q) U))
    (hterm : IsTerminalCover (G := augGraph (G := G) B q)
      (augA (B := B) (q := q)) pc) :
    IsTerminalCover (G := G) B (pc.ofAugOldImage (B := B) (q := q)) := by
  intro p hp
  obtain ⟨qth, hq, hst, hfin⟩ :=
    ofAugOldImage_exists_path (B := B) (q := q) pc hp
  have ⟨hsA, hfA⟩ := hterm qth hq
  constructor
  · obtain ⟨a, ha, hsa⟩ := (mem_augA (B := B) (q := q)).1 hsA
    have : Sum.inl p.start = Sum.inl a := hst.trans hsa
    exact (Sum.inl_injective this) ▸ ha
  · obtain ⟨a, ha, hsa⟩ := (mem_augA (B := B) (q := q)).1 hfA
    have : Sum.inl p.finish = Sum.inl a := hfin.trans hsa
    exact (Sum.inl_injective this) ▸ ha

/-- Actual original-edge `B`-ended cover of `K` obtained by deleting the
fresh vertices of a supplied spanning `augA`–`augA` path of the
augmentation graph. Singleton leftover runs are retained; no total map
sending a fresh vertex to a default old vertex is used. -/
noncomputable def leftoverCoverOfAugPath {K : Finset V}
    (p : GraphPath (augGraph (G := G) B q))
    (hp : p.support = augCarrier (q := q) K) :
    PathCover G K :=
  ((leftoverCoverOfPath p (augFresh (V := V) (q := q))).cast
      (leftoverCoverOfPath_fresh_eq_oldImage (K := K) hp)).ofAugOldImage
    (B := B) (q := q)

lemma leftoverCoverOfAugPath_card {K : Finset V}
    (p : GraphPath (augGraph (G := G) B q))
    (hp : p.support = augCarrier (q := q) K)
    (hs : p.start ∈ augA (B := B) (q := q))
    (hf : p.finish ∈ augA (B := B) (q := q)) :
    (leftoverCoverOfAugPath (B := B) (q := q) p hp).card = q + 1 := by
  simp [leftoverCoverOfAugPath, PathCover.ofAugOldImage_card, PathCover.cast_card,
    leftoverCoverOfPath_fresh_card (K := K) hp hs hf]

lemma leftoverCoverOfAugPath_terminal {K : Finset V}
    (p : GraphPath (augGraph (G := G) B q))
    (hp : p.support = augCarrier (q := q) K)
    (hs : p.start ∈ augA (B := B) (q := q))
    (hf : p.finish ∈ augA (B := B) (q := q)) :
    IsTerminalCover (G := G) B
      (leftoverCoverOfAugPath (B := B) (q := q) p hp) :=
  ofAugOldImage_terminal _
    (leftoverCoverOfPath_fresh_terminal (K := K) hp hs hf)

/-- Existence packaging of the supplied-path deletion. The path is an
input, not a proved existence theorem. -/
lemma exists_terminalCover_of_augPath {K : Finset V}
    (p : GraphPath (augGraph (G := G) B q))
    (hp : p.support = augCarrier (q := q) K)
    (hs : p.start ∈ augA (B := B) (q := q))
    (hf : p.finish ∈ augA (B := B) (q := q)) :
    ∃ pc : PathCover G K,
      pc.card = q + 1 ∧ IsTerminalCover (G := G) B pc :=
  ⟨leftoverCoverOfAugPath (B := B) (q := q) p hp,
    leftoverCoverOfAugPath_card (B := B) (q := q) p hp hs hf,
    leftoverCoverOfAugPath_terminal (B := B) (q := q) p hp hs hf⟩

end Nikoghosyan
