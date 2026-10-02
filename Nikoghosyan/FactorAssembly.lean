/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.CycleAssembly

/-!
Original-edge cycle-factor group replacement and cyclic block assembly.

Given a `CycleFactor` and a nonempty index set of DISTINCT cycles, together
with an actual `GraphCycle` whose support is exactly the union of those
selected supports, replace precisely those cycles. The result is again a
cycle factor, of cardinality `|F| - k + 1`. A globally minimum original-edge
factor (minimum over ALL original-edge factors, not a cograph-only family)
cannot admit such a merger for `k ≥ 2`.

Cyclic assembly: pairwise-disjoint original spanning paths joined by actual
cross edges in cyclic order yield one genuine original cycle. The two-block
case (`k = 2`, each block a genuine factor cycle of order ≥ 3) is included.
No Hamilton cycle is assumed as an input.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

lemma start_splice (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) :
    (p.splice q h hd).start = p.start :=
  rfl

lemma finish_splice (p q : GraphPath G) (h : G.Adj p.finish q.start)
    (hd : Disjoint p.support q.support) :
    (p.splice q h hd).finish = q.finish :=
  rfl

/-- Support-union of a list of original-edge paths. -/
def supportUnion (ps : List (GraphPath G)) : Finset V :=
  ps.foldr (fun p s => p.support ∪ s) ∅

@[simp]
lemma supportUnion_nil : supportUnion (G := G) [] = ∅ :=
  rfl

@[simp]
lemma supportUnion_cons (p : GraphPath G) (ps : List (GraphPath G)) :
    supportUnion (p :: ps) = p.support ∪ supportUnion ps :=
  rfl

lemma mem_supportUnion {ps : List (GraphPath G)} {x : V} :
    x ∈ supportUnion ps ↔ ∃ p ∈ ps, x ∈ p.support := by
  induction ps with
  | nil => simp [supportUnion]
  | cons p ps ih =>
    constructor
    · intro hx
      rw [supportUnion_cons, mem_union] at hx
      rcases hx with hxp | hxps
      · exact ⟨p, List.mem_cons_self, hxp⟩
      · obtain ⟨q, hq, hxq⟩ := ih.1 hxps
        exact ⟨q, List.mem_cons_of_mem p hq, hxq⟩
    · intro ⟨q, hq, hxq⟩
      rw [supportUnion_cons, mem_union]
      rcases List.mem_cons.1 hq with rfl | hq'
      · exact Or.inl hxq
      · exact Or.inr (ih.2 ⟨q, hq', hxq⟩)

/-- Two vertex-disjoint original-edge paths, joined by a forward original
cross edge and closed by a backward original cross edge, yield one genuine
original cycle on the support union. Both paths may be spanning paths of
factor blocks of order at least three; a Hamilton cycle is not an input. -/
def assembleTwo (p q : GraphPath G)
    (hd : Disjoint p.support q.support)
    (hfwd : G.Adj p.finish q.start)
    (hback : G.Adj q.finish p.start)
    (h3 : 3 ≤ (p.support ∪ q.support).card) : GraphCycle G :=
  (p.splice q hfwd hd).toCycle (by
    simpa [splice] using hback) (by
    simpa [support_splice] using h3)

@[simp]
lemma support_assembleTwo (p q : GraphPath G)
    (hd : Disjoint p.support q.support)
    (hfwd : G.Adj p.finish q.start)
    (hback : G.Adj q.finish p.start)
    (h3 : 3 ≤ (p.support ∪ q.support).card) :
    (assembleTwo p q hd hfwd hback h3).support = p.support ∪ q.support := by
  simp [assembleTwo, support_toCycle, support_splice]

/-- Left-fold splice of a tail onto an accumulator, as an existence lemma
so that list induction is structural. -/
lemma exists_spliceAcc (acc : GraphPath G) (rest : List (GraphPath G))
    (hdisj : ∀ q ∈ rest, Disjoint acc.support q.support)
    (hpw : rest.Pairwise fun p q => Disjoint p.support q.support)
    (hfirst : ∀ (hne : rest ≠ []),
      G.Adj acc.finish (rest.head hne).start)
    (htail : ∀ i (hi : i + 1 < rest.length),
      G.Adj (rest.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (rest.get ⟨i + 1, hi⟩).start) :
    ∃ r : GraphPath G,
      r.start = acc.start ∧
        r.finish =
          (if hne : rest ≠ [] then (rest.getLast hne).finish else acc.finish) ∧
        r.support = acc.support ∪ supportUnion rest := by
  induction rest generalizing acc with
  | nil =>
    exact ⟨acc, rfl, by simp, by simp [supportUnion]⟩
  | cons q qs ih =>
    have hadj : G.Adj acc.finish q.start :=
      hfirst (List.cons_ne_nil q qs)
    have hd : Disjoint acc.support q.support := hdisj q (by simp)
    let acc' := acc.splice q hadj hd
    have hdisj' : ∀ r ∈ qs, Disjoint acc'.support r.support := by
      intro r hr
      have hd1 : Disjoint acc.support r.support := hdisj r (by simp [hr])
      have hd2 : Disjoint q.support r.support :=
        (List.pairwise_cons.1 hpw).1 r hr
      simpa [acc', support_splice] using disjoint_union_left.2 ⟨hd1, hd2⟩
    have hpw' : qs.Pairwise fun p q => Disjoint p.support q.support :=
      (List.pairwise_cons.1 hpw).2
    have hfirst' : ∀ (hne : qs ≠ []),
        G.Adj acc'.finish (qs.head hne).start := by
      intro hne
      have hi : 0 + 1 < (q :: qs).length := by
        cases qs with
        | nil => exact (hne rfl).elim
        | cons _ _ => simp
      have h := htail 0 hi
      have hhead : qs.head hne = qs.get ⟨0, by
        cases qs with
        | nil => exact (hne rfl).elim
        | cons _ _ => simp⟩ := by
        cases qs with
        | nil => exact (hne rfl).elim
        | cons _ _ => rfl
      simpa [acc', finish_splice, hhead, List.get] using h
    have htail' : ∀ i (hi : i + 1 < qs.length),
        G.Adj (qs.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
          (qs.get ⟨i + 1, hi⟩).start := by
      intro i hi
      have hi' : (i + 1) + 1 < (q :: qs).length := by
        simpa [List.length_cons] using Nat.succ_lt_succ hi
      have h := htail (i + 1) hi'
      simpa [List.get] using h
    obtain ⟨r, hr1, hr2, hr3⟩ := ih acc' hdisj' hpw' hfirst' htail'
    refine ⟨r, ?_, ?_, ?_⟩
    · simpa [acc', start_splice] using hr1
    · cases qs with
      | nil =>
        simp [acc', finish_splice] at hr2 ⊢
        exact hr2
      | cons _ _ =>
        simpa [List.getLast_cons] using hr2
    · simpa [acc', support_splice, supportUnion, union_assoc] using hr3

lemma exists_spliceChain (ps : List (GraphPath G)) (hne : ps ≠ [])
    (hdisj : ps.Pairwise fun p q => Disjoint p.support q.support)
    (hedges : ∀ i (hi : i + 1 < ps.length),
      G.Adj (ps.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (ps.get ⟨i + 1, hi⟩).start) :
    ∃ r : GraphPath G,
      r.start = (ps.head hne).start ∧
        r.finish = (ps.getLast hne).finish ∧
        r.support = supportUnion ps := by
  match ps, hne with
  | [], h => exact (h rfl).elim
  | p :: rest, hne' =>
    have hdisj' : ∀ q ∈ rest, Disjoint p.support q.support :=
      fun q hq => (List.pairwise_cons.1 hdisj).1 q hq
    have hpw : rest.Pairwise fun a b => Disjoint a.support b.support :=
      (List.pairwise_cons.1 hdisj).2
    have hfirst : ∀ (hr : rest ≠ []), G.Adj p.finish (rest.head hr).start := by
      intro hr
      have hi : 0 + 1 < (p :: rest).length := by
        cases rest with
        | nil => exact (hr rfl).elim
        | cons _ _ => simp
      have hhead : rest.head hr = rest.get ⟨0, by
        cases rest with
        | nil => exact (hr rfl).elim
        | cons _ _ => simp⟩ := by
        cases rest with
        | nil => exact (hr rfl).elim
        | cons _ _ => rfl
      simpa [hhead, List.get] using hedges 0 hi
    have htail : ∀ i (hi : i + 1 < rest.length),
        G.Adj (rest.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
          (rest.get ⟨i + 1, hi⟩).start := by
      intro i hi
      have hi' : (i + 1) + 1 < (p :: rest).length := by
        simpa [List.length_cons] using Nat.succ_lt_succ hi
      simpa [List.get] using hedges (i + 1) hi'
    obtain ⟨r, hr1, hr2, hr3⟩ := exists_spliceAcc p rest hdisj' hpw hfirst htail
    refine ⟨r, by simpa [List.head] using hr1, ?_, by simpa [supportUnion] using hr3⟩
    cases rest with
    | nil => simpa [List.getLast] using hr2
    | cons _ _ => simpa [List.getLast_cons] using hr2

/-- Cyclic original-edge assembly of `k ≥ 2` pairwise-disjoint paths.
The closing seam is the original edge from the last finish to the first
start. -/
noncomputable def assembleCycle (ps : List (GraphPath G))
    (h2 : 2 ≤ ps.length)
    (hdisj : ps.Pairwise fun p q => Disjoint p.support q.support)
    (hedges : ∀ i (hi : i + 1 < ps.length),
      G.Adj (ps.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (ps.get ⟨i + 1, hi⟩).start)
    (hclose : G.Adj
      (ps.getLast (by intro h; simp [h] at h2)).finish
      (ps.head (by intro h; simp [h] at h2)).start)
    (h3 : 3 ≤ (supportUnion ps).card) : GraphCycle G :=
  let hne : ps ≠ [] := by intro h; simp [h] at h2
  let r := Classical.choose (exists_spliceChain ps hne hdisj hedges)
  let hr := Classical.choose_spec (exists_spliceChain ps hne hdisj hedges)
  r.toCycle (by
    have hst : r.start = (ps.head hne).start := hr.1
    have hfn : r.finish = (ps.getLast hne).finish := hr.2.1
    rw [hst, hfn]
    exact hclose) (by
    have hs : r.support = supportUnion ps := hr.2.2
    rw [hs]
    exact h3)

@[simp]
lemma support_assembleCycle (ps : List (GraphPath G))
    (h2 : 2 ≤ ps.length)
    (hdisj : ps.Pairwise fun p q => Disjoint p.support q.support)
    (hedges : ∀ i (hi : i + 1 < ps.length),
      G.Adj (ps.get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        (ps.get ⟨i + 1, hi⟩).start)
    (hclose : G.Adj
      (ps.getLast (by intro h; simp [h] at h2)).finish
      (ps.head (by intro h; simp [h] at h2)).start)
    (h3 : 3 ≤ (supportUnion ps).card) :
    (assembleCycle ps h2 hdisj hedges hclose h3).support = supportUnion ps := by
  simp [assembleCycle, support_toCycle]
  exact (Classical.choose_spec (exists_spliceChain ps (by intro h; simp [h] at h2)
    hdisj hedges)).2.2

end GraphPath

namespace CycleFactor

/-- The original-edge cycle of `F` at a list index. -/
def getCycle (F : CycleFactor G) (i : Fin F.card) : GraphCycle G :=
  F.cycles.get ⟨i.1, by simpa [CycleFactor.card] using i.2⟩

lemma getCycle_mem (F : CycleFactor G) (i : Fin F.card) :
    F.getCycle i ∈ F.cycles :=
  List.get_mem _ _

lemma disjoint_getCycle (F : CycleFactor G) {i j : Fin F.card} (hij : i ≠ j) :
    Disjoint (F.getCycle i).support (F.getCycle j).support := by
  have hi : i.1 < F.cycles.length := by simpa [CycleFactor.card] using i.2
  have hj : j.1 < F.cycles.length := by simpa [CycleFactor.card] using j.2
  wlog hlt : i.1 < j.1
  · have hle : j.1 ≤ i.1 := Nat.le_of_not_gt hlt
    rcases Nat.lt_or_eq_of_le hle with hlt' | heq
    · exact (this F hij.symm hj hi hlt').symm
    · exact (hij (Fin.ext heq.symm)).elim
  have hpw :=
    (List.pairwise_iff_get (R := fun c d : GraphCycle G =>
      Disjoint c.support d.support)).1 F.disjoint
      ⟨i.1, hi⟩ ⟨j.1, hj⟩ hlt
  simpa [getCycle] using hpw

/-- Union of the supports of the selected cycles of `F`. -/
noncomputable def selectedSupport (F : CycleFactor G) (s : Finset (Fin F.card)) :
    Finset V :=
  s.biUnion fun i => (F.getCycle i).support

lemma mem_selectedSupport {F : CycleFactor G} {s : Finset (Fin F.card)} {x : V} :
    x ∈ F.selectedSupport s ↔ ∃ i ∈ s, x ∈ (F.getCycle i).support := by
  simp [selectedSupport]

/-- Cycles of `F` whose indices lie outside the selected set. -/
noncomputable def keptCycles (F : CycleFactor G) (s : Finset (Fin F.card)) :
    List (GraphCycle G) :=
  (univ (α := Fin F.card) \ s).toList.map F.getCycle

lemma length_keptCycles (F : CycleFactor G) (s : Finset (Fin F.card)) :
    (F.keptCycles s).length = F.card - s.card := by
  simp [keptCycles, List.length_map, Finset.length_toList, card_sdiff,
    card_univ, Fintype.card_fin]

lemma pairwise_keptCycles (F : CycleFactor G) (s : Finset (Fin F.card)) :
    (F.keptCycles s).Pairwise fun c d => Disjoint c.support d.support := by
  rw [keptCycles, List.pairwise_map]
  refine List.Pairwise.imp ?_ (univ (α := Fin F.card) \ s).nodup_toList
  intro i j hij
  exact F.disjoint_getCycle hij

lemma mem_keptCycles {F : CycleFactor G} {s : Finset (Fin F.card)}
    {c : GraphCycle G} :
    c ∈ F.keptCycles s ↔ ∃ i ∉ s, F.getCycle i = c := by
  simp [keptCycles, mem_sdiff]

lemma disjoint_kept_selected (F : CycleFactor G) (s : Finset (Fin F.card))
    {i : Fin F.card} (hi : i ∉ s) :
    Disjoint (F.getCycle i).support (F.selectedSupport s) := by
  rw [Finset.disjoint_left]
  intro x hx hxS
  obtain ⟨j, hj, hxj⟩ := (mem_selectedSupport (F := F) (s := s) (x := x)).1 hxS
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  exact Finset.disjoint_left.1 (F.disjoint_getCycle hij) hx hxj

/-- Replace the selected DISTINCT cycles of `F` by a single original-edge
cycle whose support is exactly their support-union. Pairwise disjointness
and full original coverage are retained. -/
noncomputable def replaceGroup (F : CycleFactor G) (s : Finset (Fin F.card))
    (C : GraphCycle G) (hspan : C.support = F.selectedSupport s) :
    CycleFactor G where
  cycles := F.keptCycles s ++ [C]
  disjoint := by
    rw [List.pairwise_append]
    refine ⟨F.pairwise_keptCycles s, List.pairwise_singleton _ _, ?_⟩
    intro c hc d hd
    have hdC : d = C := by simpa using hd
    subst hdC
    obtain ⟨i, hi, rfl⟩ := (mem_keptCycles (F := F) (s := s)).1 hc
    simpa [hspan] using F.disjoint_kept_selected s hi
  mem_iff := by
    intro x
    obtain ⟨c, hc, hx⟩ := F.mem_iff x
    obtain ⟨n, hn⟩ := List.get_of_mem hc
    let i : Fin F.card := ⟨n.1, by simp [CycleFactor.card]⟩
    have hx' : x ∈ (F.getCycle i).support := by
      have : F.getCycle i = c := by
        simpa [getCycle, i] using hn
      simpa [this] using hx
    by_cases hi : i ∈ s
    · refine ⟨C, by simp [keptCycles], ?_⟩
      have : x ∈ F.selectedSupport s :=
        (mem_selectedSupport (F := F)).2 ⟨i, hi, hx'⟩
      simpa [hspan] using this
    · refine ⟨F.getCycle i, ?_, hx'⟩
      refine List.mem_append.2 (Or.inl ?_)
      exact (mem_keptCycles (F := F) (s := s)).2 ⟨i, hi, rfl⟩

lemma card_replaceGroup (F : CycleFactor G) (s : Finset (Fin F.card))
    (C : GraphCycle G) (hspan : C.support = F.selectedSupport s) :
    (F.replaceGroup s C hspan).card = F.card - s.card + 1 := by
  simp [replaceGroup, card, List.length_append, length_keptCycles]

lemma card_replaceGroup_lt (F : CycleFactor G) {s : Finset (Fin F.card)}
    (C : GraphCycle G) (hspan : C.support = F.selectedSupport s)
    (h2 : 2 ≤ s.card) :
    (F.replaceGroup s C hspan).card < F.card := by
  have hsle : s.card ≤ F.card := by
    simpa [card_univ, Fintype.card_fin] using card_le_card (subset_univ s)
  have hcard := F.card_replaceGroup s C hspan
  have : F.card - s.card + 1 < F.card := by omega
  exact hcard ▸ this

/-- A globally minimum original-edge cycle factor cannot admit a merger of
`k ≥ 2` of its cycles into one original cycle spanning exactly their
support union. The minimum is taken over ALL original-edge factors. -/
lemma not_exists_merge_of_min (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    (s : Finset (Fin F.card)) (h2 : 2 ≤ s.card)
    (C : GraphCycle G) (hspan : C.support = F.selectedSupport s) : False := by
  have hlt := F.card_replaceGroup_lt C hspan h2
  have hle := hmin (F.replaceGroup s C hspan)
  exact (not_le_of_gt hlt) hle

/-- Two distinct factor cycles, each supplied with a spanning original path
of its own support, joined by two actual original cross edges in cyclic
order, assemble to one genuine original cycle on the support union. -/
lemma exists_assemble_two_blocks (F : CycleFactor G)
    {i j : Fin F.card} (hij : i ≠ j)
    (p q : GraphPath G)
    (hp : p.support = (F.getCycle i).support)
    (hq : q.support = (F.getCycle j).support)
    (hfwd : G.Adj p.finish q.start)
    (hback : G.Adj q.finish p.start) :
    ∃ C : GraphCycle G,
      C.support = (F.getCycle i).support ∪ (F.getCycle j).support := by
  have hd : Disjoint p.support q.support := by
    simpa [hp, hq] using F.disjoint_getCycle hij
  have h3 : 3 ≤ (p.support ∪ q.support).card := by
    have hi := (F.getCycle i).three_le_card_support
    have hj := (F.getCycle j).three_le_card_support
    have hcup : (p.support ∪ q.support).card = p.support.card + q.support.card :=
      card_union_of_disjoint hd
    have hpcard : p.support.card = (F.getCycle i).support.card := by rw [hp]
    have hqcard : q.support.card = (F.getCycle j).support.card := by rw [hq]
    omega
  refine ⟨GraphPath.assembleTwo p q hd hfwd hback h3, ?_⟩
  simp [GraphPath.support_assembleTwo, hp, hq]

lemma selectedSupport_pair (F : CycleFactor G) {i j : Fin F.card} :
    F.selectedSupport {i, j} =
      (F.getCycle i).support ∪ (F.getCycle j).support := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, hxk⟩ := (mem_selectedSupport (F := F)).1 hx
    have hk' : k = i ∨ k = j := by simpa using hk
    rcases hk' with rfl | rfl
    · exact mem_union.2 (Or.inl hxk)
    · exact mem_union.2 (Or.inr hxk)
  · intro hx
    rw [mem_union] at hx
    rw [mem_selectedSupport]
    rcases hx with hxi | hxj
    · exact ⟨i, by simp, hxi⟩
    · exact ⟨j, by simp, hxj⟩

/-- From a two-block original assembly, the corresponding two-index group
replacement is a cycle factor of cardinality `|F| - 1`. -/
noncomputable def replaceTwo (F : CycleFactor G)
    {i j : Fin F.card} (hij : i ≠ j)
    (p q : GraphPath G)
    (hp : p.support = (F.getCycle i).support)
    (hq : q.support = (F.getCycle j).support)
    (hfwd : G.Adj p.finish q.start)
    (hback : G.Adj q.finish p.start) : CycleFactor G :=
  F.replaceGroup ({i, j} : Finset (Fin F.card))
    (Classical.choose (F.exists_assemble_two_blocks hij p q hp hq hfwd hback))
    (by
      have hC := Classical.choose_spec
        (F.exists_assemble_two_blocks hij p q hp hq hfwd hback)
      exact hC.trans (F.selectedSupport_pair).symm)

lemma card_replaceTwo (F : CycleFactor G)
    {i j : Fin F.card} (hij : i ≠ j)
    (p q : GraphPath G)
    (hp : p.support = (F.getCycle i).support)
    (hq : q.support = (F.getCycle j).support)
    (hfwd : G.Adj p.finish q.start)
    (hback : G.Adj q.finish p.start) :
    (F.replaceTwo hij p q hp hq hfwd hback).card = F.card - 1 := by
  have hspan :
      (Classical.choose (F.exists_assemble_two_blocks hij p q hp hq hfwd hback)).support =
        F.selectedSupport {i, j} := by
    have hC := Classical.choose_spec
      (F.exists_assemble_two_blocks hij p q hp hq hfwd hback)
    exact hC.trans (F.selectedSupport_pair).symm
  have hcard := F.card_replaceGroup ({i, j} : Finset (Fin F.card))
    (Classical.choose (F.exists_assemble_two_blocks hij p q hp hq hfwd hback)) hspan
  have hpair : ({i, j} : Finset (Fin F.card)).card = 2 := card_pair hij
  have hsle : 2 ≤ F.card := by
    have : ({i, j} : Finset (Fin F.card)).card ≤ F.card := by
      simpa [card_univ, Fintype.card_fin] using
        card_le_card (subset_univ ({i, j} : Finset (Fin F.card)))
    simpa [hpair] using this
  calc
    (F.replaceTwo hij p q hp hq hfwd hback).card
        = F.card - ({i, j} : Finset (Fin F.card)).card + 1 := hcard
    _ = F.card - 2 + 1 := by simp [hpair]
    _ = F.card - 1 := by omega

/-- A globally minimum original-edge factor cannot admit a two-block original
cycle assembly on distinct factor cycles. -/
lemma not_exists_two_block_merge_of_min (F : CycleFactor G)
    (hmin : ∀ F' : CycleFactor G, F.card ≤ F'.card)
    {i j : Fin F.card} (hij : i ≠ j)
    (p q : GraphPath G)
    (hp : p.support = (F.getCycle i).support)
    (hq : q.support = (F.getCycle j).support)
    (hfwd : G.Adj p.finish q.start)
    (hback : G.Adj q.finish p.start) : False := by
  have h2 : 2 ≤ F.card := by
    have : ({i, j} : Finset (Fin F.card)).card ≤ F.card := by
      simpa [card_univ, Fintype.card_fin] using
        card_le_card (subset_univ ({i, j} : Finset (Fin F.card)))
    simpa [card_pair hij] using this
  have hlt : (F.replaceTwo hij p q hp hq hfwd hback).card < F.card := by
    have hcard := F.card_replaceTwo hij p q hp hq hfwd hback
    omega
  have hle := hmin (F.replaceTwo hij p q hp hq hfwd hback)
  exact (not_le_of_gt hlt) hle

end CycleFactor

/-- Homomorphism from an induced subgraph onto original `G`. -/
def induceVal {s : Set V} : G.induce s →g G where
  toFun := Subtype.val
  map_rel' := fun h => by simpa [induce_adj] using h

/-- If `ab` were a bridge in a 1-tough graph of order at least three, a second
neighbour of `a` would lie in a different component of `G-a` from `b`,
violating the singleton cut. -/
lemma OneTough.not_isBridge (h : OneTough G) (hord : 3 ≤ Fintype.card V)
    {a b : V} (hab : G.Adj a b) : ¬ G.IsBridge s(a, b) := by
  intro hbr
  have hdeg := OneTough.two_le_ncard_neighborSet (G := G) h hord a
  have : ∃ u, G.Adj a u ∧ u ≠ b := by
    by_contra hnone
    have hsub : G.neighborSet a ⊆ ({b} : Set V) := by
      intro x hx
      have hadj : G.Adj a x := by simpa [mem_neighborSet] using hx
      have : x = b := by
        by_contra hne
        exact hnone ⟨x, hadj, hne⟩
      simp [this]
    have hcard : (G.neighborSet a).ncard ≤ 1 := by
      have := Set.ncard_le_ncard (s := G.neighborSet a) (t := ({b} : Set V))
        hsub (Set.toFinite _)
      simpa using this
    omega
  obtain ⟨u, hau, hne_ub⟩ := this
  have hua : u ≠ a := hau.ne.symm
  have hba : b ≠ a := hab.ne.symm
  let S : Finset V := {a}
  let U : Finset V := univ \ S
  have huU : u ∈ U := by simp [U, S, hua]
  have hbU : b ∈ U := by simp [U, S, hba]
  have hnr : ¬ (G.induce (U : Set V)).Reachable ⟨u, huU⟩ ⟨b, hbU⟩ := by
    intro hR
    obtain ⟨p⟩ := hR
    let pG : G.Walk u b := p.map (induceVal (s := (U : Set V)))
    have hab_not_pG : s(a, b) ∉ pG.edges := by
      intro he
      have ha_mem : a ∈ pG.support := pG.fst_mem_support_of_mem_edges he
      have ha_mem' : a ∈ (p.map (induceVal (s := (U : Set V)))).support := ha_mem
      rw [Walk.support_map, List.mem_map] at ha_mem'
      obtain ⟨z, -, hza⟩ := ha_mem'
      have haU : a ∈ U := by
        have : z.1 = a := by
          simpa [induceVal] using hza
        simpa [this] using z.property
      simp [U, S] at haU
    have hab_not : s(a, b) ∉ (Walk.cons hau pG).edges := by
      intro he
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with hfirst | hrest
      · have : u = b := by
          obtain ⟨_, h2⟩ | ⟨h1, _⟩ := Sym2.eq_iff.mp hfirst
          · exact h2.symm
          · exact (hau.ne h1).elim
        exact hne_ub this
      · exact hab_not_pG hrest
    have hreach : (G.deleteEdges {s(a, b)}).Reachable a b :=
      (reachable_deleteEdges_iff_exists_walk).2 ⟨Walk.cons hau pG, hab_not⟩
    exact (isBridge_iff.1 hbr) hreach
  have hnt : Nontrivial (G.induce (U : Set V)).ConnectedComponent :=
    ⟨⟨(G.induce (U : Set V)).connectedComponentMk ⟨u, huU⟩,
      (G.induce (U : Set V)).connectedComponentMk ⟨b, hbU⟩,
      fun hC => hnr (ConnectedComponent.exact hC)⟩⟩
  have h2 : 2 ≤ componentCount G U := by
    haveI : Nonempty (G.induce (U : Set V)).ConnectedComponent := inferInstance
    haveI : Finite (G.induce (U : Set V)).ConnectedComponent := inferInstance
    have hpos : 0 < componentCount G U := Nat.card_pos
    have hne1 : componentCount G U ≠ 1 := by
      intro h1
      have : Subsingleton (G.induce (U : Set V)).ConnectedComponent :=
        (Nat.card_eq_one_iff_unique.1 h1).1
      exact (not_subsingleton_iff_nontrivial).2 hnt this
    omega
  have hbound := h S (by simpa [U, S] using h2)
  have : componentCount G U ≤ 1 := by simpa [S] using hbound
  omega

end Nikoghosyan
