/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.Profiles
import Nikoghosyan.CycleAssembly
import Nikoghosyan.Prerequisites.TerminalPieces

/-!
# Fixed-cycle leftover runs, complementary original arcs, and exact endpoints

Manuscript `prof:prop:endpoints` and `prof:prop:incompatible`.

From one actual original-edge cycle `c` on `U` and nonempty `A ⊆ U`, open
`c` at a prescribed vertex of `A` and delete the remaining vertices of
`A` by the already-checked `leftoverPieces` recursion. Each nonempty run
`Q` is a contiguous subwalk of that opened path. The complementary
original path `r` is assembled from the prefix before `Q`, the closing
original edge at the opening vertex, and the suffix after `Q`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Nikoghosyan

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GraphPath

lemma leftoverPieces_length_le (B : Finset V) (p : GraphPath G) :
    (leftoverPieces B p).length ≤
      (p.support ∩ B).card + if p.start ∈ B then 0 else 1 := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        (leftoverPieces B p).length ≤
          (p.support ∩ B).card + if p.start ∈ B then 0 else 1)
    p.support.card ?_ p rfl
  intro n ih p hn
  by_cases hsB : p.start ∈ B
  · by_cases hnil : p.walk.Nil
    · have hsing : p.support = {p.start} := support_eq_singleton_of_nil p hnil
      simp [leftoverPieces_of_start_mem_nil hsB hnil, hsing, hsB]
    · rw [leftoverPieces_of_start_mem_cons hsB hnil]
      have hlt : (p.trimStart hnil).support.card < n := by
        simpa [hn] using trimStart_support_card_lt p hnil
      have ih' := ih _ hlt (p.trimStart hnil) rfl
      have hps : p.support = insert p.start (p.trimStart hnil).support := by
        rw [support_trimStart, insert_erase p.start_mem_support]
      have hstart_not : p.start ∉ (p.trimStart hnil).support := by
        rw [support_trimStart]; exact notMem_erase _ _
      have hcard : (p.support ∩ B).card =
          ((p.trimStart hnil).support ∩ B).card + 1 := by
        rw [hps, insert_inter_of_mem hsB, card_insert_of_notMem]
        exact fun hz => hstart_not (mem_inter.1 hz).1
      have hbound :
          ((p.trimStart hnil).support ∩ B).card +
            (if (p.trimStart hnil).start ∈ B then 0 else 1) ≤
            (p.support ∩ B).card := by
        rw [hcard]
        split_ifs <;> omega
      simpa [hsB] using ih'.trans hbound
  · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
    | none =>
      have hlist : leftoverPieces B p = [p] :=
        leftoverPieces_of_not_mem_start_none hsB hfind
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
      simp [hlist, hemp, hsB]
    | some _ =>
      have hnone : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
        simp [hfind]
      rw [leftoverPieces.eq_def]
      simp [hsB, hnone]
      have hfind' := firstB_spec (B := B) (p := p) hnone
      have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
      have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind'
      have hlt : (p.dropUntil hx).support.card < n := by
        simpa [hn] using dropUntil_support_card_lt p hx hne
      have ih' := ih _ hlt (p.dropUntil hx) rfl
      have hstartD : (p.dropUntil hx).start ∈ B := by
        simpa [dropUntil] using (mem_find?_B (B := B) hfind').2
      have hlenD : (leftoverPieces B (p.dropUntil hx)).length ≤
          ((p.dropUntil hx).support ∩ B).card := by
        simpa [hstartD] using ih'
      have hsub : (p.dropUntil hx).support ∩ B ⊆ p.support ∩ B :=
        inter_subset_inter (dropUntil_support_subset p hx) subset_rfl
      have : (leftoverPieces B (p.dropUntil hx)).length + 1 ≤
          (p.support ∩ B).card + 1 := by
        have := card_le_card hsub
        omega
      simpa [hsB] using this

lemma leftoverPieces_length_le_of_start_mem {B : Finset V} {p : GraphPath G}
    (hs : p.start ∈ B) :
    (leftoverPieces B p).length ≤ (p.support ∩ B).card := by
  have h := leftoverPieces_length_le B p
  simpa [hs] using h

lemma leftoverPieces_start_mem {B : Finset V} {p Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces B p) : Q.start ∈ p.support :=
  leftoverPieces_support_subset p Q hQ Q.start_mem_support

lemma leftoverPieces_finish_mem {B : Finset V} {p Q : GraphPath G}
    (hQ : Q ∈ leftoverPieces B p) : Q.finish ∈ p.support :=
  leftoverPieces_support_subset p Q hQ Q.finish_mem_support

lemma leftoverPieces_start_ne {B : Finset V} {p Q : GraphPath G}
    (hs : p.start ∈ B) (hQ : Q ∈ leftoverPieces B p) : Q.start ≠ p.start := by
  intro h
  exact Finset.disjoint_left.1 (leftoverPieces_disjoint_B p Q hQ)
    Q.start_mem_support (h ▸ hs)

lemma isPath_of_isSubwalk {u v u' v' : V} {p : G.Walk u v} {q : G.Walk u' v'}
    (hq : q.IsPath) (h : p.IsSubwalk q) : p.IsPath := by
  rw [Walk.isPath_def] at hq ⊢
  exact hq.sublist (Walk.isSubwalk_iff_support_isInfix.1 h).sublist

lemma isSubwalk_trimStart (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).walk.IsSubwalk p.walk := by
  rw [Walk.isSubwalk_iff_support_isInfix]
  have ht : (p.trimStart h).walk.support = p.walk.support.tail := by
    simp [trimStart, Walk.support_tail_of_not_nil p.walk h]
  rw [ht]
  exact (List.tail_suffix p.walk.support).isInfix

lemma isSubwalk_trimFinish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimFinish h).walk.IsSubwalk p.walk := by
  rw [Walk.isSubwalk_iff_support_isInfix]
  have hdl : (p.trimFinish h).walk.support = p.walk.support.dropLast :=
    Walk.support_dropLast (p := p.walk) h
  rw [hdl]
  exact (List.dropLast_prefix p.walk.support).isInfix

lemma leftoverPieces_isSubwalk {B : Finset V} (p : GraphPath G) :
    ∀ Q ∈ leftoverPieces B p, Q.walk.IsSubwalk p.walk := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        ∀ Q ∈ leftoverPieces B p, Q.walk.IsSubwalk p.walk)
    p.support.card ?_ p rfl
  intro n ih p hn Q hQ
  by_cases hsB : p.start ∈ B
  · by_cases hnil : p.walk.Nil
    · simp [leftoverPieces_of_start_mem_nil hsB hnil] at hQ
    · rw [leftoverPieces_of_start_mem_cons hsB hnil] at hQ
      have hlt : (p.trimStart hnil).support.card < n := by
        simpa [hn] using trimStart_support_card_lt p hnil
      exact (ih _ hlt (p.trimStart hnil) rfl Q hQ).trans (isSubwalk_trimStart p hnil)
  · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
    | none =>
      have hlist : leftoverPieces B p = [p] :=
        leftoverPieces_of_not_mem_start_none hsB hfind
      have : Q = p := List.mem_singleton.1 (hlist ▸ hQ)
      subst this
      exact Walk.isSubwalk_rfl _
    | some _ =>
      have hnone : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
        simp [hfind]
      rw [leftoverPieces.eq_def] at hQ
      simp [hsB, hnone] at hQ
      have hfind' := firstB_spec (B := B) (p := p) hnone
      have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
      have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind'
      have hnn : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
        hne ((takeUntil_nil_iff p hx).1 hn)
      rcases hQ with hQ | hQ
      · subst hQ
        exact (isSubwalk_trimFinish (p.takeUntil hx) hnn).trans
          (Walk.isSubwalk_takeUntil p.walk (mem_walk_support.1 hx))
      · have hlt : (p.dropUntil hx).support.card < n := by
          simpa [hn] using dropUntil_support_card_lt p hx hne
        exact (ih _ hlt (p.dropUntil hx) rfl Q hQ).trans
          (Walk.isSubwalk_dropUntil p.walk (mem_walk_support.1 hx))

lemma walk_eq_take_append_drop (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    p.walk = (p.takeUntil hx).walk.append (p.dropUntil hx).walk := by
  simp [takeUntil, dropUntil, Walk.take_spec]

lemma penultimate_append_of_not_nil {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hq : ¬ q.Nil) :
    (p.append q).penultimate = q.penultimate := by
  have hqpos : 0 < q.length := Walk.not_nil_iff_lt_length.1 hq
  have hlen : (p.append q).length = p.length + q.length := Walk.length_append p q
  have hnot : ¬ p.length + q.length - 1 < p.length := by omega
  have hsub : p.length + q.length - 1 - p.length = q.length - 1 := by omega
  simp only [Walk.penultimate, Walk.getVert_append, hlen]
  rw [if_neg hnot, hsub]

lemma snd_append_of_not_nil {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hp : ¬ p.Nil) :
    (p.append q).snd = p.snd := by
  have hppos : 0 < p.length := Walk.not_nil_iff_lt_length.1 hp
  simp only [Walk.snd, Walk.getVert_append]
  split_ifs with h
  · rfl
  · have hlen : p.length = 1 := by omega
    have hv : p.getVert 1 = v := by simpa [hlen] using p.getVert_length
    simp [hlen, Walk.getVert_zero, hv]

lemma nil_copy {u v u' v' : V} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).Nil ↔ p.Nil := by
  subst hu
  subst hv
  simp

lemma penultimate_copy {u v u' v' : V} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).penultimate = p.penultimate := by
  subst hu
  subst hv
  simp

lemma tail_copy_eq_of_eq_cons {u v w : V}
    {q : G.Walk u w} {h : G.Adj u v} {r : G.Walk v w}
    (heq : q = Walk.cons h r) (hsnd : q.snd = v) :
    q.tail.copy hsnd rfl = r := by
  subst q
  simp [Walk.tail_cons]
  cases r <;> rfl

/-- Strengthened leftover-run induction: an arbitrary original path `p`
factors as prefix `ru`, leftover run `Q`, suffix `rv`. The prefix is
nil or its penultimate vertex lies in `B`; the suffix is nil or its
first vertex after `Q.finish` lies in `B`. Recursive tails may start
outside `B`, so both nil cases are retained. -/
lemma leftoverPieces_factor {B : Finset V} (p : GraphPath G) :
    ∀ Q ∈ leftoverPieces B p,
      ∃ (ru : G.Walk p.start Q.start) (rv : G.Walk Q.finish p.finish),
        p.walk = (ru.append Q.walk).append rv ∧
          (ru.Nil ∨ ru.penultimate ∈ B) ∧
            (rv.Nil ∨ rv.snd ∈ B) := by
  refine Nat.strongRecOn (motive := fun n =>
      ∀ (p : GraphPath G), p.support.card = n →
        ∀ Q ∈ leftoverPieces B p,
          ∃ (ru : G.Walk p.start Q.start) (rv : G.Walk Q.finish p.finish),
            p.walk = (ru.append Q.walk).append rv ∧
              (ru.Nil ∨ ru.penultimate ∈ B) ∧
                (rv.Nil ∨ rv.snd ∈ B))
    p.support.card ?_ p rfl
  intro n ih p hn Q hQ
  by_cases hsB : p.start ∈ B
  · by_cases hnil : p.walk.Nil
    · simp [leftoverPieces_of_start_mem_nil hsB hnil] at hQ
    · rw [leftoverPieces_of_start_mem_cons hsB hnil] at hQ
      have hlt : (p.trimStart hnil).support.card < n := by
        simpa [hn] using trimStart_support_card_lt p hnil
      obtain ⟨ru', rv', heq', hru', hrv'⟩ :=
        ih _ hlt (p.trimStart hnil) rfl Q hQ
      obtain ⟨w, hadj, tail, hpw⟩ := Walk.not_nil_iff.1 hnil
      have htrimS : (p.trimStart hnil).start = w := by
        simp [trimStart, hpw]
      have htrimW : (p.trimStart hnil).walk.copy htrimS rfl = tail := by
        simpa [trimStart] using
          tail_copy_eq_of_eq_cons (q := p.walk) (h := hadj) (r := tail) hpw
            (by simp [hpw, Walk.snd_cons])
      let ruC : G.Walk w Q.start := ru'.copy htrimS rfl
      have htail : tail = (ruC.append Q.walk).append rv' := by
        have hcopy :=
          congrArg
            (fun t : G.Walk (p.trimStart hnil).start (p.trimStart hnil).finish =>
              t.copy htrimS rfl)
            heq'
        have hR :
            ((ru'.append Q.walk).append rv').copy htrimS rfl =
              (ruC.append Q.walk).append rv' := by
          change ((ru'.append Q.walk).append rv').copy htrimS rfl =
            ((ru'.copy htrimS rfl).append Q.walk).append rv'
          rw [← Walk.append_copy_copy (ru'.append Q.walk) rv' htrimS rfl rfl]
          rw [← Walk.append_copy_copy ru' Q.walk htrimS rfl rfl]
          simp
        rw [← hR, ← hcopy, htrimW]
      refine ⟨Walk.cons hadj ruC, rv', ?_, ?_, hrv'⟩
      · rw [hpw, htail]
        exact (Walk.cons_append hadj (ruC.append Q.walk) rv').symm
      · refine Or.inr ?_
        by_cases hnil' : ru'.Nil
        · have hnilC : ruC.Nil := (nil_copy ru' htrimS rfl).2 hnil'
          have hlen0 : ruC.length = 0 := Walk.length_eq_zero_iff.2 hnilC
          have hlen1 : (Walk.cons hadj ruC).length = 1 := by
            simp [Walk.length_cons, hlen0]
          change (Walk.cons hadj ruC).getVert ((Walk.cons hadj ruC).length - 1) ∈ B
          simp [hlen1, hsB]
        · have hnilC : ¬ ruC.Nil := fun h => hnil' ((nil_copy ru' htrimS rfl).1 h)
          have hpen : (Walk.cons hadj ruC).penultimate = ruC.penultimate :=
            Walk.penultimate_cons_of_not_nil hadj ruC hnilC
          rw [hpen, penultimate_copy ru' htrimS rfl]
          exact hru'.resolve_left hnil'
  · cases hfind : p.walk.support.find? (fun x => decide (x ∈ B)) with
    | none =>
      have hlist : leftoverPieces B p = [p] :=
        leftoverPieces_of_not_mem_start_none hsB hfind
      have : Q = p := List.mem_singleton.1 (hlist ▸ hQ)
      subst this
      exact ⟨Walk.nil, Walk.nil, by simp, Or.inl Walk.nil_nil, Or.inl Walk.nil_nil⟩
    | some _ =>
      have hnone : p.walk.support.find? (fun x => decide (x ∈ B)) ≠ none := by
        simp [hfind]
      rw [leftoverPieces.eq_def] at hQ
      simp [hsB, hnone] at hQ
      have hfind' := firstB_spec (B := B) (p := p) hnone
      have hx : firstB B p hnone ∈ p.support := (mem_find?_B (B := B) hfind').1
      have hbB : firstB B p hnone ∈ B := (mem_find?_B (B := B) hfind').2
      have hne : firstB B p hnone ≠ p.start := find?_B_ne_start hsB hfind'
      have hnn : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
        hne ((takeUntil_nil_iff p hx).1 hn)
      have hspec := walk_eq_take_append_drop p hx
      rcases hQ with hQ | hQ
      · have hQeq : Q = (p.takeUntil hx).trimFinish hnn := hQ
        have hmem : Q ∈ leftoverPieces B p := by
          rw [leftoverPieces.eq_def]; simp [hsB, hnone, hQeq]
        obtain ⟨ru, rv, heq⟩ := leftoverPieces_isSubwalk p Q hmem
        have hsQ : Q.start = p.start := by simp [hQeq, trimFinish, takeUntil]
        have hru : ru.Nil := by
          have hp : ru.IsPath := by
            have h := p.isPath
            rw [heq] at h
            exact (Walk.IsPath.of_append_left h).of_append_left
          exact hp.nil_iff_eq.2 hsQ.symm
        refine ⟨ru, rv, heq, Or.inl hru, Or.inr ?_⟩
        have hlenQ : Q.walk.length + 1 = (p.takeUntil hx).walk.length := by
          have hQlen : Q.walk.length = (p.takeUntil hx).walk.dropLast.length := by
            rw [hQeq]; rfl
          have hdl := Walk.length_dropLast (p.takeUntil hx).walk
          have hpos : 1 ≤ (p.takeUntil hx).walk.length :=
            Nat.succ_le_of_lt (Walk.not_nil_iff_lt_length.1 hnn)
          omega
        have hnnRv : ¬ rv.Nil := by
          intro hrv
          have hxW : firstB B p hnone ∈ p.walk.support :=
            (mem_walk_support (p := p)).1 hx
          have hxCat : firstB B p hnone ∈
              ru.support ++ Q.walk.support.tail ++ rv.support.tail := by
            simpa [heq, Walk.support_append] using hxW
          have hruL : ru.support = [p.start] := (Walk.nil_iff_support_eq).1 hru
          have hrvL : rv.support = [Q.finish] := (Walk.nil_iff_support_eq).1 hrv
          have : firstB B p hnone ∈ Q.walk.support.tail := by
            have hxOr : firstB B p hnone = p.start ∨
                firstB B p hnone ∈ Q.walk.support.tail := by
              simpa [hruL, hrvL, List.mem_append, List.mem_singleton] using hxCat
            rcases hxOr with hst | htail
            · exact (hne hst).elim
            · exact htail
          have hxQ : firstB B p hnone ∈ Q.support := by
            simp [GraphPath.support]
            exact List.mem_of_mem_tail this
          exact Finset.disjoint_left.1 (leftoverPieces_disjoint_B p Q hmem) hxQ hbB
        have hru0 : ru.length = 0 := Walk.length_eq_zero_iff.2 hru
        have hgetR : p.walk.getVert (Q.walk.length + 1) = rv.snd := by
          rw [heq]
          simp [Walk.getVert_append, hru0, Walk.snd]
        have hgetB : p.walk.getVert (Q.walk.length + 1) = firstB B p hnone := by
          rw [hspec, hlenQ]
          have hga :=
            Walk.getVert_append (p.takeUntil hx).walk (p.dropUntil hx).walk
              (p.takeUntil hx).walk.length
          have hlt : ¬ (p.takeUntil hx).walk.length < (p.takeUntil hx).walk.length :=
            Nat.lt_irrefl _
          have hga0 :
              ((p.takeUntil hx).walk.append (p.dropUntil hx).walk).getVert
                  (p.takeUntil hx).walk.length =
                (p.dropUntil hx).walk.getVert 0 := by
            rw [hga, if_neg hlt, Nat.sub_self]
            rfl
          have hstart : (p.dropUntil hx).start = firstB B p hnone := by
            simp [dropUntil]
          exact
            (hga0.trans (Walk.getVert_zero (p.dropUntil hx).walk)).trans hstart
        rw [← hgetR, hgetB]
        exact hbB
      · have hlt : (p.dropUntil hx).support.card < n := by
          simpa [hn] using dropUntil_support_card_lt p hx hne
        obtain ⟨ru', rv', heq', hru', hrv'⟩ :=
          ih _ hlt (p.dropUntil hx) rfl Q hQ
        have hstartD : (p.dropUntil hx).start ∈ B := by
          simpa [dropUntil] using hbB
        have hru_nn : ¬ ru'.Nil := by
          intro hnil'
          have : Q.start = (p.dropUntil hx).start := (Walk.Nil.eq hnil').symm
          exact leftoverPieces_start_ne hstartD hQ this
        refine ⟨(p.takeUntil hx).walk.append ru', rv', ?_, Or.inr ?_, hrv'⟩
        · conv_lhs => rw [hspec]
          rw [heq']
          refine (Walk.append_assoc _ _ _).trans ?_
          exact congrArg (fun t => t.append rv')
            (Walk.append_assoc (p.takeUntil hx).walk ru' Q.walk)
        · have hpen :=
            penultimate_append_of_not_nil (p.takeUntil hx).walk ru' hru_nn
          exact hpen ▸ hru'.resolve_left hru_nn

lemma leftoverPieces_factor_ru_not_nil {B : Finset V} {p Q : GraphPath G}
    (hs : p.start ∈ B) (hQ : Q ∈ leftoverPieces B p)
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (_heq : p.walk = (ru.append Q.walk).append rv) : ¬ ru.Nil := by
  intro hnil
  exact leftoverPieces_start_ne hs hQ (Walk.Nil.eq hnil).symm

lemma isPath_of_factor_left {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) : ru.IsPath := by
  have h := p.isPath
  rw [heq] at h
  exact (Walk.IsPath.of_append_left h).of_append_left

lemma isPath_of_factor_right {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) : rv.IsPath := by
  have h := p.isPath
  rw [heq] at h
  exact Walk.IsPath.of_append_right h

def ofWalk {u v : V} (w : G.Walk u v) (hw : w.IsPath) : GraphPath G where
  start := u
  finish := v
  walk := w
  isPath := hw

@[simp]
lemma support_ofWalk {u v : V} (w : G.Walk u v) (hw : w.IsPath) :
    (ofWalk w hw).support = w.support.toFinset :=
  rfl

@[simp] lemma ofWalk_start {u v : V} (w : G.Walk u v) (hw : w.IsPath) :
    (ofWalk w hw).start = u := rfl

@[simp] lemma ofWalk_finish {u v : V} (w : G.Walk u v) (hw : w.IsPath) :
    (ofWalk w hw).finish = v := rfl

@[simp] lemma ofWalk_walk {u v : V} (w : G.Walk u v) (hw : w.IsPath) :
    (ofWalk w hw).walk = w := rfl

lemma adj_trimFinish_finish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    G.Adj (p.trimFinish h).finish p.finish :=
  p.walk.adj_penultimate h

lemma walk_support_eq_singleton_of_nil {u v : V} {w : G.Walk u v}
    (h : w.Nil) : w.support = [u] :=
  (Walk.nil_iff_support_eq).1 h

lemma walk_support_eq_cons_of_not_nil {u v : V} {w : G.Walk u v}
    (h : ¬ w.Nil) : w.support = u :: w.support.tail := by
  have ht := Walk.support_tail_of_not_nil w h
  simpa [ht] using (Walk.cons_support_tail (p := w) h).symm

lemma mem_walk_concat_of_subwalk {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) :
    p.walk.support = ru.support ++ Q.walk.support.tail ++ rv.support.tail := by
  rw [heq, Walk.support_append, Walk.support_append]

lemma mem_concat_of_mem_Q_support {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    {x : V} (hx : x ∈ Q.walk.support) :
    x ∈ ru.support ++ Q.walk.support.tail ++ rv.support.tail := by
  by_cases hnil : Q.walk.Nil
  · have : x = Q.start := by
      have : Q.walk.support = [Q.start] := walk_support_eq_singleton_of_nil hnil
      simpa [this] using hx
    subst this
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (Walk.end_mem_support ru))))
  · have hcons : Q.walk.support = Q.start :: Q.walk.support.tail :=
      walk_support_eq_cons_of_not_nil hnil
    have : x = Q.start ∨ x ∈ Q.walk.support.tail := by
      rw [hcons] at hx
      exact List.mem_cons.1 hx
    rcases this with rfl | htail
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (Walk.end_mem_support ru))))
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr htail)))

lemma support_union_of_subwalk {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) :
    p.support = ru.support.toFinset ∪ Q.support ∪ rv.support.toFinset := by
  have hcat := mem_walk_concat_of_subwalk heq
  ext x
  simp only [GraphPath.support, mem_union, List.mem_toFinset]
  constructor
  · intro hx
    have hx' : x ∈ ru.support ++ Q.walk.support.tail ++ rv.support.tail := by
      simpa [hcat] using hx
    rcases List.mem_append.1 hx' with h | hrv
    · rcases List.mem_append.1 h with hru | hQt
      · exact Or.inl (Or.inl hru)
      · exact Or.inl (Or.inr (List.mem_of_mem_tail hQt))
    · exact Or.inr (List.mem_of_mem_tail hrv)
  · intro hx
    have hcat' : x ∈ ru.support ++ Q.walk.support.tail ++ rv.support.tail →
        x ∈ p.walk.support := fun h => by simpa [hcat] using h
    rcases hx with h | hrv
    · rcases h with hru | hQ
      · exact hcat' (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hru))))
      · exact hcat' (mem_concat_of_mem_Q_support (by simpa [GraphPath.support] using hQ))
    · have hxR : x ∈ rv.support := hrv
      by_cases hnilR : rv.Nil
      · have : x = Q.finish := by
          have : rv.support = [Q.finish] := walk_support_eq_singleton_of_nil hnilR
          simpa [this] using hxR
        subst this
        exact hcat' (mem_concat_of_mem_Q_support (Walk.end_mem_support Q.walk))
      · have hcons : rv.support = Q.finish :: rv.support.tail :=
          walk_support_eq_cons_of_not_nil hnilR
        have : x = Q.finish ∨ x ∈ rv.support.tail := by
          rw [hcons] at hxR
          exact List.mem_cons.1 hxR
        rcases this with rfl | htail
        · exact hcat' (mem_concat_of_mem_Q_support (Walk.end_mem_support Q.walk))
        · exact hcat' (List.mem_append.2 (Or.inr htail))

lemma inter_ru_Q {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) :
    ru.support.toFinset ∩ Q.support ⊆ {Q.start} := by
  intro x hx
  have hru : x ∈ ru.support := by simpa [List.mem_toFinset] using (mem_inter.1 hx).1
  have hQ : x ∈ Q.walk.support := by
    simpa [GraphPath.support] using (mem_inter.1 hx).2
  by_cases hxe : x = Q.start
  · simp [hxe]
  · have hnod := p.support_nodup
    have hcat := mem_walk_concat_of_subwalk heq
    have hnilQ : ¬ Q.walk.Nil := by
      intro hnil
      have : x = Q.start := by
        have : Q.walk.support = [Q.start] := walk_support_eq_singleton_of_nil hnil
        simpa [this] using hQ
      exact hxe this
    have hcons : Q.walk.support = Q.start :: Q.walk.support.tail :=
      walk_support_eq_cons_of_not_nil hnilQ
    have htail : x ∈ Q.walk.support.tail := by
      rw [hcons] at hQ
      exact (List.mem_cons.1 hQ).resolve_left hxe
    have hxP : x ∈ p.walk.support := by
      simpa [hcat] using List.mem_append.2
        (Or.inl (List.mem_append.2 (Or.inl hru)))
    have hcnt : 2 ≤ p.walk.support.count x := by
      have h1 : 1 ≤ ru.support.count x := List.count_pos_iff.mpr hru
      have h2 : 1 ≤ Q.walk.support.tail.count x := List.count_pos_iff.mpr htail
      rw [hcat, List.count_append, List.count_append]
      omega
    have : p.walk.support.count x = 1 := List.count_eq_one_of_mem hnod hxP
    omega

lemma inter_rv_Q {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) :
    rv.support.toFinset ∩ Q.support ⊆ {Q.finish} := by
  intro x hx
  have hrv : x ∈ rv.support := by simpa [List.mem_toFinset] using (mem_inter.1 hx).1
  have hQ : x ∈ Q.walk.support := by
    simpa [GraphPath.support] using (mem_inter.1 hx).2
  by_cases hxe : x = Q.finish
  · simp [hxe]
  · have hnod := p.support_nodup
    have hcat := mem_walk_concat_of_subwalk heq
    have hnilR : ¬ rv.Nil := by
      intro hnil
      have : x = Q.finish := by
        have : rv.support = [Q.finish] := walk_support_eq_singleton_of_nil hnil
        simpa [this] using hrv
      exact hxe this
    have hconsR : rv.support = Q.finish :: rv.support.tail :=
      walk_support_eq_cons_of_not_nil hnilR
    have htailR : x ∈ rv.support.tail :=
      (List.mem_cons.1 (by rwa [hconsR] at hrv)).resolve_left hxe
    have hxP : x ∈ p.walk.support := by
      rw [hcat]
      exact List.mem_append.2 (Or.inr htailR)
    have hcnt : 2 ≤ p.walk.support.count x := by
      have h2 : 1 ≤ rv.support.tail.count x := List.count_pos_iff.mpr htailR
      by_cases hxs : x = Q.start
      · subst hxs
        have h1 : 1 ≤ ru.support.count Q.start :=
          List.count_pos_iff.mpr (Walk.end_mem_support ru)
        rw [hcat, List.count_append, List.count_append]
        omega
      · have hnilQ : ¬ Q.walk.Nil := by
          intro hnil
          have : x = Q.start := by
            have : Q.walk.support = [Q.start] :=
              walk_support_eq_singleton_of_nil hnil
            simpa [this] using hQ
          exact hxs this
        have hconsQ : Q.walk.support = Q.start :: Q.walk.support.tail :=
          walk_support_eq_cons_of_not_nil hnilQ
        have htailQ : x ∈ Q.walk.support.tail :=
          (List.mem_cons.1 (by rwa [hconsQ] at hQ)).resolve_left hxs
        have h1 : 1 ≤ Q.walk.support.tail.count x := List.count_pos_iff.mpr htailQ
        rw [hcat, List.count_append, List.count_append]
        omega
    have : p.walk.support.count x = 1 := List.count_eq_one_of_mem hnod hxP
    omega

lemma sdiff_eq_prefix_suffix {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) :
    p.support \ Q.support =
      ru.support.toFinset.erase Q.start ∪ rv.support.toFinset.erase Q.finish := by
  have hU := support_union_of_subwalk heq
  have hruQ := inter_ru_Q heq
  have hrvQ := inter_rv_Q heq
  have hstart : Q.start ∈ ru.support.toFinset :=
    List.mem_toFinset.2 (Walk.end_mem_support ru)
  have hfinish : Q.finish ∈ rv.support.toFinset :=
    List.mem_toFinset.2 (Walk.start_mem_support rv)
  ext x
  simp only [hU, mem_sdiff, mem_union, mem_erase]
  constructor
  · intro ⟨hx, hxQ⟩
    rcases hx with h | hrv
    · rcases h with hru | hQ
      · exact Or.inl ⟨fun hxe => hxQ (hxe ▸ Q.start_mem_support), hru⟩
      · exact (hxQ hQ).elim
    · exact Or.inr ⟨fun hxe => hxQ (hxe ▸ Q.finish_mem_support), hrv⟩
  · intro hx
    rcases hx with ⟨hne, hru⟩ | ⟨hne, hrv⟩
    · refine ⟨Or.inl (Or.inl hru), ?_⟩
      intro hQ
      have : x ∈ ({Q.start} : Finset V) :=
        hruQ (mem_inter.2 ⟨hru, hQ⟩)
      exact hne (mem_singleton.1 this)
    · refine ⟨Or.inr hrv, ?_⟩
      intro hQ
      have : x ∈ ({Q.finish} : Finset V) :=
        hrvQ (mem_inter.2 ⟨hrv, hQ⟩)
      exact hne (mem_singleton.1 this)

lemma disjoint_trim_prefix_suffix {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv)
    (hru : ¬ ru.Nil) (hrv : ¬ rv.Nil) :
    Disjoint
      ((ofWalk ru (isPath_of_factor_left heq)).trimFinish hru).support
      ((ofWalk rv (isPath_of_factor_right heq)).trimStart hrv).support := by
  rw [disjoint_iff_inter_eq_empty]
  ext x
  constructor
  · intro hx
    have hpre := mem_inter.1 hx
    have hruS : x ∈ ru.support.toFinset.erase Q.start := by
      have hsup := support_trimFinish
        (ofWalk ru (isPath_of_factor_left heq)) hru
      simpa [hsup, support_ofWalk, ofWalk_finish] using hpre.1
    have hrvS : x ∈ rv.support.toFinset.erase Q.finish := by
      have hsup := support_trimStart
        (ofWalk rv (isPath_of_factor_right heq)) hrv
      simpa [hsup, support_ofWalk, ofWalk_start] using hpre.2
    have hxru : x ∈ ru.support := List.mem_toFinset.1 (mem_erase.1 hruS).2
    have hxrv : x ∈ rv.support := List.mem_toFinset.1 (mem_erase.1 hrvS).2
    have hxneF : x ≠ Q.finish := (mem_erase.1 hrvS).1
    have hcat := mem_walk_concat_of_subwalk heq
    have hconsR : rv.support = Q.finish :: rv.support.tail :=
      walk_support_eq_cons_of_not_nil hrv
    have htailR : x ∈ rv.support.tail :=
      (List.mem_cons.1 (by rwa [hconsR] at hxrv)).resolve_left hxneF
    have hxP : x ∈ p.walk.support := by
      simpa [hcat] using List.mem_append.2
        (Or.inl (List.mem_append.2 (Or.inl hxru)))
    have hcnt : 2 ≤ p.walk.support.count x := by
      have h1 : 1 ≤ ru.support.count x := List.count_pos_iff.mpr hxru
      have h2 : 1 ≤ rv.support.tail.count x := List.count_pos_iff.mpr htailR
      rw [hcat, List.count_append, List.count_append]
      omega
    have : p.walk.support.count x = 1 :=
      List.count_eq_one_of_mem p.support_nodup hxP
    omega
  · intro hx
    exact (notMem_empty x hx).elim

lemma support_trimFinish_ofWalk {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) (hru : ¬ ru.Nil) :
    ((ofWalk ru (isPath_of_factor_left heq)).trimFinish hru).support =
      ru.support.toFinset.erase Q.start := by
  simpa [support_ofWalk, ofWalk_finish] using
    support_trimFinish (ofWalk ru (isPath_of_factor_left heq)) hru

lemma support_trimStart_ofWalk {p Q : GraphPath G}
    {ru : G.Walk p.start Q.start} {rv : G.Walk Q.finish p.finish}
    (heq : p.walk = (ru.append Q.walk).append rv) (hrv : ¬ rv.Nil) :
    ((ofWalk rv (isPath_of_factor_right heq)).trimStart hrv).support =
      rv.support.toFinset.erase Q.finish := by
  simpa [support_ofWalk, ofWalk_start] using
    support_trimStart (ofWalk rv (isPath_of_factor_right heq)) hrv

lemma erase_eq_empty_of_nil {u v : V} {w : G.Walk u v} (h : w.Nil) :
    w.support.toFinset.erase v = ∅ := by
  have : w.support = [u] := walk_support_eq_singleton_of_nil h
  have hv : v = u := (Walk.Nil.eq h).symm
  simp [this, hv]

/-- Complementary original path of a leftover run of a path that starts in
`A` and is closed by an original edge from finish to start. Both ends lie
in `A`. If the suffix after `Q` is nil, the successor seam is the closing
edge; otherwise it is the original successor of `Q.finish` in `p`. -/
lemma exists_complement_of_leftover {A : Finset V} {p Q : GraphPath G}
    (hs : p.start ∈ A) (hQ : Q ∈ leftoverPieces A p)
    (hclose : G.Adj p.finish p.start) :
    ∃ r : GraphPath G,
      r.support = p.support \ Q.support ∧
        r.start ∈ A ∧ r.finish ∈ A ∧
          G.Adj r.finish Q.start ∧ G.Adj Q.finish r.start := by
  obtain ⟨ru, rv, heq, hruB, hrvB⟩ := leftoverPieces_factor (B := A) p Q hQ
  have hru : ¬ ru.Nil := leftoverPieces_factor_ru_not_nil hs hQ heq
  have hpreA : ru.penultimate ∈ A := hruB.resolve_left hru
  let prefixR := (ofWalk ru (isPath_of_factor_left heq)).trimFinish hru
  have hpreStart : prefixR.start = p.start := rfl
  have hpreFin : prefixR.finish = ru.penultimate := rfl
  have hadjPre : G.Adj prefixR.finish Q.start := ru.adj_penultimate hru
  have hsd := sdiff_eq_prefix_suffix heq
  by_cases hrv : rv.Nil
  · refine ⟨prefixR, ?_, ?_, ?_, hadjPre, ?_⟩
    · have hf : Q.finish = p.finish := Walk.Nil.eq hrv
      have hR : rv.support.toFinset.erase Q.finish = ∅ := by
        simpa [hf] using erase_eq_empty_of_nil hrv
      have hsd' : p.support \ Q.support = ru.support.toFinset.erase Q.start := by
        rw [hsd, hR, union_empty]
      rw [support_trimFinish_ofWalk heq hru]
      exact hsd'.symm
    · simpa [prefixR, hpreStart] using hs
    · simpa [prefixR, hpreFin] using hpreA
    · have hf : Q.finish = p.finish := Walk.Nil.eq hrv
      simpa [prefixR, hpreStart, hf] using hclose
  · have hsucA : rv.snd ∈ A := hrvB.resolve_left hrv
    let suffixR := (ofWalk rv (isPath_of_factor_right heq)).trimStart hrv
    have hdisj : Disjoint suffixR.support prefixR.support := by
      dsimp [suffixR, prefixR]
      exact (disjoint_trim_prefix_suffix heq hru hrv).symm
    have hclose' : G.Adj suffixR.finish prefixR.start := by
      change G.Adj p.finish p.start
      exact hclose
    refine ⟨suffixR.splice prefixR hclose' hdisj, ?_, ?_, ?_, ?_, ?_⟩
    · have hsup :
          (suffixR.splice prefixR hclose' hdisj).support =
            suffixR.support ∪ prefixR.support :=
        support_splice suffixR prefixR hclose' hdisj
      rw [hsup, support_trimStart_ofWalk heq hrv,
        support_trimFinish_ofWalk heq hru, union_comm]
      exact hsd.symm
    · have hst : (suffixR.splice prefixR hclose' hdisj).start = suffixR.start := rfl
      have : suffixR.start = rv.snd := rfl
      simpa [hst, this] using hsucA
    · have hf : (suffixR.splice prefixR hclose' hdisj).finish = prefixR.finish := rfl
      have : prefixR.finish = ru.penultimate := rfl
      simpa [hf, this] using hpreA
    · have hf : (suffixR.splice prefixR hclose' hdisj).finish = prefixR.finish := rfl
      simpa [hf] using hadjPre
    · have hst : (suffixR.splice prefixR hclose' hdisj).start = suffixR.start := rfl
      have : suffixR.start = rv.snd := rfl
      simpa [hst, this] using rv.adj_snd hrv

/-- Opened-cycle leftover cover of `U \ A`. -/
noncomputable def leftoverCoverOfPath (p : GraphPath G) (A : Finset V) :
    PathCover G (p.support \ A) :=
  (PathCover.ofPath p).leftoverCover (B := A)

lemma leftoverCoverOfPath_card (p : GraphPath G) (A : Finset V) :
    (leftoverCoverOfPath p A).card = (leftoverPieces A p).length := by
  simp [leftoverCoverOfPath, PathCover.leftoverCover, PathCover.ofPath,
    PathCover.card, List.length_flatMap]

lemma leftoverCoverOfPath_card_le {p : GraphPath G} {A : Finset V}
    (hs : p.start ∈ A) (hA : A ⊆ p.support) :
    (leftoverCoverOfPath p A).card ≤ A.card := by
  have hlen := leftoverPieces_length_le_of_start_mem (B := A) hs
  have hinter : p.support ∩ A = A := inter_eq_right.2 hA
  simpa [leftoverCoverOfPath_card, hinter] using hlen

lemma leftoverCoverOfPath_paths (p : GraphPath G) (A : Finset V) :
    (leftoverCoverOfPath p A).paths = leftoverPieces A p := by
  simp [leftoverCoverOfPath, PathCover.leftoverCover, PathCover.ofPath]

end GraphPath

namespace Cograph

open Nikoghosyan.GraphPath

lemma toFinset_eq_of_perm {α : Type*} [DecidableEq α] {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : l₁.toFinset = l₂.toFinset := by
  ext x
  simp [List.mem_toFinset, h.mem_iff]

/-- Open the cycle at `x` so that the spanning path plus the original
closing edge recover every edge of the prescribed cycle. -/
lemma exists_spanning_path_from_with_edges (c : GraphCycle G) {x : V}
    (hx : x ∈ c.support) :
    ∃ p : GraphPath G,
      p.support = c.support ∧ p.start = x ∧ G.Adj p.finish x ∧
        (p.walk.edges.toFinset ∪ {s(p.finish, x)}) = c.walk.edges.toFinset := by
  let c' := rotateTo c hx
  have hnil : ¬ c'.walk.Nil := c'.isCycle.not_nil
  obtain ⟨w, hadj, q, hwalk⟩ := (Walk.not_nil_iff.1 hnil)
  have hq : q.IsPath :=
    ((Walk.cons_isCycle_iff q hadj).1 (by simpa [hwalk] using c'.isCycle)).1
  let p0 : GraphPath G := ⟨w, c'.start, q, hq⟩
  have hp0 : p0.support = c'.support := by
    have hstart : c'.start ∈ q.support := Walk.end_mem_support q
    simp [p0, GraphPath.support, GraphCycle.support, hwalk, Walk.support_cons,
      insert_eq_of_mem (List.mem_toFinset.2 hstart)]
  have hx' : c'.start = x := start_rotateTo c hx
  refine ⟨p0.reverse, ?_, ?_, ?_, ?_⟩
  · rw [GraphPath.support_reverse, hp0, support_rotateTo]
  · simp [p0, GraphPath.reverse, hx']
  · simpa [p0, GraphPath.reverse, hx'] using hadj.symm
  · have hqE : p0.reverse.walk.edges.toFinset = q.edges.toFinset := by
      simp [p0, GraphPath.reverse, Walk.edges_reverse, List.toFinset_reverse]
    have hcE : c'.walk.edges.toFinset =
        insert s(c'.start, w) q.edges.toFinset := by
      simp [hwalk, Walk.edges_cons]
    have hfin : p0.reverse.finish = w := by simp [p0, GraphPath.reverse]
    have hedges :
        p0.reverse.walk.edges.toFinset ∪ {s(p0.reverse.finish, x)} =
          c'.walk.edges.toFinset := by
      rw [hqE, hcE, hfin]
      have : s(w, x) = s(c'.start, w) := by
        rw [hx']
        exact Sym2.eq_swap
      rw [this]
      simp [singleton_union]
    have hperm : c'.walk.edges.Perm c.walk.edges :=
      (Walk.rotate_edges c.walk x (mem_walk_support_of_mem_cycle hx)).perm
    rw [hedges]
    simpa [rotateTo] using toFinset_eq_of_perm hperm

/-- Deleting nonempty `A` from a fixed original cycle support yields an
actual leftover path cover of the remainder, of cardinality `≤ |A|`, whose
every path is a contiguous original subwalk of the opened cycle. -/
lemma exists_cycle_leftover_cover {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty) :
    ∃ (p : GraphPath G) (pc : PathCover G (U \ A)),
      p.support = U ∧ p.start ∈ A ∧ G.Adj p.finish p.start ∧
        (p.walk.edges.toFinset ∪ {s(p.finish, p.start)}) = c.walk.edges.toFinset ∧
          pc.card ≤ A.card ∧
            pc.paths = leftoverPieces A p ∧
              ∀ Q ∈ pc.paths, Q.walk.IsSubwalk p.walk := by
  obtain ⟨a, haA⟩ := hAne
  have hx : a ∈ c.support := by simpa [hc] using hA haA
  obtain ⟨p, hp, hs, hadj, hedges⟩ := exists_spanning_path_from_with_edges c hx
  have hpU : p.support = U := hp.trans hc
  have hstartA : p.start ∈ A := by simpa [hs] using haA
  have hAU : A ⊆ p.support := by simpa [hpU] using hA
  let pc0 := leftoverCoverOfPath p A
  have hEq : p.support \ A = U \ A := by rw [hpU]
  refine ⟨p, pc0.cast hEq, hpU, hstartA, by simpa [hs] using hadj, ?_, ?_, ?_, ?_⟩
  · simpa [hs] using hedges
  · have := leftoverCoverOfPath_card_le hstartA hAU
    simpa [PathCover.cast_card] using this
  · rw [PathCover.cast_paths, leftoverCoverOfPath_paths]
  · intro Q hQ
    have hQ' : Q ∈ leftoverPieces A p := by
      rwa [PathCover.cast_paths, leftoverCoverOfPath_paths] at hQ
    exact leftoverPieces_isSubwalk p Q hQ'

/-- Under saturation the leftover cover is a minimum cover of `U \ A`. -/
lemma cycle_leftover_cover_min_of_saturated {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hSat : Saturated (G := G) U A) :
    ∃ (p : GraphPath G) (pc : PathCover G (U \ A)),
      p.support = U ∧ p.start ∈ A ∧ G.Adj p.finish p.start ∧
        (p.walk.edges.toFinset ∪ {s(p.finish, p.start)}) = c.walk.edges.toFinset ∧
          pc.card = pathCoverNumber G (U \ A) ∧
            pc.paths = leftoverPieces A p ∧
              ∀ Q ∈ pc.paths, Q.walk.IsSubwalk p.walk := by
  obtain ⟨p, pc, hp, hs, hadj, hedges, hcard, hpaths, hsub⟩ :=
    exists_cycle_leftover_cover c hc hA hAne
  have hmin : pc.card = pathCoverNumber G (U \ A) := by
    have hle := pathCoverNumber_le (G := G) pc
    have hSat' : pathCoverNumber G (U \ A) = A.card := hSat
    exact le_antisymm (hcard.trans (le_of_eq hSat'.symm)) hle
  exact ⟨p, pc, hp, hs, hadj, hedges, hmin, hpaths, hsub⟩

/-- From a leftover run of an opened original cycle, the complementary
original path spans `U \ Q.support`, both ends lie in `A`, and both seams
to `Q.start` / `Q.finish` are original edges of that opened path plus
closing edge. -/
lemma exists_complement_arc_of_mem_leftover {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    {p : GraphPath G} {pc : PathCover G (U \ A)} {Q : GraphPath G}
    (hp : p.support = U) (hs : p.start ∈ A) (hclose : G.Adj p.finish p.start)
    (hpaths : pc.paths = leftoverPieces A p) (hQ : Q ∈ pc.paths) :
    ∃ r : GraphPath G,
      r.support = U \ Q.support ∧
        r.start ∈ A ∧ r.finish ∈ A ∧
          G.Adj r.finish Q.start ∧ G.Adj Q.finish r.start := by
  have hQ' : Q ∈ leftoverPieces A p := by simpa [hpaths] using hQ
  obtain ⟨r, hr, hrs, hrf, hpred, hsucc⟩ :=
    exists_complement_of_leftover (A := A) hs hQ' hclose
  exact ⟨r, by simpa [hp] using hr, hrs, hrf, hpred, hsucc⟩

end Cograph

end Nikoghosyan
