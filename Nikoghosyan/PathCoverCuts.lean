import Nikoghosyan.CycleAssembly

/-!
Generic path-cover deletion / cut bounds, and the distinct-path / spanning-path
endpoint relations `D(U)` and `R(U)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

lemma mem_walk_support {p : GraphPath G} {x : V} :
    x ∈ p.support ↔ x ∈ p.walk.support := by
  simp [support]

def takeUntil (p : GraphPath G) {x : V} (hx : x ∈ p.support) : GraphPath G where
  start := p.start
  finish := x
  walk := p.walk.takeUntil x (mem_walk_support.1 hx)
  isPath := p.isPath.takeUntil _

def dropUntil (p : GraphPath G) {x : V} (hx : x ∈ p.support) : GraphPath G where
  start := x
  finish := p.finish
  walk := p.walk.dropUntil x (mem_walk_support.1 hx)
  isPath := p.isPath.dropUntil _

lemma takeUntil_nil_iff (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.takeUntil hx).walk.Nil ↔ x = p.start := by
  rw [takeUntil, Walk.nil_takeUntil, eq_comm]

lemma dropUntil_nil_iff :
    ∀ (p : GraphPath G) {x : V} (hx : x ∈ p.support),
      (p.dropUntil hx).walk.Nil ↔ x = p.finish := by
  intro p x hx
  constructor
  · intro h
    exact Walk.Nil.eq h
  · intro h
    subst h
    exact (Walk.isPath_iff_nil).1 (p.dropUntil hx).isPath

lemma support_takeUntil_union_dropUntil (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.takeUntil hx).support ∪ (p.dropUntil hx).support = p.support := by
  have hx' := mem_walk_support.1 hx
  ext y
  simp [support, takeUntil, dropUntil, List.mem_toFinset]
  have happ :=
    Walk.mem_support_append_iff (t := y) (p.walk.takeUntil x hx') (p.walk.dropUntil x hx')
  have hspec := Walk.take_spec p.walk hx'
  simpa [hspec] using happ.symm

lemma nil_iff_start_eq_finish (p : GraphPath G) :
    p.walk.Nil ↔ p.start = p.finish :=
  p.isPath.nil_iff_eq

lemma support_eq_singleton_of_nil (p : GraphPath G) (h : p.walk.Nil) :
    p.support = {p.start} := by
  have hlen : p.walk.length = 0 := (Walk.length_eq_zero_iff).2 h
  have hcard : p.support.card = 1 := by
    rw [card_support, hlen]
  obtain ⟨z, hz⟩ := card_eq_one.mp hcard
  have : z = p.start := by
    have hmem := p.start_mem_support
    rw [hz] at hmem
    exact (mem_singleton.1 hmem).symm
  simp [hz, this]

/-- Drop the first vertex of a nonsingleton original-edge path. -/
def trimStart (p : GraphPath G) (h : ¬ p.walk.Nil) : GraphPath G where
  start := p.walk.snd
  finish := p.finish
  walk := p.walk.tail
  isPath := p.isPath.tail

/-- Drop the last vertex of a nonsingleton original-edge path. -/
def trimFinish (p : GraphPath G) (h : ¬ p.walk.Nil) : GraphPath G where
  start := p.start
  finish := p.walk.penultimate
  walk := p.walk.dropLast
  isPath := p.isPath.dropLast

lemma support_trimStart (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).support = p.support.erase p.start := by
  have htail : p.walk.tail.support = p.walk.support.tail :=
    Walk.support_tail_of_not_nil p.walk h
  have hcons : p.start :: p.walk.support.tail = p.walk.support := by
    simpa [htail] using Walk.cons_support_tail (p := p.walk) h
  have hnin : p.start ∉ p.walk.support.tail := by
    have hnodup := p.support_nodup
    rw [← hcons] at hnodup
    exact (List.nodup_cons.1 hnodup).1
  ext y
  simp [trimStart, support, htail, mem_erase, List.mem_toFinset]
  constructor
  · intro hy
    exact ⟨fun hxy => hnin (hxy ▸ hy), List.mem_of_mem_tail hy⟩
  · intro ⟨hyne, hy⟩
    have : y ∈ p.start :: p.walk.support.tail := by simpa [hcons] using hy
    exact (List.mem_cons.1 this).resolve_left hyne

lemma support_trimFinish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimFinish h).support = p.support.erase p.finish := by
  have hdl : p.walk.dropLast.support = p.walk.support.dropLast :=
    Walk.support_dropLast (p := p.walk) h
  have hcat : p.walk.support.dropLast ++ [p.finish] = p.walk.support := by
    simpa [hdl] using Walk.support_dropLast_concat (p := p.walk) h
  have hnin : p.finish ∉ p.walk.support.dropLast := by
    intro hmem
    have hnodup := p.support_nodup
    rw [← hcat] at hnodup
    have hcnt : 2 ≤ (p.walk.support.dropLast ++ [p.finish]).count p.finish := by
      have h1 : 1 ≤ p.walk.support.dropLast.count p.finish :=
        List.count_pos_iff.mpr hmem
      have h2 : ([p.finish] : List V).count p.finish = 1 := by simp
      rw [List.count_append, h2]
      omega
    have : (p.walk.support.dropLast ++ [p.finish]).count p.finish = 1 :=
      List.count_eq_one_of_mem hnodup (by simp)
    omega
  ext y
  simp [trimFinish, support, hdl, mem_erase, List.mem_toFinset]
  constructor
  · intro hy
    refine ⟨fun hxy => hnin (hxy ▸ hy), ?_⟩
    have : y ∈ p.walk.support.dropLast ++ [p.finish] := List.mem_append_left _ hy
    simpa [hcat] using this
  · intro ⟨hyne, hy⟩
    have : y ∈ p.walk.support.dropLast ++ [p.finish] := by simpa [hcat] using hy
    exact (List.mem_append.1 this).resolve_right (by simp [hyne])

lemma trimStart_finish (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).finish = p.finish :=
  rfl

lemma trimFinish_start (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimFinish h).start = p.start :=
  rfl

/-- Delete one vertex from a single original-edge path: keep the path if the
vertex is absent, drop a singleton, trim an endpoint, or split an internal
vertex into two nonempty original-edge pieces. -/
noncomputable def deleteVertex (p : GraphPath G) (x : V) : List (GraphPath G) :=
  if hx : x ∈ p.support then
    if hnil : p.walk.Nil then
      []
    else if hs : x = p.start then
      [p.trimStart hnil]
    else if hf : x = p.finish then
      [p.trimFinish hnil]
    else
      [(p.takeUntil hx).trimFinish (fun hnil' => hs ((takeUntil_nil_iff p hx).1 hnil')),
        (p.dropUntil hx).trimStart (fun hnil' => hf ((dropUntil_nil_iff p hx).1 hnil'))]
  else
    [p]

lemma length_deleteVertex_le (p : GraphPath G) (x : V) :
    (p.deleteVertex x).length ≤ 2 := by
  unfold deleteVertex
  split_ifs <;> simp

lemma length_deleteVertex_eq_one_of_not_mem (p : GraphPath G) {x : V}
    (hx : x ∉ p.support) :
    (p.deleteVertex x).length = 1 := by
  simp [deleteVertex, hx]

lemma length_deleteVertex_le_one_of_endpoint (p : GraphPath G) {x : V}
    (h : x = p.start ∨ x = p.finish) :
    (p.deleteVertex x).length ≤ 1 := by
  rcases h with h | h
  · simp [deleteVertex, h, start_mem_support]
    split_ifs <;> simp
  · simp [deleteVertex, h, finish_mem_support]
    split_ifs <;> simp

lemma not_nil_of_internal {p : GraphPath G} {x : V}
    (hx : x ∈ p.support) (hs : x ≠ p.start) : ¬ p.walk.Nil := by
  intro h
  have : x = p.start := by
    simpa [support_eq_singleton_of_nil p h] using hx
  exact hs this

lemma length_deleteVertex_eq_two_of_internal (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hs : x ≠ p.start) (hf : x ≠ p.finish) :
    (p.deleteVertex x).length = 2 := by
  have hnil : ¬ p.walk.Nil := not_nil_of_internal hx hs
  simp [deleteVertex, hx, hnil, hs, hf]

lemma inter_support_takeUntil_dropUntil_subset (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) :
    (p.takeUntil hx).support ∩ (p.dropUntil hx).support ⊆ {x} := by
  intro y hy
  have hx' := mem_walk_support.1 hx
  have hyL : y ∈ (p.walk.takeUntil x hx').support := by
    simpa [takeUntil, support, List.mem_toFinset] using (mem_inter.1 hy).1
  have hyR : y ∈ (p.walk.dropUntil x hx').support := by
    simpa [dropUntil, support, List.mem_toFinset] using (mem_inter.1 hy).2
  by_cases hnilR : (p.walk.dropUntil x hx').Nil
  · have : (p.dropUntil hx).support = {x} := by
      have := support_eq_singleton_of_nil (p.dropUntil hx) (by simpa [dropUntil] using hnilR)
      simpa [dropUntil] using this
    have : y = x := by
      have hyR' := (mem_inter.1 hy).2
      simpa [this] using hyR'
    simp [this]
  · have htail :
        (p.walk.dropUntil x hx').tail.support = (p.walk.dropUntil x hx').support.tail :=
      Walk.support_tail_of_not_nil _ hnilR
    have hcons :
        x :: (p.walk.dropUntil x hx').support.tail = (p.walk.dropUntil x hx').support := by
      simpa [htail] using Walk.cons_support_tail (p := p.walk.dropUntil x hx') hnilR
    have happend :
        (p.walk.takeUntil x hx').support ++ (p.walk.dropUntil x hx').support.tail =
          p.walk.support := by
      rw [← Walk.support_append, Walk.take_spec]
    by_cases hyx : y = x
    · simp [hyx]
    · have hyTail : y ∈ (p.walk.dropUntil x hx').support.tail := by
        have : y ∈ x :: (p.walk.dropUntil x hx').support.tail := by
          simpa [hcons] using hyR
        exact (List.mem_cons.1 this).resolve_left hyx
      have hyP : y ∈ p.walk.support := by
        rw [← happend]
        exact List.mem_append.2 (.inl hyL)
      have hcnt : p.walk.support.count y = 1 :=
        List.count_eq_one_of_mem p.support_nodup hyP
      rw [← happend, List.count_append] at hcnt
      have h1 : 1 ≤ (p.walk.takeUntil x hx').support.count y :=
        List.count_pos_iff.mpr hyL
      have h2 : 1 ≤ (p.walk.dropUntil x hx').support.tail.count y :=
        List.count_pos_iff.mpr hyTail
      omega

lemma disjoint_internal_pieces (p : GraphPath G) {x : V} (hx : x ∈ p.support)
    (hs : x ≠ p.start) (hf : x ≠ p.finish) :
    Disjoint
      ((p.takeUntil hx).trimFinish
        (fun hnil => hs ((takeUntil_nil_iff p hx).1 hnil))).support
      ((p.dropUntil hx).trimStart
        (fun hnil => hf ((dropUntil_nil_iff p hx).1 hnil))).support := by
  have hL : ¬ (p.takeUntil hx).walk.Nil := fun hnil =>
    hs ((takeUntil_nil_iff p hx).1 hnil)
  have hR : ¬ (p.dropUntil hx).walk.Nil := fun hnil =>
    hf ((dropUntil_nil_iff p hx).1 hnil)
  rw [support_trimFinish (p.takeUntil hx) hL, support_trimStart (p.dropUntil hx) hR]
  change Disjoint ((p.takeUntil hx).support.erase x) ((p.dropUntil hx).support.erase x)
  rw [disjoint_iff_inter_eq_empty]
  ext y
  simp [mem_erase]
  intro hyA hyx hyB
  have hy : y ∈ (p.takeUntil hx).support ∩ (p.dropUntil hx).support :=
    mem_inter.2 ⟨hyA, hyB⟩
  have : y ∈ ({x} : Finset V) :=
    inter_support_takeUntil_dropUntil_subset p hx hy
  exact hyx (mem_singleton.1 this)

lemma union_internal_pieces (p : GraphPath G) {x : V} (hx : x ∈ p.support)
    (hs : x ≠ p.start) (hf : x ≠ p.finish) :
    ((p.takeUntil hx).trimFinish
        (fun hnil => hs ((takeUntil_nil_iff p hx).1 hnil))).support ∪
      ((p.dropUntil hx).trimStart
        (fun hnil => hf ((dropUntil_nil_iff p hx).1 hnil))).support =
      p.support.erase x := by
  have hL : ¬ (p.takeUntil hx).walk.Nil := fun hnil =>
    hs ((takeUntil_nil_iff p hx).1 hnil)
  have hR : ¬ (p.dropUntil hx).walk.Nil := fun hnil =>
    hf ((dropUntil_nil_iff p hx).1 hnil)
  rw [support_trimFinish (p.takeUntil hx) hL, support_trimStart (p.dropUntil hx) hR]
  change (p.takeUntil hx).support.erase x ∪ (p.dropUntil hx).support.erase x =
    p.support.erase x
  rw [← erase_union_distrib, support_takeUntil_union_dropUntil]

lemma mem_deleteVertex_support_iff (p : GraphPath G) (x y : V) :
    (∃ q ∈ p.deleteVertex x, y ∈ q.support) ↔ y ∈ p.support.erase x := by
  constructor
  · intro ⟨q, hq, hy⟩
    unfold deleteVertex at hq
    split_ifs at hq with hx hnil hs hf
    · cases hq
    · simp only [List.mem_singleton] at hq
      subst hq
      simpa [support_trimStart, hs] using hy
    · simp only [List.mem_singleton] at hq
      subst hq
      simpa [support_trimFinish, hf] using hy
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl
      · have thisEq := union_internal_pieces p hx hs hf
        have hy' :
            y ∈ ((p.takeUntil hx).trimFinish
              (fun hnil => hs ((takeUntil_nil_iff p hx).1 hnil))).support ∪
              ((p.dropUntil hx).trimStart
                (fun hnil => hf ((dropUntil_nil_iff p hx).1 hnil))).support :=
          mem_union.2 (.inl hy)
        simpa [thisEq] using hy'
      · have thisEq := union_internal_pieces p hx hs hf
        have hy' :
            y ∈ ((p.takeUntil hx).trimFinish
              (fun hnil => hs ((takeUntil_nil_iff p hx).1 hnil))).support ∪
              ((p.dropUntil hx).trimStart
                (fun hnil => hf ((dropUntil_nil_iff p hx).1 hnil))).support :=
          mem_union.2 (.inr hy)
        simpa [thisEq] using hy'
    · simp only [List.mem_singleton] at hq
      subst hq
      exact mem_erase.2 ⟨fun hxy => hx (hxy ▸ hy), hy⟩
  · intro hy
    unfold deleteVertex
    split_ifs with hx hnil hs hf
    · have : p.support = {x} := by
        have := support_eq_singleton_of_nil p hnil
        have hx' : x = p.start := by simpa [this] using hx
        simp [this, hx']
      rw [this] at hy
      simp at hy
    · refine ⟨p.trimStart hnil, by simp, ?_⟩
      simpa [support_trimStart, hs, mem_erase] using hy
    · refine ⟨p.trimFinish hnil, by simp, ?_⟩
      simpa [support_trimFinish, hf, mem_erase] using hy
    · have hL := union_internal_pieces p hx hs hf
      have : y ∈
          ((p.takeUntil hx).trimFinish
            (fun hnil => hs ((takeUntil_nil_iff p hx).1 hnil))).support ∪
          ((p.dropUntil hx).trimStart
            (fun hnil => hf ((dropUntil_nil_iff p hx).1 hnil))).support := by
        simpa [hL] using hy
      rcases mem_union.1 this with h | h
      · exact ⟨_, by simp, h⟩
      · exact ⟨_, by simp, h⟩
    · refine ⟨p, by simp, ?_⟩
      exact (mem_erase.1 hy).2

lemma support_subset_of_mem_deleteVertex {p : GraphPath G} {x : V} {q : GraphPath G}
    (hq : q ∈ p.deleteVertex x) : q.support ⊆ p.support := by
  intro y hy
  have : y ∈ p.support.erase x := (mem_deleteVertex_support_iff p x y).1 ⟨q, hq, hy⟩
  exact mem_of_mem_erase this

lemma pairwise_deleteVertex (p : GraphPath G) (x : V) :
    (p.deleteVertex x).Pairwise fun q r => Disjoint q.support r.support := by
  unfold deleteVertex
  split_ifs with hx hnil hs hf
  · simp
  · simp
  · simp
  · simp [List.pairwise_cons, disjoint_internal_pieces p hx hs hf]
  · simp

lemma exists_mem_deleteVertex_endpoint (p : GraphPath G) {x y : V}
    (hy : y = p.start ∨ y = p.finish) (hne : y ≠ x) :
    ∃ q ∈ p.deleteVertex x, y = q.start ∨ y = q.finish := by
  unfold deleteVertex
  split_ifs with hx hnil hs hf
  · have hy' : y = p.start := by
      have heq : p.start = p.finish := (nil_iff_start_eq_finish p).1 hnil
      rcases hy with hy | hy
      · exact hy
      · exact hy.trans heq.symm
    have hx' : x = p.start := by
      simpa [support_eq_singleton_of_nil p hnil] using hx
    exact (hne (hy'.trans hx'.symm)).elim
  · refine ⟨p.trimStart hnil, by simp, ?_⟩
    rcases hy with hy | hy
    · exact (hne (hy.trans hs.symm)).elim
    · exact .inr (hy.trans (trimStart_finish p hnil).symm)
  · refine ⟨p.trimFinish hnil, by simp, ?_⟩
    rcases hy with hy | hy
    · exact .inl (hy.trans (trimFinish_start p hnil).symm)
    · exact (hne (hy.trans hf.symm)).elim
  · rcases hy with hy | hy
    · refine ⟨(p.takeUntil hx).trimFinish
        (fun hnil => hs ((takeUntil_nil_iff p hx).1 hnil)), by simp, ?_⟩
      exact .inl (hy.trans (trimFinish_start (p.takeUntil hx)
        (fun hnil => hs ((takeUntil_nil_iff p hx).1 hnil))).symm)
    · refine ⟨(p.dropUntil hx).trimStart
        (fun hnil => hf ((dropUntil_nil_iff p hx).1 hnil)), by simp, ?_⟩
      exact .inr (hy.trans (trimStart_finish (p.dropUntil hx)
        (fun hnil => hf ((dropUntil_nil_iff p hx).1 hnil))).symm)
  · exact ⟨p, by simp, hy⟩

end GraphPath

/-- Distinct-path compatibility: endpoints of two different paths in one
common minimum cover. The paper graph `D(U)`, totalized on all of `V`. -/
def DistinctPathCompatible (U : Finset V) (x y : V) : Prop :=
  x ≠ y ∧
    ∃ pc : PathCover G U, pc.card = pathCoverNumber G U ∧
      ∃ p ∈ pc.paths, ∃ q ∈ pc.paths, p ≠ q ∧
        (x = p.start ∨ x = p.finish) ∧ (y = q.start ∨ y = q.finish)

def distinctPathGraph (U : Finset V) : SimpleGraph V where
  Adj := DistinctPathCompatible (G := G) U
  symm := ⟨fun a b h =>
    ⟨h.1.symm,
      let ⟨pc, hpc, p, hp, q, hq, hne, hx, hy⟩ := h.2
      ⟨pc, hpc, q, hq, p, hp, hne.symm, hy, hx⟩⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

lemma distinctPathGraph_eq_bot_of_pathCoverNumber_le_one {U : Finset V}
    (h : pathCoverNumber G U ≤ 1) : distinctPathGraph (G := G) U = ⊥ := by
  ext x y
  constructor
  · intro hAdj
    obtain ⟨pc, hpc, p, hp, q, hq, hne, _, _⟩ := hAdj.2
    have hlen : pc.paths.length ≤ 1 := by
      have : pc.card ≤ 1 := hpc ▸ h
      simpa [PathCover.card] using this
    have : p = q := by
      match hps : pc.paths with
      | [] =>
        simp [hps] at hp
      | [r] =>
        simp [hps] at hp hq
        simp [hp, hq]
      | r₁ :: r₂ :: rest =>
        have : pc.paths.length ≥ 2 := by simp [hps]
        omega
    exact (hne this).elim
  · intro hAdj
    cases hAdj

/-- Spanning-path compatibility on an induced set `U`: the paper graph `R(U)`. -/
def SpanningPathCompatible (U : Finset V) (x y : V) : Prop :=
  x ≠ y ∧ ∃ p : GraphPath G, p.support = U ∧
    ((p.start = x ∧ p.finish = y) ∨ (p.start = y ∧ p.finish = x))

def spanningPathGraph (U : Finset V) : SimpleGraph V where
  Adj := SpanningPathCompatible (G := G) U
  symm := ⟨fun a b h =>
    ⟨h.1.symm,
      let ⟨p, hp, hends⟩ := h.2
      ⟨p, hp, hends.symm⟩⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

lemma spanningPathGraph_eq_bot_of_card_le_one {U : Finset V} (hU : U.card ≤ 1) :
    spanningPathGraph (G := G) U = ⊥ := by
  ext x y
  constructor
  · intro hAdj
    obtain ⟨p, hp, hends⟩ := hAdj.2
    have hsf : p.start ≠ p.finish := by
      rcases hends with ⟨hs, hf⟩ | ⟨hs, hf⟩
      · rw [hs, hf]; exact hAdj.1
      · rw [hs, hf]; exact hAdj.1.symm
    have h2 : 2 ≤ p.support.card := by
      have hs : p.start ∈ p.support := p.start_mem_support
      have hf : p.finish ∈ p.support := p.finish_mem_support
      have : ({p.start, p.finish} : Finset V) ⊆ p.support := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hcard : ({p.start, p.finish} : Finset V).card = 2 := by
        simp [card_insert_of_notMem, hsf]
      exact hcard.symm.trans_le (card_le_card this)
    have : 2 ≤ U.card := by simpa [hp] using h2
    omega
  · intro hAdj
    cases hAdj

lemma componentCount_le_pathCover_card {U : Finset V} (pc : PathCover G U) :
    componentCount G U ≤ pc.card := by
  let f : Fin pc.paths.length → (G.induce (U : Set V)).ConnectedComponent := fun i =>
    (G.induce (U : Set V)).connectedComponentMk
      ⟨(pc.paths.get i).start,
        pc.support_subset (List.mem_iff_get.2 ⟨i, rfl⟩) (pc.paths.get i).start_mem_support⟩
  have hf : Function.Surjective f := by
    intro C
    refine C.ind fun x => ?_
    obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x.1).1 x.2
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hp
    refine ⟨i, ConnectedComponent.sound ?_⟩
    have hsupp : p.support ⊆ U := pc.support_subset hp
    have hxsup : x.1 ∈ p.walk.support := GraphPath.mem_walk_support.1 hxp
    let w := p.walk.takeUntil x.1 hxsup
    have hwU : ∀ a ∈ w.support, a ∈ (U : Set V) := fun a ha =>
      hsupp (List.mem_toFinset.2 (Walk.support_takeUntil_subset_support p.walk hxsup ha))
    have hR : (G.induce (U : Set V)).Reachable
        ⟨p.start, hsupp p.start_mem_support⟩ x :=
      ⟨w.induce (U : Set V) hwU⟩
    have heq :
        (⟨(pc.paths.get i).start,
            pc.support_subset (List.mem_iff_get.2 ⟨i, rfl⟩)
              (pc.paths.get i).start_mem_support⟩ : (U : Set V)) =
          ⟨p.start, hsupp p.start_mem_support⟩ :=
      Subtype.ext (congrArg GraphPath.start hi)
    rw [heq]
    exact hR
  haveI : Fintype (G.induce (U : Set V)).ConnectedComponent := inferInstance
  simpa [componentCount, PathCover.card, Nat.card_eq_fintype_card, Fintype.card_fin] using
    Nat.card_le_card_of_surjective f hf

lemma componentCount_le_pathCoverNumber (U : Finset V) :
    componentCount G U ≤ pathCoverNumber G U := by
  obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
  simpa [hpc] using componentCount_le_pathCover_card pc

namespace PathCover

lemma pairwise_disjoint_of_mem {l : List (GraphPath G)}
    (h : l.Pairwise fun p q => Disjoint p.support q.support)
    {p q : GraphPath G} (hp : p ∈ l) (hq : q ∈ l) (hne : p ≠ q) :
    Disjoint p.support q.support := by
  induction l with
  | nil => cases hp
  | cons a l ih =>
    have h' := List.pairwise_cons.mp h
    simp only [List.mem_cons] at hp hq
    rcases hp with rfl | hp
    · rcases hq with rfl | hq
      · exact (hne rfl).elim
      · exact h'.1 q hq
    · rcases hq with rfl | hq
      · exact (h'.1 p hp).symm
      · exact ih h'.2 hp hq

lemma length_flatMap_deleteVertex_eq_of_forall_not_mem
    (l : List (GraphPath G)) (x : V)
    (h : ∀ p ∈ l, x ∉ p.support) :
    (l.flatMap fun p => p.deleteVertex x).length = l.length := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    have hp : x ∉ p.support := h p (by simp)
    have hps : ∀ q ∈ ps, x ∉ q.support := fun q hq =>
      h q (by simp [hq])
    simp [List.flatMap_cons, List.length_append, Nat.add_comm,
      GraphPath.length_deleteVertex_eq_one_of_not_mem p hp, ih hps]

lemma length_flatMap_deleteVertex_le {l : List (GraphPath G)} (x : V)
    (h : l.Pairwise fun p q => Disjoint p.support q.support) :
    (l.flatMap fun p => p.deleteVertex x).length ≤ l.length + 1 := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    have h' := List.pairwise_cons.mp h
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    by_cases hx : x ∈ p.support
    · have hps : ∀ q ∈ ps, x ∉ q.support := by
        intro q hq hxq
        exact (disjoint_left.1 (h'.1 q hq) hx hxq).elim
      have hpslen :
          (ps.flatMap fun q => q.deleteVertex x).length = ps.length :=
        length_flatMap_deleteVertex_eq_of_forall_not_mem ps x hps
      have : (p.deleteVertex x).length ≤ 2 := GraphPath.length_deleteVertex_le p x
      omega
    · have hp : (p.deleteVertex x).length = 1 :=
        GraphPath.length_deleteVertex_eq_one_of_not_mem p hx
      have : (ps.flatMap fun q => q.deleteVertex x).length ≤ ps.length + 1 :=
        ih h'.2
      omega

lemma length_flatMap_deleteVertex_le_of_endpoint {l : List (GraphPath G)} {x : V}
    (h : l.Pairwise fun p q => Disjoint p.support q.support)
    (hep : ∃ p ∈ l, x = p.start ∨ x = p.finish) :
    (l.flatMap fun p => p.deleteVertex x).length ≤ l.length := by
  induction l with
  | nil =>
    rcases hep with ⟨_, hnil, _⟩
    cases hnil
  | cons p ps ih =>
    have h' := List.pairwise_cons.mp h
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    rcases hep with ⟨q, hq, hxend⟩
    simp only [List.mem_cons] at hq
    rcases hq with hqp | hq
    · have hlen : (q.deleteVertex x).length ≤ 1 :=
        GraphPath.length_deleteVertex_le_one_of_endpoint q hxend
      have hxsup : x ∈ p.support := by
        rcases hxend with hxs | hxf
        · simpa [hqp, hxs] using q.start_mem_support
        · simpa [hqp, hxf] using q.finish_mem_support
      have hps : ∀ r ∈ ps, x ∉ r.support := by
        intro r hr hxr
        exact (disjoint_left.1 (h'.1 r hr) hxsup hxr).elim
      have hpslen :
          (ps.flatMap fun r => r.deleteVertex x).length = ps.length :=
        length_flatMap_deleteVertex_eq_of_forall_not_mem ps x hps
      have : (p.deleteVertex x).length ≤ 1 := by simpa [hqp] using hlen
      omega
    · have hxnp : x ∉ p.support := by
        intro hxp
        have hxq : x ∈ q.support := by
          rcases hxend with rfl | rfl
          · exact q.start_mem_support
          · exact q.finish_mem_support
        exact (disjoint_left.1 (h'.1 q hq) hxp hxq).elim
      have hp : (p.deleteVertex x).length = 1 :=
        GraphPath.length_deleteVertex_eq_one_of_not_mem p hxnp
      have : (ps.flatMap fun r => r.deleteVertex x).length ≤ ps.length :=
        ih h'.2 ⟨q, hq, hxend⟩
      omega

lemma pairwise_flatMap_deleteVertex {l : List (GraphPath G)} (x : V)
    (h : l.Pairwise fun p q => Disjoint p.support q.support) :
    (l.flatMap fun p => p.deleteVertex x).Pairwise
      fun a b => Disjoint a.support b.support := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    have h' := List.pairwise_cons.mp h
    rw [List.flatMap_cons]
    refine List.pairwise_append.mpr ⟨GraphPath.pairwise_deleteVertex p x, ih h'.2, ?_⟩
    intro a ha b hb
    obtain ⟨q, hq, hbq⟩ := List.mem_flatMap.mp hb
    have da := GraphPath.support_subset_of_mem_deleteVertex ha
    have db := GraphPath.support_subset_of_mem_deleteVertex hbq
    exact (h'.1 q hq).mono da db

/-- Rebuild a path cover after deleting one original vertex. Other paths
are unchanged; the unique path through `x`, if any, is replaced by the
zero, one or two pieces of `GraphPath.deleteVertex`. -/
noncomputable def deleteVertex {U : Finset V} (pc : PathCover G U) (x : V) :
    PathCover G (U.erase x) where
  paths := pc.paths.flatMap fun p => GraphPath.deleteVertex p x
  disjoint := pairwise_flatMap_deleteVertex x pc.disjoint
  mem_iff := by
    intro y
    constructor
    · intro hy
      have hyU : y ∈ U := mem_of_mem_erase hy
      have hyx : y ≠ x := ne_of_mem_erase hy
      obtain ⟨p, hp, hyp⟩ := (pc.mem_iff y).1 hyU
      obtain ⟨q, hq, hyq⟩ :=
        (GraphPath.mem_deleteVertex_support_iff p x y).2 (mem_erase.2 ⟨hyx, hyp⟩)
      exact ⟨q, List.mem_flatMap.2 ⟨p, hp, hq⟩, hyq⟩
    · intro ⟨q, hq, hyq⟩
      obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.1 hq
      have hy' : y ∈ p.support.erase x :=
        (GraphPath.mem_deleteVertex_support_iff p x y).1 ⟨q, hqp, hyq⟩
      refine mem_erase.2 ⟨(mem_erase.1 hy').1, (pc.mem_iff y).2 ⟨p, hp, (mem_erase.1 hy').2⟩⟩

lemma card_deleteVertex_le {U : Finset V} (pc : PathCover G U) (x : V) :
    (pc.deleteVertex x).card ≤ pc.card + 1 := by
  simpa [deleteVertex, card] using length_flatMap_deleteVertex_le x pc.disjoint

/-- `x` is an endpoint of some path of this (not necessarily minimum) cover. -/
def IsEndpoint {U : Finset V} (pc : PathCover G U) (x : V) : Prop :=
  ∃ p ∈ pc.paths, x = p.start ∨ x = p.finish

lemma card_deleteVertex_le_of_endpoint {U : Finset V} (pc : PathCover G U)
    {x : V} (h : pc.IsEndpoint x) :
    (pc.deleteVertex x).card ≤ pc.card := by
  simpa [deleteVertex, card] using
    length_flatMap_deleteVertex_le_of_endpoint pc.disjoint h

lemma length_flatMap_deleteVertex_eq_add_one_of_internal
    {l : List (GraphPath G)} {x : V}
    (h : l.Pairwise fun p q => Disjoint p.support q.support)
    {p : GraphPath G} (hp : p ∈ l)
    (hx : x ∈ p.support) (hs : x ≠ p.start) (hf : x ≠ p.finish) :
    (l.flatMap fun q => GraphPath.deleteVertex q x).length = l.length + 1 := by
  induction l with
  | nil => cases hp
  | cons a ps ih =>
    have h' := List.pairwise_cons.mp h
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    simp only [List.mem_cons] at hp
    rcases hp with hap | hp
    · have hlen : (GraphPath.deleteVertex a x).length = 2 := by
        simpa [hap] using GraphPath.length_deleteVertex_eq_two_of_internal p hx hs hf
      have hps : ∀ r ∈ ps, x ∉ r.support := by
        intro r hr hxr
        have hxsup : x ∈ a.support := by simpa [hap] using hx
        exact (disjoint_left.1 (h'.1 r hr) hxsup hxr).elim
      have hpslen :
          (ps.flatMap fun r => GraphPath.deleteVertex r x).length = ps.length :=
        length_flatMap_deleteVertex_eq_of_forall_not_mem ps x hps
      omega
    · have hxna : x ∉ a.support := by
        intro hxa
        exact (disjoint_left.1 (h'.1 p hp) hxa hx).elim
      have ha : (GraphPath.deleteVertex a x).length = 1 :=
        GraphPath.length_deleteVertex_eq_one_of_not_mem a hxna
      have : (ps.flatMap fun r => GraphPath.deleteVertex r x).length =
          ps.length + 1 := ih h'.2 hp
      omega

/-- If `x` lies on a path of this cover but is not an endpoint of that path,
deletion splits that unique path into two pieces and increases the cover
cardinality by exactly one. -/
lemma card_deleteVertex_eq_add_one_of_internal {U : Finset V}
    (pc : PathCover G U) {x : V} (hx : x ∈ U)
    (h : ∀ p ∈ pc.paths, x ≠ p.start ∧ x ≠ p.finish) :
    (pc.deleteVertex x).card = pc.card + 1 := by
  obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hx
  have hs := (h p hp).1
  have hf := (h p hp).2
  simpa [deleteVertex, card] using
    length_flatMap_deleteVertex_eq_add_one_of_internal pc.disjoint hp hxp hs hf

lemma IsEndpoint_deleteVertex {U : Finset V} (pc : PathCover G U) {x y : V}
    (hy : pc.IsEndpoint y) (hne : y ≠ x) :
    (pc.deleteVertex x).IsEndpoint y := by
  obtain ⟨p, hp, hyend⟩ := hy
  obtain ⟨q, hq, hqend⟩ := GraphPath.exists_mem_deleteVertex_endpoint p hyend hne
  refine ⟨q, ?_, hqend⟩
  exact List.mem_flatMap.2 ⟨p, hp, hq⟩

/-- One-path cover of the support of an original-edge path. -/
def ofPath (p : GraphPath G) : PathCover G p.support where
  paths := [p]
  disjoint := by simp
  mem_iff := by
    intro x
    simp

lemma ofPath_card (p : GraphPath G) : (ofPath p).card = 1 := by
  simp [ofPath, card]

end PathCover

lemma pathCoverNumber_erase_le (U : Finset V) (x : V) :
    pathCoverNumber G (U.erase x) ≤ pathCoverNumber G U + 1 := by
  obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
  have hle := pathCoverNumber_le (G := G) (pc.deleteVertex x)
  have hcard := pc.card_deleteVertex_le x
  omega

lemma pathCoverNumber_erase_le_of_eligible {U : Finset V} {x : V}
    (h : Eligible G U x) :
    pathCoverNumber G (U.erase x) ≤ pathCoverNumber G U := by
  obtain ⟨pc, hpc, p, hp, hx⟩ := h
  have hle := pathCoverNumber_le (G := G) (pc.deleteVertex x)
  have hcard := pc.card_deleteVertex_le_of_endpoint ⟨p, hp, hx⟩
  omega

lemma pathCoverNumber_sdiff_le (U X : Finset V) (hX : X ⊆ U) :
    pathCoverNumber G (U \ X) ≤ pathCoverNumber G U + X.card := by
  induction X using Finset.induction generalizing U with
  | empty =>
    simp
  | insert x X hx ih =>
    have hxU : x ∈ U := hX (mem_insert_self x X)
    have hXsub : X ⊆ U.erase x := by
      intro y hy
      exact mem_erase.2 ⟨fun hxy => hx (hxy ▸ hy), hX (mem_insert_of_mem hy)⟩
    have hEq : U \ insert x X = U.erase x \ X := by
      rw [sdiff_insert, erase_sdiff_distrib, erase_eq_of_notMem hx]
    rw [hEq]
    have h1 := ih (U := U.erase x) hXsub
    have h2 := pathCoverNumber_erase_le (G := G) U x
    have hcard : (insert x X).card = X.card + 1 := card_insert_of_notMem hx
    omega

lemma pathCoverNumber_sdiff_le_of_eligible {U X : Finset V} (hX : X ⊆ U)
    {x : V} (hxX : x ∈ X) (hE : Eligible G U x) :
    pathCoverNumber G (U \ X) ≤ pathCoverNumber G U + X.card - 1 := by
  have hEq : U \ X = U.erase x \ X.erase x := by
    have : x ∉ U \ X := fun h => (mem_sdiff.1 h).2 hxX
    rw [← erase_sdiff_distrib, erase_eq_of_notMem this]
  rw [hEq]
  have hsub : X.erase x ⊆ U.erase x := by
    intro y hy
    exact mem_erase.2 ⟨(mem_erase.1 hy).1, hX (mem_of_mem_erase hy)⟩
  have h1 := pathCoverNumber_sdiff_le (G := G) (U.erase x) (X.erase x) hsub
  have h2 := pathCoverNumber_erase_le_of_eligible (G := G) hE
  have hcard : (X.erase x).card = X.card - 1 := card_erase_of_mem hxX
  have hpos : 1 ≤ X.card := Nat.succ_le_of_lt (card_pos.2 ⟨x, hxX⟩)
  omega

lemma componentCount_sdiff_le (U X : Finset V) (hX : X ⊆ U) :
    componentCount G (U \ X) ≤ pathCoverNumber G U + X.card :=
  (componentCount_le_pathCoverNumber (U \ X)).trans
    (pathCoverNumber_sdiff_le U X hX)

lemma componentCount_erase_le (U : Finset V) (x : V) :
    componentCount G (U.erase x) ≤ pathCoverNumber G U + 1 := by
  by_cases hx : x ∈ U
  · simpa [sdiff_singleton_eq_erase] using
      componentCount_sdiff_le U {x} (singleton_subset_iff.2 hx)
  · have : U.erase x = U := erase_eq_of_notMem hx
    have h := componentCount_le_pathCoverNumber (G := G) U
    simpa [this] using h.trans (Nat.le_succ _)

lemma componentCount_sdiff_le_of_eligible {U X : Finset V} (hX : X ⊆ U)
    {x : V} (hxX : x ∈ X) (hE : Eligible G U x) :
    componentCount G (U \ X) ≤ pathCoverNumber G U + X.card - 1 :=
  (componentCount_le_pathCoverNumber (U \ X)).trans
    (pathCoverNumber_sdiff_le_of_eligible hX hxX hE)

lemma componentCount_erase_le_of_eligible {U : Finset V} {x : V}
    (hE : Eligible G U x) :
    componentCount G (U.erase x) ≤ pathCoverNumber G U := by
  have hx : x ∈ U := hE.mem
  have h := componentCount_sdiff_le_of_eligible (singleton_subset_iff.2 hx)
    (mem_singleton_self x) hE
  simpa [sdiff_singleton_eq_erase, card_singleton] using h

/-- Equality in the generic cut bound forces every deleted vertex to be
ineligible. Empty cuts satisfy the inclusion vacuously. -/
lemma eq_cut_bound_imp_subset_ineligible {U X : Finset V} (hX : X ⊆ U)
    (heq : componentCount G (U \ X) = pathCoverNumber G U + X.card) :
    X ⊆ ineligibleSet G U := by
  intro x hx
  refine (mem_ineligibleSet_iff (G := G)).mpr ⟨hX hx, ?_⟩
  intro hE
  have hle := componentCount_sdiff_le_of_eligible hX hx hE
  have hpos : 1 ≤ X.card := Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)
  omega

lemma eq_cut_bound_singleton_imp_ineligible {U : Finset V} {x : V}
    (hx : x ∈ U)
    (heq : componentCount G (U.erase x) = pathCoverNumber G U + 1) :
    x ∈ ineligibleSet G U := by
  have := eq_cut_bound_imp_subset_ineligible (singleton_subset_iff.2 hx)
    (by simpa [sdiff_singleton_eq_erase, card_singleton] using heq)
  simpa using this

lemma DistinctPathCompatible.eligible_left {U : Finset V} {x y : V}
    (h : DistinctPathCompatible (G := G) U x y) : Eligible G U x := by
  obtain ⟨_, pc, hpc, p, hp, _, _, _, hx, _⟩ := h
  exact ⟨pc, hpc, p, hp, hx⟩

lemma DistinctPathCompatible.eligible_right {U : Finset V} {x y : V}
    (h : DistinctPathCompatible (G := G) U x y) : Eligible G U y := by
  obtain ⟨_, pc, hpc, _, _, q, hq, _, _, hy⟩ := h
  exact ⟨pc, hpc, q, hq, hy⟩

lemma distinctPathGraph_adj_mem_eligibleSet {U : Finset V} {x y : V}
    (h : (distinctPathGraph (G := G) U).Adj x y) :
    x ∈ eligibleSet G U ∧ y ∈ eligibleSet G U :=
  ⟨(mem_eligibleSet_iff (G := G)).mpr ⟨h.eligible_left.mem, h.eligible_left⟩,
    (mem_eligibleSet_iff (G := G)).mpr ⟨h.eligible_right.mem, h.eligible_right⟩⟩

lemma pathCoverNumber_eq_zero_iff (U : Finset V) :
    pathCoverNumber G U = 0 ↔ U = ∅ := by
  constructor
  · intro h
    obtain ⟨pc, hpc⟩ := exists_min_pathCover (G := G) U
    have hlen : pc.paths.length = 0 := by
      simpa [PathCover.card] using hpc.trans h
    have hp : pc.paths = [] := List.length_eq_zero_iff.mp hlen
    ext z
    simp [pc.mem_iff, hp]
  · intro h
    subst h
    exact pathCoverNumber_empty (G := G)

lemma one_le_pathCoverNumber_of_nonempty {U : Finset V} (hU : U.Nonempty) :
    1 ≤ pathCoverNumber G U := by
  have : pathCoverNumber G U ≠ 0 := by
    intro h
    exact hU.ne_empty ((pathCoverNumber_eq_zero_iff (G := G) U).1 h)
  omega

lemma SpanningPathCompatible.eligible_left {U : Finset V} {x y : V}
    (h : SpanningPathCompatible (G := G) U x y) : Eligible G U x := by
  obtain ⟨_hne, p, hp, hends⟩ := h
  subst hp
  have hxend : x = p.start ∨ x = p.finish := by
    rcases hends with h | h
    · exact .inl h.1.symm
    · exact .inr h.2.symm
  have hle : pathCoverNumber G p.support ≤ 1 := by
    simpa [PathCover.ofPath_card] using
      pathCoverNumber_le (G := G) (PathCover.ofPath p)
  have hpos : 1 ≤ pathCoverNumber G p.support := by
    refine one_le_pathCoverNumber_of_nonempty ⟨x, ?_⟩
    rcases hxend with rfl | rfl
    · exact p.start_mem_support
    · exact p.finish_mem_support
  refine ⟨PathCover.ofPath p, ?_, p, List.mem_singleton.mpr rfl, hxend⟩
  rw [PathCover.ofPath_card, le_antisymm hle hpos]

lemma SpanningPathCompatible.eligible_right {U : Finset V} {x y : V}
    (h : SpanningPathCompatible (G := G) U x y) : Eligible G U y := by
  obtain ⟨hne, p, hp, hends⟩ := h
  have hsymm : SpanningPathCompatible (G := G) U y x :=
    ⟨hne.symm, p, hp, hends.symm⟩
  exact hsymm.eligible_left

lemma spanningPathGraph_adj_mem_eligibleSet {U : Finset V} {x y : V}
    (h : (spanningPathGraph (G := G) U).Adj x y) :
    x ∈ eligibleSet G U ∧ y ∈ eligibleSet G U :=
  ⟨(mem_eligibleSet_iff (G := G)).mpr ⟨h.eligible_left.mem, h.eligible_left⟩,
    (mem_eligibleSet_iff (G := G)).mpr ⟨h.eligible_right.mem, h.eligible_right⟩⟩

/-- Eligible-carrier restriction of the paper graph `D(U)`. Ambient
outsiders and ineligible vertices are excluded, so later multipartite
claims apply on this carrier rather than on all of `V`. -/
noncomputable def distinctPathGraphOnEligible (U : Finset V) :
    SimpleGraph (eligibleSet G U : Set V) :=
  (distinctPathGraph (G := G) U).induce _

lemma distinctPathGraphOnEligible_adj_iff {U : Finset V}
    {x y : (eligibleSet G U : Set V)} :
    (distinctPathGraphOnEligible (G := G) U).Adj x y ↔
      DistinctPathCompatible (G := G) U x.1 y.1 :=
  Iff.rfl

/-- Eligible-carrier restriction of the paper graph `R(U)`. -/
noncomputable def spanningPathGraphOnEligible (U : Finset V) :
    SimpleGraph (eligibleSet G U : Set V) :=
  (spanningPathGraph (G := G) U).induce _

lemma spanningPathGraphOnEligible_adj_iff {U : Finset V}
    {x y : (eligibleSet G U : Set V)} :
    (spanningPathGraphOnEligible (G := G) U).Adj x y ↔
      SpanningPathCompatible (G := G) U x.1 y.1 :=
  Iff.rfl

lemma distinctPathGraphOnEligible_eq_bot_of_pathCoverNumber_le_one {U : Finset V}
    (h : pathCoverNumber G U ≤ 1) :
    distinctPathGraphOnEligible (G := G) U = ⊥ := by
  ext x y
  constructor
  · intro hAdj
    have : (distinctPathGraph (G := G) U).Adj x.1 y.1 := hAdj
    have : (⊥ : SimpleGraph V).Adj x.1 y.1 := by
      simpa [distinctPathGraph_eq_bot_of_pathCoverNumber_le_one (G := G) h] using this
    cases this
  · intro hAdj
    cases hAdj

lemma spanningPathGraphOnEligible_eq_bot_of_card_le_one {U : Finset V}
    (hU : U.card ≤ 1) :
    spanningPathGraphOnEligible (G := G) U = ⊥ := by
  ext x y
  constructor
  · intro hAdj
    have : (spanningPathGraph (G := G) U).Adj x.1 y.1 := hAdj
    have : (⊥ : SimpleGraph V).Adj x.1 y.1 := by
      simpa [spanningPathGraph_eq_bot_of_card_le_one (G := G) hU] using this
    cases this
  · intro hAdj
    cases hAdj

end Nikoghosyan
