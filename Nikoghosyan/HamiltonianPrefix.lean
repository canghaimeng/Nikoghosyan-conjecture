/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.VertexInsertion

/-!
Original-path prefixes and Hamiltonian prefix scaffolding.

Every bounded index `n ≤ r.walk.length` yields an original `GraphPath`
`r.prefixTake n` whose support is `{ r.walk.getVert i | i ≤ n }`. Path
simplicity keeps the next vertex outside that prefix. Traceable-extension
toughness is applied to the INITIAL cycle `c` and that real prefix, using
the INITIAL row hypotheses; later row conditions are not assumed.

On a genuine current cycle whose support is the previous union, the host
forbidden-pattern hypothesis on the whole `c.support ∪ r.support` makes
the ENTIRE current antineighbourhood
`γ.support \ rowProfile γ.support x` a cograph, including previously
inserted vertices of `r`. Combined with `OneToughOn` of the next host,
the checked one-vertex strict-cut theorem supplies `p < |A|` for that
current remainder.

The named rule `ProfileEndedSpanningPath` is the still-open protected
A-ended spanning-path obligation. Conditional composition along actual
prefixes is scaffolding for manuscript `prof:thm:prefix`. It is not that
theorem, and it is not `prof:cor:insertion`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Induced-`(P₄ ∪ P₁)`-freeness on a specified original support. -/
def NoInducedP4UnionP1On (G : SimpleGraph V) (J : Finset V) : Prop :=
  ∀ ⦃a b c d x : V⦄,
    a ∈ J → b ∈ J → c ∈ J → d ∈ J → x ∈ J →
    InducedP4 G a b c d →
    x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d

lemma NoInducedP4UnionP1On.mono {J K : Finset V}
    (h : NoInducedP4UnionP1On G K) (hJK : J ⊆ K) :
    NoInducedP4UnionP1On G J :=
  fun _ _ _ _ _ ha hb hc hd hx hp hxa hxb hxc hxd =>
    h (hJK ha) (hJK hb) (hJK hc) (hJK hd) (hJK hx) hp hxa hxb hxc hxd

lemma NoInducedP4UnionP1On.of_global (h : NoInducedP4UnionP1 G) (J : Finset V) :
    NoInducedP4UnionP1On G J :=
  fun _ _ _ _ _ _ _ _ _ _ hp hxa hxb hxc hxd => h hp hxa hxb hxc hxd

lemma rowProfile_subset_of_subset {H H' : Finset V} {v : V}
    (h : H ⊆ H') :
    rowProfile (G := G) H v ⊆ rowProfile (G := G) H' v := by
  intro x hx
  have hx' := (mem_rowProfile_iff (G := G)).1 hx
  exact (mem_rowProfile_iff (G := G)).2 ⟨h hx'.1, hx'.2⟩

lemma insert_union_right {x : V} {s t : Finset V} :
    insert x (s ∪ t) = s ∪ insert x t := by
  ext y
  simp [mem_insert, mem_union]

namespace GraphPath

/-- The original-edge prefix of the first `n` darts. Indices `n` larger
than `walk.length` are capped at the finish by `Walk.getVert`. -/
def prefixTake (p : GraphPath G) (n : ℕ) : GraphPath G where
  start := p.start
  finish := p.walk.getVert n
  walk := p.walk.take n
  isPath := p.isPath.take n

lemma support_prefixTake_subset (p : GraphPath G) (n : ℕ) :
    (p.prefixTake n).support ⊆ p.support := by
  intro y hy
  have hy' : y ∈ (p.walk.take n).support := by
    simpa [prefixTake, GraphPath.support] using hy
  have : (p.walk.take n).support ⊆ p.walk.support := by
    simpa [Walk.support_take] using List.take_subset (n + 1) p.walk.support
  exact List.mem_toFinset.2 (this hy')

lemma length_prefixTake_of_le (p : GraphPath G) {n : ℕ}
    (hn : n ≤ p.walk.length) :
    (p.prefixTake n).walk.length = n := by
  simp [prefixTake, Walk.take_length, hn]

lemma finish_prefixTake (p : GraphPath G) (n : ℕ) :
    (p.prefixTake n).finish = p.walk.getVert n :=
  rfl

lemma start_prefixTake (p : GraphPath G) (n : ℕ) :
    (p.prefixTake n).start = p.start :=
  rfl

lemma getVert_mem_path_support (p : GraphPath G) (i : ℕ) :
    p.walk.getVert i ∈ p.support :=
  List.mem_toFinset.2 (Walk.getVert_mem_support p.walk i)

/-- `getVert` is injective on `0, …, length`. Capped indices past
`walk.length` are excluded. -/
lemma getVert_injective_of_le_length (p : GraphPath G) {i j : ℕ}
    (hi : i ≤ p.walk.length) (hj : j ≤ p.walk.length)
    (heq : p.walk.getVert i = p.walk.getVert j) : i = j := by
  have hi' : i < p.walk.support.length := by
    rw [Walk.length_support]
    omega
  have hj' : j < p.walk.support.length := by
    rw [Walk.length_support]
    omega
  have hiE := Walk.getVert_eq_support_getElem p.walk hi
  have hjE := Walk.getVert_eq_support_getElem p.walk hj
  have hinj := (Walk.isPath_iff_injective_get_support p.walk).1 p.isPath
  have : p.walk.support.get ⟨i, hi'⟩ = p.walk.support.get ⟨j, hj'⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem, ← hiE, ← hjE, heq]
  exact congrArg Fin.val (hinj this)

lemma mem_support_prefixTake (p : GraphPath G) {n : ℕ}
    (hn : n ≤ p.walk.length) {y : V} :
    y ∈ (p.prefixTake n).support ↔ ∃ i ≤ n, p.walk.getVert i = y := by
  constructor
  · intro hy
    have hy' : y ∈ (p.walk.take n).support := by
      simpa [prefixTake, GraphPath.support] using hy
    obtain ⟨i, hiEq, hiLen⟩ :=
      (Walk.mem_support_iff_exists_getVert (p := p.walk.take n)).1 hy'
    have hi' : i ≤ n := by
      have : i ≤ (p.walk.take n).length := hiLen
      simpa [Walk.take_length, hn] using this
    refine ⟨i, hi', ?_⟩
    have hget : (p.walk.take n).getVert i = p.walk.getVert i := by
      simp [Walk.take_getVert, inf_eq_right.2 hi']
    exact hget.symm.trans hiEq
  · intro ⟨i, hi, hiy⟩
    have hget : (p.walk.take n).getVert i = p.walk.getVert i := by
      simp [Walk.take_getVert, inf_eq_right.2 hi]
    have hmem : (p.walk.take n).getVert i ∈ (p.walk.take n).support :=
      Walk.getVert_mem_support (p.walk.take n) i
    have : y ∈ (p.walk.take n).support := by
      rw [← hiy, ← hget]
      exact hmem
    simpa [prefixTake, GraphPath.support] using this

lemma support_prefixTake_zero (p : GraphPath G) :
    (p.prefixTake 0).support = {p.start} := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, hi, rfl⟩ := (p.mem_support_prefixTake (Nat.zero_le _)).1 hy
    have : i = 0 := Nat.le_zero.1 hi
    subst this
    simp [Walk.getVert_zero]
  · intro hy
    have : y = p.start := mem_singleton.1 hy
    subst this
    exact (p.mem_support_prefixTake (Nat.zero_le _)).2
      ⟨0, le_rfl, Walk.getVert_zero p.walk⟩

lemma support_prefixTake_length (p : GraphPath G) :
    (p.prefixTake p.walk.length).support = p.support := by
  ext y
  constructor
  · intro hy
    exact p.support_prefixTake_subset p.walk.length hy
  · intro hy
    have hy' : y ∈ p.walk.support := by simpa [support] using hy
    obtain ⟨i, rfl, hi⟩ := (Walk.mem_support_iff_exists_getVert).1 hy'
    exact (p.mem_support_prefixTake le_rfl).2 ⟨i, hi, rfl⟩

/-- The next original vertex after a proper prefix is new. -/
lemma next_not_mem_prefixTake (p : GraphPath G) {n : ℕ}
    (hn : n < p.walk.length) :
    p.walk.getVert (n + 1) ∉ (p.prefixTake n).support := by
  intro hmem
  obtain ⟨i, hi, heq⟩ := (p.mem_support_prefixTake (le_of_lt hn)).1 hmem
  have hieq : i = n + 1 :=
    p.getVert_injective_of_le_length (hi.trans (le_of_lt hn))
      (Nat.succ_le_of_lt hn) heq
  omega

lemma support_prefixTake_succ (p : GraphPath G) {n : ℕ}
    (hn : n < p.walk.length) :
    (p.prefixTake (n + 1)).support =
      insert (p.walk.getVert (n + 1)) (p.prefixTake n).support := by
  have hn1 : n + 1 ≤ p.walk.length := Nat.succ_le_of_lt hn
  have hn0 : n ≤ p.walk.length := le_of_lt hn
  ext y
  constructor
  · intro hy
    obtain ⟨i, hi, rfl⟩ := (p.mem_support_prefixTake hn1).1 hy
    rcases Nat.le_succ_iff.1 hi with hle | rfl
    · exact mem_insert_of_mem ((p.mem_support_prefixTake hn0).2 ⟨i, hle, rfl⟩)
    · exact mem_insert_self _ _
  · intro hy
    rcases mem_insert.1 hy with rfl | hy'
    · exact (p.mem_support_prefixTake hn1).2 ⟨n + 1, le_rfl, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := (p.mem_support_prefixTake hn0).1 hy'
      exact (p.mem_support_prefixTake hn1).2 ⟨i, hi.trans (Nat.le_succ n), rfl⟩

end GraphPath

lemma start_ne_finish_of_three_le_card (p : GraphPath G)
    (h : 3 ≤ p.support.card) : p.start ≠ p.finish := by
  intro heq
  have hnil : p.walk.Nil := (p.nil_iff_start_eq_finish).2 heq
  have h1 : p.support.card = 1 := by
    rw [p.support_eq_singleton_of_nil hnil]
    exact card_singleton _
  omega

/-- Every actual prefix of `r` is 1-tough with the INITIAL cycle, using
the INITIAL row hypotheses. No later-row or prefix-toughness assumption. -/
lemma oneToughOn_of_prefixTake (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v))
    {n : ℕ} (_hn : n ≤ r.walk.length) :
    OneToughOn G (c.support ∪ (r.prefixTake n).support) :=
  oneToughOn_of_traceable_extension c (r.prefixTake n)
    (hdisj.mono_right (r.support_prefixTake_subset n))
    (fun v hv => hrow v (r.support_prefixTake_subset n hv))

/-- The current remainder after deleting the actual current profile of
the next vertex is a cograph, including previously inserted vertices. -/
lemma isCograph_current_remainder (γ : GraphCycle G) {x : V}
    (hx : x ∉ γ.support)
    (hOn : NoInducedP4UnionP1On G (insert x γ.support)) :
    IsCograph G (γ.support \ rowProfile (G := G) γ.support x) :=
  isCograph_sdiff_rowProfile_insert γ hx hOn

/-- Current-row strict cut: `OneToughOn` of the next host plus the
derived current remainder cograph. The profile is computed on the
current cycle support, not only on the initial Hamiltonian block. -/
theorem strict_pathCover_of_current_remainder (γ : GraphCycle G) {x : V}
    (hx : x ∉ γ.support)
    (hJ : OneToughOn G (insert x γ.support))
    (hOn : NoInducedP4UnionP1On G (insert x γ.support)) :
    pathCoverNumber G (γ.support \ rowProfile (G := G) γ.support x) <
      (rowProfile (G := G) γ.support x).card :=
  strict_pathCover_of_oneToughOn_cycle_of_host γ hx hJ hOn

/-- Explicit insertion rule: a genuine original spanning path of the
current cycle support with both ends in the actual current profile.
This names the still-open protected-sufficiency obligation. It is not
the manuscript one-vertex corollary. -/
def ProfileEndedSpanningPath (G : SimpleGraph V) : Prop :=
  ∀ (c : GraphCycle G) (x : V),
    x ∉ c.support →
      OneToughOn G (insert x c.support) →
        IsCograph G (c.support \ rowProfile (G := G) c.support x) →
          ∃ p : GraphPath G,
            p.support = c.support ∧
              p.start ∈ rowProfile (G := G) c.support x ∧
                p.finish ∈ rowProfile (G := G) c.support x

/-- Conditional one-vertex splice: the named rule plus the checked
elementary cycle insertion. Distinct path ends are derived from the
cycle-support order. This is not `prof:cor:insertion`. -/
theorem exists_inserted_cycle_of_profileEndedSpanningPath
    (hRule : ProfileEndedSpanningPath G)
    (c : GraphCycle G) {x : V}
    (hx : x ∉ c.support)
    (hJ : OneToughOn G (insert x c.support))
    (hK : IsCograph G (c.support \ rowProfile (G := G) c.support x)) :
    ∃ γ : GraphCycle G,
      γ.support = insert x c.support ∧ 3 ≤ γ.support.card := by
  obtain ⟨p, hp, hs, hf⟩ := hRule c x hx hJ hK
  have hne : p.start ≠ p.finish := by
    have h3 := c.three_le_card_support
    rw [← hp] at h3
    exact start_ne_finish_of_three_le_card p h3
  exact exists_inserted_cycle_of_profile_ends p c hp hx hs hf hne

/-- Finite original-path prefix induction, conditional on the named
insertion rule. At each index the current `OneToughOn` is derived from
the INITIAL cycle and the real prefix, and the current remainder
cograph is derived from the host forbidden-pattern hypothesis on the
whole union. This is not manuscript `prof:thm:prefix`. -/
theorem exists_cycle_of_prefixTake_of_profileEndedSpanningPath
    (hRule : ProfileEndedSpanningPath G)
    (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v))
    (hOn : NoInducedP4UnionP1On G (c.support ∪ r.support))
    (n : ℕ) (hn : n ≤ r.walk.length) :
    ∃ γ : GraphCycle G,
      γ.support = c.support ∪ (r.prefixTake n).support := by
  induction n with
  | zero =>
    have hx : r.start ∉ c.support :=
      disjoint_right.1 hdisj r.start_mem_support
    have hsupp0 : (r.prefixTake 0).support = {r.start} :=
      r.support_prefixTake_zero
    have hJ : OneToughOn G (insert r.start c.support) := by
      have hunion : insert r.start c.support =
          c.support ∪ (r.prefixTake 0).support := by
        rw [hsupp0, insert_eq, union_comm]
      rw [hunion]
      exact oneToughOn_of_prefixTake c r hdisj hrow (Nat.zero_le _)
    have hOn0 : NoInducedP4UnionP1On G (insert r.start c.support) := by
      have hsub : insert r.start c.support ⊆ c.support ∪ r.support := by
        intro y hy
        rcases mem_insert.1 hy with rfl | hy'
        · exact mem_union.2 (Or.inr r.start_mem_support)
        · exact mem_union.2 (Or.inl hy')
      exact hOn.mono hsub
    have hK : IsCograph G
        (c.support \ rowProfile (G := G) c.support r.start) :=
      isCograph_current_remainder c hx hOn0
    obtain ⟨γ, hγ, _⟩ :=
      exists_inserted_cycle_of_profileEndedSpanningPath hRule c hx hJ hK
    refine ⟨γ, ?_⟩
    rw [hγ, hsupp0, insert_eq, union_comm]
  | succ n ih =>
    have hn0 : n ≤ r.walk.length := Nat.le_of_succ_le hn
    have hnlt : n < r.walk.length := Nat.lt_of_succ_le hn
    obtain ⟨γ, hγ⟩ := ih hn0
    set x := r.walk.getVert (n + 1)
    have hxR : x ∈ r.support := r.getVert_mem_path_support (n + 1)
    have hxC : x ∉ c.support := disjoint_right.1 hdisj hxR
    have hxP : x ∉ (r.prefixTake n).support :=
      r.next_not_mem_prefixTake hnlt
    have hx : x ∉ γ.support := by
      rw [hγ]
      exact fun h => (mem_union.1 h).elim hxC hxP
    have hinsert :
        insert x γ.support = c.support ∪ (r.prefixTake (n + 1)).support := by
      rw [hγ, insert_union_right, r.support_prefixTake_succ hnlt]
    have hJ : OneToughOn G (insert x γ.support) := by
      rw [hinsert]
      exact oneToughOn_of_prefixTake c r hdisj hrow hn
    have hOnx : NoInducedP4UnionP1On G (insert x γ.support) := by
      have hsub : insert x γ.support ⊆ c.support ∪ r.support := by
        rw [hinsert]
        intro y hy
        rcases mem_union.1 hy with hyH | hyP
        · exact mem_union.2 (Or.inl hyH)
        · exact mem_union.2 (Or.inr (r.support_prefixTake_subset (n + 1) hyP))
      exact hOn.mono hsub
    have hK : IsCograph G
        (γ.support \ rowProfile (G := G) γ.support x) :=
      isCograph_current_remainder γ hx hOnx
    obtain ⟨γ', hγ', _⟩ :=
      exists_inserted_cycle_of_profileEndedSpanningPath hRule γ hx hJ hK
    refine ⟨γ', ?_⟩
    simpa [hinsert] using hγ'

/-- Conditional composition over the full original path. Not
`prof:thm:prefix`. -/
theorem exists_cycle_union_of_profileEndedSpanningPath
    (hRule : ProfileEndedSpanningPath G)
    (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v))
    (hOn : NoInducedP4UnionP1On G (c.support ∪ r.support)) :
    ∃ γ : GraphCycle G, γ.support = c.support ∪ r.support := by
  obtain ⟨γ, hγ⟩ :=
    exists_cycle_of_prefixTake_of_profileEndedSpanningPath
      hRule c r hdisj hrow hOn r.walk.length le_rfl
  refine ⟨γ, ?_⟩
  simpa [r.support_prefixTake_length] using hγ

theorem exists_cycle_union_of_profileEndedSpanningPath_of_global
    (hRule : ProfileEndedSpanningPath G)
    (c : GraphCycle G) (r : GraphPath G)
    (hdisj : Disjoint c.support r.support)
    (hrow : ∀ v ∈ r.support,
      (rowProfile (G := G) c.support v).Nonempty ∧
        NoTightContainer G c.support (rowProfile (G := G) c.support v))
    (hG : NoInducedP4UnionP1 G) :
    ∃ γ : GraphCycle G, γ.support = c.support ∪ r.support :=
  exists_cycle_union_of_profileEndedSpanningPath hRule c r hdisj hrow
    (NoInducedP4UnionP1On.of_global hG _)

end Nikoghosyan
