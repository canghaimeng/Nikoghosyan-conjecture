/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.FactorAuxiliary

/-!
Phase 9: actual auxiliary deletion transport and general coloured-cycle
closure.

Preserves the accepted `FactorAuxiliary` bodies. From an original walk in
`G.deleteEdges {e}` one obtains an auxiliary walk that never visits the
physical vertex `w_e`; inducing it into `aux - w_e` yields reachability of
the two endpoint blocks. Combined with the checked `G-e` connectedness from
1-toughness, a physical vertex is not a Yeo splitter (no extra reachability
premise).

A properly coloured auxiliary cycle, rotated to a block vertex, selects
`k ≥ 2` distinct blocks and cyclic physical edges. With one global port map
and per-block realisation of opposite ports (the same function that colours
`aux`), spanning original paths assemble to a `k`-block original cycle and
contradict a globally minimum factor. The two-block four-edge case is
included.

Applying the checked unrestricted-colour Yeo theorem then produces a block
splitter. Original attachments of one component of `G` minus that block are
monochromatic by transporting an outside walk into `aux` minus the block.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Port : Type*} [DecidableEq Port]

lemma mem_support_eq_rec {α : Type*} {H : SimpleGraph α} {u u' v : α}
    (h : u = u') (w : H.Walk u v) (x : α) :
    x ∈ (h ▸ w).support ↔ x ∈ w.support := by
  subst h
  rfl

lemma support_inl_rec {P : BlockPartition V ι} {i j k : ι} (h : i = j)
    (w : (aux (G := G) P).Walk (.inl j) (.inl k))
    (x : ι ⊕ PhysEdge (G := G) P) :
    x ∈ (h ▸ w : (aux (G := G) P).Walk (.inl i) (.inl k)).support ↔
      x ∈ w.support := by
  subst h
  rfl

lemma toPhys_val (P : BlockPartition V ι) {a b : V} (h : G.Adj a b)
    (hne : P.index a ≠ P.index b) :
    (toPhys (G := G) P h hne).1 = s(a, b) :=
  rfl

lemma toPhys_eq_of_val (P : BlockPartition V ι) {a b : V} (h : G.Adj a b)
    (hne : P.index a ≠ P.index b) {e : PhysEdge (G := G) P}
    (he : e.1 = s(a, b)) :
    toPhys (G := G) P h hne = e := by
  apply Subtype.ext
  simp [toPhys, he]

lemma PhysEdge.eq_toPhys {P : BlockPartition V ι} (e : PhysEdge (G := G) P) :
    ∃ (a b : V) (h : G.Adj a b) (hne : P.index a ≠ P.index b),
      e = toPhys (G := G) P h hne := by
  obtain ⟨a, b, he, hadj, hne⟩ := PhysEdge.eq_mk (G := G) e
  exact ⟨a, b, hadj, hne, (toPhys_eq_of_val P hadj hne he).symm⟩

lemma deleteEdges_not_mem_edges {e : Sym2 V} {u v : V}
    (w : (G.deleteEdges {e}).Walk u v) : e ∉ w.edges := by
  intro he
  have : e ∈ (G.deleteEdges {e}).edgeSet := w.edges_subset_edgeSet he
  simp [SimpleGraph.edgeSet_deleteEdges] at this

/-- Every physical vertex appearing on `mapWalk` comes from a genuine
original cross-edge of the source walk. -/
lemma inr_mem_mapWalk_imp_edges (P : BlockPartition V ι) :
    ∀ {u v : V} (w : G.Walk u v) (e : PhysEdge (G := G) P),
      Sum.inr e ∈ (mapWalk (G := G) P w).support → e.1 ∈ w.edges
  | _, _, Walk.nil, e, h => by
    simp [mapWalk] at h
  | u, _, Walk.cons (v := w) hadj p, e, hmem => by
    have ih := inr_mem_mapWalk_imp_edges P p
    by_cases hEq : P.index u = P.index w
    · rw [mapWalk, dif_pos hEq] at hmem
      exact List.mem_cons_of_mem _
        (ih e ((support_inl_rec hEq (mapWalk (G := G) P p) (Sum.inr e)).1 hmem))
    · rw [mapWalk, dif_neg hEq] at hmem
      simp only [Walk.support_cons, List.mem_cons] at hmem
      rcases hmem with h0 | h1 | hrest
      · cases h0
      · have heq : e = toPhys (G := G) P hadj hEq := Sum.inr.inj h1
        subst heq
        simp [toPhys, Walk.edges_cons]
      · exact List.mem_cons_of_mem _ (ih e hrest)

lemma mapWalk_not_mem_deleted (P : BlockPartition V ι)
    {u v : V} {e : PhysEdge (G := G) P}
    (w : (G.deleteEdges {e.1}).Walk u v) :
    Sum.inr e ∉ (mapWalk (G := G) P (w.mapLe (G.deleteEdges_le {e.1}))).support := by
  intro hmem
  have hedge :
      e.1 ∈ (w.mapLe (G.deleteEdges_le {e.1})).edges :=
    inr_mem_mapWalk_imp_edges P _ e hmem
  have hedge' : e.1 ∈ w.edges := by
    simpa [Walk.edges_mapLe_eq_edges] using hedge
  exact deleteEdges_not_mem_edges (e := e.1) w hedge'

lemma sum_inl_ne_inr (i : ι) (e : PhysEdge (G := G) P) :
    Sum.inl i ≠ Sum.inr e :=
  fun h => (Sum.inr_ne_inl h.symm).elim

/-- From an actual `G - e` walk, the mapped auxiliary walk induces into
`aux - w_e` between the endpoint block vertices. -/
noncomputable def mapWalkDelete (P : BlockPartition V ι)
    {u v : V} {e : PhysEdge (G := G) P}
    (w : (G.deleteEdges {e.1}).Walk u v) :
    (Yeo.deleteGraph (aux (G := G) P) (Sum.inr e)).Walk
      ⟨Sum.inl (P.index u), sum_inl_ne_inr (P.index u) e⟩
      ⟨Sum.inl (P.index v), sum_inl_ne_inr (P.index v) e⟩ := by
  let wG := w.mapLe (G.deleteEdges_le {e.1})
  let wAux := mapWalk (G := G) P wG
  have havoid : ∀ x ∈ wAux.support, x ∈ Yeo.deleteSet (Sum.inr e) := by
    intro x hx hxe
    subst hxe
    exact mapWalk_not_mem_deleted P w hx
  exact (wAux.induce (Yeo.deleteSet (Sum.inr e)) havoid).copy
    (Subtype.ext rfl) (Subtype.ext rfl)

lemma reachable_blocks_of_deleteEdges (P : BlockPartition V ι)
    {u v : V} {e : PhysEdge (G := G) P}
    (h : (G.deleteEdges {e.1}).Reachable u v) :
    (Yeo.deleteGraph (aux (G := G) P) (Sum.inr e)).Reachable
      ⟨Sum.inl (P.index u), sum_inl_ne_inr (P.index u) e⟩
      ⟨Sum.inl (P.index v), sum_inl_ne_inr (P.index v) e⟩ := by
  obtain ⟨w⟩ := h
  exact ⟨mapWalkDelete P w⟩

/-- Endpoint-block reachability in `aux - w_e` from 1-toughness: `G - e`
is connected, so the two ends of `e` remain joined, and the walk map
avoids precisely the physical vertex of `e`. -/
lemma reachable_endpoint_blocks_of_oneTough (P : BlockPartition V ι)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {a b : V} (hab : G.Adj a b) (hne : P.index a ≠ P.index b) :
    (Yeo.deleteGraph (aux (G := G) P)
        (Sum.inr (toPhys (G := G) P hab hne))).Reachable
      ⟨Sum.inl (P.index a), by intro h; cases h⟩
      ⟨Sum.inl (P.index b), by intro h; cases h⟩ := by
  have hconn := deleteEdges_connected_of_oneTough (G := G) hT hord hab
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  have hR := hconn.preconnected a b
  simpa [toPhys_val] using
    reachable_blocks_of_deleteEdges P (e := toPhys (G := G) P hab hne) hR

/-- Unconditional: under 1-toughness of order at least three, a physical
vertex is not a Yeo splitter. Deletion reachability is derived, not assumed. -/
lemma not_splittingVertex_phys_of_oneTough (P : BlockPartition V ι)
    (port : V → Port) (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {a b : V} (hab : G.Adj a b) (hne : P.index a ≠ P.index b) :
    ¬ Yeo.SplittingVertex (auxColoring (G := G) P port)
        (Sum.inr (toPhys (G := G) P hab hne)) :=
  not_splittingVertex_phys (G := G) P port hab hne
    (reachable_endpoint_blocks_of_oneTough P hT hord hab hne)

lemma not_splittingVertex_physEdge_of_oneTough (P : BlockPartition V ι)
    (port : V → Port) (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (e : PhysEdge (G := G) P) :
    ¬ Yeo.SplittingVertex (auxColoring (G := G) P port) (Sum.inr e) := by
  obtain ⟨a, b, hab, hne, rfl⟩ := PhysEdge.eq_toPhys e
  exact not_splittingVertex_phys_of_oneTough P port hT hord hab hne

/-- After deleting `w_e`, every pair of block vertices remains reachable:
pick original vertices in those blocks and transport a `G - e` walk. -/
lemma reachable_all_blocks_deletePhys (P : BlockPartition V ι)
    (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    {a b : V} (hab : G.Adj a b) (hne : P.index a ≠ P.index b)
    (i j : ι) :
    (Yeo.deleteGraph (aux (G := G) P)
        (Sum.inr (toPhys (G := G) P hab hne))).Reachable
      ⟨Sum.inl i, by intro h; cases h⟩
      ⟨Sum.inl j, by intro h; cases h⟩ := by
  obtain ⟨ui, hui⟩ := P.nonempty i
  obtain ⟨uj, huj⟩ := P.nonempty j
  have hi : P.index ui = i := P.index_eq hui
  have hj : P.index uj = j := P.index_eq huj
  have hconn := deleteEdges_connected_of_oneTough (G := G) hT hord hab
  haveI : Nonempty V :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hord)
  have hR := hconn.preconnected ui uj
  have hmap :=
    reachable_blocks_of_deleteEdges P
      (e := toPhys (G := G) P hab hne) hR
  simpa [toPhys_val, hi, hj] using hmap

lemma endpointOf_eq_of_mem (P : BlockPartition V ι) {i : ι}
    {e : PhysEdge (G := G) P} (h : incident (G := G) P i e) {x : V}
    (hx1 : x ∈ e.1) (hx2 : x ∈ P.blocks i) :
    endpointOf (G := G) P i e h = x := by
  have hy1 := endpointOf_mem_edge (G := G) P i e h
  have hy2 := endpointOf_mem_block (G := G) P i e h
  obtain ⟨a, b, he, _, hne⟩ := PhysEdge.eq_mk (G := G) e
  have hx : x = a ∨ x = b := by
    simpa [he] using hx1
  have hy : endpointOf (G := G) P i e h = a ∨
      endpointOf (G := G) P i e h = b := by
    simpa [he] using hy1
  have not_both :
      ¬ (a ∈ P.blocks i ∧ b ∈ P.blocks i) := by
    intro ⟨ha, hb⟩
    exact hne ((P.index_eq ha).trans (P.index_eq hb).symm)
  rcases hx with rfl | rfl
  · rcases hy with hy | hy
    · exact hy
    · exact (not_both ⟨hx2, by simpa [hy] using hy2⟩).elim
  · rcases hy with hy | hy
    · exact (not_both ⟨by simpa [hy] using hy2, hx2⟩).elim
    · exact hy

lemma endpointOf_toPhys_left (P : BlockPartition V ι) {a b : V}
    (h : G.Adj a b) (hne : P.index a ≠ P.index b) :
    endpointOf (G := G) P (P.index a) (toPhys (G := G) P h hne)
      (toPhys_incident_left (G := G) P h hne) = a :=
  endpointOf_eq_of_mem P _ (by simp [toPhys]) (P.mem_index a)

lemma endpointOf_toPhys_right (P : BlockPartition V ι) {a b : V}
    (h : G.Adj a b) (hne : P.index a ≠ P.index b) :
    endpointOf (G := G) P (P.index b) (toPhys (G := G) P h hne)
      (toPhys_incident_right (G := G) P h hne) = b :=
  endpointOf_eq_of_mem P _ (by simp [toPhys]) (P.mem_index b)

lemma adj_of_endpoints (P : BlockPartition V ι) {i j : ι}
    {e : PhysEdge (G := G) P}
    (hi : incident (G := G) P i e) (hj : incident (G := G) P j e)
    (hij : i ≠ j) :
    G.Adj (endpointOf (G := G) P i e hi) (endpointOf (G := G) P j e hj) := by
  obtain ⟨a, b, he, hadj, hne⟩ := PhysEdge.eq_mk (G := G) e
  have hxi := endpointOf_mem_edge (G := G) P i e hi
  have hxj := endpointOf_mem_edge (G := G) P j e hj
  have hyi := endpointOf_mem_block (G := G) P i e hi
  have hyj := endpointOf_mem_block (G := G) P j e hj
  have hiab : endpointOf (G := G) P i e hi = a ∨
      endpointOf (G := G) P i e hi = b := by
    simpa [he] using hxi
  have hjab : endpointOf (G := G) P j e hj = a ∨
      endpointOf (G := G) P j e hj = b := by
    simpa [he] using hxj
  have hab_ne : a ≠ b := by
    intro h
    subst h
    simp at hne
  have not_same :
      endpointOf (G := G) P i e hi ≠ endpointOf (G := G) P j e hj := by
    intro h
    have : i = j :=
      (P.index_eq hyi).symm.trans (by simp [h, P.index_eq hyj])
    exact hij this
  rcases hiab with hi' | hi' <;> rcases hjab with hj' | hj'
  · exact (not_same (hi'.trans hj'.symm)).elim
  · simpa [hi', hj'] using hadj
  · simpa [hi', hj'] using hadj.symm
  · exact (not_same (hi'.trans hj'.symm)).elim

/-- One global port map together with spanning-path realisation on each
block using that same map. This is generic helper data until the actual
cograph `R` theorem supplies it. -/
structure GlobalPortData (P : BlockPartition V ι) (Port : Type*) where
  port : V → Port
  realize :
    ∀ (i : ι) {x y : V},
      x ∈ P.blocks i → y ∈ P.blocks i → port x ≠ port y →
        ∃ p : GraphPath G, p.start = x ∧ p.finish = y ∧ p.support = P.blocks i

noncomputable def GlobalPortData.realizedPath {P : BlockPartition V ι}
    (R : GlobalPortData (G := G) P Port) (i : ι) {x y : V}
    (hx : x ∈ P.blocks i) (hy : y ∈ P.blocks i) (hp : R.port x ≠ R.port y) :
    GraphPath G :=
  Classical.choose (R.realize i hx hy hp)

lemma GlobalPortData.realizedPath_spec {P : BlockPartition V ι}
    (R : GlobalPortData (G := G) P Port) (i : ι) {x y : V}
    (hx : x ∈ P.blocks i) (hy : y ∈ P.blocks i) (hp : R.port x ≠ R.port y) :
    (R.realizedPath i hx hy hp).start = x ∧
      (R.realizedPath i hx hy hp).finish = y ∧
        (R.realizedPath i hx hy hp).support = P.blocks i :=
  Classical.choose_spec (R.realize i hx hy hp)

lemma aux_adj_sum {P : BlockPartition V ι}
    {u v : ι ⊕ PhysEdge (G := G) P} (h : (aux (G := G) P).Adj u v) :
    (∃ i e, u = .inl i ∧ v = .inr e) ∨
      (∃ i e, u = .inr e ∧ v = .inl i) := by
  cases u with
  | inl i =>
    cases v with
    | inl j => exact (aux_not_adj_inl (G := G) i j h).elim
    | inr e => exact Or.inl ⟨i, e, rfl, rfl⟩
  | inr e =>
    cases v with
    | inl i => exact Or.inr ⟨i, e, rfl, rfl⟩
    | inr f => exact (aux_not_adj_inr (G := G) e f h).elim

lemma aux_getVert_isBlock {P : BlockPartition V ι} :
    ∀ {u v : ι ⊕ PhysEdge (G := G) P} (w : (aux (G := G) P).Walk u v)
      (n : ℕ), n ≤ w.length →
      ((∃ i, w.getVert n = .inl i) ↔ ((∃ i, u = .inl i) ↔ Even n))
  | _, _, Walk.nil, n, hn => by
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    simp [Walk.getVert]
  | u, _, Walk.cons (v := w) hadj p, n, hn => by
    cases n with
    | zero =>
      simp [Walk.getVert]
    | succ n' =>
      have hn' : n' ≤ p.length := by
        simpa [Walk.length_cons] using Nat.succ_le_succ_iff.mp hn
      have hopp : (∃ i, w = .inl i) ↔ ¬ ∃ i, u = .inl i := by
        rcases aux_adj_sum hadj with ⟨j, e, hu, hv⟩ | ⟨j, e, hu, hv⟩
        · subst hu
          subst hv
          simp
        · subst hu
          subst hv
          simp
      have hgv : (Walk.cons hadj p).getVert (n' + 1) = p.getVert n' := rfl
      rw [show (∃ i, (Walk.cons hadj p).getVert (n' + 1) = .inl i) ↔
            (∃ i, p.getVert n' = .inl i) by simp [hgv]]
      rw [aux_getVert_isBlock p n' hn']
      rw [hopp, Nat.even_add_one]
      exact not_iff_comm.trans Iff.comm

lemma aux_getVert_even_inl {P : BlockPartition V ι} {i : ι}
    {x : ι ⊕ PhysEdge (G := G) P}
    (w : (aux (G := G) P).Walk (.inl i) x) {n : ℕ}
    (hn : n ≤ w.length) (he : Even n) :
    ∃ j, w.getVert n = .inl j := by
  refine (aux_getVert_isBlock w n hn).mpr ?_
  simp [he]

lemma aux_cycle_even_length {P : BlockPartition V ι} {i : ι}
    {w : (aux (G := G) P).Walk (.inl i) (.inl i)} (_hc : w.IsCycle) :
    Even w.length := by
  have hend : w.getVert w.length = .inl i := Walk.getVert_length w
  have : ∃ j, w.getVert w.length = .inl j := ⟨i, hend⟩
  exact ((aux_getVert_isBlock w w.length le_rfl).mp this).mp ⟨i, rfl⟩

lemma aux_cycle_four_le {P : BlockPartition V ι} {i : ι}
    {w : (aux (G := G) P).Walk (.inl i) (.inl i)} (hc : w.IsCycle) :
    4 ≤ w.length := by
  have h3 : 3 ≤ w.length := hc.three_le_length
  have he : Even w.length := aux_cycle_even_length hc
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp he
  have : 2 ≤ k := by omega
  omega

/-- Yeo on the auxiliary colouring yields a block splitter: physical
vertices are excluded by the unconditional 1-tough transport. -/
lemma exists_block_splitter [Nonempty ι] (P : BlockPartition V ι)
    (port : V → Port) (hT : OneTough G) (hord : 3 ≤ Fintype.card V)
    (hpc : ¬ Yeo.HasProperlyColoredCycle (auxColoring (G := G) P port)) :
    ∃ i : ι, Yeo.SplittingVertex (auxColoring (G := G) P port) (.inl i) := by
  haveI : Nonempty (ι ⊕ PhysEdge (G := G) P) :=
    ⟨.inl (Classical.arbitrary ι)⟩
  obtain ⟨v, hv⟩ :=
    Yeo.yeo_separator (c := auxColoring (G := G) P port) hpc
  cases v with
  | inl i => exact ⟨i, hv⟩
  | inr e =>
    exact (not_splittingVertex_physEdge_of_oneTough P port hT hord e hv).elim

lemma mapWalk_not_mem_block {P : BlockPartition V ι} :
    ∀ {u v : V} (w : G.Walk u v) {i : ι}
      (hidx : ∀ x ∈ w.support, P.index x ≠ i),
      Sum.inl i ∉ (mapWalk (G := G) P w).support
  | _, _, Walk.nil, i, hidx, hmem => by
    simp [mapWalk] at hmem
    exact hidx _ (by simp [Walk.support]) (hmem.symm)
  | u, _, Walk.cons (v := w) hadj p, i, hidx, hmem => by
    have hidxp : ∀ x ∈ p.support, P.index x ≠ i := by
      intro x hx
      exact hidx x (by simp [Walk.support_cons, hx])
    by_cases hEq : P.index u = P.index w
    · rw [mapWalk, dif_pos hEq] at hmem
      exact mapWalk_not_mem_block p hidxp
        ((support_inl_rec hEq (mapWalk (G := G) P p) _).1 hmem)
    · rw [mapWalk, dif_neg hEq] at hmem
      simp only [Walk.support_cons, List.mem_cons] at hmem
      rcases hmem with h0 | h1 | hrest
      · exact hidx u (by simp) (by cases h0; rfl)
      · cases h1
      · exact mapWalk_not_mem_block p hidxp hrest

lemma reachable_aux_delete_block {P : BlockPartition V ι} {i : ι}
    {x y : V} (hx : P.index x ≠ i) (hy : P.index y ≠ i)
    (h : (G.induce {z | P.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (Yeo.deleteGraph (aux (G := G) P) (.inl i)).Reachable
      ⟨.inl (P.index x), by intro h'; cases h'; exact hx rfl⟩
      ⟨.inl (P.index y), by intro h'; cases h'; exact hy rfl⟩ := by
  obtain ⟨wInd⟩ := h
  let wG : G.Walk x y :=
    wInd.map (Embedding.induce {z | P.index z ≠ i}).toHom
  have hidx : ∀ z ∈ wG.support, P.index z ≠ i := by
    intro z hz
    rw [show wG.support = wInd.support.map
        (Embedding.induce {z | P.index z ≠ i}).toHom from Walk.support_map _ _] at hz
    obtain ⟨sz, _, hval⟩ := List.mem_map.1 hz
    have hcoe :
        (Embedding.induce (G := G) {z | P.index z ≠ i}).toHom sz = sz.val :=
      rfl
    have hzval : z = sz.val := hval.symm.trans hcoe
    rw [hzval]
    exact sz.property
  have havoid : ∀ t ∈ (mapWalk (G := G) P wG).support,
      t ∈ Yeo.deleteSet (.inl i) := by
    intro t ht ht'
    subst ht'
    exact mapWalk_not_mem_block wG hidx ht
  exact ⟨(mapWalk (G := G) P wG).induce (Yeo.deleteSet (.inl i)) havoid |>.copy
    (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- One-way attachment transport: two original attachments of the same
outside component into a splitting block use the same port. -/
lemma attachment_port_eq {P : BlockPartition V ι} (port : V → Port)
    {i : ι} (hsplit : Yeo.SplittingVertex (auxColoring (G := G) P port) (.inl i))
    {x y a b : V}
    (hx : P.index x ≠ i) (hy : P.index y ≠ i)
    (ha : P.index a = i) (hb : P.index b = i)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (hW : (G.induce {z | P.index z ≠ i}).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    port a = port b := by
  have hne_xa : P.index x ≠ P.index a := by simpa [ha] using hx
  have hne_yb : P.index y ≠ P.index b := by simpa [hb] using hy
  let ex := toPhys (G := G) P hxa hne_xa
  let ey := toPhys (G := G) P hyb hne_yb
  have hadx : (aux (G := G) P).Adj (.inl (P.index x)) (.inr ex) :=
    toPhys_incident_left (G := G) P hxa hne_xa
  have hady : (aux (G := G) P).Adj (.inl (P.index y)) (.inr ey) :=
    toPhys_incident_left (G := G) P hyb hne_yb
  have hada : (aux (G := G) P).Adj (.inl i) (.inr ex) := by
    simpa [ha] using toPhys_incident_right (G := G) P hxa hne_xa
  have hadb : (aux (G := G) P).Adj (.inl i) (.inr ey) := by
    simpa [hb] using toPhys_incident_right (G := G) P hyb hne_yb
  have hreach_xy := reachable_aux_delete_block hx hy hW
  have hx_e : (Yeo.deleteGraph (aux (G := G) P) (.inl i)).Adj
      ⟨.inl (P.index x), by intro h'; cases h'; exact hx rfl⟩
      ⟨.inr ex, by intro h'; cases h'⟩ := hadx
  have hy_e : (Yeo.deleteGraph (aux (G := G) P) (.inl i)).Adj
      ⟨.inl (P.index y), by intro h'; cases h'; exact hy rfl⟩
      ⟨.inr ey, by intro h'; cases h'⟩ := hady
  have hconn :
      (Yeo.deleteGraph (aux (G := G) P) (.inl i)).Reachable
        ⟨.inr ex, by intro h'; cases h'⟩
        ⟨.inr ey, by intro h'; cases h'⟩ :=
    (hx_e.reachable.symm.trans hreach_xy).trans hy_e.reachable
  have hcol :=
    hsplit ⟨.inr ex, by intro h'; cases h'⟩ ⟨.inr ey, by intro h'; cases h'⟩
      hada hadb hconn
  have enda : endpointOf (G := G) P i ex hada = a := by
    have hi : i = P.index a := ha.symm
    subst hi
    exact endpointOf_toPhys_right P hxa hne_xa
  have endb : endpointOf (G := G) P i ey hadb = b := by
    have hi : i = P.index b := hb.symm
    subst hi
    exact endpointOf_toPhys_right P hyb hne_yb
  have ca : (auxColor (G := G) P port hada).2 = port a := by
    simp [auxColor, enda]
  have cb : (auxColor (G := G) P port hadb).2 = port b := by
    simp [auxColor, endb]
  have hcol2 : (auxColor (G := G) P port hada).2 =
      (auxColor (G := G) P port hadb).2 :=
    congrArg Prod.snd (by simpa [auxColoring] using hcol)
  rw [ca, cb] at hcol2
  exact hcol2

lemma two_le_componentCount_of_not_reachable {U : Finset V} {x y : V}
    (hx : x ∈ U) (hy : y ∈ U)
    (h : ¬ (G.induce (U : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    2 ≤ componentCount G U := by
  let cx := (G.induce (U : Set V)).connectedComponentMk ⟨x, hx⟩
  let cy := (G.induce (U : Set V)).connectedComponentMk ⟨y, hy⟩
  have hne : cx ≠ cy := by
    intro hxy
    exact h (ConnectedComponent.eq.1 hxy)
  haveI : Nontrivial (G.induce (U : Set V)).ConnectedComponent := ⟨cx, cy, hne⟩
  have hlt : 1 < Fintype.card (G.induce (U : Set V)).ConnectedComponent :=
    Fintype.one_lt_card
  have : 2 ≤ Fintype.card (G.induce (U : Set V)).ConnectedComponent :=
    Nat.succ_le_of_lt hlt
  simpa [componentCount, Nat.card_eq_fintype_card] using this

/-- A walk in an induced set with no edges from `A` to `B` that starts in `A`
never leaves `A`. -/
lemma induce_walk_stays_left {A B : Finset V}
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : V} (hx : x ∈ A) (hxy : x ∈ A ∪ B) (hy : y ∈ A ∪ B)
    (w : (G.induce ((A ∪ B : Finset V) : Set V)).Walk ⟨x, hxy⟩ ⟨y, hy⟩) :
    y ∈ A := by
  have hvert : ∀ n, n ≤ w.length → (w.getVert n).1 ∈ A := by
    intro n hn
    induction n with
    | zero =>
      simpa [Walk.getVert_zero] using hx
    | succ n ih =>
      have hn' : n < w.length := Nat.lt_of_succ_le hn
      have hadj := w.adj_getVert_succ hn'
      have hAdjG : G.Adj (w.getVert n).1 (w.getVert (n + 1)).1 := by
        simpa [SimpleGraph.induce_adj] using hadj
      have hA : (w.getVert n).1 ∈ A := ih (Nat.le_of_lt hn')
      have hneib : (w.getVert (n + 1)).1 ∈ A ∪ B := (w.getVert (n + 1)).property
      rcases mem_union.1 hneib with hA' | hB
      · exact hA'
      · exact (hno _ hA _ hB hAdjG).elim
  simpa [Walk.getVert_length] using hvert w.length le_rfl

/-- Singleton original attachment of a nonempty outside set into a factor
block contradicts 1-toughness. -/
lemma not_singleton_attachment (hT : OneTough G) (_hord : 3 ≤ Fintype.card V)
    (F : CycleFactor G) {i : Fin F.card} {p : V}
    (hp : p ∈ (F.getCycle i).support)
    (hWne : (univ \ (F.getCycle i).support).Nonempty)
    (hatt : ∀ {x a : V}, a ∈ (F.getCycle i).support →
      x ∈ univ \ (F.getCycle i).support → G.Adj x a → a = p) :
    False := by
  have hpU : p ∈ (univ : Finset V) := mem_univ p
  let H := (F.getCycle i).support
  let A := H.erase p
  let B := univ \ H
  have hAne : A.Nonempty := by
    have h3 : 3 ≤ H.card := (F.getCycle i).three_le_card_support
    have hcard : A.card = H.card - 1 := card_erase_of_mem hp
    have : 0 < A.card := by
      have : 2 ≤ H.card - 1 := Nat.le_sub_of_add_le (by omega)
      omega
    exact card_pos.mp this
  have hBne : B.Nonempty := hWne
  have hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a ha b hb hadj
    have haH : a ∈ H := mem_of_mem_erase ha
    have hap : a ≠ p := ne_of_mem_erase ha
    have : a = p := hatt (a := a) (x := b) haH (by simpa [B] using hb) hadj.symm
    exact hap this
  have hAU : A ∪ B = univ.erase p := by
    ext z
    constructor
    · intro hz
      rw [mem_union] at hz
      rcases hz with hzA | hzB
      · exact mem_erase.2 ⟨ne_of_mem_erase hzA, mem_univ z⟩
      · have hzH : z ∉ H := (mem_sdiff.1 hzB).2
        exact mem_erase.2 ⟨fun hzp => hzH (hzp ▸ hp), mem_univ z⟩
    · intro hz
      obtain ⟨hzp, _⟩ := mem_erase.1 hz
      by_cases hzH : z ∈ H
      · exact mem_union.2 (Or.inl (mem_erase.2 ⟨hzp, hzH⟩))
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨mem_univ z, hzH⟩))
  have hxA : hAne.choose ∈ A ∪ B := mem_union_left _ hAne.choose_spec
  have hyB : hBne.choose ∈ A ∪ B := mem_union_right _ hBne.choose_spec
  have hnr :
      ¬ (G.induce ((A ∪ B : Finset V) : Set V)).Reachable
        ⟨hAne.choose, hxA⟩ ⟨hBne.choose, hyB⟩ := by
    intro hR
    obtain ⟨w⟩ := hR
    have hyA : hBne.choose ∈ A :=
      induce_walk_stays_left hno hAne.choose_spec hxA hyB w
    have hyB' : hBne.choose ∈ B := hBne.choose_spec
    have : hBne.choose ∈ H := mem_of_mem_erase hyA
    have : hBne.choose ∉ H := (mem_sdiff.1 hyB').2
    exact this ‹_ ∈ H›
  have h2 : 2 ≤ componentCount G (A ∪ B) :=
    two_le_componentCount_of_not_reachable hxA hyB hnr
  have hEq : univ \ {p} = A ∪ B := by
    simp [hAU, sdiff_singleton_eq_erase]
  have h2' : 2 ≤ componentCount G (univ \ {p}) := by
    simpa [hEq] using h2
  have hle := hT {p} h2'
  simp at hle
  omega

end Nikoghosyan


