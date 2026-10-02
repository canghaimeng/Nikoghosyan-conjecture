/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Nikoghosyan.PathBlockInsertion

/-!
Generic cycle-piece callback: insert an omitted original block into a
complementary path that retains an actual original edge.

If `r` is an original path that omits a block `Q` (`Disjoint Q.support
r.support`) and retains an original edge `u—v` as an actual walk-edge —
supplied by a `PrefixEdgeFactor`, not inferred from `u, v ∈ r.support` —
then `insertBlock` places all of `Q` onto `r` across the original seams
`u—Q.start` and `Q.finish—v`, without changing original-`A` incidences.

G2 must derive actual membership `s(u,v) ∈ r.edges` in the complement
from the exact complement-edge identity in `CycleEdgeRetention`
(filtered closed edges with both endpoints outside `Q.support`, or the
equivalent delete-`Q`-edges / delete-two-seams form). An edge-subset of
a prescribed cycle does not prove that a chosen old edge survives. This
module does not reconstruct leftover runs, does not prove same-sign
wrapping, and does not close `prof:thm:protected`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

variable {r : GraphPath G} {u v : V}

/-- The retained dart is the actual factor edge, not a support pair. -/
lemma retained_old_edge (F : PrefixEdgeFactor r u v) :
    s(u, v) ∈ r.edges :=
  F.old_mem_edges

/-- Insert an omitted outside block `Q` into a complementary path `r` at
the actual retained dart `u—v`. -/
def insertOmittedBlock (F : PrefixEdgeFactor r u v) (Q : GraphPath G)
    (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) : GraphPath G :=
  F.insertBlock Q hd hs hf

lemma insertOmittedBlock_start (F : PrefixEdgeFactor r u v) (Q : GraphPath G)
    (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).start = r.start :=
  F.insertBlock_start Q hd hs hf

lemma insertOmittedBlock_finish (F : PrefixEdgeFactor r u v) (Q : GraphPath G)
    (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).finish = r.finish :=
  F.insertBlock_finish Q hd hs hf

/-- The operation puts all of `Q` onto the complementary path. -/
theorem insertOmittedBlock_support (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).support = r.support ∪ Q.support :=
  F.insertBlock_support Q hd hs hf

/-- Exact outside-block sdiff: after insertion the complement vertices
are recovered by deleting `Q`. -/
theorem insertOmittedBlock_support_sdiff (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).support \ Q.support = r.support := by
  rw [insertOmittedBlock_support]
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro ⟨hx, hxQ⟩
    exact hx.resolve_right hxQ
  · intro hx
    exact ⟨Or.inl hx, disjoint_right.1 hd hx⟩

lemma insertOmittedBlock_start_mem_A (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (hA : r.start ∈ A) :
    (insertOmittedBlock F Q hd hs hf).start ∈ A := by
  simpa [insertOmittedBlock_start] using hA

lemma insertOmittedBlock_finish_mem_A (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (hA : r.finish ∈ A) :
    (insertOmittedBlock F Q hd hs hf).finish ∈ A := by
  simpa [insertOmittedBlock_finish] using hA

lemma insertOmittedBlock_contains_block (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    Q.support ⊆ (insertOmittedBlock F Q hd hs hf).support :=
  F.block_support_subset_insertBlock Q hd hs hf

theorem insertOmittedBlock_edges (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).edges =
      r.edges.erase s(u, v) ∪ Q.edges ∪
        {s(u, Q.start), s(Q.finish, v)} :=
  F.insertBlock_edges Q hd hs hf

/-- Original-`A` incidences, including original `A` seams of `r`, are
exactly unchanged. Block edges and the two new seams meet no vertex of
`A`. -/
theorem insertOmittedBlock_AIncident (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (huA : u ∉ A) (hvA : v ∉ A) (hAQ : Disjoint Q.support A) :
    (insertOmittedBlock F Q hd hs hf).AIncident A = r.AIncident A :=
  F.AIncident_insertBlock Q hd hs hf huA hvA hAQ

theorem insertOmittedBlock_incidentEdges (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V} {b : V}
    (hbA : b ∈ A) (huA : u ∉ A) (hvA : v ∉ A)
    (hAQ : Disjoint Q.support A) :
    (insertOmittedBlock F Q hd hs hf).incidentEdges b = r.incidentEdges b :=
  F.incidentEdges_insertBlock Q hd hs hf hbA huA hvA hAQ

theorem protectedAt_insertOmittedBlock (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v)
    {c : GraphCycle G} {A : Finset V}
    (huA : u ∉ A) (hvA : v ∉ A) (hAQ : Disjoint Q.support A)
    (hP : r.ProtectedAt c A) :
    (insertOmittedBlock F Q hd hs hf).ProtectedAt c A :=
  F.protectedAt_insertBlock Q hd hs hf huA hvA hAQ hP

/-- If after insertion the path spans the prescribed cycle, the exact
internal-2 / endpoint-1 bridge applies. The complementary path is not
assumed to span the cycle before insertion. -/
theorem protected_exact_of_insertOmittedBlock (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v)
    (c : GraphCycle G) {A : Finset V}
    (hsup : (insertOmittedBlock F Q hd hs hf).support = c.support)
    (hA : A ⊆ (insertOmittedBlock F Q hd hs hf).support)
    (huA : u ∉ A) (hvA : v ∉ A) (hAQ : Disjoint Q.support A)
    (hP : r.ProtectedAt c A) :
    (insertOmittedBlock F Q hd hs hf).ProtectedAt c A ∧
      (insertOmittedBlock F Q hd hs hf).start = r.start ∧
        (insertOmittedBlock F Q hd hs hf).finish = r.finish ∧
          (∀ b ∈ A,
            (insertOmittedBlock F Q hd hs hf).incidentEdges b =
              r.incidentEdges b) ∧
            (∀ b ∈ A, b ≠ r.start → b ≠ r.finish →
              (insertOmittedBlock F Q hd hs hf).incidentEdges b =
                c.incidentEdges b) := by
  obtain ⟨hProt, hst, hfin, hinc, hinter, _, _⟩ :=
    F.protected_exact_of_insertBlock Q hd hs hf c hsup hA huA hvA hAQ hP
  exact ⟨hProt, hst, hfin, hinc, hinter⟩

end GraphPath

end Nikoghosyan
