/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Basic
import Nikoghosyan.Cograph.Basic

/-!
# Transport between cograph predicates and the canonical foundation

`Nikoghosyan.Cograph.InducedP4` is a structure with the four distinct vertices,
the three path edges, and the three missing chords. The canonical
`Nikoghosyan.InducedP4` is the same mathematical predicate as a flattened
conjunction. This module records the equivalences; a cotree is not used.
-/

universe u

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The structured induced-`P4` predicate is definitionally the same data as the
canonical flattened conjunction. -/
lemma inducedP4_iff {G : SimpleGraph V} {a b c d : V} :
    InducedP4 G a b c d ↔ Nikoghosyan.InducedP4 G a b c d := by
  constructor
  · intro h
    exact ⟨h.ne_ab, h.ne_ac, h.ne_ad, h.ne_bc, h.ne_bd, h.ne_cd,
      h.adj_ab, h.adj_bc, h.adj_cd, h.not_ac, h.not_ad, h.not_bd⟩
  · intro h
    rcases h with ⟨nab, nac, nad, nbc, nbd, ncd, eab, ebc, ecd, nac', nad', nbd'⟩
    exact
      { ne_ab := nab
        ne_ac := nac
        ne_ad := nad
        ne_bc := nbc
        ne_bd := nbd
        ne_cd := ncd
        adj_ab := eab
        adj_bc := ebc
        adj_cd := ecd
        not_ac := nac'
        not_ad := nad'
        not_bd := nbd' }

lemma isCograph_iff {G : SimpleGraph V} {U : Finset V} :
    IsCograph G U ↔ Nikoghosyan.IsCograph G U := by
  constructor
  · intro h a b c d ha hb hc hd hp
    exact h ha hb hc hd (inducedP4_iff.2 hp)
  · intro h a b c d ha hb hc hd hp
    exact h ha hb hc hd (inducedP4_iff.1 hp)

lemma noInducedP4UnionP1_iff {G : SimpleGraph V} :
    NoInducedP4UnionP1 G ↔ Nikoghosyan.NoInducedP4UnionP1 G := by
  constructor
  · intro h a b c d x hp hxa hxb hxc hxd
    exact h (inducedP4_iff.2 hp) hxa hxb hxc hxd
  · intro h a b c d x hp hxa hxb hxc hxd
    exact h (inducedP4_iff.1 hp) hxa hxb hxc hxd

lemma isCographGraph_iff_isCograph_univ {G : SimpleGraph V} :
    IsCographGraph G ↔ Nikoghosyan.IsCograph G Finset.univ := by
  rw [isCographGraph_iff_univ, isCograph_iff]

/-- Canonical `antineighbors` is the finset of the set-valued `antineighborhood`. -/
lemma antineighbors_coe (G : SimpleGraph V) (v : V) :
    (Nikoghosyan.antineighbors G v : Set V) = antineighborhood G v := by
  ext x
  simp [Nikoghosyan.antineighbors, antineighborhood]

end Cograph
end Nikoghosyan
