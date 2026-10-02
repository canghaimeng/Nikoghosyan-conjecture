/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.PathCoverJoin

/-!
# N-ary original complete join from checked binary recurrences

Manuscript grouping recipe: a finite nonempty family of nonempty pairwise
disjoint blocks with every original cross edge present has
`p(U) = max 1 (max_i (p(X_i) - |U \ X_i|))`. If every original child is
balanced against the outside, the binary balanced cycle on the first block
versus the union of the rest applies when `|U| ≥ 3`. Capacity of the grouped
remainder is derived, not assumed.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Union of a finite list of vertex blocks. -/
def unionList : List (Finset V) → Finset V
  | [] => ∅
  | a :: t => a ∪ unionList t

lemma unionList_cons (a : Finset V) (t : List (Finset V)) :
    unionList (a :: t) = a ∪ unionList t := rfl

lemma subset_unionList_of_mem {xs : List (Finset V)} {A : Finset V}
    (h : A ∈ xs) : A ⊆ unionList xs := by
  induction xs with
  | nil => cases h
  | cons b t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact subset_union_left
    · exact (ih h).trans subset_union_right

lemma disjoint_unionList_of_pairwise {A : Finset V} {t : List (Finset V)}
    (h : ∀ B ∈ t, Disjoint A B) : Disjoint A (unionList t) := by
  induction t with
  | nil => simp [unionList]
  | cons B t ih =>
    rw [unionList_cons, disjoint_union_right]
    exact ⟨h B (List.mem_cons.2 (Or.inl rfl)),
      ih fun C hC => h C (List.mem_cons.2 (Or.inr hC))⟩

lemma mem_unionList_iff {xs : List (Finset V)} {x : V} :
    x ∈ unionList xs ↔ ∃ A ∈ xs, x ∈ A := by
  induction xs with
  | nil => simp [unionList]
  | cons A t ih =>
    simp only [unionList_cons, mem_union, ih, List.mem_cons]
    constructor
    · intro h
      rcases h with hxA | ⟨B, hB, hxB⟩
      · exact ⟨A, Or.inl rfl, hxA⟩
      · exact ⟨B, Or.inr hB, hxB⟩
    · intro ⟨B, hB, hxB⟩
      rcases hB with rfl | hB
      · exact Or.inl hxB
      · exact Or.inr ⟨B, hB, hxB⟩

def PairwiseDisjointBlocks (xs : List (Finset V)) : Prop :=
  List.Pairwise Disjoint xs

def PairwiseCompleteJoin (xs : List (Finset V)) : Prop :=
  ∀ A ∈ xs, ∀ B ∈ xs, A ≠ B → G.IsCompleteBetween (A : Set V) (B : Set V)

lemma pairwiseDisjoint_cons {A : Finset V} {t : List (Finset V)}
    (h : PairwiseDisjointBlocks (A :: t)) :
    (∀ B ∈ t, Disjoint A B) ∧ PairwiseDisjointBlocks t :=
  List.pairwise_cons.1 h

lemma completeJoin_unionList {A : Finset V} {t : List (Finset V)}
    (hAne : A.Nonempty)
    (hdisj : ∀ B ∈ t, Disjoint A B)
    (hcomp : PairwiseCompleteJoin (G := G) (A :: t))
    (hne : ∀ B ∈ t, B.Nonempty) :
    G.IsCompleteBetween (A : Set V) (unionList t : Set V) := by
  intro a ha b hb
  obtain ⟨B, hB, hbB⟩ := mem_unionList_iff.1 (show b ∈ unionList t from hb)
  have hAB : A ≠ B := by
    intro hEq
    have : Disjoint A B := hdisj B hB
    have hA0 : A = ∅ := disjoint_self.1 (by simpa [hEq] using this)
    exact hAne.ne_empty hA0
  exact hcomp A (List.mem_cons.2 (Or.inl rfl)) B (List.mem_cons.2 (Or.inr hB))
    hAB ha hbB

lemma card_unionList_cons {A : Finset V} {t : List (Finset V)}
    (hdisj : ∀ B ∈ t, Disjoint A B) :
    (unionList (A :: t)).card = A.card + (unionList t).card := by
  rw [unionList_cons, card_union_of_disjoint (disjoint_unionList_of_pairwise hdisj)]

lemma unionList_nonempty_of {t : List (Finset V)}
    (htne : t ≠ []) (hne : ∀ B ∈ t, B.Nonempty) :
    (unionList t).Nonempty := by
  cases t with
  | nil => exact (htne rfl).elim
  | cons B rest =>
    exact (hne B (List.mem_cons.2 (Or.inl rfl))).mono
      (subset_unionList_of_mem (List.mem_cons.2 (Or.inl rfl)))

/-- Maximum truncated child excess `max_i (p(X_i) - (|U| - |X_i|))`. -/
noncomputable def maxChildExcess (U : Finset V) (xs : List (Finset V)) : ℕ :=
  xs.foldr (fun X acc => max (pathCoverNumber G X - (U.card - X.card)) acc) 0

lemma maxChildExcess_cons (U A : Finset V) (t : List (Finset V)) :
    maxChildExcess (G := G) U (A :: t) =
      max (pathCoverNumber G A - (U.card - A.card))
        (maxChildExcess (G := G) U t) :=
  rfl

lemma max_tsub_distrib (a b c : ℕ) : max a b - c = max (a - c) (b - c) := by
  omega

/-- If every block satisfies `|U| - |X| = |W| - |X| + k`, the excess list
scales by truncated subtraction of `k`. -/
lemma maxChildExcess_of_add_card {U W : Finset V} (k : ℕ) :
    ∀ xs : List (Finset V),
      (∀ X ∈ xs, U.card - X.card = (W.card - X.card) + k) →
        maxChildExcess (G := G) U xs = maxChildExcess (G := G) W xs - k
  | [], _ => by simp [maxChildExcess]
  | X :: t, h => by
    have hX := h X (List.mem_cons.2 (Or.inl rfl))
    have ht : ∀ Y ∈ t, U.card - Y.card = (W.card - Y.card) + k :=
      fun Y hY => h Y (List.mem_cons.2 (Or.inr hY))
    have hcell :
        pathCoverNumber G X - (U.card - X.card) =
          (pathCoverNumber G X - (W.card - X.card)) - k := by omega
    simp only [maxChildExcess_cons, hcell,
      maxChildExcess_of_add_card k t ht, max_tsub_distrib]

lemma maxChildExcess_scale_union {A : Finset V} {t : List (Finset V)}
    (hdisj : ∀ B ∈ t, Disjoint A B) :
    maxChildExcess (G := G) (unionList (A :: t)) t =
      maxChildExcess (G := G) (unionList t) t - A.card := by
  refine maxChildExcess_of_add_card A.card t ?_
  intro X hX
  have hXsub : X ⊆ unionList t := subset_unionList_of_mem hX
  have hU := card_unionList_cons hdisj
  have hle : X.card ≤ (unionList t).card := card_le_card hXsub
  omega

lemma pathCoverNumber_nary_singleton {A : Finset V} (hA : A.Nonempty) :
    pathCoverNumber G A =
      max 1 (maxChildExcess (G := G) A [A]) := by
  have hp : 1 ≤ pathCoverNumber G A :=
    one_le_pathCoverNumber_of_nonempty (G := G) hA
  simp [maxChildExcess, hp]

lemma pathCoverNumber_nary_cons {A : Finset V} {t : List (Finset V)}
    (hA : A.Nonempty) (htne : t ≠ [])
    (hne : ∀ B ∈ t, B.Nonempty)
    (hdisj : PairwiseDisjointBlocks (A :: t))
    (hcomp : PairwiseCompleteJoin (G := G) (A :: t))
    (hIH : pathCoverNumber G (unionList t) =
      max 1 (maxChildExcess (G := G) (unionList t) t)) :
    pathCoverNumber G (unionList (A :: t)) =
      max 1 (maxChildExcess (G := G) (unionList (A :: t)) (A :: t)) := by
  have htpair := pairwiseDisjoint_cons hdisj
  have hBne : (unionList t).Nonempty := unionList_nonempty_of htne hne
  have hAB : G.IsCompleteBetween (A : Set V) (unionList t : Set V) :=
    completeJoin_unionList hA htpair.1 hcomp hne
  have hbin := pathCoverNumber_complete_join hA hBne hAB
  have hU : unionList (A :: t) = A ∪ unionList t := unionList_cons A t
  have hscale := maxChildExcess_scale_union (G := G) (A := A) (t := t) htpair.1
  have hAex :
      pathCoverNumber G A - ((unionList (A :: t)).card - A.card) =
        pathCoverNumber G A - (unionList t).card := by
    have := card_unionList_cons htpair.1
    omega
  have ha1 : 1 - A.card = 0 := by
    have : 1 ≤ A.card := Nat.succ_le_of_lt (card_pos.2 hA)
    omega
  have hpBsub :
      pathCoverNumber G (unionList t) - A.card =
        maxChildExcess (G := G) (unionList t) t - A.card := by
    rw [hIH, max_tsub_distrib, ha1]
    omega
  have hmax :
      max 1 (max (pathCoverNumber G A - (unionList t).card)
        (pathCoverNumber G (unionList t) - A.card)) =
      max 1 (maxChildExcess (G := G) (unionList (A :: t)) (A :: t)) := by
    simp only [maxChildExcess_cons, hAex, hpBsub, hscale]
  simpa [hU] using hbin.trans hmax

lemma pathCoverNumber_nary :
    ∀ (xs : List (Finset V)),
      xs ≠ [] →
      (∀ A ∈ xs, A.Nonempty) →
      PairwiseDisjointBlocks xs →
      PairwiseCompleteJoin (G := G) xs →
        pathCoverNumber G (unionList xs) =
          max 1 (maxChildExcess (G := G) (unionList xs) xs)
  | [A], _, hne, _, _ => by
    simpa [unionList] using pathCoverNumber_nary_singleton (hne A (by simp))
  | A :: B :: t, _, hne, hdisj, hcomp => by
    have hrest_ne : (B :: t : List (Finset V)) ≠ [] := by simp
    have hne_rest : ∀ C ∈ B :: t, C.Nonempty := fun C hC =>
      hne C (List.mem_cons.2 (Or.inr hC))
    have hdisj_rest : PairwiseDisjointBlocks (B :: t) :=
      (pairwiseDisjoint_cons hdisj).2
    have hcomp_rest : PairwiseCompleteJoin (G := G) (B :: t) := by
      intro C hC D hD hCD
      exact hcomp C (List.mem_cons.2 (Or.inr hC)) D (List.mem_cons.2 (Or.inr hD)) hCD
    have hIH :=
      pathCoverNumber_nary (B :: t) hrest_ne hne_rest hdisj_rest hcomp_rest
    exact pathCoverNumber_nary_cons (hne A (by simp)) hrest_ne hne_rest
      hdisj hcomp hIH

lemma maxChildExcess_le_of_balanced {A : Finset V} {t : List (Finset V)}
    (hdisj : ∀ B ∈ t, Disjoint A B)
    (hbal : ∀ X ∈ t,
      pathCoverNumber G X ≤ (unionList (A :: t)).card - X.card) :
    maxChildExcess (G := G) (unionList t) t ≤ A.card := by
  have hgen :
      ∀ zs : List (Finset V),
        (∀ Z ∈ zs, Z ∈ t) →
          maxChildExcess (G := G) (unionList t) zs ≤ A.card := by
    intro zs
    induction zs with
    | nil => intro; simp [maxChildExcess]
    | cons Z zs ih =>
      intro hmem
      simp only [maxChildExcess_cons]
      have hZ : Z ∈ t := hmem Z (List.mem_cons.2 (Or.inl rfl))
      have hpZ := hbal Z hZ
      have hZsub : Z ⊆ unionList t := subset_unionList_of_mem hZ
      have hleZ : Z.card ≤ (unionList t).card := card_le_card hZsub
      have hU := card_unionList_cons hdisj
      have hcell : pathCoverNumber G Z - ((unionList t).card - Z.card) ≤ A.card := by
        omega
      exact max_le hcell (ih fun W hW => hmem W (List.mem_cons.2 (Or.inr hW)))
  exact hgen t (fun Z hZ => hZ)

lemma pathCoverNumber_grouped_balanced {A : Finset V} {t : List (Finset V)}
    (hA : A.Nonempty) (htne : t ≠ [])
    (hne : ∀ B ∈ t, B.Nonempty)
    (hdisj : PairwiseDisjointBlocks (A :: t))
    (hcomp : PairwiseCompleteJoin (G := G) (A :: t))
    (hbal : ∀ X ∈ A :: t,
      pathCoverNumber G X ≤ (unionList (A :: t)).card - X.card) :
    pathCoverNumber G A ≤ (unionList t).card ∧
      pathCoverNumber G (unionList t) ≤ A.card := by
  have htpair := pairwiseDisjoint_cons hdisj
  have hUcard := card_unionList_cons htpair.1
  have hpA : pathCoverNumber G A ≤ (unionList (A :: t)).card - A.card :=
    hbal A (List.mem_cons.2 (Or.inl rfl))
  have hpA' : pathCoverNumber G A ≤ (unionList t).card := by omega
  have hdisj_rest : PairwiseDisjointBlocks t := htpair.2
  have hcomp_rest : PairwiseCompleteJoin (G := G) t := by
    intro C hC D hD hCD
    exact hcomp C (List.mem_cons.2 (Or.inr hC)) D (List.mem_cons.2 (Or.inr hD)) hCD
  have hIH := pathCoverNumber_nary t htne hne hdisj_rest hcomp_rest
  have hmaxB :=
    maxChildExcess_le_of_balanced htpair.1
      (fun X hX => hbal X (List.mem_cons.2 (Or.inr hX)))
  have hpB : pathCoverNumber G (unionList t) ≤ A.card := by
    have h1 : 1 ≤ A.card := Nat.succ_le_of_lt (card_pos.2 hA)
    rw [hIH]
    exact max_le h1 hmaxB
  exact ⟨hpA', hpB⟩

lemma exists_nary_complete_join_cycle {A : Finset V} {t : List (Finset V)}
    (hA : A.Nonempty) (htne : t ≠ [])
    (hne : ∀ B ∈ t, B.Nonempty)
    (hdisj : PairwiseDisjointBlocks (A :: t))
    (hcomp : PairwiseCompleteJoin (G := G) (A :: t))
    (hbal : ∀ X ∈ A :: t,
      pathCoverNumber G X ≤ (unionList (A :: t)).card - X.card)
    (h3 : 3 ≤ (unionList (A :: t)).card) :
    ∃ c : GraphCycle G, c.support = unionList (A :: t) := by
  obtain ⟨hpA, hpB⟩ :=
    pathCoverNumber_grouped_balanced hA htne hne hdisj hcomp hbal
  have htpair := pairwiseDisjoint_cons hdisj
  have hBne : (unionList t).Nonempty := unionList_nonempty_of htne hne
  have hAB : G.IsCompleteBetween (A : Set V) (unionList t : Set V) :=
    completeJoin_unionList hA htpair.1 hcomp hne
  obtain ⟨c, hc⟩ :=
    exists_complete_join_cycle hA hBne hAB hpA hpB
      (by simpa [unionList_cons] using h3)
  refine ⟨c, ?_⟩
  simpa [unionList_cons] using hc

lemma exists_nary_complete_join_spanning_path {A : Finset V} {t : List (Finset V)}
    (hA : A.Nonempty) (htne : t ≠ [])
    (hne : ∀ B ∈ t, B.Nonempty)
    (hdisj : PairwiseDisjointBlocks (A :: t))
    (hcomp : PairwiseCompleteJoin (G := G) (A :: t))
    (hbal : ∀ X ∈ A :: t,
      pathCoverNumber G X ≤ (unionList (A :: t)).card - X.card) :
    ∃ r : GraphPath G,
      r.support = unionList (A :: t) ∧ r.start ∈ A ∧ r.finish ∈ unionList t := by
  obtain ⟨hpA, hpB⟩ :=
    pathCoverNumber_grouped_balanced hA htne hne hdisj hcomp hbal
  have htpair := pairwiseDisjoint_cons hdisj
  have hBne : (unionList t).Nonempty := unionList_nonempty_of htne hne
  have hAB : G.IsCompleteBetween (A : Set V) (unionList t : Set V) :=
    completeJoin_unionList hA htpair.1 hcomp hne
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_complete_join_spanning_path hA hBne hAB hpA hpB
  refine ⟨r, ?_, hs, hf⟩
  simpa [unionList_cons] using hr

end Cograph
end Nikoghosyan
