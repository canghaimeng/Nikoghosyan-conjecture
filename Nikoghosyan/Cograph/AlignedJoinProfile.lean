import Nikoghosyan.Cograph.SaturatedJoin

namespace Nikoghosyan.Cograph

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- One genuine eligible endpoint on `X` fixes the dominant side whenever
the joined carrier needs at least two paths. No cycle or cograph is assumed. -/
theorem aligned_join_profile_of_eligible {X Y : Finset V} {x : V}
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXY : G.IsCompleteBetween (X : Set V) (Y : Set V))
    (h2 : 2 ≤ pathCoverNumber G (X ∪ Y))
    (hxE : x ∈ eligibleSet G (X ∪ Y)) (hxX : x ∈ X) :
    pathCoverNumber G X = pathCoverNumber G (X ∪ Y) + Y.card ∧
      eligibleSet G (X ∪ Y) = eligibleSet G X ∧
      pathCoverNumber G (X ∪ Y) + Y.card ≤ X.card := by
  have hdisj := disjoint_of_completeBetween hXY
  have hYX : G.IsCompleteBetween (Y : Set V) (X : Set V) :=
    fun {_} hy {_} hx => (hXY hx hy).symm
  have hYle : pathCoverNumber G Y ≤ X.card := by
    by_contra hnot
    have hYdom : X.card < pathCoverNumber G Y := Nat.lt_of_not_ge hnot
    have hE := eligibleSet_complete_join_dominant hY hX hYX hYdom
    have hxEY : x ∈ eligibleSet G Y := by
      have hxRev : x ∈ eligibleSet G (Y ∪ X) := by
        simpa [union_comm] using hxE
      rw [hE] at hxRev
      exact hxRev
    exact disjoint_left.1 hdisj hxX (eligibleSet_subset (G := G) Y hxEY)
  have hXdom : Y.card < pathCoverNumber G X := by
    by_contra hnot
    have hXle : pathCoverNumber G X ≤ Y.card := Nat.le_of_not_gt hnot
    have hformula := pathCoverNumber_complete_join hX hY hXY
    have hone : pathCoverNumber G (X ∪ Y) = 1 := by
      simpa [Nat.sub_eq_zero_of_le hXle, Nat.sub_eq_zero_of_le hYle] using hformula
    omega
  have hp := pathCoverNumber_add_card_of_dominant hX hY hXY hXdom
  refine ⟨hp, eligibleSet_complete_join_dominant hX hY hXY hXdom, ?_⟩
  rw [← hp]
  exact pathCoverNumber_le_card (G := G) X

end Nikoghosyan.Cograph
