/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Nikoghosyan.Cograph.EndpointCuts

/-!
# Profile scattering maximum

Manuscript `cog:prop:profile`: for `A ⊆ U` with nonempty cograph remainder
`K = U \ A`, the integer `δ_A = p(K) - |A|` is an upper bound on
`c(U \ T) - |T|` for every `T` with `A ⊆ T ⊆ U`, including remainders with
zero or one component. The container `T_A = A ∪ F(K)` attains the bound and
is the unique largest maximizer. No toughness or Hamiltonicity hypothesis is
imposed on `U`. Truncated natural subtraction is never used for `δ_A`.
-/

universe u

set_option linter.unusedSectionVars false

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Integer scattering `δ_A = p(U \ A) - |A|`. Negative values are retained. -/
noncomputable def profileDelta (U A : Finset V) : ℤ :=
  (pathCoverNumber G (U \ A) : ℤ) - (A.card : ℤ)

/-- Canonical candidate maximizer `T_A = A ∪ F(U \ A)`. -/
noncomputable def profileContainer (U A : Finset V) : Finset V :=
  A ∪ ineligibleSet G (U \ A)

lemma sdiff_eq_nested_sdiff {A T U : Finset V} (hAT : A ⊆ T) (_hTU : T ⊆ U) :
    U \ T = (U \ A) \ (T \ A) := by
  ext x
  simp only [mem_sdiff]
  constructor
  · intro hx
    exact ⟨⟨hx.1, fun hA => hx.2 (hAT hA)⟩, fun hTA => hx.2 hTA.1⟩
  · intro hx
    exact ⟨hx.1.1, fun hT => hx.2 ⟨hT, hx.1.2⟩⟩

lemma card_eq_add_sdiff {A T : Finset V} (hAT : A ⊆ T) :
    T.card = A.card + (T \ A).card := by
  have hdisj : Disjoint A (T \ A) := disjoint_sdiff
  have hunion : A ∪ (T \ A) = T := union_sdiff_of_subset hAT
  have := card_union_of_disjoint (s := A) (t := T \ A) hdisj
  simpa [hunion] using this

lemma profileDelta_le_of_nested {U A T : Finset V}
    (hAT : A ⊆ T) (hTU : T ⊆ U) :
    (componentCount G (U \ T) : ℤ) - (T.card : ℤ) ≤ profileDelta (G := G) U A := by
  have hEq : U \ T = (U \ A) \ (T \ A) := sdiff_eq_nested_sdiff hAT hTU
  have hXsub : T \ A ⊆ U \ A := sdiff_subset_sdiff hTU (subset_refl _)
  have hcle := componentCount_sdiff_le (G := G) (U \ A) (T \ A) hXsub
  have hcard := card_eq_add_sdiff hAT
  simp only [profileDelta, hEq]
  omega

lemma profileContainer_subset {U A : Finset V} (hA : A ⊆ U) :
    profileContainer (G := G) U A ⊆ U := by
  intro x hx
  rcases mem_union.1 hx with hA' | hF
  · exact hA hA'
  · exact (mem_sdiff.1 (ineligibleSet_subset (G := G) (U \ A) hF)).1

lemma sdiff_profileContainer {U A : Finset V} (hA : A ⊆ U) :
    U \ profileContainer (G := G) U A =
      (U \ A) \ ineligibleSet G (U \ A) := by
  have hF : ineligibleSet G (U \ A) ⊆ U \ A :=
    ineligibleSet_subset (G := G) (U \ A)
  have hAT : A ⊆ profileContainer (G := G) U A := subset_union_left
  have hTU := profileContainer_subset (G := G) hA
  have hnested := sdiff_eq_nested_sdiff hAT hTU
  have hX : profileContainer (G := G) U A \ A = ineligibleSet G (U \ A) := by
    have hdisj : Disjoint A (ineligibleSet G (U \ A)) := by
      refine disjoint_left.2 ?_
      intro x hxA hxF
      exact (mem_sdiff.1 (hF hxF)).2 hxA
    have : (A ∪ ineligibleSet G (U \ A)) \ A = ineligibleSet G (U \ A) := by
      rw [union_sdiff_left, sdiff_eq_left.2 hdisj.symm]
    simpa [profileContainer] using this
  simpa [hX] using hnested

lemma profileContainer_card {U A : Finset V} (_hA : A ⊆ U) :
    (profileContainer (G := G) U A).card =
      A.card + (ineligibleSet G (U \ A)).card := by
  have hdisj : Disjoint A (ineligibleSet G (U \ A)) := by
    refine disjoint_left.2 ?_
    intro x hxA hxF
    exact (mem_sdiff.1
      (ineligibleSet_subset (G := G) (U \ A) hxF)).2 hxA
  simpa [profileContainer] using
    (card_union_of_disjoint (s := A) (t := ineligibleSet G (U \ A)) hdisj)

/-- `T_A` attains `δ_A` on every nonempty cograph remainder. -/
lemma profileContainer_attains {U A : Finset V}
    (hA : A ⊆ U) (hK : IsCograph G (U \ A))
    (_hKne : (U \ A).Nonempty) :
    (componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A := by
  have hF := componentCount_sdiff_ineligibleSet_eq (cotreeOn_of_isCograph hK)
  have hrem := sdiff_profileContainer (G := G) hA
  have hcard := profileContainer_card (G := G) hA
  simp only [profileDelta, hrem, hcard]
  omega

lemma profileContainer_attains_of_canonical {U A : Finset V}
    (hA : A ⊆ U) (hK : Nikoghosyan.IsCograph G (U \ A))
    (hKne : (U \ A).Nonempty) :
    (componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A :=
  profileContainer_attains hA (isCograph_iff.2 hK) hKne

/-- Every maximizer is contained in `T_A`. -/
lemma profile_maximizer_subset_container {U A T : Finset V}
    (hAT : A ⊆ T) (hTU : T ⊆ U) (_hK : IsCograph G (U \ A))
    (hatt :
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
        profileDelta (G := G) U A) :
    T ⊆ profileContainer (G := G) U A := by
  have hEq : U \ T = (U \ A) \ (T \ A) := sdiff_eq_nested_sdiff hAT hTU
  have hXsub : T \ A ⊆ U \ A := sdiff_subset_sdiff hTU (subset_refl _)
  have hcard := card_eq_add_sdiff hAT
  have hcle := componentCount_sdiff_le (G := G) (U \ A) (T \ A) hXsub
  have heqNat :
      componentCount G ((U \ A) \ (T \ A)) =
        pathCoverNumber G (U \ A) + (T \ A).card := by
    simp only [profileDelta, hEq] at hatt
    omega
  have hXinc :=
    eq_cut_bound_imp_subset_ineligible (G := G) (U := U \ A) (X := T \ A)
      hXsub heqNat
  intro x hxT
  by_cases hxA : x ∈ A
  · exact mem_union.2 (Or.inl hxA)
  · exact mem_union.2 (Or.inr (hXinc (mem_sdiff.2 ⟨hxT, hxA⟩)))

lemma profile_maximizer_subset_container_of_canonical {U A T : Finset V}
    (hAT : A ⊆ T) (hTU : T ⊆ U) (hK : Nikoghosyan.IsCograph G (U \ A))
    (hatt :
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
        profileDelta (G := G) U A) :
    T ⊆ profileContainer (G := G) U A :=
  profile_maximizer_subset_container hAT hTU (isCograph_iff.2 hK) hatt

/-- Packaged profile-scattering maximum: `δ_A` is the exact maximum of
`c(U \ T) - |T|` over `A ⊆ T ⊆ U`, and `T_A` is the unique largest maximizer. -/
lemma profile_scattering_maximum {U A : Finset V}
    (hA : A ⊆ U) (hK : IsCograph G (U \ A)) (hKne : (U \ A).Nonempty) :
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) ≤
        profileDelta (G := G) U A) ∧
    ((componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T ⊆ profileContainer (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T.card ≤ (profileContainer (G := G) U A).card) := by
  refine ⟨?_, profileContainer_attains hA hK hKne, ?_, ?_⟩
  · intro T hAT hTU
    exact profileDelta_le_of_nested hAT hTU
  · intro T hAT hTU hatt
    exact profile_maximizer_subset_container hAT hTU hK hatt
  · intro T hAT hTU hatt
    exact card_le_card
      (profile_maximizer_subset_container hAT hTU hK hatt)

lemma profile_scattering_maximum_of_canonical {U A : Finset V}
    (hA : A ⊆ U) (hK : Nikoghosyan.IsCograph G (U \ A))
    (hKne : (U \ A).Nonempty) :
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) ≤
        profileDelta (G := G) U A) ∧
    ((componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T ⊆ profileContainer (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T.card ≤ (profileContainer (G := G) U A).card) :=
  profile_scattering_maximum hA (isCograph_iff.2 hK) hKne

end Cograph
end Nikoghosyan
