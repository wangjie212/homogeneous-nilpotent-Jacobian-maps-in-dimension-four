import DimensionFourDependence.ConeParameterDifferential
import DimensionFourDependence.GaussRulingIncidence

/-! # The original Gauss parameter in the actual image-cone residue field

The image prime's residue field embeds into the original source field
by evaluating at H. The original Gauss curve and its rational parameter
are lifted through this embedding, preserving every normal coordinate.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- Evaluation at the actual original map embeds the function field
of its image cone into the original source function field. -/
noncomputable def imageConeResidueEmbedding
    (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (imageRelationIdeal H).ResidueField →ₐ[K] FractionRing (MvPolynomial (Fin 4) K) := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] FractionRing (MvPolynomial (Fin 4) K) :=
    aeval (fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i))
  have hker : imageRelationIdeal H = RingHom.ker f := imageRelationIdeal_eq_rational_relations H
  apply Ideal.ResidueField.liftₐ (imageRelationIdeal H) f hker.le
  intro p hp
  change IsUnit (f p)
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply hp
  rw [hker]
  exact hz

/-- Every original polynomial retains its exact value under the
constructed cone embedding. -/
theorem imageConeResidueEmbedding_polynomial
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : MvPolynomial (Fin 4) K) :
    imageConeResidueEmbedding H (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p) =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (aeval H p) := by
  unfold imageConeResidueEmbedding
  rw [Ideal.ResidueField.liftₐ_algebraMap, ← aeval_polynomial_to_fraction]

/-- The entire actual Gauss field, not just its parameter, lies in
the image-cone field's actual realization in the original source. -/
theorem actual_gauss_field_le_imageConeResidueEmbedding_range
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) ≤
      (imageConeResidueEmbedding H).fieldRange := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  apply AlgHom.mem_fieldRange.mpr
  refine ⟨algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (pderiv i I.equation) /
    algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField
      (pderiv (imageNormalPivot H I) I.equation), ?_⟩
  rw [map_div₀, imageConeResidueEmbedding_polynomial, imageConeResidueEmbedding_polynomial]
  rfl

/-- The original birational Gauss parameter is realized in the actual
image-cone residue field, before any finite closed Gauss cover. -/
noncomputable def imageConeGaussHom
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    RatFunc K →ₐ[K] (imageRelationIdeal H).ResidueField :=
  (imageConeResidueEmbedding H).equivFieldRange.symm.toAlgHom.comp
    ((gaussParameterSourceHom H I e).codRestrict
      (imageConeResidueEmbedding H).fieldRange.toSubalgebra
      (fun r => actual_gauss_field_le_imageConeResidueEmbedding_range H I (e r).property))

/-- Realizing the cone parameter in the original source recovers the
original Gauss parameter homomorphism on every rational function. -/
theorem imageConeGaussHom_realization
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) (r : RatFunc K) :
    imageConeResidueEmbedding H (imageConeGaussHom H I e r) = gaussParameterSourceHom H I e r := by
  change ((imageConeResidueEmbedding H).equivFieldRange
    ((imageConeResidueEmbedding H).equivFieldRange.symm _ ) : FractionRing (MvPolynomial (Fin 4) K)) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The actual cone normal pivot is nonzero; this is derived from
the original image normal pivot through the faithful cone embedding. -/
theorem image_cone_normal_pivot_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField
      (pderiv (imageNormalPivot H I) I.equation) ≠ 0 := by
  intro hz
  have he := congrArg (imageConeResidueEmbedding H) hz
  rw [imageConeResidueEmbedding_polynomial, map_zero] at he
  exact imageNormalPivot_ne_zero H I he

/-- Every original cone normal ratio equals the same actual rational
function of the original Gauss parameter as at the generic output. -/
theorem imageConeGaussHom_normal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) (i : Fin 4) :
    imageConeGaussHom H I e (gaussParameterNormal H I e i) =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (pderiv i I.equation) /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField
          (pderiv (imageNormalPivot H I) I.equation) := by
  apply (imageConeResidueEmbedding H).injective
  change imageConeResidueEmbedding H (imageConeGaussHom H I e (gaussParameterNormal H I e i)) =
    imageConeResidueEmbedding H (_ / _)
  rw [imageConeGaussHom_realization, gaussParameterSourceHom_normal,
    map_div₀, imageConeResidueEmbedding_polynomial, imageConeResidueEmbedding_polynomial]
  rfl

/-- The original Gauss parameter is transcendental in the actual
cone field, without a supplied transcendence or chosen differential. -/
theorem imageConeGaussHom_parameter_transcendental
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    Transcendental K (imageConeGaussHom H I e RatFunc.X) := by
  intro ht
  exact RatFunc.transcendental_X
    ((isAlgebraic_algHom_iff (imageConeGaussHom H I e) (imageConeGaussHom H I e).injective).mp ht)

end DimensionFourDependence
