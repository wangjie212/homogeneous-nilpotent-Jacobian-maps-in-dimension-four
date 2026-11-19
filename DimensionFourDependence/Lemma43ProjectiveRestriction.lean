import DimensionFourDependence.Lemma43ConeRestriction
import DimensionFourDependence.ProjectiveImage

/-! # Lemma 4.3 for the actual projective image restriction

The image of the restriction of [P] is represented by the actual
projective image of P composed with H. Its equality with the original
image gives equality of the original cone relation primes. This supplies
the field pullback used in the checked cone contradiction.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A primitive polynomial part is defined at the actual image
generic point: its components cannot all vanish on the image cone. -/
theorem primitive_part_composite_image_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (P : Fin 4 → MvPolynomial (Fin 4) K)
    (hprim : IsPrimitiveVec P) : (fun i => aeval H (P i)) ≠ 0 := by
  intro hz
  apply I.irreducible.not_isUnit
  apply hprim I.equation
  intro i
  exact (I.relation_iff_dvd H hrank (P i)).mp (congrFun hz i)

/-- The actual projective restriction is dominant exactly when its
closed image, computed from the original generic parametrization H,
equals the original projective image in Mathlib's projective spectrum. -/
noncomputable def originalProjectiveRestrictionDominant
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) : Prop :=
  projectiveImageSet (fun i => aeval H (P i)) (Nat.mul_pos hd hD)
      (fun i => (hP i).aeval H hH) (primitive_part_composite_image_ne_zero H hrank I P hprim) =
    projectiveImageSet H hd hH hH0

/-- Equality of the actual projective image closures gives the exact
cone substitution kernel. No dominance of the affine cone is an extra
hypothesis in the projective restriction theorem. -/
theorem original_projective_restriction_dominance_constructs_cone_kernel
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim) :
    ∀ z : MvPolynomial (Fin 4) K,
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (aeval P z) = 0 ↔
        z ∈ imageRelationIdeal H := by
  have hclosure := hdom
  unfold originalProjectiveRestrictionDominant at hclosure
  have he : imageRelationIdeal (fun i => aeval H (P i)) = imageRelationIdeal H :=
    (projectiveImageSet_vanishingIdeal (fun i => aeval H (P i)) (Nat.mul_pos hd hD)
      (fun i => (hP i).aeval H hH) (primitive_part_composite_image_ne_zero H hrank I P hprim)).symm.trans
      ((congrArg (fun Z => (ProjectiveSpectrum.vanishingIdeal Z).toIdeal) hclosure).trans
        (projectiveImageSet_vanishingIdeal H hd hH hH0))
  intro z
  rw [Ideal.algebraMap_residueField_eq_zero]
  change aeval H (aeval P z) = 0 ↔ z ∈ imageRelationIdeal H
  rw [comp_aeval_apply P (aeval H) z]
  change z ∈ imageRelationIdeal (fun i => aeval H (P i)) ↔ z ∈ imageRelationIdeal H
  rw [he]

/-- Lemma 4.3: the actual dominant projective restriction of the
primitive part cannot preserve the original birational Gauss parameter.
The projective dominance hypothesis constructs its own field pullback;
every local and differential input to the contradiction is derived. -/
theorem lemma_4_3_projective_restriction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim) :
    let hcone := original_projective_restriction_dominance_constructs_cone_kernel
      H hd hH hH0 hrank I P hD hP hprim hdom
    dominantConeRestriction (imageRelationIdeal H) P hcone
      (imageConeGaussHom H I e RatFunc.X) ≠ imageConeGaussHom H I e RatFunc.X :=
  no_dominant_original_gauss_parameter_preserving_cone_restriction H hd hH hN hind hrank I e
    g hg P hHP (original_projective_restriction_dominance_constructs_cone_kernel
      H hd hH hH0 hrank I P hD hP hprim hdom)

end DimensionFourDependence
