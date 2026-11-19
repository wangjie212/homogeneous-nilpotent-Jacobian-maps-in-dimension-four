import DimensionFourDependence.PrimitiveBoundaryImage
import DimensionFourDependence.Lemma43ProjectiveRestriction

/-! # Projective generic points under homogeneous polynomial substitution

A generic projective point detects exactly the original homogeneous
relations. Primitivity makes P defined there, and its substituted point
is the actual generic point of the composed projective image.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K κ : Type*} [Field K] [Field κ] [Algebra K κ]

/-- Homogeneous membership in an extension-field projective point
is exactly vanishing at its actual coordinate vector. -/
theorem projectiveFieldPoint_homogeneous_mem {σ : Type*}
    (b : σ → κ) (hb : b ≠ 0) (p : MvPolynomial σ K) {m : ℕ} (hp : p.IsHomogeneous m) :
    p ∈ (projectiveFieldPoint (E := K) b hb).asHomogeneousIdeal ↔ aeval b p = 0 := by
  change projectiveFieldPointMap (E := K) b p = 0 ↔ _
  rw [projectiveFieldPointMap_homogeneous b hp, Polynomial.monomial_eq_zero_iff]

/-- Nonzero proportional extension-field coordinate vectors define
the same actual point of the original projective spectrum. -/
theorem projectiveFieldPoint_eq_of_proportional {σ : Type*}
    (b y : σ → κ) (hb : b ≠ 0) (hy : y ≠ 0) (c : κ) (hc : c ≠ 0)
    (hby : ∀ i, b i = c * y i) :
    projectiveFieldPoint (E := K) b hb = projectiveFieldPoint (E := K) y hy := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro m p hp
  change p.IsHomogeneous m at hp
  rw [projectiveFieldPoint_homogeneous_mem b hb p hp, projectiveFieldPoint_homogeneous_mem y hy p hp,
    funext hby, homogeneous_aeval_scale_indexed p hp y c]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero m hc))

variable [CharZero K]

/-- The actual primitive part cannot vanish at a generic projective
point of the original image. Genericity is equality of actual points,
not an assumed affine evaluation kernel. -/
theorem primitive_part_defined_at_projective_generic_point
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P)
    (b : Fin 4 → κ) (hb : b ≠ 0)
    (hgeneric : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0) :
    (fun i => aeval b (P i)) ≠ 0 := by
  intro hz
  apply I.irreducible.not_isUnit
  apply hprim I.equation
  intro i
  have hm := (projectiveFieldPoint_homogeneous_mem b hb (P i) (hP i)).mpr (congrFun hz i)
  rw [hgeneric] at hm
  exact (I.relation_iff_dvd H hrank (P i)).mp hm

omit [CharZero K] in
/-- Homogeneous substitution of a generic projective coordinate point
is the actual generic point of the composed image. -/
theorem homogeneous_substitution_projective_generic_point
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D)
    (hP : IsHomogMap P D) (hC0 : (fun i => aeval H (P i)) ≠ 0)
    (b : Fin 4 → κ) (hb : b ≠ 0) (hPb : (fun i => aeval b (P i)) ≠ 0)
    (hgeneric : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0) :
    projectiveFieldPoint (E := K) (fun i => aeval b (P i)) hPb =
      projectiveImageGenericPoint (fun i => aeval H (P i)) (Nat.mul_pos hd hD)
        (fun i => (hP i).aeval H hH) hC0 := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro m p hp
  change p.IsHomogeneous m at hp
  have hrel : aeval P p ∈ (projectiveFieldPoint (E := K) b hb).asHomogeneousIdeal ↔
      aeval P p ∈ (projectiveImageGenericPoint H hd hH hH0).asHomogeneousIdeal := by rw [hgeneric]
  rw [projectiveFieldPoint_homogeneous_mem b hb (aeval P p) (hp.aeval P hP)] at hrel
  change aeval b (aeval P p) = 0 ↔ aeval H (aeval P p) = 0 at hrel
  rw [comp_aeval_apply P (aeval b) p, comp_aeval_apply P (aeval H) p] at hrel
  rw [projectiveFieldPoint_homogeneous_mem _ hPb p hp]
  exact hrel

/-- If a generic original image direction maps projectively to a
generic original image target, the actual projective restriction is
dominant. Both genericities are actual projective-spectrum point equalities. -/
theorem generic_source_and_target_construct_projective_restriction_dominance
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D)
    (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P)
    (b y : Fin 4 → κ) (hb : b ≠ 0) (hy : y ≠ 0)
    (hbgen : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0)
    (hygen : projectiveFieldPoint (E := K) y hy = projectiveImageGenericPoint H hd hH hH0)
    (c : κ) (hc : c ≠ 0) (hby : ∀ i, aeval b (P i) = c * y i) :
    originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim := by
  have hPb := primitive_part_defined_at_projective_generic_point H hd hH hH0 hrank I P hP hprim b hb hbgen
  have hC0 := primitive_part_composite_image_ne_zero H hrank I P hprim
  have hpoint := homogeneous_substitution_projective_generic_point H hd hH hH0 P hD hP hC0 b hb hPb hbgen
  have he : projectiveImageGenericPoint (fun i => aeval H (P i)) (Nat.mul_pos hd hD)
      (fun i => (hP i).aeval H hH) hC0 = projectiveImageGenericPoint H hd hH hH0 :=
    hpoint.symm.trans ((projectiveFieldPoint_eq_of_proportional _ y hPb hy c hc hby).trans hygen)
  unfold originalProjectiveRestrictionDominant projectiveImageSet
  rw [he]

end DimensionFourDependence
