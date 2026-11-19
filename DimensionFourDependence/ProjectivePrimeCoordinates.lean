import DimensionFourDependence.ProjectiveBoundaryProjection

/-! # Every actual projective-spectrum prime has extension-field coordinates

The fraction field of the prime quotient gives the original coordinate
values. Relevance supplies a nonzero coordinate, and homogeneous equation
membership identifies their actual point with the given prime. This
allows boundary statements for field-valued points to apply to every
prime of the actual projective infinity section.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma : Type*} [Field F]

/-- Relevance of an actual polynomial projective prime supplies an
original coordinate outside the prime. -/
theorem projectiveSpectrum_exists_coordinate_not_mem
    (z : ProjectiveSpectrum (homogeneousSubmodule sigma F)) :
    ∃ i : sigma, X i ∉ z.asHomogeneousIdeal := by
  by_contra hnone
  push Not at hnone
  apply z.not_irrelevant_le
  have hvars : idealOfVars sigma F ≤ z.asHomogeneousIdeal.toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hnone i
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn P hP
  apply hvars
  rw [← pow_one (idealOfVars sigma F)]
  apply (mem_pow_idealOfVars_iff 1 P).mpr
  intro m hm
  have he : Finsupp.degree m = n := by
    change P.IsHomogeneous n at hP
    simpa only [Finsupp.degree_apply] using (hP.degree_eq_sum_deg_support hm).symm
  omega

/-- Original homogeneous coordinate values in the fraction field
of an actual projective prime quotient. -/
noncomputable def projectivePrimeCoordinate
    (z : ProjectiveSpectrum (homogeneousSubmodule sigma F)) (i : sigma) :
    FractionRing (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal) :=
  algebraMap (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal) _
    (Ideal.Quotient.mk z.asHomogeneousIdeal.toIdeal (X i))

/-- Evaluation on those actual coordinates is the canonical quotient
map followed by its fraction-field inclusion, for every polynomial. -/
theorem projectivePrimeCoordinate_aeval
    (z : ProjectiveSpectrum (homogeneousSubmodule sigma F)) (P : MvPolynomial sigma F) :
    aeval (projectivePrimeCoordinate z) P =
      algebraMap (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal)
        (FractionRing (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal))
          (Ideal.Quotient.mk z.asHomogeneousIdeal.toIdeal P) := by
  let phi : MvPolynomial sigma F →ₐ[F]
      FractionRing (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal) :=
    (IsScalarTower.toAlgHom F (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal)
      (FractionRing (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal))).comp
        (Ideal.Quotient.mkₐ F z.asHomogeneousIdeal.toIdeal)
  have he : aeval (projectivePrimeCoordinate z) = phi := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [aeval_X]
    rfl
  exact DFunLike.congr_fun he P

/-- A coordinate value is zero precisely when its original coordinate
belongs to the original projective prime. -/
theorem projectivePrimeCoordinate_eq_zero_iff
    (z : ProjectiveSpectrum (homogeneousSubmodule sigma F)) (i : sigma) :
    projectivePrimeCoordinate z i = 0 ↔ X i ∈ z.asHomogeneousIdeal := by
  change algebraMap (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal)
    (FractionRing (MvPolynomial sigma F ⧸ z.asHomogeneousIdeal.toIdeal))
      (Ideal.Quotient.mk z.asHomogeneousIdeal.toIdeal (X i)) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- The canonical original coordinate vector of every relevant
homogeneous prime is nonzero. -/
theorem projectivePrimeCoordinate_ne_zero
    (z : ProjectiveSpectrum (homogeneousSubmodule sigma F)) : projectivePrimeCoordinate z ≠ 0 := by
  obtain ⟨i, hi⟩ := projectiveSpectrum_exists_coordinate_not_mem z
  intro hzero
  exact hi ((projectivePrimeCoordinate_eq_zero_iff z i).mp (congrFun hzero i))

/-- Every actual projective-spectrum prime is the actual point of
its canonical extension-field coordinate vector. -/
theorem projectivePrimeCoordinate_represents
    (z : ProjectiveSpectrum (homogeneousSubmodule sigma F)) :
    projectiveFieldPoint (E := F) (projectivePrimeCoordinate z) (projectivePrimeCoordinate_ne_zero z) = z := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d P hP
  change P.IsHomogeneous d at hP
  rw [projectiveFieldPoint_homogeneous_mem _ _ P hP, projectivePrimeCoordinate_aeval]
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  rfl

end DimensionFourDependence
