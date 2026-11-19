import DimensionFourDependence.GenericDirectionTangent

/-! # Nonvanishing of the tangent at a base point on the actual generic fiber

The base point need not have independent coordinates. The actual source
point on its line can be independent over the direction field. Euler's
identity makes the tangent constant along that line, so nonvanishing at
the actual source point descends to the chosen base point.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {E G : Type*} [Field E] [Field G] [Algebra E G] {n : ℕ}

/-- A covector annihilating the direction has the same value along
the actual affine line, after mapping its base-point value. -/
theorem annihilating_covector_value_on_affine_line
    (a x A : Fin n → E) (t : G) (z : Fin n → G)
    (hz : ∀ i, z i = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (horth : ∑ i, a i * A i = 0) :
    (∑ i, algebraMap E G (a i) * z i) = algebraMap E G (∑ i, a i * x i) := by
  classical
  calc
    _ = (∑ i, algebraMap E G (a i * x i)) + (∑ i, algebraMap E G (a i * A i)) * t := by
      simp_rw [hz, mul_add, ← mul_assoc, ← map_mul]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [← map_sum, ← map_sum, horth, map_zero, zero_mul, add_zero]

variable {K F : Type*} [Field K] [CharZero K] [Field F]
    [Algebra K F] [Algebra K E] [Algebra K G]
    [Algebra F E] [Algebra F G]
    [IsScalarTower K F E] [IsScalarTower K F G] [IsScalarTower K E G] [IsScalarTower F E G]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Independence of the actual projected source point, rather than
of its chosen base point, forces the actual tangent base value nonzero. -/
theorem independent_fiber_source_constructs_nonzero_tangent_base_value
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (x : Fin n → E) (t : G) (z : Fin n → G)
    (hz : ∀ i, z i = algebraMap E G (x i) + algebraMap F G (A i) * t)
    (hind : AlgebraicIndependent F z) :
    (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) ≠ 0 := by
  let a : Fin n → F := fun i => aeval A (pderiv i Φ)
  have hvalue : aeval A Φ = 0 :=
    (principal_projective_equation_vanishing_iff_dvd A Φ hI Φ hΦ).mpr (dvd_refl Φ)
  have hgrad := principal_projective_equation_gradient_ne_zero A Φ hirr.ne_zero hΦ hI
  have hTz := independent_base_point_tangent_ne_zero A Φ hgrad z hind
  have haE (i : Fin n) : aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) = algebraMap F E (a i) :=
    (comp_aeval_apply A (IsScalarTower.toAlgHom K F E) (pderiv i Φ)).symm
  have haG (i : Fin n) : aeval (fun k => algebraMap F G (A k)) (pderiv i Φ) = algebraMap F G (a i) :=
    (comp_aeval_apply A (IsScalarTower.toAlgHom K F G) (pderiv i Φ)).symm
  have horth : (∑ i, algebraMap F E (a i) * algebraMap F E (A i)) = 0 := by
    simp_rw [← map_mul]
    rw [← map_sum]
    have he := homogeneous_equation_gradient_annihilates_point A Φ hΦ hvalue
    simpa only [a, mul_comm, he, map_zero] using congrArg (algebraMap F E) he
  have hline := annihilating_covector_value_on_affine_line
    (fun i => algebraMap F E (a i)) x (fun i => algebraMap F E (A i)) t z
      (by intro i; simpa only [IsScalarTower.algebraMap_apply F E G] using hz i) horth
  intro hzero
  apply hTz
  simp_rw [haG]
  rw [show (∑ i, algebraMap F G (a i) * z i) =
    algebraMap E G (∑ i, algebraMap F E (a i) * x i) by
      simpa only [IsScalarTower.algebraMap_apply F E G] using hline]
  simp_rw [haE] at hzero
  rw [hzero, map_zero]

end DimensionFourDependence
