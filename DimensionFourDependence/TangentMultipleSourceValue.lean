import DimensionFourDependence.GenericFiberTangentNonvanishing

/-! # A tangent multiple at the fiber base point has its exact source value

The tangent covector annihilates the affine direction by Euler's
identity. Its value at the actual projected source point is therefore
the image of its base-point value. The actual finite-field multiplier
then replaces r by the same linear form on the original source point.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F E G : Type*} [Field F] [Field E] [Field G]
    [Algebra F E] [Algebra F G] [Algebra E G] [IsScalarTower F E G] {n : ℕ}

/-- An annihilating covector's base-point multiple retains its exact
linear source-point value on the actual affine fiber line. -/
theorem annihilating_covector_multiple_actual_source_value
    (τ A : Fin n → F) (x : Fin n → E) (t : G) (z : Fin n → G)
    (hz : ∀ i, z i = algebraMap E G (x i) + algebraMap F G (A i) * t)
    (horth : ∑ i, τ i * A i = 0) (r : E) (u : F)
    (hr : r = algebraMap F E u * (∑ i, algebraMap F E (τ i) * x i)) :
    algebraMap E G r = algebraMap F G u * (∑ i, algebraMap F G (τ i) * z i) := by
  have horthE : (∑ i, algebraMap F E (τ i) * algebraMap F E (A i)) = 0 := by
    simpa only [map_sum, map_mul, map_zero] using congrArg (algebraMap F E) horth
  have hline := annihilating_covector_value_on_affine_line
    (fun i => algebraMap F E (τ i)) x (fun i => algebraMap F E (A i)) t z
    (by intro i; simpa only [IsScalarTower.algebraMap_apply F E G] using hz i) horthE
  have hlinear : (∑ i, algebraMap F G (τ i) * z i) =
      algebraMap E G (∑ i, algebraMap F E (τ i) * x i) := by
    simpa only [IsScalarTower.algebraMap_apply F E G] using hline
  rw [hr, map_mul, IsScalarTower.algebraMap_apply F E G, ← hlinear]

variable {K : Type*} [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E]

/-- The actual gradient tangent multiple supplied by the finite-field
construction becomes a linear form at the actual source point. Tangent
annihilation is derived from the homogeneous direction equation. -/
theorem homogeneous_direction_tangent_multiple_actual_source_value
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hzero : aeval A Φ = 0)
    (x : Fin n → E) (t : G) (z : Fin n → G)
    (hz : ∀ i, z i = algebraMap E G (x i) + algebraMap F G (A i) * t)
    (r : E) (u : F)
    (hr : r = algebraMap F E u *
      (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i)) :
    algebraMap E G r = algebraMap F G u *
      aeval z (linearFormPolynomial (fun i => aeval A (pderiv i Φ))) := by
  let τ : Fin n → F := fun i => aeval A (pderiv i Φ)
  have horth : (∑ i, τ i * A i) = 0 := by
    simpa only [τ, mul_comm] using homogeneous_equation_gradient_annihilates_point A Φ hΦ hzero
  have hgrad (i : Fin n) : aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) = algebraMap F E (τ i) :=
    (comp_aeval_apply A (IsScalarTower.toAlgHom K F E) (pderiv i Φ)).symm
  simp_rw [hgrad] at hr
  have he := annihilating_covector_multiple_actual_source_value τ A x t z hz horth r u hr
  simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using he

end DimensionFourDependence
