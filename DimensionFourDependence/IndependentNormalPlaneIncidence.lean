import DimensionFourDependence.IndependentNormalPencilBase

/-! # A nonplanar normal family has no point at a source-independent parameter -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2000000

variable {K F G : Type*} [Field K] [Field F] [Field G]
  [Algebra K F] [Algebra K G] [Algebra F G] [IsScalarTower K F G]

/-- Incidence in an independent rational normal family at a parameter
transcendental over all point coordinates forces the point to be zero. -/
theorem independent_rational_normal_transcendental_incidence_forces_zero
    {n : ℕ} (w : Fin n → RatFunc K) (hw : LinearIndependent K w)
    (φ : RatFunc K →ₐ[K] G) (ht : Transcendental F (φ RatFunc.X))
    (x : Fin n → F)
    (hplane : ∑ i, φ (w i) * algebraMap F G (x i) = 0) : x = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    exact Subsingleton.elim _ _
  have hw0 : w ≠ 0 := by
    intro hz
    exact hw.ne_zero ⟨0, Nat.pos_of_ne_zero hn⟩ (congrFun hz _)
  obtain ⟨v, _hv, _hprim, r, hr, hrep⟩ := rational_vector_primitive_polynomial_presentation w hw0
  have hv : LinearIndependent K v := by
    let f : Polynomial K →ₗ[K] RatFunc K :=
      r • (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)).toLinearMap
    apply LinearIndependent.of_comp f
    convert hw using 1
    funext i
    exact (hrep i).symm
  have hrepφ (i : Fin n) : φ (w i) = φ r * Polynomial.aeval (φ RatFunc.X) (v i) := by
    rw [hrep i, map_mul, rational_function_algHom_polynomial_value]
  have hinc : ∑ i, algebraMap F G (x i) * Polynomial.aeval (φ RatFunc.X) (v i) = 0 := by
    have he : φ r * (∑ i, algebraMap F G (x i) * Polynomial.aeval (φ RatFunc.X) (v i)) = 0 := by
      rw [Finset.mul_sum]
      convert hplane using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hrepφ]
      ring
    exact (mul_eq_zero.mp he).resolve_left ((map_ne_zero φ).mpr hr)
  exact independent_polynomial_covector_extended_kernel_zero v hv x
    (transcendental_parameter_plane_incidence_mem_coefficient_kernel v x (φ RatFunc.X) ht hinc)

end DimensionFourDependence
