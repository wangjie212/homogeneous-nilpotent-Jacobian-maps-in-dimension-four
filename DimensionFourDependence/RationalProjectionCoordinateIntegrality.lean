import DimensionFourDependence.InfinityScaledMonicRoot

/-! # The actual rational projection coordinates are integral in both frames

The finite coordinate and constants are images of actual polynomials.
The infinity parameter, constants and scaled constants are images of
elements of the actual rational-function infinity valuation ring.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]

section Finite

variable [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L]

/-- The actual rational projection variable is integral over the finite
polynomial base through its specified function-field embedding. -/
theorem projection_variable_isIntegral_finite :
    IsIntegral (Polynomial k) (algebraMap (RatFunc k) L RatFunc.X) := by
  have h : IsIntegral (Polynomial k) (algebraMap (Polynomial k) L Polynomial.X) := isIntegral_algebraMap
  rwa [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) L, RatFunc.algebraMap_X] at h

/-- Every coefficient constant is integral over the actual finite
polynomial base. -/
theorem projection_constant_isIntegral_finite (a : k) :
    IsIntegral (Polynomial k) (algebraMap (RatFunc k) L (RatFunc.C a)) := by
  have h : IsIntegral (Polynomial k) (algebraMap (Polynomial k) L (Polynomial.C a)) := isIntegral_algebraMap
  rwa [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) L, RatFunc.algebraMap_C] at h

end Finite

variable [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- The image of any actual infinity-regular rational function is
integral over the actual infinity valuation ring. -/
theorem infinity_regular_image_isIntegral
    (z : RatFunc k) (hz : z ∈ rationalInfinityRing k) :
    IsIntegral (rationalInfinityRing k) (algebraMap (RatFunc k) L z) := by
  let a : rationalInfinityRing k := ⟨z, hz⟩
  have h : IsIntegral (rationalInfinityRing k) (algebraMap (rationalInfinityRing k) L a) :=
    isIntegral_algebraMap
  rw [IsScalarTower.algebraMap_apply (rationalInfinityRing k) (RatFunc k) L] at h
  exact h

/-- The actual infinity parameter is integral in the infinity base. -/
theorem projection_parameter_isIntegral_infinity :
    IsIntegral (rationalInfinityRing k) (algebraMap (RatFunc k) L (RatFunc.X⁻¹)) := by
  apply infinity_regular_image_isIntegral
  apply (rationalInfinityRing_mem_iff _).mpr
  rw [RatFunc.intDegree_inv, RatFunc.intDegree_X]
  norm_num

/-- Constants are integral over the actual infinity valuation ring. -/
theorem projection_constant_isIntegral_infinity (a : k) :
    IsIntegral (rationalInfinityRing k) (algebraMap (RatFunc k) L (RatFunc.C a)) := by
  apply infinity_regular_image_isIntegral
  apply (rationalInfinityRing_mem_iff _).mpr
  rw [RatFunc.intDegree_C]

/-- Multiplying a constant by the actual infinity parameter gives an
integral value in the infinity frame. -/
theorem projection_scaled_constant_isIntegral_infinity (a : k) :
    IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * algebraMap (RatFunc k) L (RatFunc.C a)) := by
  rw [← map_mul]
  apply infinity_regular_image_isIntegral
  have h := scaled_polynomial_mem_infinity_of_degree_le (Polynomial.C a) 1 (by simp)
  simpa only [pow_one, RatFunc.algebraMap_C] using h

end DimensionFourDependence
