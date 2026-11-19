import DimensionFourDependence.RationalInfinityDegree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # A section regular on both base charts has norm degree at most the field degree

The section may be any element of the finite function-field extension.
Integrality on the finite chart makes its norm a polynomial. Integrality
after multiplication by the infinity uniformizer bounds that polynomial's
degree by the actual extension degree. No coordinate expression for the
section or polynomial degree bound is assumed.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k L : Type u} [Field k] [Field L] [Algebra (RatFunc k) L]
  [Module.Finite (RatFunc k) L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- Regularity of the section in the infinity frame makes its norm
regular there after the precise field-degree scaling. -/
theorem scaled_field_norm_mem_infinity
    (z : L) (hinfinity : IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L RatFunc.X⁻¹ * z)) :
    (RatFunc.X⁻¹ : RatFunc k) ^ Module.finrank (RatFunc k) L * Algebra.norm (RatFunc k) z ∈
      rationalInfinityRing k := by
  have hn := Algebra.isIntegral_norm (RatFunc k) hinfinity
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hn
  have hw' : (w : RatFunc k) = Algebra.norm (RatFunc k)
      (algebraMap (RatFunc k) L RatFunc.X⁻¹ * z) := hw
  have hmem : Algebra.norm (RatFunc k)
      (algebraMap (RatFunc k) L RatFunc.X⁻¹ * z) ∈ rationalInfinityRing k := hw' ▸ w.property
  simpa only [map_mul, Algebra.norm_algebraMap] using hmem

variable [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L]

/-- Two genuine section regularity conditions construct a nonzero
polynomial norm of degree at most the actual finite projection degree. -/
theorem field_norm_polynomial_degree_le_of_two_regularities
    (z : L) (hz : z ≠ 0) (hfinite : IsIntegral (Polynomial k) z)
    (hinfinity : IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L RatFunc.X⁻¹ * z)) :
    ∃ p : Polynomial k, p ≠ 0 ∧
      algebraMap (Polynomial k) (RatFunc k) p = Algebra.norm (RatFunc k) z ∧
        p.natDegree ≤ Module.finrank (RatFunc k) L := by
  have hn := Algebra.isIntegral_norm (RatFunc k) hfinite
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hn
  have hp0 : p ≠ 0 := by
    intro hzero
    have hnorm : Algebra.norm (RatFunc k) z = 0 := hp.symm.trans (by simp [hzero])
    exact (Algebra.norm_ne_zero_iff.mpr hz) hnorm
  refine ⟨p, hp0, hp, ?_⟩
  apply polynomial_degree_le_of_scaled_mem_infinity
  rw [hp]
  exact scaled_field_norm_mem_infinity z hinfinity

end DimensionFourDependence
