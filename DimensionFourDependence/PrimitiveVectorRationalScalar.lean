import DimensionFourDependence.QuasiTranslationFiberDivisorTangency

/-! # A rational scalar of a primitive source polynomial vector is polynomial -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {m n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- The actual reduced denominator of a rational scalar is a unit if
all its products with a primitive vector are original polynomials.
This constructs the scalar polynomial and the original factorization. -/
theorem primitive_vector_rational_scalar_constructs_polynomial_factor
    (W H : Fin m → R₀) (hprim : IsPrimitiveVec W) (r : F₀)
    (hrep : ∀ i, algebraMap R₀ F₀ (H i) = r * algebraMap R₀ F₀ (W i)) :
    ∃ g : R₀, algebraMap R₀ F₀ g = r ∧ ∀ i, H i = g * W i := by
  obtain ⟨a, b, hrel, hfrac⟩ := IsFractionRing.exists_reduced_fraction R₀ r
  have hb : (b : R₀) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hbF : algebraMap R₀ F₀ (b : R₀) ≠ 0 :=
    fun h => hb (IsFractionRing.injective R₀ F₀ (h.trans (map_zero _).symm))
  have hr : r = algebraMap R₀ F₀ a / algebraMap R₀ F₀ (b : R₀) := by
    rw [IsFractionRing.mk'_eq_div] at hfrac
    exact hfrac.symm
  have hclear (i) : (b : R₀) * H i = a * W i := by
    apply IsFractionRing.injective R₀ F₀
    rw [map_mul, map_mul, hrep i, hr]
    field_simp
  have hdiv (i) : (b : R₀) ∣ W i := hrel.symm.dvd_of_dvd_mul_left
    (show (b : R₀) ∣ a * W i from ⟨H i, (hclear i).symm⟩)
  obtain ⟨b', hbb'⟩ := (hprim (b : R₀) hdiv).exists_right_inv
  let g := a * b'
  have hg : algebraMap R₀ F₀ g = r := by
    rw [hr]
    apply (eq_div_iff hbF).mpr
    change algebraMap R₀ F₀ (a * b') * algebraMap R₀ F₀ (b : R₀) = _
    rw [← map_mul]
    congr 1
    calc
      a * b' * (b : R₀) = a * ((b : R₀) * b') := by ring
      _ = a := by rw [hbb', mul_one]
  refine ⟨g, hg, ?_⟩
  intro i
  apply IsFractionRing.injective R₀ F₀
  rw [map_mul, hg, hrep]

end DimensionFourDependence
