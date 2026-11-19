import DimensionFourDependence.PrincipalVanishingDivisor
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # A nonzero radial linear element cannot be a unit in an integral cone extension -/

namespace DimensionFourDependence

variable {A B F : Type*} [CommRing A] [CommRing B] [Field F]

/-- An inverse with a pole at the radial origin is not integral
over any coefficient algebra contained in the radial polynomial ring. -/
theorem inverse_radial_linear_value_not_isIntegral
    (u : F) (hu : u ≠ 0) :
    ¬ IsIntegral (Polynomial F) (RatFunc.C u * RatFunc.X : RatFunc F)⁻¹ := by
  intro hi
  obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Polynomial F) (K := RatFunc F)).mp hi
  have hnonzero : (RatFunc.C u * RatFunc.X : RatFunc F) ≠ 0 :=
    mul_ne_zero ((map_ne_zero RatFunc.C).mpr hu) RatFunc.X_ne_zero
  have hprod : (Polynomial.C u * Polynomial.X) * p = 1 := by
    apply IsFractionRing.injective (Polynomial F) (RatFunc F)
    calc
      _ = (RatFunc.C u * RatFunc.X) * algebraMap (Polynomial F) (RatFunc F) p := by
        rw [map_mul, map_mul]
        rfl
      _ = 1 := hp ▸ mul_inv_cancel₀ hnonzero
      _ = algebraMap (Polynomial F) (RatFunc F) 1 := (map_one _).symm
  have hzero := congrArg (Polynomial.eval (0 : F)) hprod
  simp at hzero

variable [Algebra A B] [Algebra.IsIntegral A B]

/-- An integral cone element with positive radial weight has no
regular inverse. This uses its actual polynomial-valued coefficient map. -/
theorem integral_radial_linear_element_not_isUnit
    (f : A →+* Polynomial F) (φ : B →+* RatFunc F)
    (hcomp : φ.comp (algebraMap A B) = (algebraMap (Polynomial F) (RatFunc F)).comp f)
    (b : B) (u : F) (hu : u ≠ 0)
    (hb : φ b = RatFunc.C u * RatFunc.X) : ¬ IsUnit b := by
  intro hunit
  obtain ⟨c, hbc⟩ := hunit.exists_right_inv
  have hnonzero : (RatFunc.C u * RatFunc.X : RatFunc F) ≠ 0 :=
    mul_ne_zero ((map_ne_zero RatFunc.C).mpr hu) RatFunc.X_ne_zero
  have hprod : (RatFunc.C u * RatFunc.X : RatFunc F) * φ c = 1 := by
    rw [← hb, ← map_mul, hbc, map_one]
  have hc : φ c = (RatFunc.C u * RatFunc.X : RatFunc F)⁻¹ := by
    apply mul_left_cancel₀ hnonzero
    rw [hprod, mul_inv_cancel₀ hnonzero]
  have hi : IsIntegral (Polynomial F) (φ c) :=
    (Algebra.IsIntegral.isIntegral (R := A) c).map_of_comp_eq f φ hcomp.symm
  exact inverse_radial_linear_value_not_isIntegral u hu (hc ▸ hi)

variable [IsDomain B] [IsNoetherianRing B]

/-- A nonzero positive-weight element in an actual Noetherian
integral cone extension constructs a height-one vanishing prime. -/
theorem integral_radial_linear_element_has_vanishing_divisor
    (f : A →+* Polynomial F) (φ : B →+* RatFunc F)
    (hcomp : φ.comp (algebraMap A B) = (algebraMap (Polynomial F) (RatFunc F)).comp f)
    (b : B) (u : F) (hu : u ≠ 0)
    (hb : φ b = RatFunc.C u * RatFunc.X) :
    ∃ q : PrimeSpectrum B, q.asIdeal.height = 1 ∧ b ∈ q.asIdeal := by
  have hb0 : b ≠ 0 := fun hzero =>
    (mul_ne_zero ((map_ne_zero RatFunc.C).mpr hu) RatFunc.X_ne_zero)
      (hb.symm.trans ((congrArg φ hzero).trans (map_zero φ)))
  exact nonzero_nonunit_function_has_vanishing_divisor b hb0
    (integral_radial_linear_element_not_isUnit f φ hcomp b u hu hb)

end DimensionFourDependence
