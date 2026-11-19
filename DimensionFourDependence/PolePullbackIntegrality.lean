import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # A constant parameter pole forces an integral reciprocal

If n(t) = H d(t), where H is regular over a normal source ring and a is
an actual constant pole (d(a)=0, n(a)≠0), then (t-a)⁻¹ is integral over
the source ring. Reversing the translated polynomial relation gives a
monic equation. In the source fraction field, normality makes the
reciprocal regular. No pole-pullback or local geometric assertion is assumed.
-/

namespace DimensionFourDependence

open Polynomial

/-- A relation with unit constant coefficient makes the reciprocal of
its nonzero root integral, by reversal and unit normalization. -/
theorem inverse_integral_of_unit_constant_relation
    {R F : Type*} [CommRing R] [Nontrivial R] [Field F] [Algebra R F]
    (z : F) (hz : z ≠ 0) (P : Polynomial R)
    (hP : aeval z P = 0) (hconstant : IsUnit (P.coeff 0)) :
    IsIntegral R z⁻¹ := by
  classical
  let : Invertible z := invertibleOfNonzero hz
  have hreverse : aeval z⁻¹ P.reverse = 0 := by
    simpa only [aeval_def, invOf_eq_inv] using
      (eval₂_reverse_eq_zero_iff (algebraMap R F) z P).mpr hP
  obtain ⟨u, hu⟩ := hconstant
  refine ⟨C (↑(u⁻¹) : R) * P.reverse, ?_, ?_⟩
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (hu ▸ u.ne_zero), ← hu]
    exact Units.inv_mul u
  · simp only [eval₂_mul, eval₂_C, ← aeval_def, hreverse, mul_zero]

/-- A genuine constant pole of a rational expression gives a monic
relation for the reciprocal of the translated parameter. -/
theorem constant_pole_pullback_reciprocal_isIntegral
    {K R F : Type*} [Field K] [CommRing R] [Nontrivial R] [Field F]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    (n d : Polynomial K) (a : K) (hd : d.eval a = 0) (hn : n.eval a ≠ 0)
    (t : F) (ht : t ≠ algebraMap K F a) (H : R)
    (hvalue : aeval t n = algebraMap R F H * aeval t d) :
    IsIntegral R (t - algebraMap K F a)⁻¹ := by
  classical
  let P : Polynomial R :=
    (n.map (algebraMap K R)).comp (X + C (algebraMap K R a)) -
      C H * (d.map (algebraMap K R)).comp (X + C (algebraMap K R a))
  have hP : aeval (t - algebraMap K F a) P = 0 := by
    simpa [P, aeval_comp, aeval_map_algebraMap, ← IsScalarTower.algebraMap_apply K R F] using
      sub_eq_zero.mpr hvalue
  have hc : P.coeff 0 = algebraMap K R (n.eval a) := by
    simp [P, coeff_zero_eq_eval_zero, eval_comp, eval_map, hd]
  apply inverse_integral_of_unit_constant_relation _ (sub_ne_zero.mpr ht) P hP
  rw [hc]
  exact (isUnit_iff_ne_zero.mpr hn).map (algebraMap K R)

/-- In a normal source domain, a pole can pull back only where the
reciprocal of its translated parameter is regular. -/
theorem constant_pole_pullback_reciprocal_regular
    {K R F : Type*} [Field K] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra K R] [Algebra K F] [Algebra R F]
    [IsScalarTower K R F] [IsFractionRing R F]
    (n d : Polynomial K) (a : K) (hd : d.eval a = 0) (hn : n.eval a ≠ 0)
    (t : F) (ht : t ≠ algebraMap K F a) (H : R)
    (hvalue : aeval t n = algebraMap R F H * aeval t d) :
    ∃ U : R, algebraMap R F U = (t - algebraMap K F a)⁻¹ :=
  IsIntegrallyClosed.algebraMap_eq_of_integral
    (constant_pole_pullback_reciprocal_isIntegral n d a hd hn t ht H hvalue)

end DimensionFourDependence
