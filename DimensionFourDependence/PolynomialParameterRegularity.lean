import DimensionFourDependence.PolePullbackIntegrality
import DimensionFourDependence.PrimitiveRationalVector
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Polynomiality after a polynomial parameter substitution

A nonconstant polynomial function of a parameter, with regular source
value, makes that parameter integral and hence regular in a normal
source fraction field. Conversely substitution of a nonconstant source
polynomial cannot remove a rational-function denominator.
-/

namespace DimensionFourDependence

open Polynomial

/-- A nonconstant polynomial value over constant coefficients makes
its parameter integral over the ring in which that value is regular. -/
theorem parameter_isIntegral_of_nonconstant_polynomial_value
    {L R F : Type*} [Field L] [CommRing R] [Nontrivial R] [Field F]
    [Algebra L R] [Algebra L F] [Algebra R F] [IsScalarTower L R F]
    (n : Polynomial L) (hn : 0 < n.natDegree) (t : F) (H : R)
    (hvalue : aeval t n = algebraMap R F H) : IsIntegral R t := by
  classical
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have hlc : n.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hn0)
  let M : Polynomial R := (n * C n.leadingCoeff⁻¹).map (algebraMap L R)
  have hmonic : M.Monic := (monic_mul_leadingCoeff_inv hn0).map (algebraMap L R)
  have hdeg : M.natDegree ≠ 0 := by
    simpa only [M, natDegree_map, natDegree_mul_C hlc] using Nat.ne_of_gt hn
  apply IsIntegral.of_aeval_monic hmonic hdeg
  have hM : aeval t M = algebraMap R F (H * algebraMap L R n.leadingCoeff⁻¹) := by
    simp only [M, aeval_map_algebraMap, map_mul, aeval_C, hvalue,
      ← IsScalarTower.algebraMap_apply L R F]
  rw [hM]
  exact isIntegral_algebraMap

/-- Normality turns the preceding monic equation into an actual
polynomial source expression for the original parameter. -/
theorem parameter_regular_of_nonconstant_polynomial_value
    {L R F : Type*} [Field L] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra L R] [Algebra L F] [Algebra R F]
    [IsScalarTower L R F] [IsFractionRing R F]
    (n : Polynomial L) (hn : 0 < n.natDegree) (t : F) (H : R)
    (hvalue : aeval t n = algebraMap R F H) :
    ∃ T : R, algebraMap R F T = t :=
  IsIntegrallyClosed.algebraMap_eq_of_integral
    (parameter_isIntegral_of_nonconstant_polynomial_value n hn t H hvalue)

/-- A reduced rational expression whose pullback by a nonconstant
polynomial is polynomial has constant denominator. Bezout coprimality
survives substitution, so its substituted denominator is a unit. -/
theorem polynomial_parameter_coprime_denominator_constant
    {L : Type*} [Field L] (T : Polynomial L) (hT : 0 < T.natDegree)
    (n d : Polynomial L) (hcop : IsCoprime n d) (H : Polynomial L)
    (hvalue : n.comp T = H * d.comp T) : d.natDegree = 0 := by
  have hc : IsCoprime (n.comp T) (d.comp T) :=
    hcop.map (Polynomial.aeval T).toRingHom
  have hdvd : d.comp T ∣ n.comp T := ⟨H, hvalue.trans (mul_comm _ _)⟩
  have hu : IsUnit (d.comp T) := hc.symm.isUnit_of_dvd hdvd
  have hz : d.natDegree * T.natDegree = 0 := by
    rw [← natDegree_comp]
    exact natDegree_eq_zero_of_isUnit hu
  exact (Nat.mul_eq_zero.mp hz).resolve_right (Nat.ne_of_gt hT)

/-- A rational function whose value is polynomial under a nonconstant
polynomial parameter is itself a polynomial. Its full rational value,
not merely its poles, is recovered by the returned polynomial. -/
theorem rational_function_polynomial_of_polynomial_parameter
    {L F : Type*} [Field L] [Field F] [Algebra L F]
    [Algebra (Polynomial L) F] [IsScalarTower L (Polynomial L) F]
    [IsFractionRing (Polynomial L) F]
    (f : RatFunc L →ₐ[L] F) (T : Polynomial L) (hT : 0 < T.natDegree)
    (ht : algebraMap (Polynomial L) F T = f RatFunc.X)
    (r : RatFunc L) (H : Polynomial L)
    (hH : f r = algebraMap (Polynomial L) F H) :
    ∃ Q : Polynomial L, algebraMap (Polynomial L) (RatFunc L) Q = r := by
  have hnum : algebraMap (Polynomial L) (RatFunc L) r.num =
      r * algebraMap (Polynomial L) (RatFunc L) r.denom := by
    exact (div_eq_iff (RatFunc.algebraMap_ne_zero r.denom_ne_zero)).mp (RatFunc.num_div_denom r)
  have heq := congrArg f hnum
  simp only [map_mul, rational_function_algHom_polynomial_value, hH] at heq
  have hcomp (p : Polynomial L) : algebraMap (Polynomial L) F (p.comp T) =
      aeval (f RatFunc.X) p := by
    rw [← ht]
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom L (Polynomial L) F) T p).symm
  have hp : r.num.comp T = H * r.denom.comp T := by
    apply IsFractionRing.injective (Polynomial L) F
    simpa only [map_mul, hcomp] using heq
  have hd := polynomial_parameter_coprime_denominator_constant T hT r.num r.denom
    r.isCoprime_num_denom H hp
  refine ⟨r.num * C (r.denom.coeff 0)⁻¹, ?_⟩
  calc
    algebraMap (Polynomial L) (RatFunc L) (r.num * C (r.denom.coeff 0)⁻¹) =
        algebraMap (Polynomial L) (RatFunc L) r.num /
          algebraMap (Polynomial L) (RatFunc L) r.denom := by
      rw [eq_C_of_natDegree_eq_zero hd]
      simp [div_eq_mul_inv, RatFunc.algebraMap_C]
    _ = r := RatFunc.num_div_denom r

end DimensionFourDependence
