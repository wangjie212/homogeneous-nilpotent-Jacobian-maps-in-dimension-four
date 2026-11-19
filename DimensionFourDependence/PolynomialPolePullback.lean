import DimensionFourDependence.PolePullbackIntegrality
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Polynomial pullbacks have at most one constant parameter pole

Two distinct translated parameter reciprocals cannot both be polynomials
in one source variable unless the parameter is scalar. Likewise a polynomial
parameter cannot have a polynomial translated reciprocal. These identities
make the uniqueness and the change-of-parameter steps in §4.5 algebraic.
-/

namespace DimensionFourDependence

open Polynomial

variable {L F : Type*} [Field L] [Field F]
    [Algebra L F] [Algebra (Polynomial L) F]
    [IsScalarTower L (Polynomial L) F] [IsFractionRing (Polynomial L) F]

/-- A nonconstant polynomial parameter has no polynomial reciprocal
of any constant translate. -/
theorem polynomial_parameter_and_reciprocal_force_scalar
    (t : F) (a : L) (ht : t ≠ algebraMap L F a)
    (T U : Polynomial L) (hT : algebraMap (Polynomial L) F T = t)
    (hU : algebraMap (Polynomial L) F U = (t - algebraMap L F a)⁻¹) :
    ∃ c : L, algebraMap L F c = t := by
  have hprod : (T - C a) * U = 1 := by
    apply IsFractionRing.injective (Polynomial L) F
    simpa only [map_mul, map_sub, map_one, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply L (Polynomial L) F,
      hT, hU] using mul_inv_cancel₀ (sub_ne_zero.mpr ht)
  have hunit : IsUnit (T - C a) := IsUnit.of_mul_eq_one _ hprod
  obtain ⟨c, _hc, heq⟩ := Polynomial.isUnit_iff.mp hunit
  refine ⟨c + a, ?_⟩
  have hTc : T = C (c + a) := by
    rw [map_add]
    linear_combination -heq
  rw [← hT, hTc]
  exact (IsScalarTower.algebraMap_apply L (Polynomial L) F (c + a))

/-- Two distinct constant translates cannot have polynomial reciprocals
for a nonscalar rational parameter. -/
theorem two_distinct_regular_reciprocals_force_scalar
    (t : F) (a b : L) (hab : a ≠ b)
    (hta : t ≠ algebraMap L F a) (htb : t ≠ algebraMap L F b)
    (U V : Polynomial L)
    (hU : algebraMap (Polynomial L) F U = (t - algebraMap L F a)⁻¹)
    (hV : algebraMap (Polynomial L) F V = (t - algebraMap L F b)⁻¹) :
    ∃ c : L, algebraMap L F c = t := by
  have hprod : (1 + C (a - b) * U) * (1 - C (a - b) * V) = 1 := by
    apply IsFractionRing.injective (Polynomial L) F
    simp only [map_mul, map_add, map_sub, map_one, hU, hV, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply L (Polynomial L) F]
    field_simp [sub_ne_zero.mpr hta, sub_ne_zero.mpr htb]
    ring
  have hunit : IsUnit (1 + C (a - b) * U) := IsUnit.of_mul_eq_one _ hprod
  obtain ⟨c, _hc, heq⟩ := Polynomial.isUnit_iff.mp hunit
  have hUC : U = C ((c - 1) / (a - b)) := by
    have ha : C (a - b) ≠ (0 : Polynomial L) := by
      simpa only [map_zero] using Polynomial.C_injective.ne (sub_ne_zero.mpr hab)
    apply mul_left_cancel₀ ha
    rw [← map_mul, mul_div_cancel₀ _ (sub_ne_zero.mpr hab)]
    simp only [map_sub, map_one] at heq ⊢
    linear_combination -heq
  have hUF : algebraMap (Polynomial L) F U = algebraMap L F ((c - 1) / (a - b)) := by
    rw [hUC]
    exact (IsScalarTower.algebraMap_apply L (Polynomial L) F _).symm
  refine ⟨a + ((c - 1) / (a - b))⁻¹, ?_⟩
  rw [map_add, map_inv₀, ← hUF, hU, inv_inv]
  ring

/-- For a nonscalar source parameter, genuine constant poles of
polynomially pulled-back rational expressions are unique. The two
expressions may come from different coordinates of the original map. -/
theorem polynomial_pullback_constant_pole_unique
    (t : F) (ht : ¬ ∃ c : L, algebraMap L F c = t)
    (n d n' d' : Polynomial L) (a b : L)
    (hd : d.eval a = 0) (hn : n.eval a ≠ 0)
    (hd' : d'.eval b = 0) (hn' : n'.eval b ≠ 0)
    (H H' : Polynomial L)
    (hvalue : aeval t n = algebraMap (Polynomial L) F H * aeval t d)
    (hvalue' : aeval t n' = algebraMap (Polynomial L) F H' * aeval t d') : a = b := by
  by_contra hab
  have hta : t ≠ algebraMap L F a := fun h => ht ⟨a, h.symm⟩
  have htb : t ≠ algebraMap L F b := fun h => ht ⟨b, h.symm⟩
  obtain ⟨U, hU⟩ := constant_pole_pullback_reciprocal_regular n d a hd hn t hta H hvalue
  obtain ⟨V, hV⟩ := constant_pole_pullback_reciprocal_regular n' d' b hd' hn' t htb H' hvalue'
  exact ht (two_distinct_regular_reciprocals_force_scalar t a b hab hta htb U V hU hV)

/-- A genuine constant pole constructs a nonconstant polynomial source
parameter by moving that pole to infinity: u = 1/(t-a). -/
theorem constant_pole_constructs_nonconstant_polynomial_parameter
    (t : F) (ht : ¬ ∃ c : L, algebraMap L F c = t)
    (n d : Polynomial L) (a : L) (hd : d.eval a = 0) (hn : n.eval a ≠ 0)
    (H : Polynomial L)
    (hvalue : aeval t n = algebraMap (Polynomial L) F H * aeval t d) :
    ∃ U : Polynomial L, 0 < U.natDegree ∧
      algebraMap (Polynomial L) F U = (t - algebraMap L F a)⁻¹ := by
  have hta : t ≠ algebraMap L F a := fun h => ht ⟨a, h.symm⟩
  obtain ⟨U, hU⟩ := constant_pole_pullback_reciprocal_regular n d a hd hn t hta H hvalue
  refine ⟨U, ?_, hU⟩
  by_contra hdeg
  have hC := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hdeg)
  apply ht
  refine ⟨a + (U.coeff 0)⁻¹, ?_⟩
  have hu : algebraMap L F (U.coeff 0) = (t - algebraMap L F a)⁻¹ := by
    rw [IsScalarTower.algebraMap_apply L (Polynomial L) F]
    change algebraMap (Polynomial L) F (C (U.coeff 0)) = _
    rw [← hC, hU]
  rw [map_add, map_inv₀, hu, inv_inv]
  ring

end DimensionFourDependence
