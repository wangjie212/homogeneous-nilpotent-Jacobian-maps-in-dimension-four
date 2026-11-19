import DimensionFourDependence.PolynomialParameterRegularity
import DimensionFourDependence.ConstantReciprocalParameterEquiv

/-! # A rational curve field with a regular value has a regular generator -/

namespace DimensionFourDependence

open Polynomial

universe u
set_option maxHeartbeats 1500000

variable {K : Type u} [Field K]

/-- A reduced constant denominator represents an actual polynomial. -/
theorem ratFunc_exists_polynomial_of_denom_degree_zero (r : RatFunc K)
    (hd : r.denom.natDegree = 0) :
    ∃ A : Polynomial K, algebraMap (Polynomial K) (RatFunc K) A = r := by
  have hD : algebraMap (Polynomial K) (RatFunc K) r.denom = RatFunc.C (r.denom.coeff 0) :=
    (congrArg (algebraMap (Polynomial K) (RatFunc K)) (eq_C_of_natDegree_eq_zero hd)).trans
      (RatFunc.algebraMap_C _)
  refine ⟨r.num * C (r.denom.coeff 0)⁻¹, ?_⟩
  calc
    algebraMap (Polynomial K) (RatFunc K) (r.num * C (r.denom.coeff 0)⁻¹) =
      algebraMap (Polynomial K) (RatFunc K) r.num /
        algebraMap (Polynomial K) (RatFunc K) r.denom := by
      rw [hD]
      simp only [map_mul, RatFunc.algebraMap_C, map_inv₀, div_eq_mul_inv]
    _ = r := RatFunc.num_div_denom r

variable {R F : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F]
  [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F] [IsFractionRing R F]

omit [IsDomain R] [IsIntegrallyClosed R] [Algebra K R] [IsScalarTower K R F] [IsFractionRing R F] in
/-- A reduced rational function whose image is regular satisfies
the cleared numerator-denominator relation in the original source. -/
theorem rational_function_regular_value_cleared
    (f : RatFunc K →ₐ[K] F) (r : RatFunc K) (H : R)
    (hH : f r = algebraMap R F H) :
    aeval (f RatFunc.X) r.num = algebraMap R F H * aeval (f RatFunc.X) r.denom := by
  have hnum : algebraMap (Polynomial K) (RatFunc K) r.num =
      r * algebraMap (Polynomial K) (RatFunc K) r.denom :=
    (div_eq_iff (RatFunc.algebraMap_ne_zero r.denom_ne_zero)).mp (RatFunc.num_div_denom r)
  have he := congrArg f hnum
  change f (algebraMap (Polynomial K) (RatFunc K) r.num) =
    f (r * algebraMap (Polynomial K) (RatFunc K) r.denom) at he
  simpa only [map_mul, rational_function_algHom_polynomial_value, hH] using he

variable [IsAlgClosed K]

/-- A nonconstant regular value allows a generator of the whole rational
field to be chosen in the normal source domain. -/
theorem rational_curve_field_with_regular_value_has_regular_generator
    (f : RatFunc K →ₐ[K] F) (r : RatFunc K) (H : R)
    (hH : f r = algebraMap R F H) (hn : ¬ ∃ c : K, f r = algebraMap K F c) :
    ∃ (g : RatFunc K →ₐ[K] F) (T : R),
      g.fieldRange = f.fieldRange ∧ algebraMap R F T = g RatFunc.X := by
  by_cases hd : r.denom.natDegree = 0
  · obtain ⟨A, hA⟩ := ratFunc_exists_polynomial_of_denom_degree_zero r hd
    have he : aeval (f RatFunc.X) A = algebraMap R F H := by
      rw [← rational_function_algHom_polynomial_value, hA, hH]
    have ha : 0 < A.natDegree := by
      by_contra h
      apply hn
      refine ⟨A.coeff 0, ?_⟩
      rw [← hA, rational_function_algHom_polynomial_value,
        eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h), aeval_C]
      simp
    obtain ⟨T, hT⟩ := parameter_regular_of_nonconstant_polynomial_value A ha (f RatFunc.X) H he
    exact ⟨f, T, rfl, hT⟩
  · have hpos : 0 < r.denom.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root r.denom hpos.ne'
    have hna : r.num.eval a ≠ 0 :=
      (Polynomial.aeval_ne_zero_of_isCoprime r.isCoprime_num_denom a).resolve_right (by simpa using ha)
    have ht : f RatFunc.X ≠ algebraMap K F a := by
      intro he
      have hAlg : IsAlgebraic K (f RatFunc.X) := he ▸ isAlgebraic_algebraMap (A := F) a
      exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff f f.injective).mp hAlg)
    obtain ⟨T, hT⟩ := constant_pole_pullback_reciprocal_regular r.num r.denom a ha hna
      (f RatFunc.X) ht H (rational_function_regular_value_cleared f r H hH)
    let e := constantReciprocalParameterEquiv a
    let g := f.comp e.toAlgHom
    refine ⟨g, T, ?_, ?_⟩
    · ext v
      change (∃ p, f (e p) = v) ↔ ∃ q, f q = v
      exact ⟨fun ⟨p, hp⟩ => ⟨e p, hp⟩,
        fun ⟨q, hq⟩ => ⟨e.symm q, by rw [e.apply_symm_apply, hq]⟩⟩
    · change algebraMap R F T = f (constantReciprocalParameterEquiv a RatFunc.X)
      rw [constantReciprocalParameterEquiv_X, map_inv₀, map_sub, AlgHom.commutes]
      exact hT

end DimensionFourDependence
