import DimensionFourDependence.PrimitiveParameterLinearForm

/-! # A primitive linear power cannot hide a parameter denominator

The reduced numerator and denominator of a rational scalar have no
common root. Specializing a proposed denominator root in the whole
polynomial coefficient identity contradicts the nonzero primitive linear
power. Thus the scalar is an actual polynomial in the parameter.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K σ : Type*} [Field K] [IsAlgClosed K]

/-- A scalar multiplying a polynomial form with no finite constant
base point is polynomial whenever the entire product has polynomial
parameter coefficients. -/
theorem no_constant_base_point_form_rational_scalar_is_polynomial
    (B P : MvPolynomial σ (Polynomial K))
    (hB : ∀ a : K, MvPolynomial.map (Polynomial.evalRingHom a) B ≠ 0)
    (r : RatFunc K)
    (hP : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) P =
      C r * MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) B) :
    ∃ a : Polynomial K, algebraMap (Polynomial K) (RatFunc K) a = r := by
  classical
  have hnum : algebraMap (Polynomial K) (RatFunc K) r.num =
      r * algebraMap (Polynomial K) (RatFunc K) r.denom :=
    (div_eq_iff (RatFunc.algebraMap_ne_zero r.denom_ne_zero)).mp (RatFunc.num_div_denom r)
  have hcleared : C r.denom * P = C r.num * B := by
    apply MvPolynomial.map_injective (algebraMap (Polynomial K) (RatFunc K))
      (RatFunc.algebraMap_injective K)
    simp only [map_mul, MvPolynomial.map_C, hP]
    rw [← mul_assoc, ← map_mul, mul_comm _ r, ← hnum]
  have hdegree : r.denom.natDegree = 0 := by
    by_contra hdeg
    have hpos : 0 < r.denom.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root r.denom hpos.ne'
    have hn : r.num.eval a ≠ 0 := by
      have hcop := Polynomial.aeval_ne_zero_of_isCoprime r.isCoprime_num_denom a
      exact hcop.resolve_right (by simpa using ha)
    have heq := congrArg (MvPolynomial.map (Polynomial.evalRingHom a)) hcleared
    simp only [map_mul, MvPolynomial.map_C] at heq
    change C (r.denom.eval a) * MvPolynomial.map (Polynomial.evalRingHom a) P =
      C (r.num.eval a) * MvPolynomial.map (Polynomial.evalRingHom a) B at heq
    rw [ha, map_zero, zero_mul] at heq
    exact (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hn) (hB a)) heq.symm
  have hD := Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hDmap : algebraMap (Polynomial K) (RatFunc K) r.denom = RatFunc.C (r.denom.coeff 0) :=
    (congrArg (algebraMap (Polynomial K) (RatFunc K)) hD).trans (RatFunc.algebraMap_C _)
  refine ⟨r.num * Polynomial.C ((r.denom.coeff 0)⁻¹), ?_⟩
  calc
    algebraMap (Polynomial K) (RatFunc K) (r.num * Polynomial.C ((r.denom.coeff 0)⁻¹)) =
        algebraMap (Polynomial K) (RatFunc K) r.num /
          algebraMap (Polynomial K) (RatFunc K) r.denom := by
      rw [hDmap]
      simp only [map_mul, RatFunc.algebraMap_C, map_inv₀, div_eq_mul_inv]
    _ = r := RatFunc.num_div_denom r

variable {n : ℕ}

/-- In particular, a rational scalar multiplying a primitive polynomial
linear power is an actual polynomial scalar. -/
theorem primitive_parameter_linear_power_scalar_is_polynomial
    (v : Fin n → Polynomial K)
    (hprimitive : ∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r)
    (d : ℕ) (r : RatFunc K) (P : MvPolynomial (Fin n) (Polynomial K))
    (hP : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) P =
      C r * (linearFormPolynomial (fun i => algebraMap (Polynomial K) (RatFunc K) (v i))) ^ d) :
    ∃ a : Polynomial K, algebraMap (Polynomial K) (RatFunc K) a = r := by
  apply no_constant_base_point_form_rational_scalar_is_polynomial
    (polynomialParameterLinearForm v ^ d) P
    (primitive_parameter_linear_power_specialization_ne_zero v hprimitive d) r
  simpa only [map_pow, polynomialParameterLinearForm_map] using hP

end DimensionFourDependence
