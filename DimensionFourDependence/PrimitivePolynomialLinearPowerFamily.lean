import DimensionFourDependence.PrimitiveParameterScalarGauss

/-! # A common rational linear factor has primitive polynomial normalization

A rational covector supplies its own primitive polynomial representative.
The same scalar change is applied to every member of the pure-power
family. Polynomiality of each whole form then forces its normalized
scalar factor to be a polynomial, using the proved finite-base-point
Gauss argument. All polynomial forms are recovered exactly.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}

/-- A family of polynomial forms with one nonzero common rational
linear factor constructs a primitive polynomial covector and polynomial
scalar factors, with no finite base point and exact whole-form identities. -/
theorem rational_linear_power_family_constructs_primitive_polynomial_factors
    (P : Fin m → MvPolynomial (Fin n) (Polynomial K))
    (b : Fin n → RatFunc K) (hb : b ≠ 0) (r : Fin m → RatFunc K) (d : ℕ)
    (hP : ∀ i, MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P i) =
      C (r i) * linearFormPolynomial b ^ d) :
    ∃ v : Fin n → Polynomial K, v ≠ 0 ∧
      (∀ q : Polynomial K, (∀ j, q ∣ v j) → IsUnit q) ∧
      (∀ a : K, ∃ j, (v j).eval a ≠ 0) ∧
      ∃ (s : RatFunc K) (A : Fin m → Polynomial K), s ≠ 0 ∧
        (∀ j, b j = s * algebraMap (Polynomial K) (RatFunc K) (v j)) ∧
        (∀ i, algebraMap (Polynomial K) (RatFunc K) (A i) = r i * s ^ d ∧
          P i = C (A i) * polynomialParameterLinearForm v ^ d) := by
  classical
  obtain ⟨v, hv, hprimitive, s, hs, hrep⟩ := rational_vector_primitive_polynomial_presentation b hb
  have hlin : linearFormPolynomial b = C s *
      linearFormPolynomial (fun j => algebraMap (Polynomial K) (RatFunc K) (v j)) := by
    simp only [linearFormPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hrep j, map_mul, mul_assoc]
  have hscaled (i : Fin m) : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P i) =
      C (r i * s ^ d) * linearFormPolynomial (fun j => algebraMap (Polynomial K) (RatFunc K) (v j)) ^ d := by
    rw [hP i, hlin, mul_pow, ← map_pow, ← mul_assoc, ← map_mul]
  have hex (i : Fin m) := primitive_parameter_linear_power_scalar_is_polynomial
    v hprimitive d (r i * s ^ d) (P i) (hscaled i)
  choose A hA using hex
  refine ⟨v, hv, hprimitive, primitive_parameter_covector_no_constant_base_point v hprimitive,
    s, A, hs, hrep, ?_⟩
  intro i
  refine ⟨hA i, ?_⟩
  apply MvPolynomial.map_injective (algebraMap (Polynomial K) (RatFunc K))
    (RatFunc.algebraMap_injective K)
  rw [map_mul, MvPolynomial.map_C, map_pow, polynomialParameterLinearForm_map, hA i]
  exact hscaled i

end DimensionFourDependence
