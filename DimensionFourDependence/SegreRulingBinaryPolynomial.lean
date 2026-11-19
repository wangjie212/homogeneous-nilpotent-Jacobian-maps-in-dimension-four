import DimensionFourDependence.SegreFiniteRadialProductFactorization

/-! # Exact binary restriction and bounded affine polynomials on either Segre ruling -/

namespace DimensionFourDependence

open Matrix

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- The varying coordinate on the ruling with the specified fixed ratio. -/
def segreRulingRemainingIndex (j : Fin 3) : Fin 3 := if j = 1 then 2 else 1

/-- Restrict an original ternary covector to its original Segre ruling,
retaining its actual parameter coefficient in the same finite field. -/
def segreRulingBinaryCoefficients (j : Fin 3) (t : C) (A : Fin 3 → C) : Fin 2 → C :=
  ![A 0 + t * A j, A (segreRulingRemainingIndex j)]

/-- The binary restriction has exactly the original covector value. -/
theorem segre_ruling_covector_binary_pairing
    (j : Fin 3) (hj : j ≠ 0) (t : C) (A : Fin 3 → C) (Y : Fin 3 → F)
    (hruling : Y j = algebraMap C F t * Y 0) :
    (fun i => algebraMap C F (A i)) ⬝ᵥ Y =
      algebraMap C F (segreRulingBinaryCoefficients j t A 0) * Y 0 +
        algebraMap C F (segreRulingBinaryCoefficients j t A 1) * Y (segreRulingRemainingIndex j) := by
  fin_cases j
  · exact False.elim (hj rfl)
  · change Y 1 = algebraMap C F t * Y 0 at hruling
    simp [segreRulingBinaryCoefficients, segreRulingRemainingIndex, dotProduct, Fin.sum_univ_succ,
      map_add, map_mul, hruling]
    ring
  · change Y 2 = algebraMap C F t * Y 0 at hruling
    simp [segreRulingBinaryCoefficients, segreRulingRemainingIndex, dotProduct, Fin.sum_univ_succ,
      map_add, map_mul, hruling]
    ring

/-- The exact affine polynomial of an original binary linear form. -/
noncomputable def segreRulingAffineFactor (A : Fin 2 → C) : Polynomial C :=
  Polynomial.C (A 0) + Polynomial.C (A 1) * Polynomial.X

/-- The affine ruling polynomial retains the linear-times-dth-power presentation. -/
noncomputable def segreRulingPowerPolynomial (R B : Fin 2 → C) (d : ℕ) : Polynomial C :=
  segreRulingAffineFactor R * segreRulingAffineFactor B ^ d

theorem segreRulingAffineFactor_natDegree_le_one (A : Fin 2 → C) :
    (segreRulingAffineFactor A).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

/-- The original ruling power polynomial has degree at most d+1,
including constant restrictions and proportional linear factors. -/
theorem segreRulingPowerPolynomial_natDegree_le (R B : Fin 2 → C) (d : ℕ) :
    (segreRulingPowerPolynomial R B d).natDegree ≤ d + 1 := by
  unfold segreRulingPowerPolynomial
  calc
    _ ≤ (segreRulingAffineFactor R).natDegree + (segreRulingAffineFactor B ^ d).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + d := add_le_add (segreRulingAffineFactor_natDegree_le_one R)
      (Polynomial.natDegree_pow_le.trans (by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left d (segreRulingAffineFactor_natDegree_le_one B)))
    _ = d + 1 := Nat.add_comm _ _

/-- Removing the original radial scale gives exactly the product of
the two original affine linear factors at the original varying ratio. -/
theorem binary_linear_power_normalized_identity
    (r q a b c e : F) (hr : r ≠ 0) (d : ℕ) :
    (a * r + b * q) * (c * r + e * q) ^ d / r ^ (d + 1) =
      (a + b * (q / r)) * (c + e * (q / r)) ^ d := by
  have hA : a * r + b * q = r * (a + b * (q / r)) := by field_simp [hr]
  have hB : c * r + e * q = r * (c + e * (q / r)) := by field_simp [hr]
  rw [hA, hB, mul_pow, pow_succ]
  field_simp [hr]

/-- The scale-free value of the original factorization is the exact
bounded polynomial in the original varying ruling coordinate. -/
theorem segre_ruling_factored_pairing_normalized_polynomial_value
    (j : Fin 3) (hj : j ≠ 0) (t : C) (R B : Fin 3 → C) (Y : Fin 3 → F)
    (hY0 : Y 0 ≠ 0) (hruling : Y j = algebraMap C F t * Y 0) (d : ℕ) :
    ((fun i => algebraMap C F (R i)) ⬝ᵥ Y) * ((fun i => algebraMap C F (B i)) ⬝ᵥ Y) ^ d / Y 0 ^ (d + 1) =
      Polynomial.aeval (Y (segreRulingRemainingIndex j) / Y 0)
        (segreRulingPowerPolynomial (segreRulingBinaryCoefficients j t R)
          (segreRulingBinaryCoefficients j t B) d) := by
  rw [segre_ruling_covector_binary_pairing j hj t R Y hruling,
    segre_ruling_covector_binary_pairing j hj t B Y hruling,
    binary_linear_power_normalized_identity _ _ _ _ _ _ hY0]
  simp only [segreRulingPowerPolynomial, segreRulingAffineFactor, map_mul, map_pow, map_add,
    Polynomial.aeval_C, Polynomial.aeval_X]

end DimensionFourDependence
