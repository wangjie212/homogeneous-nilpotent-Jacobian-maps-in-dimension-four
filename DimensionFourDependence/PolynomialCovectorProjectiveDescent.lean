import DimensionFourDependence.AlgebraicPolynomialDescent
import DimensionFourDependence.PencilBaseNormalKernel

/-! # Constant projected direction from the scaled polynomial power

Independent normal jets make the three transverse polynomial normal
coordinates an injective coefficient system. Projective descent of a
scaled polynomial power therefore descends the original three source
coordinates up to a single scalar. The scalar and original-field
direction are constructed from the full coefficient equations.
-/

namespace DimensionFourDependence

open Matrix Module Polynomial

attribute [local instance] Polynomial.algebra

set_option maxHeartbeats 2500000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- An injective original-field coefficient system descends any
solution whose right-hand side has original-field coefficients. -/
theorem injective_matrix_solution_constructs_base_vector
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (hker : LinearMap.ker A.toLin' = ⊥)
    (x : Fin n → F) (b : Fin m → K)
    (hx : A.map (algebraMap K F) *ᵥ x = fun i => algebraMap K F (b i)) :
    ∃ c : Fin n → K, x = fun i => algebraMap K F (c i) := by
  obtain ⟨T, hT⟩ := matrix_exists_mul_of_ker_le A (1 : Matrix (Fin n) (Fin n) K)
    (by rw [hker]; exact bot_le)
  have hTF : T.map (algebraMap K F) * A.map (algebraMap K F) = 1 := by
    rw [← Matrix.map_mul, ← hT]
    simp
  refine ⟨T *ᵥ b, ?_⟩
  calc
    x = (T.map (algebraMap K F) * A.map (algebraMap K F)) *ᵥ x := by rw [hTF, one_mulVec]
    _ = T.map (algebraMap K F) *ᵥ (fun i => algebraMap K F (b i)) := by rw [← mulVec_mulVec, hx]
    _ = fun i => algebraMap K F ((T *ᵥ b) i) := by
      funext i
      simp only [mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

/-- A polynomial coefficient system with one-dimensional kernel
equal to the fourth-axis direction is injective on the first three
coordinates. -/
theorem polynomial_covector_ternary_coefficient_kernel_eq_bot
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hvlast : v (Fin.last 3) = 0) :
    LinearMap.ker ((polynomialCovectorCoefficientMatrix v).submatrix id Fin.castSucc).toLin' = ⊥ := by
  let A := polynomialCovectorCoefficientMatrix v
  have haxis : A *ᵥ (Fin.snoc (0 : Fin 3 → K) 1 : Fin 4 → K) = 0 := by
    funext j
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Fin.snoc_last, mul_one, zero_add,
      A, polynomialCovectorCoefficientMatrix, hvlast, Polynomial.coeff_zero]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hAx : A *ᵥ (Fin.snoc x 0 : Fin 4 → K) = 0 := by
    funext j
    have he := congrFun hx j
    change (A.submatrix id Fin.castSucc *ᵥ x) j = 0 at he
    simp only [mulVec, dotProduct, Matrix.submatrix_apply, id_eq] at he
    change (∑ i : Fin 4, A j i * (Fin.snoc x 0 : Fin 4 → K) i) = 0
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero] using he
  have hz := small_matrix_kernel_containing_fourth_axis (F := K) A hdim haxis
    (Fin.snoc x 0) (by simpa using hAx)
  funext i
  simpa only [Fin.snoc_castSucc, Pi.zero_apply] using hz i

/-- A nonzero transverse point gives a nonzero polynomial normal
pairing when the original coefficient kernel is just the vertex axis. -/
theorem polynomial_covector_ternary_pairing_ne_zero
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hvlast : v (Fin.last 3) = 0) (x : Fin 3 → F) (hx : x ≠ 0) :
    (∑ i : Fin 3, C (x i) * Polynomial.map (algebraMap K F) (v i.castSucc)) ≠ 0 := by
  intro hpoly
  let A := (polynomialCovectorCoefficientMatrix v).submatrix id Fin.castSucc
  have hAx : A.map (algebraMap K F) *ᵥ x = 0 := by
    funext j
    have he := congrArg (fun p : Polynomial F => p.coeff j.val) hpoly
    simpa only [A, mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id_eq,
      polynomialCovectorCoefficientMatrix, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
      Polynomial.coeff_map, Polynomial.coeff_zero, mul_comm, Pi.zero_apply] using he
  obtain ⟨c, hc⟩ := injective_matrix_solution_constructs_base_vector A
    (polynomial_covector_ternary_coefficient_kernel_eq_bot v hdim hvlast) x 0 (by
      funext j
      simpa only [Pi.zero_apply, map_zero] using congrFun hAx j)
  have hcA : A *ᵥ c = 0 := by
    funext j
    apply (algebraMap K F).injective
    have he := congrFun hAx j
    rw [hc] at he
    simpa only [mulVec, dotProduct, Matrix.map_apply, ← map_mul, ← map_sum, map_zero,
      Pi.zero_apply] using he
  have hc0 : c = 0 := by
    have hmem : c ∈ LinearMap.ker A.toLin' := hcA
    rw [polynomial_covector_ternary_coefficient_kernel_eq_bot v hdim hvlast,
      Submodule.mem_bot] at hmem
    exact hmem
  apply hx
  funext i
  simp only [hc, hc0, Pi.zero_apply, map_zero]

/-- Descent of the whole polynomial pairing descends the original
transverse vector up to the same nonzero scalar. -/
theorem polynomial_covector_projective_polynomial_descent_constructs_direction
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hvlast : v (Fin.last 3) = 0) (x : Fin 3 → F) (c : F) (hc : c ≠ 0)
    (Q : Polynomial K)
    (hpoly : (∑ i : Fin 3, C (x i) * Polynomial.map (algebraMap K F) (v i.castSucc)) =
      C c * Q.map (algebraMap K F)) :
    ∃ b : Fin 3 → K, x = c • (fun i => algebraMap K F (b i)) := by
  let A := (polynomialCovectorCoefficientMatrix v).submatrix id Fin.castSucc
  let y : Fin 3 → F := fun i => x i / c
  have hy : (∑ i : Fin 3, C (y i) * Polynomial.map (algebraMap K F) (v i.castSucc)) =
      Q.map (algebraMap K F) := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hc)
    calc
      C c * (∑ i : Fin 3, C (y i) * Polynomial.map (algebraMap K F) (v i.castSucc)) =
          ∑ i : Fin 3, C (x i) * Polynomial.map (algebraMap K F) (v i.castSucc) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_assoc, ← C_mul]
        congr 2
        dsimp only [y]
        field_simp
      _ = C c * Q.map (algebraMap K F) := hpoly
  have hyA : A.map (algebraMap K F) *ᵥ y =
      fun j => algebraMap K F (Q.coeff j.val) := by
    funext j
    have he := congrArg (fun p : Polynomial F => p.coeff j.val) hy
    simpa only [A, mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id_eq,
      polynomialCovectorCoefficientMatrix, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
      Polynomial.coeff_map, mul_comm] using he
  obtain ⟨b, hb⟩ := injective_matrix_solution_constructs_base_vector A
    (polynomial_covector_ternary_coefficient_kernel_eq_bot v hdim hvlast) y
    (fun j => Q.coeff j.val) hyA
  refine ⟨b, ?_⟩
  funext i
  have he := congrFun hb i
  change x i / c = algebraMap K F (b i) at he
  change x i = c * algebraMap K F (b i)
  exact (div_eq_iff hc).mp he |>.trans (mul_comm _ _)

variable [IsAlgClosed K]

/-- The scaled-power identity of the cone base-curve argument
constructs a fixed original-field projected direction. -/
theorem polynomial_covector_algebraic_scaled_power_constructs_constant_direction
    (w : Fin 4 → RatFunc K) (v : Fin 4 → Polynomial K) (r : RatFunc K)
    (hLI : LinearIndependent (RatFunc K) (rationalParameterJetMatrix w).row)
    (hrep : ∀ i, w i = r * algebraMap (Polynomial K) (RatFunc K) (v i))
    (hvlast : v (Fin.last 3) = 0) (x : Fin 3 → F) (hx : x ≠ 0)
    (h : F) (hh : h ≠ 0) (d : ℕ) (hd : 0 < d)
    (halg : IsAlgebraic (Polynomial K) (C h⁻¹ *
      (∑ i : Fin 3, C (x i) * Polynomial.map (algebraMap K F) (v i.castSucc)) ^ d)) :
    ∃ (c : F) (b : Fin 3 → K), c ≠ 0 ∧ b ≠ 0 ∧
      x = c • (fun i => algebraMap K F (b i)) := by
  let P : Polynomial F := ∑ i : Fin 3, C (x i) * Polynomial.map (algebraMap K F) (v i.castSucc)
  have hdim := polynomial_normal_coefficient_kernel_finrank_le_one w v r hLI hrep
  have hP : P ≠ 0 := polynomial_covector_ternary_pairing_ne_zero v hdim hvlast x hx
  obtain ⟨Q, hQ⟩ := algebraic_scaled_power_constructs_projective_polynomial_descent P hP h hh d hd halg
  obtain ⟨b, hb⟩ := polynomial_covector_projective_polynomial_descent_constructs_direction
    v hdim hvlast x P.leadingCoeff (leadingCoeff_ne_zero.mpr hP) Q hQ
  refine ⟨P.leadingCoeff, b, leadingCoeff_ne_zero.mpr hP, ?_, hb⟩
  intro hb0
  apply hx
  rw [hb, hb0]
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, map_zero, smul_eq_mul, mul_zero]

end DimensionFourDependence
