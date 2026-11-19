import DimensionFourDependence.PencilBaseNormalKernel
import DimensionFourDependence.ClosedGaussNormalJetRealization
import DimensionFourDependence.MatrixKernelScalarExtension
import DimensionFourDependence.CommonVertexNonlinearExclusion

/-! # A pencil base maps to zero when the actual normal coordinates are independent -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- An independent polynomial covector has no nonzero coefficient-kernel
vector, even after an arbitrary extension of the constants. -/
theorem independent_polynomial_covector_extended_kernel_zero
    {n : ℕ} (v : Fin n → Polynomial K) (hv : LinearIndependent K v)
    (x : Fin n → F)
    (hx : (polynomialCovectorCoefficientMatrix v).map (algebraMap K F) *ᵥ x = 0) : x = 0 := by
  have hker : LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin' ≤
      LinearMap.ker (1 : Matrix (Fin n) (Fin n) K).toLin' := by
    intro c hc
    have hp := (polynomial_covector_coefficient_kernel_iff v c).mp hc
    have hz : c = 0 := funext (Fintype.linearIndependent_iff.mp hv c
      (by simpa only [Polynomial.smul_eq_C_mul] using hp))
    rw [hz]
    exact Submodule.zero_mem _
  have he := matrix_kernel_le_after_scalar_extension
    (polynomialCovectorCoefficientMatrix v) (1 : Matrix (Fin n) (Fin n) K) hker hx
  have hone : (1 : Matrix (Fin n) (Fin n) K).map (algebraMap K F) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  change (1 : Matrix (Fin n) (Fin n) K).map (algebraMap K F) *ᵥ x = 0 at he
  simpa only [hone, Matrix.one_mulVec] using he

/-- Every field-valued base point maps to zero if the polynomial
normal defining the source pencil has independent coordinates. -/
theorem pencil_base_outputs_zero_of_independent_polynomial_normal
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (H : Fin 4 → MvPolynomial (Fin 4) K) (v : Fin 4 → Polynomial K)
    (hv : LinearIndependent K v)
    (hsection : (∑ i, Polynomial.aeval
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
      (v i) * algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0)
    (ψ : MvPolynomial (Fin 4) K →ₐ[K] F) (hpψ : ψ p = 0) (hqψ : ψ q = 0) :
    ∀ i, ψ (H i) = 0 := by
  have he := independent_polynomial_covector_extended_kernel_zero v hv (fun i => ψ (H i))
    (pencil_base_output_mem_normal_coefficient_kernel p q hq hrel H v hsection ψ hpψ hqψ)
  exact fun i => congrFun he i

variable [CharZero K]

/-- Independence of the original actual normal forces all four
outputs to vanish on the whole original reduced closed-Gauss pencil base. -/
theorem original_independent_normal_pencil_base_outputs_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hNormal : LinearIndependent K (rationalImageNormal H I.equation))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
    (ψ : MvPolynomial (Fin 4) K →ₐ[K] F) (hpψ : ψ p = 0) (hqψ : ψ q = 0) :
    ∀ i, ψ (H i) = 0 := by
  let f := closedGaussParameterSourceHom H I e
  let w := closedGaussParameterNormal H I e
  let a := rationalImageNormal H I.equation (imageNormalPivot H I)
  have ha : a ≠ 0 := imageNormalPivot_ne_zero H I
  have hw : LinearIndependent K w := by
    apply LinearIndependent.of_comp (a • f.toLinearMap)
    convert hNormal using 1
    funext i
    change a * f (w i) = rationalImageNormal H I.equation i
    rw [closedGaussParameterSourceHom_normal, mul_div_cancel₀ _ ha]
  have hw0 : w ≠ 0 := by
    intro hz
    exact hw.ne_zero 0 (congrFun hz 0)
  obtain ⟨v, _hv, _hprimitive, r, hr, hrep⟩ := rational_vector_primitive_polynomial_presentation w hw0
  have hv : LinearIndependent K v := by
    let g : Polynomial K →ₗ[K] RatFunc K :=
      r • (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)).toLinearMap
    apply LinearIndependent.of_comp g
    convert hw using 1
    funext i
    exact (hrep i).symm
  have hrepF (i : Fin 4) : f (w i) = f r * Polynomial.aeval (f RatFunc.X) (v i) := by
    rw [hrep i, map_mul, rational_function_algHom_polynomial_value]
  have hpair : (∑ i, f (w i) * algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0 := by
    simpa only [f, w, closedGaussParameterSourceHom_normal, dotProduct] using
      I.normalized_normal_dot_output_eq_zero H hd hH
  have hsection : (∑ i, Polynomial.aeval (f RatFunc.X) (v i) *
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0 := by
    have he : f r * (∑ i, Polynomial.aeval (f RatFunc.X) (v i) *
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0 := by
      rw [Finset.mul_sum]
      convert hpair using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hrepF i]
      ring
    exact (mul_eq_zero.mp he).resolve_left ((map_ne_zero f).mpr hr)
  apply pencil_base_outputs_zero_of_independent_polynomial_normal
    p q hq hrel H v hv ?_ ψ hpψ hqψ
  rw [← hparameter]
  exact hsection

omit F in
/-- The vanishing holds at nonclosed base points: every original
output lies in the radical of the original two-equation pencil base. -/
theorem original_independent_normal_pencil_base_radical_contains_outputs
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hNormal : LinearIndependent K (rationalImageNormal H I.equation))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q) :
    ∀ i, H i ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).radical := by
  intro i
  rw [Ideal.radical_eq_sInf]
  apply Ideal.mem_sInf.mpr
  intro Q hQ
  let : Q.IsPrime := hQ.2
  let ψ : MvPolynomial (Fin 4) K →ₐ[K] Q.ResidueField := IsScalarTower.toAlgHom K _ _
  apply Ideal.algebraMap_residueField_eq_zero.mp
  exact original_independent_normal_pencil_base_outputs_zero H hd hH I hNormal e p q hq hrel hparameter ψ
    (Ideal.algebraMap_residueField_eq_zero.mpr (hQ.1 (Ideal.subset_span (by simp))))
    (Ideal.algebraMap_residueField_eq_zero.mpr (hQ.1 (Ideal.subset_span (by simp)))) i

end DimensionFourDependence
