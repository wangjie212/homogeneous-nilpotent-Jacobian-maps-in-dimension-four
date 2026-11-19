import DimensionFourDependence.PolynomialCovectorCoefficientKernel
import DimensionFourDependence.SmallKernelScalarExtension
import DimensionFourDependence.PrimitiveRationalVector

/-! # Independent normal jets leave at most one fixed projective point in the moving planes -/

namespace DimensionFourDependence

open Matrix Module

section ConstantRelations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Independent actual normal jets force the original-field space
of constant normal relations to have dimension at most one. -/
theorem normal_constant_relation_space_finrank_le_one
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row) :
    finrank K (LinearMap.ker (Fintype.linearCombination K w)) ≤ 1 := by
  by_cases hker : LinearMap.ker (Fintype.linearCombination K w) = ⊥
  · have hz : finrank K (LinearMap.ker (Fintype.linearCombination K w)) = 0 :=
      Submodule.finrank_eq_zero.mpr hker
    omega
  · obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
    have hrel : w ⬝ᵥ (fun i => algebraMap K F (c i)) = 0 := by
      change Fintype.linearCombination K w c = 0 at hc
      simpa only [Fintype.linearCombination_apply, Algebra.smul_def, dotProduct, mul_comm] using hc
    have hcC := constant_normal_relation_mem_characteristic D w c hrel
    rw [normal_constant_relation_space_eq_span_characteristic D w hLI c hc0 hcC,
      finrank_span_singleton hc0]

end ConstantRelations

variable {K : Type*} [Field K]

/-- Clearing the actual rational normal's denominators preserves its
constant plane intersection: the finite coefficient kernel of its polynomial
representative has dimension at most one over the original field. -/
theorem polynomial_normal_coefficient_kernel_finrank_le_one
    (w : Fin 4 → RatFunc K) (v : Fin 4 → Polynomial K) (r : RatFunc K)
    (hLI : LinearIndependent (RatFunc K) (rationalParameterJetMatrix w).row)
    (hrep : ∀ i, w i = r * algebraMap (Polynomial K) (RatFunc K) (v i)) :
    finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1 := by
  have hle : LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin' ≤
      LinearMap.ker (Fintype.linearCombination K w) := by
    intro c hc
    have hp := (polynomial_covector_coefficient_kernel_iff v c).mp hc
    have hpF := congrArg (algebraMap (Polynomial K) (RatFunc K)) hp
    have hz : ∑ i, algebraMap K (RatFunc K) (c i) *
        algebraMap (Polynomial K) (RatFunc K) (v i) = 0 := by
      simpa only [map_sum, map_mul, map_zero, RatFunc.algebraMap_C,
        ← RatFunc.algebraMap_eq_C] using hpF
    change Fintype.linearCombination K w c = 0
    simp only [Fintype.linearCombination_apply, Algebra.smul_def]
    calc
      _ = r * (∑ i, algebraMap K (RatFunc K) (c i) *
          algebraMap (Polynomial K) (RatFunc K) (v i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrep i]
        ring
      _ = 0 := by rw [hz, mul_zero]
  exact (Submodule.finrank_mono hle).trans
    (normal_constant_relation_space_finrank_le_one (rationalParameterDerivative K) w hLI)

variable {E L : Type*} [Field E] [Field L] [Algebra K E] [Algebra K L]
  [Algebra E L] [IsScalarTower K E L]

/-- For a moving plane with independent original normal jets,
every point incident at a parameter transcendental over its coordinate
field lies on one original constant line. The same line works for all points. -/
theorem normal_plane_transcendental_incidence_constant_generator
    (w : Fin 4 → RatFunc K) (v : Fin 4 → Polynomial K) (r : RatFunc K)
    (hLI : LinearIndependent (RatFunc K) (rationalParameterJetMatrix w).row)
    (hrep : ∀ i, w i = r * algebraMap (Polynomial K) (RatFunc K) (v i)) :
    ∃ c : Fin 4 → K, ∀ (x : Fin 4 → E) (t : L), Transcendental E t →
      (∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) →
        ∃ a : E, x = a • (fun i => algebraMap K E (c i)) := by
  obtain ⟨c, _hc, hgen⟩ := matrix_kernel_finrank_le_one_constant_generator (E := E)
    (polynomialCovectorCoefficientMatrix v)
    (polynomial_normal_coefficient_kernel_finrank_le_one w v r hLI hrep)
  exact ⟨c, fun x t ht hp => hgen x
    (transcendental_parameter_plane_incidence_mem_coefficient_kernel v x t ht hp)⟩

/-- A nonzero incident point at such a transcendental parameter has
all its projective coordinate ratios in the original constant field. -/
theorem normal_plane_transcendental_incidence_projective_ratios_descend
    (w : Fin 4 → RatFunc K) (v : Fin 4 → Polynomial K) (r : RatFunc K)
    (hLI : LinearIndependent (RatFunc K) (rationalParameterJetMatrix w).row)
    (hrep : ∀ i, w i = r * algebraMap (Polynomial K) (RatFunc K) (v i))
    (x : Fin 4 → E) (t : L) (ht : Transcendental E t)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0)
    (a : Fin 4) (ha : x a ≠ 0) :
    ∃ b : Fin 4 → K, b a = 1 ∧ ∀ i, x i / x a = algebraMap K E (b i) :=
  small_matrix_kernel_projective_ratios_descend (polynomialCovectorCoefficientMatrix v)
    (polynomial_normal_coefficient_kernel_finrank_le_one w v r hLI hrep) x
    (transcendental_parameter_plane_incidence_mem_coefficient_kernel v x t ht hplane) a ha

end DimensionFourDependence
