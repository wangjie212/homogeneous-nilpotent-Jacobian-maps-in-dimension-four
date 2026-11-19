import DimensionFourDependence.AffineTangentNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Descending independent tangent directions by coefficient functionals

The tangent equation is linear in its five coefficients. Every linear
functional from the extension field to the original field therefore gives
an original-field tangent equation. If the two horizontal coefficients
are linearly independent over the original field, a linear left inverse
constructs the two normalized horizontal lifts directly.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The actual tangent action is a linear combination of five original
polynomials, with all extension-field dependence in its five coefficients. -/
theorem affineProjectedTangentAction_coefficient_extension_expansion
    (u : Fin 2 → E) (b : Fin 3 → E) (P : MvPolynomial (Fin 3) K) :
    affineProjectedTangentAction u b (MvPolynomial.map (algebraMap K E) P) =
      C (u 0) * MvPolynomial.map (algebraMap K E) (pderiv 0 P) +
      C (u 1) * MvPolynomial.map (algebraMap K E) (pderiv 1 P) +
      C (b 0) * MvPolynomial.map (algebraMap K E) (pderiv 2 P) +
      C (b 1) * MvPolynomial.map (algebraMap K E) (X 0 * pderiv 2 P) +
      C (b 2) * MvPolynomial.map (algebraMap K E) (X 1 * pderiv 2 P) := by
  simp only [affineProjectedTangentAction, affineTangentVerticalCoefficient,
    pderiv_map, map_mul, MvPolynomial.map_X]
  ring

/-- Applying any original-field linear coefficient functional to a
whole extension-field tangent identity gives a whole original-field
tangent identity for the same original polynomial. -/
theorem affine_tangent_equation_descends_by_linear_coefficient_functional
    (P : MvPolynomial (Fin 3) K) (u : Fin 2 → E) (b : Fin 3 → E)
    (hzero : affineProjectedTangentAction u b (MvPolynomial.map (algebraMap K E) P) = 0)
    (φ : E →ₗ[K] K) :
    affineProjectedTangentAction (fun i => φ (u i)) (fun i => φ (b i)) P = 0 := by
  have hscalar (a : E) (r : K) : φ (a * algebraMap K E r) = φ a * r := by
    rw [mul_comm]
    rw [← Algebra.smul_def]
    rw [map_smul]
    simp [smul_eq_mul, mul_comm]
  rw [affineProjectedTangentAction_coefficient_extension_expansion] at hzero
  ext m
  have hc := congrArg (fun Q : MvPolynomial (Fin 3) E => φ (Q.coeff m)) hzero
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_map, map_add,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero, hscalar] at hc
  have hexpand := affineProjectedTangentAction_coefficient_extension_expansion
    (E := K) (fun i => φ (u i)) (fun i => φ (b i)) P
  simp only [Algebra.algebraMap_self, MvPolynomial.map_id] at hexpand
  rw [hexpand]
  simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc

/-- Independent horizontal coefficients admit two original-field linear
functionals with exactly the two normalized horizontal coordinate values. -/
theorem independent_horizontal_coefficients_construct_dual_coordinates
    (u : Fin 2 → E) (hu : LinearIndependent K u) :
    ∃ φ : Fin 2 → E →ₗ[K] K, ∀ i j : Fin 2, φ i (u j) = if j = i then 1 else 0 := by
  classical
  let L := Fintype.linearCombination K u
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hu.fintypeLinearCombination_injective)
  have hgu (j : Fin 2) : g (u j) = Pi.single j 1 := by
    have he := LinearMap.congr_fun hg (Pi.single j 1)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, L,
      Fintype.linearCombination_apply_single, one_smul] using he
  refine ⟨fun i => (LinearMap.proj i).comp g, ?_⟩
  intro i j
  simp [hgu, Pi.single_apply, eq_comm]

/-- A single extension-field tangent identity whose two horizontal
coefficients are independent over the original field constructs both
normalized original-field tangent lifts, without choosing cover points. -/
theorem independent_horizontal_coefficient_tangent_constructs_original_normalized_lifts
    (P : MvPolynomial (Fin 3) K) (u : Fin 2 → E) (hu : LinearIndependent K u)
    (b : Fin 3 → E)
    (hzero : affineProjectedTangentAction u b (MvPolynomial.map (algebraMap K E) P) = 0) :
    ∃ b₀ b₁ : Fin 3 → K, affineTangentLiftX b₀ P = 0 ∧ affineTangentLiftZ b₁ P = 0 := by
  obtain ⟨φ, hφ⟩ := independent_horizontal_coefficients_construct_dual_coordinates u hu
  have h0 := affine_tangent_equation_descends_by_linear_coefficient_functional P u b hzero (φ 0)
  have h1 := affine_tangent_equation_descends_by_linear_coefficient_functional P u b hzero (φ 1)
  refine ⟨fun j => φ 0 (b j), fun j => φ 1 (b j), ?_, ?_⟩
  · simpa [affineProjectedTangentAction, affineTangentLiftX_apply, hφ] using h0
  · simpa [affineProjectedTangentAction, affineTangentLiftZ_apply, hφ] using h1

end DimensionFourDependence
