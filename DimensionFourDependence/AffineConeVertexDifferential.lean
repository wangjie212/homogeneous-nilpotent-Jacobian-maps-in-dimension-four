import DimensionFourDependence.VertexPreservingSourcePartial
import DimensionFourDependence.ChangedGaussVertexDifferential
import DimensionFourDependence.SecondCoordinateAffineChart

/-! # The constructed affine cone parameter has nonzero vertex partial

The original reduced pencil supplies the nonzero rational vertex
partial. It survives the entire changed Gauss cover and original source
coordinate conjugacy. The actual chart chain rule then gives P_w nonzero
and transcendence over the two original transverse affine coordinates.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

section ChainRule

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- The multivariate chain rule for an arbitrary actual ambient field
derivation and a polynomial evaluated at its original coordinate values. -/
theorem derivation_multivariate_aeval_chain_rule
    (D : Derivation K F F) (x : Fin n → F) (P : MvPolynomial (Fin n) K) :
    D (aeval x P) = ∑ i, aeval x (pderiv i P) * D (x i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, ← Finset.sum_add_distrib]
    simp [add_mul]
  | mul_X p k hp =>
    have he : (∑ j, aeval x (pderiv j (p * X k)) * D (x j)) =
        x k * (∑ j, aeval x (pderiv j p) * D (x j)) + aeval x p * D (x k) := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X,
        add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · simp [Pi.single_apply]
    rw [he, map_mul, aeval_X, D.leibniz, hp]
    simp only [smul_eq_mul]
    ring

end ChainRule

variable {K : Type*} [Field K]

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "D₀" => rationalPartial (K := K) (Fin.last 3)
local notation "y₀" => rationalCoordinate (K := K) (1 : Fin 4)
local notation "x₀" => closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))

/-- The actual vertex derivation kills both transverse affine source
ratios, including their full field of rational combinations. -/
theorem second_chart_transverse_coordinate_vertex_partials_zero (i : Fin 2) :
    D₀ ((![rationalCoordinate (K := K) (0 : Fin 4) / y₀,
      rationalCoordinate (K := K) (2 : Fin 4) / y₀] : Fin 2 → S₀) i) = 0 := by
  fin_cases i <;> simp [Derivation.leibniz_div, rationalPartial_coordinate]

/-- The actual rational vertex partial on the source field is 1/y
times the affine w partial of every chart polynomial. -/
theorem second_chart_polynomial_source_vertex_partial
    (P : MvPolynomial (Fin 3) K) :
    D₀ (aeval x₀ P) = aeval x₀ (pderiv (2 : Fin 3) P) / y₀ := by
  have hy : y₀ ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective R₀ S₀).ne (X_ne_zero (1 : Fin 4))
  have h0 : D₀ (rationalCoordinate (K := K) (0 : Fin 4) / y₀) = 0 := by
    simp [Derivation.leibniz_div, rationalPartial_coordinate]
  have h1 : D₀ (rationalCoordinate (K := K) (2 : Fin 4) / y₀) = 0 := by
    simp [Derivation.leibniz_div, rationalPartial_coordinate]
  have h2 : D₀ (rationalCoordinate (K := K) (3 : Fin 4) / y₀) = y₀⁻¹ := by
    simp [Derivation.leibniz_div, rationalPartial_coordinate] <;> field_simp [hy]
  rw [derivation_multivariate_aeval_chain_rule]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change aeval x₀ (pderiv 0 P) * D₀ (rationalCoordinate (K := K) (0 : Fin 4) / y₀) +
      (aeval x₀ (pderiv 1 P) * D₀ (rationalCoordinate (K := K) (2 : Fin 4) / y₀) +
        aeval x₀ (pderiv 2 P) * D₀ (rationalCoordinate (K := K) (3 : Fin 4) / y₀)) = _
  rw [h0, h1, h2, mul_zero, mul_zero, zero_add, zero_add, div_eq_mul_inv]

/-- A nonzero actual source vertex differential forces the constructed
affine parameter polynomial's w partial nonzero. -/
theorem affine_chart_parameter_vertex_partial_ne_zero_of_source_value
    (t : S₀) (P : MvPolynomial (Fin 3) K) (hvalue : t = aeval x₀ P)
    (ht : D₀ t ≠ 0) : pderiv (2 : Fin 3) P ≠ 0 := by
  intro hz
  have he := second_chart_polynomial_source_vertex_partial P
  rw [← hvalue, hz, map_zero, zero_div] at he
  exact ht he

variable [CharZero K]

/-- The actual original reduced pencil constructs nonzero vertex
differentials after both the changed Gauss cover and the constructed
source conjugacy, and hence P_w≠0 and transcendence over K(x/y,z/y). -/
theorem actual_conjugate_gauss_affine_parameter_vertex_differential
    (H : Fin 4 → R₀) (I : ImageRelationWitness H)
    (e₀ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : R₀) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e₀ RatFunc.X =
      algebraMap R₀ S₀ p / algebraMap R₀ S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (T S : Matrix (Fin 3) (Fin 3) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
    (t : S₀) (ht : t = matrixSourceFractionEquiv
      (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
        (closedGaussParameterSourceHom H I e RatFunc.X))
    (P : MvPolynomial (Fin 3) K) (hP : t = aeval x₀ P) :
    D₀ t ≠ 0 ∧ pderiv (2 : Fin 3) P ≠ 0 ∧
      Transcendental (IntermediateField.adjoin K (Set.range
        (![rationalCoordinate (K := K) (0 : Fin 4) / y₀,
          rationalCoordinate (K := K) (2 : Fin 4) / y₀] : Fin 2 → S₀))) t := by
  have hchanged := actual_closed_gauss_changed_parameter_vertex_partial_ne_zero
    H I e₀ e p q hp0 hq0 hrel hp hq hparameter hvertex
  have hnonzero : D₀ t ≠ 0 := by
    rw [ht, vertex_preserving_source_fraction_partial]
    simpa only [map_zero] using (matrixSourceFractionEquiv
      (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST).injective.ne hchanged
  exact ⟨hnonzero, affine_chart_parameter_vertex_partial_ne_zero_of_source_value t P hP hnonzero,
    nonzero_derivation_value_transcendental_over_coordinate_field D₀ _
      second_chart_transverse_coordinate_vertex_partials_zero t hnonzero⟩

end DimensionFourDependence
