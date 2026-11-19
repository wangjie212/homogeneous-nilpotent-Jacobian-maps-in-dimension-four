import DimensionFourDependence.NilpotentThreeVectorOrbit
import DimensionFourDependence.IndependentVectorCoordinateColumns
import DimensionFourDependence.PolynomialJacobianPointEvaluation
import DimensionFourDependence.QuasiTranslationDependenceDescent

/-! # The actual original map constructs a normalized Jacobian point frame -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A source point with nonzero second nilpotent Jacobian iterate
constructs an actual inverse coordinate pair. Its first three columns
are the point and its two iterates, and the first two Jacobian columns
at the first coordinate point are the next coordinate vectors. -/
theorem nilpotent_jacobian_point_constructs_normalized_three_column_coordinates
    (H : Fin 4 → R₀) (hN : IsNilpotent (jac H))
    (x : Fin 4 → K) (hx : ((jac H).map (aeval x)) ^ 2 *ᵥ x ≠ 0) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K,
      T * S = 1 ∧ S * T = 1 ∧
      (∀ i, T i 0 = x i) ∧
      (∀ i, T i 1 = (((jac H).map (aeval x)) *ᵥ x) i) ∧
      (∀ i, T i 2 = (((jac H).map (aeval x)) ^ 2 *ᵥ x) i) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 0 (linearPolynomialConjugate T S H i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 1 (linearPolynomialConjugate T S H i)) = if i = 2 then 1 else 0) := by
  classical
  let N : Matrix (Fin 4) (Fin 4) K := (jac H).map (aeval x)
  have hnil : IsNilpotent N := hN.map (aeval x).toRingHom.mapMatrix
  have hli := nilpotent_second_iterate_ne_zero_three_vector_orbit_independent N hnil x hx
  let e : Fin 3 ↪ Fin 4 := ⟨Fin.castSucc, Fin.castSucc_injective 3⟩
  obtain ⟨T, S, hTS, hST, hcol⟩ :=
    independent_vector_family_constructs_inverse_coordinate_columns ![x, N *ᵥ x, N ^ 2 *ᵥ x] hli e
  have hc0 (i) : T i 0 = x i := hcol 0 i
  have hc1 (i) : T i 1 = (N *ᵥ x) i := hcol 1 i
  have hc2 (i) : T i 2 = (N ^ 2 *ᵥ x) i := hcol 2 i
  have ht0 : T *ᵥ Pi.single (0 : Fin 4) (1 : K) = x := by
    funext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hc0 i
  have ht1 : T *ᵥ Pi.single (1 : Fin 4) (1 : K) = N *ᵥ x := by
    funext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hc1 i
  have ht2 : T *ᵥ Pi.single (2 : Fin 4) (1 : K) = N ^ 2 *ᵥ x := by
    funext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hc2 i
  have heval : (jac (linearPolynomialConjugate T S H)).map (aeval (Pi.single (0 : Fin 4) (1 : K))) =
      S * N * T := by
    rw [linear_polynomial_conjugate_jacobian_point_value, ht0]
  have hj0 : ((jac (linearPolynomialConjugate T S H)).map (aeval (Pi.single (0 : Fin 4) (1 : K)))) *ᵥ
      Pi.single (0 : Fin 4) (1 : K) = Pi.single (1 : Fin 4) (1 : K) := by
    calc
      _ = S *ᵥ (N *ᵥ (T *ᵥ Pi.single (0 : Fin 4) (1 : K))) := by
        rw [heval, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = S *ᵥ (T *ᵥ Pi.single (1 : Fin 4) (1 : K)) := by rw [ht0, ht1]
      _ = _ := by rw [Matrix.mulVec_mulVec, hST, Matrix.one_mulVec]
  have hj1 : ((jac (linearPolynomialConjugate T S H)).map (aeval (Pi.single (0 : Fin 4) (1 : K)))) *ᵥ
      Pi.single (1 : Fin 4) (1 : K) = Pi.single (2 : Fin 4) (1 : K) := by
    calc
      _ = S *ᵥ (N *ᵥ (T *ᵥ Pi.single (1 : Fin 4) (1 : K))) := by
        rw [heval, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = S *ᵥ (T *ᵥ Pi.single (2 : Fin 4) (1 : K)) := by
        simp only [ht1, ht2, pow_two, ← Matrix.mulVec_mulVec]
      _ = _ := by rw [Matrix.mulVec_mulVec, hST, Matrix.one_mulVec]
  refine ⟨T, S, hTS, hST, hc0, hc1, hc2, ?_, ?_⟩
  · intro i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, jac,
      Matrix.of_apply, Pi.single_apply] using congrFun hj0 i
  · intro i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, jac,
      Matrix.of_apply, Pi.single_apply] using congrFun hj1 i

variable [CharZero K]

/-- Every remaining independent original homogeneous nilpotent map
constructs this normalization over the original characteristic-zero
field. All coordinate data and the witnessing point are derived;
homogeneity, nilpotence and independence survive in those coordinates. -/
theorem original_independent_homogeneous_nilpotent_map_constructs_normalized_point_frame
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K,
      T * S = 1 ∧ S * T = 1 ∧
      IsHomogMap (linearPolynomialConjugate T S H) d ∧
      IsNilpotent (jac (linearPolynomialConjugate T S H)) ∧
      ¬ComponentsDependent (linearPolynomialConjugate T S H) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 0 (linearPolynomialConjugate T S H i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 1 (linearPolynomialConjugate T S H i)) = if i = 2 then 1 else 0) := by
  obtain ⟨x, hx⟩ := nonzero_second_polynomial_jacobian_iterate_constructs_source_point H
    (original_independent_homogeneous_four_variable_squared_jacobian_euler_ne_zero H hd hH hind)
  obtain ⟨T, S, hTS, hST, _hc0, _hc1, _hc2, hj0, hj1⟩ :=
    nilpotent_jacobian_point_constructs_normalized_three_column_coordinates H hN x hx
  exact ⟨T, S, hTS, hST, linearPolynomialConjugate_homogeneous T S H hH,
    linearPolynomialConjugate_nilpotent T S hTS hST H hN,
    linearPolynomialConjugate_componentsIndependent T S hTS hST H hind, hj0, hj1⟩

end DimensionFourDependence
