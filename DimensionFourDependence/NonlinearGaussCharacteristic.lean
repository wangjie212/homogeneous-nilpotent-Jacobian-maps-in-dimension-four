import DimensionFourDependence.CommonVertexNonlinearExclusion
import DimensionFourDependence.ActualGaussNormalSpan

/-! # A nonlinear Gauss-curve fiber forces the moving characteristic branch -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- A constant relation on the normalized parameter normal is a
relation on the actual original normal, with its original source realization. -/
theorem gauss_parameter_constant_relation_constructs_original_common_vertex
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (v : Fin 4 → K)
    (hv : gaussParameterNormal H I e ⬝ᵥ (fun i => algebraMap K (RatFunc K) (v i)) = 0) :
    rationalImageNormal H I.equation ⬝ᵥ
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)) = 0 := by
  let f := gaussParameterSourceHom H I e
  have he := congrArg f hv
  simp only [dotProduct, map_sum, map_mul, map_zero, f.commutes] at he
  simp only [f, gaussParameterSourceHom_normal, div_mul_eq_mul_div] at he
  rw [← Finset.sum_div] at he
  have hmul := congrArg (fun z => z * rationalImageNormal H I.equation (imageNormalPivot H I)) he
  rw [div_mul_cancel₀ _ (imageNormalPivot_ne_zero H I), zero_mul] at hmul
  exact hmul

variable [IsAlgClosed K]

/-- Nonlinearity excludes the constant-characteristic alternative.
The remaining characteristic has independent tangent, spans the actual
Gauss ruling with that tangent, and has no constant hyperplane relation. -/
theorem nonlinear_geometric_component_constructs_moving_gauss_characteristic
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let w := gaussParameterNormal H I e
      LinearIndependent (RatFunc K) (normalCharacteristicMatrix (rationalParameterDerivative K) w).row ∧
      ∃ b : Fin 4 → RatFunc K, b ≠ 0 ∧
        b ∈ normalCharacteristicSubspace (rationalParameterDerivative K) w ∧
        LinearIndependent (RatFunc K) ![b, fun i => rationalParameterDerivative K (b i)] ∧
        normalRulingSubspace (rationalParameterDerivative K) w =
          Submodule.span (RatFunc K) (Set.range ![b, fun i => rationalParameterDerivative K (b i)]) ∧
        (∀ c : Fin 4 → K, (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) ∧
        LinearIndependent K w ∧
        finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) = 4 := by
  obtain ⟨e, hLI, halt⟩ := actual_gauss_characteristic_alternative_exact_normal_spans
    H (by omega) hH hind I hGauss
  refine ⟨e, hLI, ?_⟩
  rcases halt with ⟨v, hv, hvC, _hspan⟩ | hmoving
  · have hnormal : gaussParameterNormal H I e ⬝ᵥ
        (fun i => algebraMap K (RatFunc K) (v i)) = 0 := congrFun hvC 0
    exact False.elim (original_common_vertex_map_has_no_nonlinear_geometric_component
      H hd hH hN hrank hind I hGauss v hv
      (gauss_parameter_constant_relation_constructs_original_common_vertex H I e v hnormal)
      E P hP hline)
  · exact hmoving

end DimensionFourDependence
