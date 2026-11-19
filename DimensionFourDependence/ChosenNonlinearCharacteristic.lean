import DimensionFourDependence.NonlinearGaussCharacteristic
import DimensionFourDependence.ExtendedChosenGaussCharacteristic
import DimensionFourDependence.CharacteristicImageDegreeLowerBound

/-! # A nonlinear original fiber gives the characteristic of the actual chosen ruling -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 10000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The nonplanar characteristic can be constructed for the very Gauss
parameter used by the native root construction, with no change of ruling. -/
theorem chosen_nonlinear_geometric_component_constructs_characteristic
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (F : Type u) [Field F] [Algebra (polynomialOutputField H) F] [Algebra K F]
    [IsScalarTower K (polynomialOutputField H) F] [IsAlgClosed F]
    [Algebra.IsAlgebraic (polynomialOutputField H) F]
    (P : Ideal (MvPolynomial (Fin 4) F)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal F (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := F) (primeQuotientCoordinate P)) :
    let e := actualGaussRulingParameterChoice H I hH (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss
    let w := gaussParameterNormal H I e
    ∃ b : Fin 4 → RatFunc K, b ≠ 0 ∧
      b ∈ normalCharacteristicSubspace (rationalParameterDerivative K) w ∧
      LinearIndependent (RatFunc K) ![b, fun i => rationalParameterDerivative K (b i)] ∧
      normalRulingSubspace (rationalParameterDerivative K) w =
        Submodule.span (RatFunc K) (Set.range ![b, fun i => rationalParameterDerivative K (b i)]) ∧
      (∀ c : Fin 4 → K, (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) ∧
      (∀ n : ℕ, 3 * n + 1 ≤ projectiveHilbertFunction
        (projectiveFieldPointIdeal (E := K) b).toIdeal n) := by
  let e := actualGaussRulingParameterChoice H I hH (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss
  have hLI : LinearIndependent (RatFunc K)
      (normalCharacteristicMatrix (rationalParameterDerivative K) (gaussParameterNormal H I e)).row :=
    actualGaussRulingParameterChoice_jet_independent H I hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss
  obtain ⟨b, hb0, hbC, _hbD, halt⟩ :=
    rational_gauss_ruling_constant_vertex_or_characteristic_tangent (gaussParameterNormal H I e) hLI
  rcases halt with ⟨v, hv, _s, _hs, _he, hvC⟩ | ⟨hpair, hspan⟩
  · have hnormal : gaussParameterNormal H I e ⬝ᵥ
        (fun i => algebraMap K (RatFunc K) (v i)) = 0 := congrFun hvC 0
    exact False.elim (original_common_vertex_map_has_no_nonlinear_geometric_component
      H hd hH hN hrank hind I hGauss v hv
      (gauss_parameter_constant_relation_constructs_original_common_vertex H I e v hnormal)
      F P hP hline)
  · have hplane := actual_characteristic_tangent_has_no_constant_hyperplane H
      (Nat.lt_trans Nat.zero_lt_one hd) hH hind I e b hspan
    exact ⟨b, hb0, hbC, hpair, hspan, hplane,
      nonplanar_rational_curve_projective_hilbert_lower_bound b hb0 hplane⟩

end DimensionFourDependence
