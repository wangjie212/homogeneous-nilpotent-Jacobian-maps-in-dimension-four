import DimensionFourDependence.CharacteristicPencilDegreeTwo
import DimensionFourDependence.OriginalNonlinearCharacteristicRoot

/-! # The original nonlinear map constructs its own degree-two characteristic pencil curve -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [kField : Field K] [kCharZero : CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- The original Gauss coefficients carry a nonzero characteristic
root and its exact pencil curve with positive Hilbert degree at most two. -/
noncomputable def ActualCharacteristicGaussPencilCurveDegreeTwoData
    (F : Type u) [Field F] [Algebra (closedGaussParameterField H I) F]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) F] : Prop :=
  let N := extendedClosedGaussNormalizationScheme H I F hH e
  letI : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I F hH e
  letI : Algebra F N.functionField := extendedClosedGaussOwnFunctionFieldAlgebra H I F hH e
  let w := extendedClosedGaussNormalizationHyperplaneWeight H I F hH e
  ∃ (cS cN : Fin 4 → F) (r : N.functionField), cS ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧
    r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I F cS) ∧
    CharacteristicNativeRulingRootFactorization H I F hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r ∧
    HasActualGaussRootNumerator H I F e cN ∧
    ∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree
      (projectiveFieldPointIdeal (E := pencilCoefficientCurveField (E := F)
        (nativeCharacteristicPencilValue H I F hH e
          (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)) w).toIdeal D

/-- A finite actual Gauss coefficient extension supplies its own
root, full relatively closed pencil coefficients and positive degree. -/
noncomputable def ActualFiniteCharacteristicPencilCurveDegreeTwoDataExists : Prop :=
  ∃ (F : Type u) (hF : Field F),
    letI : Field F := hF
    ∃ aCF : Algebra (closedGaussParameterField H I) F,
      letI : Algebra (closedGaussParameterField H I) F := aCF
      ∃ hfin : Module.Finite (closedGaussParameterField H I) F,
        letI : Module.Finite (closedGaussParameterField H I) F := hfin
        letI : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
        ActualCharacteristicGaussPencilCurveDegreeTwoData H I hH e hd hind hGauss F

/-- Finite actual root data construct the exact generic pencil
curve's positive degree bound, rather than a bound conditional on degree existence. -/
theorem finite_characteristic_root_data_constructs_pencil_curve_degree_two
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hdata : ActualFiniteCharacteristicGaussRootDataExists H I hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    ActualFiniteCharacteristicPencilCurveDegreeTwoDataExists H I hH e hd hind hGauss := by
  obtain ⟨F, hF, aCF, hfin, hroot⟩ := hdata
  let fieldF : Field F := hF
  let algCF : Algebra (closedGaussParameterField H I) F := aCF
  let finCF : Module.Finite (closedGaussParameterField H I) F := hfin
  let algebraicCF : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
  have hdegree := @actual_characteristic_root_data_constructs_pencil_curve_degree_two
    K kField kCharZero H I F fieldF algCF algebraicCF d hH e hind hGauss finCF hd hN hrank hroot
  exact ⟨F, fieldF, algCF, finCF, hdegree⟩

omit e in
/-- An actual nonlinear geometric generic component forces the
original nilpotent Gauss-curve map to construct a characteristic pencil
whose own relatively closed generic curve has positive degree at most two.
No finite coefficients, pencil data, curve degree or comparison is supplied. -/
theorem original_nonlinear_gauss_curve_map_constructs_pencil_curve_degree_two
    [IsAlgClosed K] (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I,
      ActualFiniteCharacteristicPencilCurveDegreeTwoDataExists H I hH e hd hind hGauss := by
  obtain ⟨e, hroot⟩ := original_nonlinear_gauss_curve_map_constructs_characteristic_root_factorization
    H I hH hind hGauss hd hN hrank E P hP hline
  exact ⟨e, finite_characteristic_root_data_constructs_pencil_curve_degree_two
    H I hH e hd hind hGauss hN hrank hroot⟩

end DimensionFourDependence
