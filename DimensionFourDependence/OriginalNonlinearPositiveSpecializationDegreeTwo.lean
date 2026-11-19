import DimensionFourDependence.CharacteristicPencilSpecializedDegreeTwo

/-! # An original nonlinear Gauss-curve map constructs a positive degree-two divisor image -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [kField : Field K] [kCharZero : CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- Finite original Gauss coefficients carry the same root, a
positive generic pencil degree, and an actual root divisor with its
own positive specialized curve degree at most two. -/
noncomputable def ActualFiniteCharacteristicPositiveDegreeTwoSpecializationDataExists : Prop :=
  ∃ (F : Type u) (hF : Field F),
    letI : Field F := hF
    ∃ aCF : Algebra (closedGaussParameterField H I) F,
      letI : Algebra (closedGaussParameterField H I) F := aCF
      ∃ hfin : Module.Finite (closedGaussParameterField H I) F,
        letI : Module.Finite (closedGaussParameterField H I) F := hfin
        letI : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
        ActualCharacteristicGaussPositiveDegreeTwoSpecializationData H I F hH e hd hind hGauss

/-- The given finite positive generic curve data construct the
same root's positive actual source-coordinate divisor degree bound. -/
theorem finite_characteristic_degree_two_data_construct_positive_divisor_specialization
    (hdata : ActualFiniteCharacteristicPencilCurveDegreeTwoDataExists H I hH e hd hind hGauss) :
    ActualFiniteCharacteristicPositiveDegreeTwoSpecializationDataExists H I hH e hd hind hGauss := by
  obtain ⟨F, hF, aCF, hfin, hgeneric⟩ := hdata
  let fieldF : Field F := hF
  let algCF : Algebra (closedGaussParameterField H I) F := aCF
  let finCF : Module.Finite (closedGaussParameterField H I) F := hfin
  let algebraicCF : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
  have hspecial := @actual_degree_two_characteristic_pencil_constructs_positive_divisor_specialization
    K kField kCharZero H I F fieldF algCF algebraicCF d hH e hd hind hGauss finCF hgeneric
  exact ⟨F, fieldF, algCF, finCF, hspecial⟩

omit e in
/-- A specified actual nonlinear geometric generic component of
the original map constructs finite characteristic coefficients and an
actual zero divisor whose original source-coordinate image has positive
curve degree at most two over its constructed coefficient residue field.
No root, divisor, coefficient valuation or curve degree is supplied. -/
theorem original_nonlinear_gauss_curve_map_constructs_positive_degree_two_divisor_specialization
    [IsAlgClosed K] (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I,
      ActualFiniteCharacteristicPositiveDegreeTwoSpecializationDataExists H I hH e hd hind hGauss := by
  obtain ⟨e, hgeneric⟩ := original_nonlinear_gauss_curve_map_constructs_pencil_curve_degree_two
    H I hH hd hind hGauss hN hrank E P hP hline
  exact ⟨e, finite_characteristic_degree_two_data_construct_positive_divisor_specialization
    H I hH e hd hind hGauss hgeneric⟩

end DimensionFourDependence
