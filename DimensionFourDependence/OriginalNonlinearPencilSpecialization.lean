import DimensionFourDependence.CharacteristicPencilDivisorSpecialization
import DimensionFourDependence.OriginalNonlinearCharacteristicPencil

/-! # The original nonlinear map constructs its characteristic pencil specialization -/

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

/-- Finite original Gauss coefficients carry the actual characteristic
pencil, its coefficient curve, and its internally constructed
algebraic-residue divisor with the coordinate degree comparison. -/
noncomputable def ActualFiniteCharacteristicGaussSpecializationDataExists : Prop :=
  ∃ (F : Type u) (hF : Field F),
    letI : Field F := hF
    ∃ aCF : Algebra (closedGaussParameterField H I) F,
      letI : Algebra (closedGaussParameterField H I) F := aCF
      ∃ hfin : Module.Finite (closedGaussParameterField H I) F,
        letI : Module.Finite (closedGaussParameterField H I) F := hfin
        letI : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
        ActualCharacteristicGaussSpecializationData H I F hH e hd hind hGauss

/-- The given original finite pencil coefficients retain their
source realization and root while constructing all additional
coefficient-curve and divisor-specialization data. -/
theorem finite_characteristic_pencil_geometry_constructs_divisor_specialization
    (hdata : ActualFiniteCharacteristicGaussPencilDataExists H I hH e hd hind hGauss) :
    ActualFiniteCharacteristicGaussSpecializationDataExists H I hH e hd hind hGauss := by
  obtain ⟨F, hF, aCF, hfin, hpencil⟩ := hdata
  let fieldF : Field F := hF
  let algCF : Algebra (closedGaussParameterField H I) F := aCF
  let finCF : Module.Finite (closedGaussParameterField H I) F := hfin
  let algebraicCF : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
  have hspecialization := @actual_characteristic_pencil_geometry_constructs_divisor_specialization
    K kField kCharZero H I F fieldF algCF algebraicCF d hH e finCF hd hind hGauss hpencil
  exact ⟨F, fieldF, algCF, finCF, hspecialization⟩

omit e in
/-- The original nonlinear geometric component constructs the
transcendental characteristic pencil, actual relatively closed
coefficient curve, and an actual divisor with algebraic coefficient
residue and the original-coordinate specialization comparison. -/
theorem original_nonlinear_gauss_curve_map_constructs_characteristic_pencil_specialization
    [IsAlgClosed K] (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I,
      ActualFiniteCharacteristicGaussSpecializationDataExists H I hH e hd hind hGauss := by
  obtain ⟨e, hpencil⟩ := original_nonlinear_gauss_curve_map_constructs_regular_characteristic_pencil_geometry
    H I hH hd hind hGauss hN hrank E P hP hline
  exact ⟨e, finite_characteristic_pencil_geometry_constructs_divisor_specialization
    H I hH e hd hind hGauss hpencil⟩

end DimensionFourDependence
