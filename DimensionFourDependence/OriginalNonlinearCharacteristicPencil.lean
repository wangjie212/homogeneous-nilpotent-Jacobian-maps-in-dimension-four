import DimensionFourDependence.CharacteristicGaussPencilGeometry
import DimensionFourDependence.OriginalNonlinearCharacteristicRoot

/-! # The original nonlinear map constructs the characteristic pencil and its divisor geometry -/

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

/-- A finite extension of the actual original closed Gauss field
carries the original characteristic pencil, its nonempty root divisor,
and the proved absence of common tangent-plane divisors. -/
noncomputable def ActualFiniteCharacteristicGaussPencilDataExists : Prop :=
  ∃ (F : Type u) (hF : Field F),
    letI : Field F := hF
    ∃ aCF : Algebra (closedGaussParameterField H I) F,
      letI : Algebra (closedGaussParameterField H I) F := aCF
      ∃ hfin : Module.Finite (closedGaussParameterField H I) F,
        letI : Module.Finite (closedGaussParameterField H I) F := hfin
        letI : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
        ActualCharacteristicGaussPencilData H I F hH e hd hind hGauss

/-- The same specified finite original root coefficients construct
the richer actual pencil geometry; no different coefficient action,
zero divisor or root value is chosen. -/
theorem finite_characteristic_root_data_constructs_regular_pencil_geometry
    (hdata : ActualFiniteCharacteristicGaussRootDataExists H I hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    ActualFiniteCharacteristicGaussPencilDataExists H I hH e hd hind hGauss := by
  obtain ⟨F, hF, aCF, hfin, hroot⟩ := hdata
  let fieldF : Field F := hF
  let algCF : Algebra (closedGaussParameterField H I) F := aCF
  let finCF : Module.Finite (closedGaussParameterField H I) F := hfin
  let algebraicCF : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
  have hgeometry := @actual_characteristic_root_data_constructs_regular_pencil_geometry
    K kField kCharZero H I F fieldF algCF algebraicCF finCF d hH e hd hind hGauss hroot
  exact ⟨F, fieldF, algCF, finCF, hgeometry⟩

omit e in
/-- The original nonlinear-map hypotheses now construct the actual
finite characteristic pencil with regular root section, a nonempty root
divisor, no common divisor with the tangent plane, and no root zero
mapping onto an original source divisor. -/
theorem original_nonlinear_gauss_curve_map_constructs_regular_characteristic_pencil_geometry
    [IsAlgClosed K] (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I,
      ActualFiniteCharacteristicGaussPencilDataExists H I hH e hd hind hGauss := by
  obtain ⟨e, hroot⟩ := original_nonlinear_gauss_curve_map_constructs_characteristic_root_factorization
    H I hH hind hGauss hd hN hrank E P hP hline
  exact ⟨e, finite_characteristic_root_data_constructs_regular_pencil_geometry
    H I hH e hd hind hGauss hroot⟩

end DimensionFourDependence
