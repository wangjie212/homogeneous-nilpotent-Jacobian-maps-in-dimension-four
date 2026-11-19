import DimensionFourDependence.CharacteristicRootOriginalFiberDegree
import DimensionFourDependence.OriginalNonlinearCharacteristicRoot

/-! # A nonlinear original Gauss-curve map constructs full and radial fiber degree bounds -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [kField : Field K] [kCharZero : CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The original map admits an actual independent output chart in
which both its full affine generic fiber and its radial projective
source curve have Hilbert degree at most two. -/
noncomputable def OriginalFullAndRadialFiberDegreeAtMostTwo : Prop :=
  ∃ (p : Equiv.Perm (Fin 4))
    (_hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H (p i.castSucc)))),
    (∀ D : ℕ, HasCurveHilbertDegree (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))) D → D ≤ 2) ∧
    (∀ D : ℕ, HasCurveHilbertDegree (projectiveFieldPointIdeal
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))).toIdeal D → D ≤ 2)

variable (I : ImageRelationWitness H) {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- The finite characteristic coefficients are eliminated while
their field is abstract. The conclusion retains the actual original
fiber coordinate field and requires no fixed source vertex. -/
theorem finite_characteristic_root_data_bound_original_full_and_radial_fibers
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hdata : ActualFiniteCharacteristicGaussRootDataExists H I hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    OriginalFullAndRadialFiberDegreeAtMostTwo H := by
  obtain ⟨F, hF, aCF, hfin, hroot⟩ := hdata
  let fieldF : Field F := hF
  let algCF : Algebra (closedGaussParameterField H I) F := aCF
  let finCF : Module.Finite (closedGaussParameterField H I) F := hfin
  let algebraicCF : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
  have hdegree := @actual_characteristic_root_data_constructs_original_fiber_degree_bounds
    K kField kCharZero H I F fieldF algCF algebraicCF d hH e hd hind hGauss hN hrank hroot
  obtain ⟨p, hY, _h, _hh, hfull, hradial⟩ := hdegree
  exact ⟨p, hY, hfull, hradial⟩

include I hH hd hind hGauss

omit e in
/-- A specified actual nonlinear geometric component forces the
original Gauss-curve map's full and radial generic-fiber degree bounds
by two. All root, coefficient, graph-chart and boundary data are constructed. -/
theorem original_nonlinear_gauss_curve_map_constructs_full_and_radial_fiber_degree_two_bounds
    [IsAlgClosed K] (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    OriginalFullAndRadialFiberDegreeAtMostTwo H := by
  obtain ⟨e, hroot⟩ := original_nonlinear_gauss_curve_map_constructs_characteristic_root_factorization
    H I hH hind hGauss hd hN hrank E P hP hline
  exact finite_characteristic_root_data_bound_original_full_and_radial_fibers
    H I hH e hd hind hGauss hN hrank hroot

end DimensionFourDependence
