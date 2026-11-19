import DimensionFourDependence.BoundaryGaussFieldComparison
import DimensionFourDependence.ActualDevelopableBoundaryEquation

/-! # Actual original-Gauss algebraic boundary directions satisfy (4.3)

The original Gauss-field algebraicity now supplies the closed-parameter
algebraicity used in the checked cubic argument. Projecting a full
four-coordinate boundary lift to its actual first three graph
coordinates preserves every scale and residue equation.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]

/-- The original actual quadratic and cubic equations give zero
acceleration at a full boundary lift whose actual coordinates are
algebraic over the original Gauss field. Ruling membership, constancy
and the closed-parameter algebraicity are derived internally. -/
theorem actual_full_boundary_original_gauss_algebraic_zero_acceleration
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h c q k : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hGauss : gaussImageDimension H I = 1) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h c)
    (hk : (k : FractionRing (MvPolynomial (Fin 4) K)) = thirdFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h c q)
    {O κ : Type u} [CommRing O] [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) O]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra O (FractionRing (MvPolynomial (Fin 4) K))]
    [IsScalarTower (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) O (FractionRing (MvPolynomial (Fin 4) K))]
    [Algebra K κ]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    (π : O →ₐ[coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))] κ)
    (hinj : Function.Injective (algebraMap O (FractionRing (MvPolynomial (Fin 4) K))))
    (s : FractionRing (MvPolynomial (Fin 4) K)) (z : Option (Fin 4) → O)
    (hz0 : algebraMap O (FractionRing (MvPolynomial (Fin 4) K)) (z none) = s)
    (hz : ∀ i, algebraMap O (FractionRing (MvPolynomial (Fin 4) K)) (z (some i)) =
      s * rationalCoordinate (K := K) i) (hres0 : π (z none) = 0)
    (halg : ∀ i, IsAlgebraic (actualBoundaryOriginalGaussField H hrank p hY I κ) (π (z (some i)))) :
    let Y := fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))
    let L := coefficientField (K := K) Y
    let f := closedGaussCoefficientParameterHom H I p hY h hh e
    let A := closedGaussCoefficientGraphSlope H I p hY h hh e
    coordinateEuler (fun i => π (z (some (p i.castSucc)))) (extendedCoefficientPartial Y hY κ)
      (coordinateEuler (fun i => π (z (some (p i.castSucc)))) (extendedCoefficientPartial Y hY κ)
        (algebraMap L κ (parametricRulingDenominator f A (coefficientCoordinate (K := K) Y) * c))) = 0 := by
  let z₃ : Option (Fin 3) → O := fun j => j.elim (z none) (fun i => z (some (p i.castSucc)))
  exact actual_closed_gauss_parameter_algebraic_residue_boundary_zero_acceleration H I p hY h hh e
    hGauss hd hH c q k hq hk κ π hinj s z₃ hz0 (fun i => hz (p i.castSucc)) hres0
    (fun i => actual_boundary_original_gauss_algebraic_implies_closed_parameter_algebraic
      H hrank I p hY h hh e κ _ (halg (p i.castSucc)))

end DimensionFourDependence
