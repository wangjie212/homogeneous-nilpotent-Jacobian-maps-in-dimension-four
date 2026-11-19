import DimensionFourDependence.GeometricConstantProjectedDirection
import DimensionFourDependence.PolynomialMapScalarExtension

/-! # The constant-direction exclusion descends to the original base field

The paper permits passage to an algebraically closed coefficient field.
Homogeneity, the nilpotent Jacobian and its rank are preserved by the
actual polynomial coefficient extension. The geometric fixed-direction
exclusion over that field then gives dependence, which descends to the
original field by the checked coefficient-matrix argument.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K B : Type*} [Field K] [CharZero K] [Field B] [IsAlgClosed B] [Algebra K B]
    (H : Fin 4 → MvPolynomial (Fin 4) K)

local notation "HB" => fun i => MvPolynomial.map (algebraMap K B) (H i)

/-- Dependence forced by algebraic projected-direction ratios over
an algebraically closed coefficient extension is dependence over the
original field, with every original map hypothesis transported. -/
theorem original_dependence_of_extended_geometric_algebraic_projected_direction
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E] [Algebra (polynomialOutputField (HB)) E] [Algebra B E]
    [IsScalarTower B (polynomialOutputField (HB)) E]
    [Algebra.IsAlgebraic (polynomialOutputField (HB)) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField (HB)) (rationalCoordinate (K := B) (n := 4)))).minimalPrimes)
    (x A : Fin 3 → E) (t : FractionRing (MvPolynomial (Fin 4) E ⧸ P))
    (hx : ∀ i : Fin 3, primeQuotientCoordinate P i.castSucc =
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (x i) +
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (A i) * t)
    (j : Fin 3) (hj : A j ≠ 0) (halg : ∀ i : Fin 3, IsAlgebraic B (A i / A j))
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : ComponentsDependent H := by
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  have hHB : IsHomogMap (HB) d := fun i => (hH i).map (algebraMap K B)
  have hNB : IsNilpotent (jac (HB)) := by
    rw [jac_map_coefficients]
    exact hN.map (MvPolynomial.map (algebraMap K B)).mapMatrix
  have hrB : polyRank (jac (HB)) = 3 := by
    rw [polyRank_jac_map_coefficients]
    exact hrank
  apply componentsDependent_of_map B H
  exact dependence_of_geometric_algebraic_projected_direction
    (HB) hd hHB hNB hrB E P hP x A t hx j hj halg hline

end DimensionFourDependence
