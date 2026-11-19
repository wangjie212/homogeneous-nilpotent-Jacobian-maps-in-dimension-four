import DimensionFourDependence.TernaryJacobianDerivation

/-! # The first actual affine plane equation of the embedded ternary curve -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1400000

variable {K : Type*} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

noncomputable def ternaryGraphGradient
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w : coefficientField (K := K) Y) (j : Fin 2) : F :=
  (coefficientPartial (K := K) Y hY j w : F)

theorem ternaryGraph_rationalJacobian
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w : coefficientField (K := K) Y) :
    rationalJacobian (![Y 0, Y 1, (w : F)] : Fin 3 → F) =
      ternaryGraphMatrix (ternaryRationalGradient (Y 0)) (ternaryRationalGradient (Y 1))
        (ternaryGraphGradient Y hY w 0) (ternaryGraphGradient Y hY w 1) := by
  funext i j
  fin_cases i
  · rfl
  · rfl
  · change rationalPartial (K := K) j (w : F) =
      ternaryGraphGradient Y hY w 0 * rationalPartial (K := K) j (Y 0) +
      ternaryGraphGradient Y hY w 1 * rationalPartial (K := K) j (Y 1)
    rw [coefficient_chain_rule Y hY, Fin.sum_univ_two]
    simp only [ternaryGraphGradient, mul_comm]

noncomputable def ternaryGraphPlaneValue
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w : coefficientField (K := K) Y) : F :=
  x 2 - ternaryGraphGradient Y hY w 0 * x 0 - ternaryGraphGradient Y hY w 1 * x 1

/-- The nilpotent principal-minor identity places the exact plane
constant in the field of constants of the embedded generic curve. -/
theorem ternaryGraphPlaneValue_mem_coefficientField
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w : coefficientField (K := K) Y)
    (hN : IsNilpotent (rationalJacobian (![Y 0, Y 1, (w : F)] : Fin 3 → F))) :
    ternaryGraphPlaneValue Y hY w ∈ coefficientField (K := K) Y := by
  let D := ternaryJacobianDerivation (K := K) (Y 0) (Y 1)
  let C₀ := ternaryJacobianDirection (Y 0) (Y 1)
  let p := ternaryGraphGradient Y hY w 0
  let q := ternaryGraphGradient Y hY w 1
  have hp : D p = 0 := vertical_derivation_kills_coefficient_field Y D
    (ternaryJacobianDerivation_kills_pair Y) (coefficientPartial Y hY 0 w)
  have hq : D q = 0 := vertical_derivation_kills_coefficient_field Y D
    (ternaryJacobianDerivation_kills_pair Y) (coefficientPartial Y hY 1 w)
  have hx (j : Fin 3) : D (x j) = C₀ j := ternaryJacobianDerivation_apply_coordinate _ _ j
  rw [ternaryGraph_rationalJacobian Y hY w] at hN
  have hcross : C₀ 2 - p * C₀ 0 - q * C₀ 1 = 0 :=
    nilpotent_ternaryGraphMatrix_cross_relation _ _ p q hN
  have hD : D (ternaryGraphPlaneValue Y hY w) = 0 := by
    change D (x 2 - p * x 0 - q * x 1) = 0
    simp only [map_sub, Derivation.leibniz, hp, hq, hx, smul_eq_mul, mul_zero, add_zero]
    exact hcross
  have hmem : ternaryGraphPlaneValue Y hY w ∈ derivationConstants D := hD
  rw [ternaryJacobianDerivation_constants Y hY] at hmem
  exact hmem

end DimensionFourDependence
