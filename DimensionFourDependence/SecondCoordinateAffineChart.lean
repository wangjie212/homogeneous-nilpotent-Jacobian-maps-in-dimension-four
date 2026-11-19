import DimensionFourDependence.FixedConeAffineParameter
import DimensionFourDependence.HomogeneousDehomogenize

/-! # The actual affine source chart y=1 and its partial derivatives

The existing original-source dehomogenization is identified with the
explicit substitution (x,1,z,w). Transverse partial derivatives commute
with this substitution. The missing y derivative is recovered from the
original homogeneous Euler identity.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The original second-coordinate chart, with free coordinates x,z,w. -/
noncomputable def secondCoordinateAffineChart :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  projectiveSourceDehomogenize (finSuccEquiv' (1 : Fin 4))

/-- The entire original chart map is the explicit substitution (x,1,z,w). -/
theorem secondCoordinateAffineChart_eq_aeval :
    (secondCoordinateAffineChart (K := K)) = aeval ![X 0, 1, X 1, X 2] := by
  apply MvPolynomial.algHom_ext
  intro i
  have h0 : (finSuccEquiv' (1 : Fin 4)) 0 = some (0 : Fin 3) := by decide
  have h2 : (finSuccEquiv' (1 : Fin 4)) 2 = some (1 : Fin 3) := by decide
  have h3 : (finSuccEquiv' (1 : Fin 4)) 3 = some (2 : Fin 3) := by decide
  fin_cases i <;> simp [secondCoordinateAffineChart, projectiveSourceDehomogenize,
    projectiveDehomogenize, h0, h2, h3]

/-- The chart's complete original-source value is the homogeneous
polynomial divided by the appropriate power of y. -/
theorem secondCoordinateAffineChart_homogeneous_source_value
    (F : MvPolynomial (Fin 4) K) {d : ℕ} (hF : F.IsHomogeneous d) :
    aeval (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4)))
      (secondCoordinateAffineChart F) =
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) F /
          rationalCoordinate (K := K) (1 : Fin 4) ^ d := by
  rw [← projectiveSourceFullChartCoordinateEquiv_source]
  change (projectiveSourceSectionHom (finSuccEquiv' (1 : Fin 4)) F :
    FractionRing (MvPolynomial (Fin 4) K)) = _
  exact projectiveSourceSectionHom_homogeneous_value _ F hF

/-- Equality in the actual y=1 chart determines two original homogeneous
forms of the same degree. -/
theorem secondCoordinateAffineChart_injective_homogeneous
    (F G : MvPolynomial (Fin 4) K) {d : ℕ}
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (h : secondCoordinateAffineChart F = secondCoordinateAffineChart G) : F = G := by
  let s := finSuccEquiv' (1 : Fin 4)
  apply (renameEquiv K s).injective
  apply homogeneous_dehomogenize_injective _ _ hF.rename_isHomogeneous hG.rename_isHomogeneous
  exact h

/-- The actual original x partial commutes with the affine chart. -/
theorem secondCoordinateAffineChart_pderiv_x (F : MvPolynomial (Fin 4) K) :
    pderiv (0 : Fin 3) (secondCoordinateAffineChart F) =
      secondCoordinateAffineChart (pderiv (0 : Fin 4) F) := by
  rw [secondCoordinateAffineChart_eq_aeval, pderiv_aeval]
  simp [Fin.sum_univ_succ, pderiv_X]

/-- The actual original z partial commutes with the affine chart. -/
theorem secondCoordinateAffineChart_pderiv_z (F : MvPolynomial (Fin 4) K) :
    pderiv (1 : Fin 3) (secondCoordinateAffineChart F) =
      secondCoordinateAffineChart (pderiv (2 : Fin 4) F) := by
  rw [secondCoordinateAffineChart_eq_aeval, pderiv_aeval]
  simp [Fin.sum_univ_succ, pderiv_X]

/-- The actual original w partial commutes with the affine chart. -/
theorem secondCoordinateAffineChart_pderiv_w (F : MvPolynomial (Fin 4) K) :
    pderiv (2 : Fin 3) (secondCoordinateAffineChart F) =
      secondCoordinateAffineChart (pderiv (3 : Fin 4) F) := by
  rw [secondCoordinateAffineChart_eq_aeval, pderiv_aeval]
  simp [Fin.sum_univ_succ, pderiv_X]

/-- The missing homogeneous y partial is the original degree times
the chart polynomial minus its affine Euler derivative. -/
theorem secondCoordinateAffineChart_pderiv_y
    (F : MvPolynomial (Fin 4) K) {d : ℕ} (hF : F.IsHomogeneous d) :
    secondCoordinateAffineChart (pderiv (1 : Fin 4) F) =
      (d : MvPolynomial (Fin 3) K) * secondCoordinateAffineChart F -
        (X 0 * pderiv 0 (secondCoordinateAffineChart F) +
          X 1 * pderiv 1 (secondCoordinateAffineChart F) +
          X 2 * pderiv 2 (secondCoordinateAffineChart F)) := by
  have he := congrArg (secondCoordinateAffineChart (K := K)) hF.sum_X_mul_pderiv
  simp only [nsmul_eq_mul, map_sum, map_mul, map_natCast] at he
  have hX (i : Fin 4) : secondCoordinateAffineChart (X i : MvPolynomial (Fin 4) K) =
      (![X 0, 1, X 1, X 2] : Fin 4 → MvPolynomial (Fin 3) K) i := by
    rw [secondCoordinateAffineChart_eq_aeval, aeval_X]
  simp [Fin.sum_univ_succ, hX] at he
  change X 0 * secondCoordinateAffineChart (pderiv (0 : Fin 4) F) +
      (secondCoordinateAffineChart (pderiv (1 : Fin 4) F) +
        (X 1 * secondCoordinateAffineChart (pderiv (2 : Fin 4) F) +
          X 2 * secondCoordinateAffineChart (pderiv (3 : Fin 4) F))) =
      (d : MvPolynomial (Fin 3) K) * secondCoordinateAffineChart F at he
  rw [← secondCoordinateAffineChart_pderiv_x, ← secondCoordinateAffineChart_pderiv_z,
    ← secondCoordinateAffineChart_pderiv_w] at he
  linear_combination he

end DimensionFourDependence
