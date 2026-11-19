import DimensionFourDependence.AffineConeTrace
import DimensionFourDependence.ConeRankOneTraceElimination

/-! # The actual cone Jacobian on the affine chart

All four columns of the original Jacobian are reconstructed from the
affine cone formulas. Homogeneous Euler supplies the omitted radial
column. This identifies the actual coefficient-mapped nilpotent Jacobian
with the rank-one cone matrix used in the trace elimination.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The full homogeneous Jacobian reconstructed from its affine chart
coordinate polynomials, with Euler supplying its y column. -/
noncomputable def homogeneousAffineChartJacobian (d : ℕ)
    (F : Fin 4 → MvPolynomial (Fin 3) K) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) K) :=
  fun i => ![pderiv 0 (F i), (d : MvPolynomial (Fin 3) K) * F i -
    (X 0 * pderiv 0 (F i) + X 1 * pderiv 1 (F i) + X 2 * pderiv 2 (F i)),
    pderiv 1 (F i), pderiv 2 (F i)]

/-- The original homogeneous Jacobian maps to the complete Euler
reconstruction on the actual second-coordinate affine chart. -/
theorem secondCoordinateAffineChart_jacobian_matrix
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d) :
    (jac H).map secondCoordinateAffineChart =
      homogeneousAffineChartJacobian d (fun i => secondCoordinateAffineChart (H i)) := by
  apply Matrix.ext
  intro i j
  change secondCoordinateAffineChart (pderiv j (H i)) =
    homogeneousAffineChartJacobian d (fun i => secondCoordinateAffineChart (H i)) i j
  fin_cases j
  · exact (secondCoordinateAffineChart_pderiv_x _).symm
  · exact secondCoordinateAffineChart_pderiv_y _ (hH i)
  · exact (secondCoordinateAffineChart_pderiv_z _).symm
  · exact (secondCoordinateAffineChart_pderiv_w _).symm

/-- The actual affine parameter gradient in all four homogeneous
source directions, including its degree-zero radial Euler value. -/
noncomputable def affineConeParameterGradient (P : MvPolynomial (Fin 3) K) :
    Fin 4 → MvPolynomial (Fin 3) K :=
  ![pderiv 0 P, -(X 0 * pderiv 0 P + X 1 * pderiv 1 P + X 2 * pderiv 2 P),
    pderiv 1 P, pderiv 2 P]

/-- The entire fourth affine cone coordinate in the original variables. -/
noncomputable def affineConeMixedPolynomial (P : MvPolynomial (Fin 3) K)
    (B : Fin 3 → Polynomial K) : MvPolynomial (Fin 3) K :=
  Polynomial.aeval P (B 0) * X 0 + Polynomial.aeval P (B 1) + Polynomial.aeval P (B 2) * X 1

/-- The rank-one cone matrix with every coefficient specialized to the
actual original affine polynomial parameter. -/
noncomputable def affineConeJacobianMatrix (d : ℕ) (P : MvPolynomial (Fin 3) K)
    (A B : Fin 3 → Polynomial K) : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) K) :=
  coneRankOneChartMatrix (d : MvPolynomial (Fin 3) K)
    (fun i => Polynomial.aeval P (A i)) (fun i => Polynomial.aeval P (A i).derivative)
    (fun i => Polynomial.aeval P (B i)) (affineConeMixedPolynomial P B)
    (affineConeMixedPolynomial P (fun i => (B i).derivative)) (affineConeParameterGradient P)

/-- The four complete affine cone identities construct the entire
original Jacobian matrix on y=1, rather than only its trace. -/
theorem actual_cone_affine_polynomial_forms_construct_jacobian_matrix
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (P : MvPolynomial (Fin 3) K) (A B : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, secondCoordinateAffineChart (H i.castSucc) = Polynomial.aeval P (A i))
    (hlast : secondCoordinateAffineChart (H (Fin.last 3)) = affineConeMixedPolynomial P B) :
    (jac H).map secondCoordinateAffineChart = affineConeJacobianMatrix d P A B := by
  rw [secondCoordinateAffineChart_jacobian_matrix H hH]
  have h0 : secondCoordinateAffineChart (H 0) = Polynomial.aeval P (A 0) := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) by decide] using hfirst 0
  have h1 : secondCoordinateAffineChart (H 1) = Polynomial.aeval P (A 1) := by
    simpa only [show (1 : Fin 3).castSucc = (1 : Fin 4) by decide] using hfirst 1
  have h2 : secondCoordinateAffineChart (H 2) = Polynomial.aeval P (A 2) := by
    simpa only [show (2 : Fin 3).castSucc = (2 : Fin 4) by decide] using hfirst 2
  have h3 : secondCoordinateAffineChart (H 3) = affineConeMixedPolynomial P B := by
    simpa only [show Fin.last 3 = (3 : Fin 4) by decide] using hlast
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [homogeneousAffineChartJacobian, affineConeJacobianMatrix, coneRankOneChartMatrix,
      affineConeMixedPolynomial, affineConeParameterGradient, h0, h1, h2, h3,
      affine_partial_polynomial_parameter_chain_rule, Derivation.leibniz, smul_eq_mul] <;> ring

/-- The constructed full affine cone matrix inherits actual
nilpotence from the original four-variable Jacobian. -/
theorem actual_nilpotent_cone_affine_jacobian_matrix
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (P : MvPolynomial (Fin 3) K) (A B : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, secondCoordinateAffineChart (H i.castSucc) = Polynomial.aeval P (A i))
    (hlast : secondCoordinateAffineChart (H (Fin.last 3)) = affineConeMixedPolynomial P B) :
    IsNilpotent (affineConeJacobianMatrix d P A B) := by
  rw [← actual_cone_affine_polynomial_forms_construct_jacobian_matrix H hH P A B hfirst hlast]
  exact hN.map (secondCoordinateAffineChart (K := K)).toRingHom.mapMatrix

end DimensionFourDependence
