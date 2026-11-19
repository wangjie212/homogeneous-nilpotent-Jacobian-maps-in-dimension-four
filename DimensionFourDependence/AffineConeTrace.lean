import DimensionFourDependence.AffineConePolynomialForms

/-! # The original nilpotent trace on the affine cone chart

The original homogeneous Euler identity recovers the y derivative omitted
by the affine chart. Substituting the constructed four affine coordinate
identities into the actual zero trace gives the complete polynomial
constraint in the still-unidentified affine parameter P(x,z,w).
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The trace polynomial on y=1 before identifying the parameter P.
The free affine variables are x,z,w, in that order. -/
noncomputable def affineConeTracePolynomial (d : ℕ) (P : MvPolynomial (Fin 3) K)
    (A B : Fin 3 → Polynomial K) : MvPolynomial (Fin 3) K :=
  (d : MvPolynomial (Fin 3) K) * Polynomial.aeval P (A 1) -
    (X 0 * pderiv 0 P + X 1 * pderiv 1 P + X 2 * pderiv 2 P) *
      Polynomial.aeval P (A 1).derivative +
    Polynomial.aeval P (A 0).derivative * pderiv 0 P +
    Polynomial.aeval P (A 2).derivative * pderiv 1 P +
    (Polynomial.aeval P (B 0).derivative * X 0 + Polynomial.aeval P (B 1).derivative +
      Polynomial.aeval P (B 2).derivative * X 1) * pderiv 2 P

/-- The univariate parameter chain rule for every actual affine partial. -/
theorem affine_partial_polynomial_parameter_chain_rule
    (i : Fin 3) (P : MvPolynomial (Fin 3) K) (A : Polynomial K) :
    pderiv i (Polynomial.aeval P A) = Polynomial.aeval P A.derivative * pderiv i P := by
  simpa only [smul_eq_mul, mul_comm] using (pderiv (R := K) i).map_aeval A P

/-- The full original trace after dehomogenizing, including the y row
reconstructed from the original homogeneous degree. -/
theorem secondCoordinateAffineChart_trace_jacobian
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d) :
    secondCoordinateAffineChart (Matrix.trace (jac H)) =
      pderiv 0 (secondCoordinateAffineChart (H 0)) +
        ((d : MvPolynomial (Fin 3) K) * secondCoordinateAffineChart (H 1) -
          (X 0 * pderiv 0 (secondCoordinateAffineChart (H 1)) +
            X 1 * pderiv 1 (secondCoordinateAffineChart (H 1)) +
            X 2 * pderiv 2 (secondCoordinateAffineChart (H 1)))) +
        pderiv 1 (secondCoordinateAffineChart (H 2)) +
        pderiv 2 (secondCoordinateAffineChart (H 3)) := by
  simp only [Matrix.trace, Matrix.diag, jac, Matrix.of_apply, map_sum, map_add, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero]
  change secondCoordinateAffineChart (pderiv (0 : Fin 4) (H 0)) +
      (secondCoordinateAffineChart (pderiv (1 : Fin 4) (H 1)) +
        (secondCoordinateAffineChart (pderiv (2 : Fin 4) (H 2)) +
          secondCoordinateAffineChart (pderiv (3 : Fin 4) (H 3)))) = _
  rw [← secondCoordinateAffineChart_pderiv_x, secondCoordinateAffineChart_pderiv_y (H 1) (hH 1),
    ← secondCoordinateAffineChart_pderiv_z, ← secondCoordinateAffineChart_pderiv_w]
  ring

/-- The actual original nilpotent Jacobian forces the full affine cone
trace polynomial to vanish after constructing its four chart identities. -/
theorem nilpotent_cone_affine_polynomial_forms_trace_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (P : MvPolynomial (Fin 3) K)
    (A B : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, secondCoordinateAffineChart (H i.castSucc) = Polynomial.aeval P (A i))
    (hlast : secondCoordinateAffineChart (H (Fin.last 3)) =
      Polynomial.aeval P (B 0) * X 0 + Polynomial.aeval P (B 1) + Polynomial.aeval P (B 2) * X 1) :
    affineConeTracePolynomial d P A B = 0 := by
  have h0 : secondCoordinateAffineChart (H 0) = Polynomial.aeval P (A 0) := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) by decide] using hfirst 0
  have h1 : secondCoordinateAffineChart (H 1) = Polynomial.aeval P (A 1) := by
    simpa only [show (1 : Fin 3).castSucc = (1 : Fin 4) by decide] using hfirst 1
  have h2 : secondCoordinateAffineChart (H 2) = Polynomial.aeval P (A 2) := by
    simpa only [show (2 : Fin 3).castSucc = (2 : Fin 4) by decide] using hfirst 2
  have h3 : secondCoordinateAffineChart (H 3) =
      Polynomial.aeval P (B 0) * X 0 + Polynomial.aeval P (B 1) + Polynomial.aeval P (B 2) * X 1 := by
    simpa only [show Fin.last 3 = (3 : Fin 4) by decide] using hlast
  have ht := secondCoordinateAffineChart_trace_jacobian H hH
  rw [trace_jac_zero H hN, map_zero, h0, h1, h2, h3] at ht
  simp [affine_partial_polynomial_parameter_chain_rule, Derivation.leibniz, smul_eq_mul] at ht
  dsimp only [affineConeTracePolynomial]
  linear_combination -ht

/-- The actual four original source identities alone construct the
affine polynomial formulas and their nilpotent trace constraint. -/
theorem nilpotent_cone_source_values_construct_affine_trace_constraint
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H))
    (t : FractionRing (MvPolynomial (Fin 4) K)) (P : MvPolynomial (Fin 3) K)
    (A B : Fin 3 → Polynomial K)
    (ht : t = aeval (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))) P)
    (hfirst : ∀ i : Fin 3, algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H i.castSucc) = Polynomial.aeval t (A i) * rationalCoordinate (K := K) (1 : Fin 4) ^ d)
    (hlast : algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (Fin.last 3)) = rationalCoordinate (K := K) (1 : Fin 4) ^ (d - 1) *
        ∑ i : Fin 3, Polynomial.aeval t (B i) * rationalCoordinate (K := K) i.castSucc) :
    affineConeTracePolynomial d P A B = 0 := by
  obtain ⟨hf, hl⟩ := complete_cone_source_values_construct_affine_polynomial_identities
    H hd hH t P A B ht hfirst hlast
  exact nilpotent_cone_affine_polynomial_forms_trace_zero H hH hN P A B hf hl

end DimensionFourDependence
