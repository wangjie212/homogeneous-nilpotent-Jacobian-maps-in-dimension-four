import DimensionFourDependence.SourceTranscendence

/-! # The derivation tangent to a generic fiber

This constructs the actual derivation `D_u = u · ∇_X` on the source rational
function field and identifies its constant field in the rank-three setup
of Lemma 2.2, once three independent outputs have been selected.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The rational vector field with coefficient vector `u`. -/
noncomputable def sourceVectorDerivation (u : Fin n → FractionRing (MvPolynomial (Fin n) K)) :
    Derivation K (FractionRing (MvPolynomial (Fin n) K)) (FractionRing (MvPolynomial (Fin n) K)) :=
  ∑ i, u i • rationalPartial (K := K) i

theorem sourceVectorDerivation_apply (u : Fin n → FractionRing (MvPolynomial (Fin n) K))
    (f : FractionRing (MvPolynomial (Fin n) K)) :
    sourceVectorDerivation u f = ∑ i, u i * rationalPartial (K := K) i f := by
  simp [sourceVectorDerivation, Derivation.smul_apply, smul_eq_mul]

theorem sourceVectorDerivation_coordinate (u : Fin n → FractionRing (MvPolynomial (Fin n) K))
    (j : Fin n) : sourceVectorDerivation u (rationalCoordinate (K := K) j) = u j := by
  simp [sourceVectorDerivation_apply, rationalPartial_coordinate]

theorem sourceVectorDerivation_ne_zero (u : Fin n → FractionRing (MvPolynomial (Fin n) K))
    (hu : u ≠ 0) : sourceVectorDerivation u ≠ 0 := by
  intro hD
  apply hu
  funext j
  have h := congrArg (fun D : Derivation K (FractionRing (MvPolynomial (Fin n) K))
    (FractionRing (MvPolynomial (Fin n) K)) => D (rationalCoordinate (K := K) j)) hD
  simpa [sourceVectorDerivation_coordinate] using h

/-- The Jacobian over the rational function field, including rectangular
maps such as the selected three output coordinates. -/
noncomputable def rationalJacobian {m : ℕ}
    (Y : Fin m → FractionRing (MvPolynomial (Fin n) K)) :
    Matrix (Fin m) (Fin n) (FractionRing (MvPolynomial (Fin n) K)) :=
  Matrix.of fun i j => rationalPartial (K := K) j (Y i)

/-- A right-kernel vector of the output Jacobian gives a vertical derivation. -/
theorem sourceVectorDerivation_vertical {m : ℕ}
    (Y : Fin m → FractionRing (MvPolynomial (Fin n) K))
    (u : Fin n → FractionRing (MvPolynomial (Fin n) K))
    (hu : rationalJacobian Y *ᵥ u = 0) (j : Fin m) :
    sourceVectorDerivation u (Y j) = 0 := by
  have h := congrFun hu j
  simp only [Matrix.mulVec, dotProduct, rationalJacobian, Matrix.of_apply, Pi.zero_apply] at h
  rw [sourceVectorDerivation_apply]
  simpa only [mul_comm] using h

/-- On polynomial maps, this is the polynomial Jacobian after embedding
its entries in the source rational function field. -/
theorem rationalJacobian_polynomial {m : ℕ} (H : Fin m → MvPolynomial (Fin n) K) :
    rationalJacobian (fun i => algebraMap (MvPolynomial (Fin n) K) _ (H i)) =
      (Matrix.of fun i j => pderiv j (H i)).map
        (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))) := by
  ext i j
  exact rationalPartial_polynomial j (H i)

/-- The field-theoretic conclusion used in Lemma 2.2 for the actual
nonzero tangent vector and three independent output coordinates. -/
theorem tangent_derivation_constants [CharZero K]
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K))
    (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0) :
    derivationConstants (sourceVectorDerivation u) =
      (coefficientField (K := K) Y).restrictScalars K := by
  exact vertical_constants_rational_four Y hY (sourceVectorDerivation u)
    (sourceVectorDerivation_ne_zero u hu) (sourceVectorDerivation_vertical Y u hker)

end DimensionFourDependence
