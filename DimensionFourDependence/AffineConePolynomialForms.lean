import DimensionFourDependence.SecondCoordinateAffineChart

/-! # The original cone source values give actual affine polynomial identities

Algebraic independence of the three actual chart ratios descends the
complete source-value formulas to identities in K[x,z,w]. Homogeneity
supplies the precise powers of y to cancel, including the fourth mixed
coordinate. No affine coordinate formula is assumed.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))
local notation "y₀" => rationalCoordinate (K := K) (1 : Fin 4)

/-- The source identity F=y^d A(t) constructs the actual affine
polynomial identity F(x,1,z,w)=A(P), for t=P on the chart. -/
theorem cone_scalar_source_value_constructs_affine_polynomial_identity
    (F : R₀) {d : ℕ} (hF : F.IsHomogeneous d)
    (t : S₀) (P : MvPolynomial (Fin 3) K) (A : Polynomial K)
    (ht : t = aeval x₀ P)
    (hvalue : algebraMap R₀ S₀ F = Polynomial.aeval t A * y₀ ^ d) :
    secondCoordinateAffineChart F = Polynomial.aeval P A := by
  have hy : y₀ ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective R₀ S₀).ne (X_ne_zero (1 : Fin 4))
  apply projective_source_chart_evaluation_injective (finSuccEquiv' (1 : Fin 4))
  rw [secondCoordinateAffineChart_homogeneous_source_value F hF, hvalue,
    ← Polynomial.aeval_algHom_apply, ← ht]
  exact mul_div_cancel_right₀ _ (pow_ne_zero d hy)

/-- The full fourth source identity constructs its entire affine
polynomial expression B₁(P)x+B₂(P)+B₃(P)z. -/
theorem cone_mixed_source_value_constructs_affine_polynomial_identity
    (F : R₀) {d : ℕ} (hd : 0 < d) (hF : F.IsHomogeneous d)
    (t : S₀) (P : MvPolynomial (Fin 3) K) (B : Fin 3 → Polynomial K)
    (ht : t = aeval x₀ P)
    (hvalue : algebraMap R₀ S₀ F = y₀ ^ (d - 1) *
      ∑ i : Fin 3, Polynomial.aeval t (B i) * rationalCoordinate (K := K) i.castSucc) :
    secondCoordinateAffineChart F =
      Polynomial.aeval P (B 0) * X 0 + Polynomial.aeval P (B 1) +
        Polynomial.aeval P (B 2) * X 1 := by
  have hy : y₀ ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective R₀ S₀).ne (X_ne_zero (1 : Fin 4))
  have hpow : y₀ ^ d = y₀ ^ (d - 1) * y₀ := by
    rw [← pow_succ]
    congr 1
    omega
  apply projective_source_chart_evaluation_injective (finSuccEquiv' (1 : Fin 4))
  rw [secondCoordinateAffineChart_homogeneous_source_value F hF, hvalue]
  simp only [map_add, map_mul, aeval_X, ← Polynomial.aeval_algHom_apply, ← ht]
  rw [second_coordinate_cone_chart_point, hpow,
    mul_div_mul_left _ _ (pow_ne_zero (d - 1) hy)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (Polynomial.aeval t (B 0) * rationalCoordinate (K := K) (0 : Fin 4) +
      (Polynomial.aeval t (B 1) * y₀ + Polynomial.aeval t (B 2) * rationalCoordinate (K := K) (2 : Fin 4))) / y₀ =
    Polynomial.aeval t (B 0) * (rationalCoordinate (K := K) (0 : Fin 4) / y₀) +
      Polynomial.aeval t (B 1) + Polynomial.aeval t (B 2) * (rationalCoordinate (K := K) (2 : Fin 4) / y₀)
  field_simp [hy] <;> ring

/-- All four original cone source formulas construct the complete
polynomial coordinate identities on the actual affine chart y=1. -/
theorem complete_cone_source_values_construct_affine_polynomial_identities
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (t : S₀) (P : MvPolynomial (Fin 3) K) (A B : Fin 3 → Polynomial K)
    (ht : t = aeval x₀ P)
    (hfirst : ∀ i : Fin 3, algebraMap R₀ S₀ (H i.castSucc) =
      Polynomial.aeval t (A i) * y₀ ^ d)
    (hlast : algebraMap R₀ S₀ (H (Fin.last 3)) = y₀ ^ (d - 1) *
      ∑ i : Fin 3, Polynomial.aeval t (B i) * rationalCoordinate (K := K) i.castSucc) :
    (∀ i : Fin 3, secondCoordinateAffineChart (H i.castSucc) = Polynomial.aeval P (A i)) ∧
    secondCoordinateAffineChart (H (Fin.last 3)) =
      Polynomial.aeval P (B 0) * X 0 + Polynomial.aeval P (B 1) + Polynomial.aeval P (B 2) * X 1 := by
  exact ⟨fun i => cone_scalar_source_value_constructs_affine_polynomial_identity
      (H i.castSucc) (hH i.castSucc) t P (A i) ht (hfirst i),
    cone_mixed_source_value_constructs_affine_polynomial_identity
      (H (Fin.last 3)) hd (hH (Fin.last 3)) t P B ht hlast⟩

end DimensionFourDependence
