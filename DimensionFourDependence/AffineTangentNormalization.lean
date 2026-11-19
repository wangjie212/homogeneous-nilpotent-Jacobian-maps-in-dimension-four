import DimensionFourDependence.AffineTangentCommutator

/-! # Independent projected affine tangent fields construct normalized lifts

The inverse of the actual two-by-two horizontal direction matrix gives
both normalized tangent lifts and their entire affine vertical coefficients.
Only the original two tangent equations and nonzero direction determinant
are supplied; the normalization and annihilation equations are constructed.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The polynomial action of an affine triangular field with its actual
constant horizontal direction and full affine vertical coefficient. -/
noncomputable def affineProjectedTangentAction
    (u : Fin 2 → K) (b : Fin 3 → K) (P : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  C (u 0) * pderiv 0 P + C (u 1) * pderiv 1 P + affineTangentVerticalCoefficient b * pderiv 2 P

/-- The original two affine tangent equations with independent projected
directions construct both normalized original polynomial tangent lifts. -/
theorem independent_projected_affine_tangents_construct_normalized_lifts
    (P : MvPolynomial (Fin 3) K) (u v : Fin 2 → K)
    (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) (l m : Fin 3 → K)
    (hu : affineProjectedTangentAction u l P = 0)
    (hv : affineProjectedTangentAction v m P = 0) :
    ∃ b c : Fin 3 → K, affineTangentLiftX b P = 0 ∧ affineTangentLiftZ c P = 0 := by
  let Δ := u 0 * v 1 - u 1 * v 0
  let b : Fin 3 → K := fun i => (v 1 * l i - u 1 * m i) / Δ
  let c : Fin 3 → K := fun i => (u 0 * m i - v 0 * l i) / Δ
  have hb : affineTangentVerticalCoefficient b = C Δ⁻¹ *
      (C (v 1) * affineTangentVerticalCoefficient l - C (u 1) * affineTangentVerticalCoefficient m) := by
    simp only [affineTangentVerticalCoefficient, b, div_eq_mul_inv, map_mul, map_sub]
    ring
  have hc : affineTangentVerticalCoefficient c = C Δ⁻¹ *
      (C (u 0) * affineTangentVerticalCoefficient m - C (v 0) * affineTangentVerticalCoefficient l) := by
    simp only [affineTangentVerticalCoefficient, c, div_eq_mul_inv, map_mul, map_sub]
    ring
  have hunit : C Δ⁻¹ * C Δ = (1 : MvPolynomial (Fin 3) K) := by
    rw [← map_mul, inv_mul_cancel₀ hdet, map_one]
  dsimp only [Δ] at hunit
  simp only [map_sub, map_mul] at hunit
  dsimp only [affineProjectedTangentAction] at hu hv
  refine ⟨b, c, ?_, ?_⟩
  · rw [affineTangentLiftX_apply, hb]
    linear_combination C Δ⁻¹ * C (v 1) * hu - C Δ⁻¹ * C (u 1) * hv - pderiv 0 P * hunit
  · rw [affineTangentLiftZ_apply, hc]
    linear_combination C Δ⁻¹ * C (u 0) * hv - C Δ⁻¹ * C (v 0) * hu - pderiv 1 P * hunit

end DimensionFourDependence
