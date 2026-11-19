import DimensionFourDependence.CoefficientIsotropicBasis
import DimensionFourDependence.NormalizedPlaneCoordinates

/-! # Normalizing an isotropic direction modulo the radial direction

Subtract its radial component in one nonzero radial coordinate, then
scale a surviving coordinate to one. Radial Hessian and cubic identities
preserve both conditions (3.4), and mixed pairings remain nonzero.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F] {n : ℕ}

/-- A direction independent of the radial vector has a representative
with one prescribed zero coordinate and another coordinate equal to one. -/
theorem exists_normalized_radial_direction
    (Y Z : Fin n → F) (hYZ : LinearIndependent F ![Y, Z]) (a : Fin n) (hYa : Y a ≠ 0) :
    ∃ (U : Fin n → F) (b : Fin n) (r s : F), s ≠ 0 ∧
      (∀ i, U i = s * (Z i + r * Y i)) ∧ U a = 0 ∧ U b = 1 ∧ b ≠ a := by
  let r : F := -Z a / Y a
  let V : Fin n → F := fun i => Z i + r * Y i
  have hVa : V a = 0 := by
    dsimp only [V, r]
    field_simp [hYa]
    ring
  have hV : V ≠ 0 := by
    intro hv
    have hrel : r • Y + (1 : F) • Z = 0 := by
      funext i
      have he := congrFun hv i
      change Z i + r * Y i = 0 at he
      change r * Y i + 1 * Z i = 0
      linear_combination he
    have he := Fintype.linearIndependent_iff.mp hYZ ![r, 1]
      (by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hrel)
    exact one_ne_zero (he 1)
  obtain ⟨b, hb⟩ : ∃ b, V b ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hV
  refine ⟨(fun i => (V b)⁻¹ * V i), b, r, (V b)⁻¹, inv_ne_zero hb, fun _ => rfl, ?_, ?_, ?_⟩
  · change (V b)⁻¹ * V a = 0
    rw [hVa, mul_zero]
  · exact inv_mul_cancel₀ hb
  · intro he
    exact hb (he ▸ hVa)

/-- Scaling and a radial shift preserve quadratic and cubic isotropy
under the actual Euler radial identities. -/
theorem radial_normalization_preserves_isotropy
    (T : Matrix (Fin n) (Fin n) F) (C : Fin n → Fin n → Fin n → F)
    (hT : ∀ i j, T i j = T j i)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (Y Z U : Fin n → F) (hY : ∀ v, matrixBilinearPairing T Y v = 0)
    (hCY : ∀ v w, tensorTrilinearPairing C Y v w = -matrixBilinearPairing T v w)
    (hZ : matrixBilinearPairing T Z Z = 0) (hCZ : tensorTrilinearPairing C Z Z Z = 0)
    (r s : F) (hU : ∀ i, U i = s * (Z i + r * Y i)) :
    matrixBilinearPairing T U U = 0 ∧ tensorTrilinearPairing C U U U = 0 := by
  have hZY : matrixBilinearPairing T Z Y = 0 :=
    (matrixBilinearPairing_symmetric T hT Z Y).trans (hY Z)
  have hQ : matrixBilinearPairing T (fun i => Z i + r * Y i) (fun i => Z i + r * Y i) = 0 := by
    simp only [matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
      matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right,
      hY, hZY, hZ, mul_zero, add_zero]
  have hC : tensorTrilinearPairing C (fun i => Z i + r * Y i)
      (fun i => Z i + r * Y i) (fun i => Z i + r * Y i) = 0 :=
    (symmetric_cubic_radial_shift T C h12 h23 Y Z hY hCY hZ r).trans hCZ
  rw [funext hU]
  constructor
  · rw [matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right, hQ, mul_zero, mul_zero]
  · rw [tensorTrilinearPairing_scale_left, tensorTrilinearPairing_scale_middle,
      tensorTrilinearPairing_scale_right, hC, mul_zero, mul_zero, mul_zero]

/-- The mixed pairing of two radially shifted, rescaled directions
changes only by their nonzero scaling factors. -/
theorem radial_normalization_mixed_pairing
    (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Y Z W U V : Fin n → F) (hY : ∀ w, matrixBilinearPairing T Y w = 0)
    (r s r' s' : F) (hU : ∀ i, U i = s * (Z i + r * Y i))
    (hV : ∀ i, V i = s' * (W i + r' * Y i)) :
    matrixBilinearPairing T U V = s * s' * matrixBilinearPairing T Z W := by
  have hZY : matrixBilinearPairing T Z Y = 0 :=
    (matrixBilinearPairing_symmetric T hT Z Y).trans (hY Z)
  rw [funext hU, funext hV]
  simp only [matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right,
    matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
    hY, hZY, mul_zero, add_zero]
  ring

end DimensionFourDependence
