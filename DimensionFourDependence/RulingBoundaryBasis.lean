import DimensionFourDependence.RulingCoordinateBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Constructing an invertible infinity-chart basis from the actual ruling dual

A nonzero normal supplies a normal vector with pairing one. Two
vectors dual to the ruling forms are independent inside its kernel.
The normal vector, transverse ruling vector, and fixed-root vector
therefore form an actual invertible three-coordinate matrix.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F]

/-- The original-coordinate columns of the chart, ordered as normal,
transverse ruling, and fixed-root directions. -/
noncomputable def rulingBoundaryCoordinateMatrix (w z b : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => ![w, z, b] j i

/-- A nonzero normal constructs its own normalized normal vector. -/
theorem exists_normal_pairing_one (a : Fin 3 → F) (ha : a ≠ 0) :
    ∃ w : Fin 3 → F, a ⬝ᵥ w = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using ha
  refine ⟨Pi.single i (a i)⁻¹, ?_⟩
  rw [dotProduct_single, mul_inv_cancel₀ hi]

/-- The exact normal and dual pairings force independence of the
three actual chart vectors. -/
theorem ruling_boundary_triple_independent
    (a m s w z b : Fin 3 → F)
    (haw : a ⬝ᵥ w = 1) (haz : a ⬝ᵥ z = 0) (hab : a ⬝ᵥ b = 0)
    (hmz : m ⬝ᵥ z = 0) (hmb : m ⬝ᵥ b = 1)
    (hsz : s ⬝ᵥ z = 1) (hsb : s ⬝ᵥ b = 0) : LinearIndependent F ![w, z, b] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have he : g 0 • w + g 1 • z + g 2 • b = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hg
  have ha := congrArg (fun v => a ⬝ᵥ v) he
  have hg0 : g 0 = 0 := by
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, haw, haz, hab,
      mul_one, mul_zero, add_zero, dotProduct_zero] using ha
  simp only [hg0, zero_smul, zero_add] at he
  have hm := congrArg (fun v => m ⬝ᵥ v) he
  have hg2 : g 2 = 0 := by
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hmz, hmb,
      mul_one, mul_zero, zero_add, dotProduct_zero] using hm
  have hs := congrArg (fun v => s ⬝ᵥ v) he
  have hg1 : g 1 = 0 := by
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hsz, hsb,
      mul_one, mul_zero, add_zero, dotProduct_zero] using hs
  fin_cases i <;> assumption

/-- The original column matrix of the three chart vectors has
nonzero determinant, so the chart is an actual coordinate change. -/
theorem rulingBoundaryCoordinateMatrix_det_ne_zero
    (a m s w z b : Fin 3 → F)
    (haw : a ⬝ᵥ w = 1) (haz : a ⬝ᵥ z = 0) (hab : a ⬝ᵥ b = 0)
    (hmz : m ⬝ᵥ z = 0) (hmb : m ⬝ᵥ b = 1)
    (hsz : s ⬝ᵥ z = 1) (hsb : s ⬝ᵥ b = 0) :
    (rulingBoundaryCoordinateMatrix w z b).det ≠ 0 := by
  have hcol : LinearIndependent F (rulingBoundaryCoordinateMatrix w z b).col :=
    ruling_boundary_triple_independent a m s w z b haw haz hab hmz hmb hsz hsb
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcol))

/-- The original normal and the ruling dual construct an invertible
chart with the original nonzero normal pairing normalized to one. -/
theorem exists_ruling_boundary_coordinate_matrix
    (a m s z b : Fin 3 → F) (ha : a ≠ 0)
    (haz : a ⬝ᵥ z = 0) (hab : a ⬝ᵥ b = 0)
    (hmz : m ⬝ᵥ z = 0) (hmb : m ⬝ᵥ b = 1)
    (hsz : s ⬝ᵥ z = 1) (hsb : s ⬝ᵥ b = 0) :
    ∃ w : Fin 3 → F, a ⬝ᵥ w = 1 ∧ (rulingBoundaryCoordinateMatrix w z b).det ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_normal_pairing_one a ha
  exact ⟨w, hw, rulingBoundaryCoordinateMatrix_det_ne_zero a m s w z b hw haz hab hmz hmb hsz hsb⟩

variable {E : Type*} [Field E] [Algebra F E]

/-- The specified coefficient extension preserves the actual chart matrix. -/
theorem rulingBoundaryCoordinateMatrix_map (w z b : Fin 3 → F) :
    (rulingBoundaryCoordinateMatrix w z b).map (algebraMap F E) =
      rulingBoundaryCoordinateMatrix (fun i => algebraMap F E (w i))
        (fun i => algebraMap F E (z i)) (fun i => algebraMap F E (b i)) := by
  ext i j
  fin_cases j <;> rfl

/-- The actual invertible chart stays invertible after the given
coefficient-field extension. -/
theorem rulingBoundaryCoordinateMatrix_map_det_ne_zero (w z b : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    (rulingBoundaryCoordinateMatrix (fun i => algebraMap F E (w i))
      (fun i => algebraMap F E (z i)) (fun i => algebraMap F E (b i))).det ≠ 0 := by
  rw [← rulingBoundaryCoordinateMatrix_map]
  change ((algebraMap F E).mapMatrix (rulingBoundaryCoordinateMatrix w z b)).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (algebraMap F E)).mpr hdet

end DimensionFourDependence
