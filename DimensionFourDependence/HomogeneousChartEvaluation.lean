import DimensionFourDependence.ProjectiveChartOverlaps
import DimensionFourDependence.HomogeneousResidueSpecialization
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Actual evaluation of projective homogeneous affine charts

The degree-zero localization at X_a evaluates at the original source
ratios. Its image is exactly their original coefficient subalgebra.
These are the coordinate rings used by Mathlib's actual Proj charts.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "Aₐ" a:max => HomogeneousLocalization.Away 𝒢 (X a)

/-- Evaluation of the actual degree-zero homogeneous localization in
the original source field. -/
noncomputable def homogeneousCoordinateChartEval
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) : Aₐ a →+* F :=
  (Localization.awayLift (aeval x).toRingHom (X a)
    (isUnit_iff_ne_zero.mpr (by change aeval x (X a) ≠ 0; rw [aeval_X]; exact ha))).comp
      (algebraMap (Aₐ a) (Localization.Away (X a : MvPolynomial (Fin 4) C)))

/-- A homogeneous fraction has its original numerator divided by the
actual chart coordinate power. -/
theorem homogeneousCoordinateChartEval_mk
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) (n : ℕ)
    (P : MvPolynomial (Fin 4) C) (hP : P ∈ 𝒢 (n • (1 : ℕ))) :
    homogeneousCoordinateChartEval x a ha
      (Away.mk 𝒢 (isHomogeneous_X (R := C) a) n P hP) = aeval x P / (x a) ^ n := by
  change Localization.awayLift (aeval x).toRingHom (X a)
    (isUnit_iff_ne_zero.mpr (by change aeval x (X a) ≠ 0; rw [aeval_X]; exact ha))
    (Away.mk 𝒢 (isHomogeneous_X (R := C) a) n P hP).val = _
  rw [Away.val_mk]
  have hm := Localization.awayLift_mk (aeval x).toRingHom (X a) P (x a)⁻¹
    (by change aeval x (X a) * (x a)⁻¹ = 1; rw [aeval_X]; exact mul_inv_cancel₀ ha) n
  change Localization.awayLift (aeval x).toRingHom (X a) _
    (Localization.mk P ⟨X a ^ n, n, rfl⟩) = (aeval x) P * ((x a)⁻¹) ^ n at hm
  simpa only [div_eq_mul_inv, inv_pow] using hm

/-- That fraction is also evaluation on the actual normalized source coordinates. -/
theorem homogeneousCoordinateChartEval_mk_normalized
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) (n : ℕ)
    (P : MvPolynomial (Fin 4) C) (hP : P ∈ 𝒢 (n • (1 : ℕ))) :
    homogeneousCoordinateChartEval x a ha
      (Away.mk 𝒢 (isHomogeneous_X (R := C) a) n P hP) =
        aeval (fun i => x i / x a) P := by
  rw [homogeneousCoordinateChartEval_mk]
  have hp : P.IsHomogeneous n := by simpa using hP
  have hs := homogeneous_aeval_scale_indexed P hp x (x a)⁻¹
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hs.symm

/-- Every actual Proj affine coordinate evaluates in the original
ratio-generated source chart algebra. -/
theorem homogeneousCoordinateChartEval_mem
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) (z : Aₐ a) :
    homogeneousCoordinateChartEval x a ha z ∈ projectiveCoordinateChartAlgebra (C := C) x a := by
  obtain ⟨n, P, hP, rfl⟩ := Away.mk_surjective 𝒢 (isHomogeneous_X (R := C) a) z
  rw [homogeneousCoordinateChartEval_mk_normalized]
  change aeval (fun i => x i / x a) P ∈ Algebra.adjoin C (Set.range (fun i => x i / x a))
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨P, rfl⟩

/-- The actual affine-chart evaluation, with its original source chart as codomain. -/
noncomputable def homogeneousCoordinateChartToSource
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) :
    Aₐ a →+* projectiveCoordinateChartAlgebra (C := C) x a :=
  (homogeneousCoordinateChartEval x a ha).codRestrict _ (homogeneousCoordinateChartEval_mem x a ha)

/-- The Proj homogeneous affine chart surjects onto exactly the actual
original-coefficient source chart, with no extra coordinate generators. -/
theorem homogeneousCoordinateChartToSource_surjective
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) :
    Function.Surjective (homogeneousCoordinateChartToSource (C := C) x a ha) := by
  intro z
  have hpre : ∀ y : F, y ∈ projectiveCoordinateChartAlgebra (C := C) x a →
      ∃ w : Aₐ a, homogeneousCoordinateChartEval x a ha w = y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨Away.mk 𝒢 (isHomogeneous_X (R := C) a) 1 (X i) (by simpa using isHomogeneous_X (R := C) i), ?_⟩
      rw [homogeneousCoordinateChartEval_mk]
      simp only [aeval_X, pow_one]
    | algebraMap c =>
      refine ⟨Away.mk 𝒢 (isHomogeneous_X (R := C) a) 0 (MvPolynomial.C c)
        (isHomogeneous_C (Fin 4) c), ?_⟩
      rw [homogeneousCoordinateChartEval_mk]
      simp only [aeval_C, pow_zero, div_one]
    | add y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁⟩ := ih₁
      obtain ⟨w₂, hw₂⟩ := ih₂
      exact ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂]⟩
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁⟩ := ih₁
      obtain ⟨w₂, hw₂⟩ := ih₂
      exact ⟨w₁ * w₂, by rw [map_mul, hw₁, hw₂]⟩
  obtain ⟨w, hw⟩ := hpre z.val z.property
  exact ⟨w, Subtype.ext hw⟩

end DimensionFourDependence
