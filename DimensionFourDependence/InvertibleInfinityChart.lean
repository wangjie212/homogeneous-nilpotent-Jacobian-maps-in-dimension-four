import DimensionFourDependence.InfinityCoordinateElimination
import DimensionFourDependence.LinearProjectionCoordinateChange
import DimensionFourDependence.ExtendedProjectiveInfinityChart
import DimensionFourDependence.RulingBoundaryBasis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # The constructed infinity chart is an actual graded coordinate equivalence

The nonzero determinant already obtained from the ruling dual produces
an invertible linear polynomial substitution. Its projective coordinates
are the normal and transverse chart variables together with the fixed
boundary direction. Dehomogenizing the substitution recovers the exact
original infinity-chart map, including its entire closure ideal.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {F : Type*} [Field F]

/-- The actual linear equivalence given by the constructed chart matrix. -/
noncomputable def rulingBoundaryLinearEquiv (w z b : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) :=
  (rulingBoundaryCoordinateMatrix w z b).toLinearEquiv'
    (Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet))

/-- This actual linear equivalence retains the specified original columns. -/
theorem rulingBoundaryLinearEquiv_matrix (w z b : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    LinearMap.toMatrix' (rulingBoundaryLinearEquiv w z b hdet).toLinearMap =
      rulingBoundaryCoordinateMatrix w z b := by
  change LinearMap.toMatrix' (Matrix.toLin' (rulingBoundaryCoordinateMatrix w z b)) = _
  exact LinearMap.toMatrix'_toLin' _

/-- The actual invertible homogeneous-coordinate change associated
to the original affine infinity chart b+u w+v z. -/
noncomputable def homogeneousBoundaryChartEquiv (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    MvPolynomial (Fin 3) F ≃ₐ[F] MvPolynomial (Option (Fin 2)) F :=
  (linearPolynomialCoordinateEquiv (rulingBoundaryLinearEquiv w z b hdet)).trans
    (renameEquiv F (finSuccEquiv' (Fin.last 2)))

/-- The forward substitution is precisely the original chart matrix
followed by making its last coordinate the chart coordinate. -/
theorem homogeneousBoundaryChartEquiv_apply (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0)
    (P : MvPolynomial (Fin 3) F) :
    homogeneousBoundaryChartEquiv b w z hdet P =
      rename (finSuccEquiv' (Fin.last 2))
        (linearPolynomialPullback (rulingBoundaryCoordinateMatrix w z b) P) := by
  change rename (finSuccEquiv' (Fin.last 2))
    (linearPolynomialPullback (LinearMap.toMatrix'
      (rulingBoundaryLinearEquiv w z b hdet).toLinearMap) P) = _
  rw [rulingBoundaryLinearEquiv_matrix]

/-- The new homogeneous coordinates give the exact original vector
b t+w u+z v, with t the chart homogenizing coordinate. -/
theorem homogeneousBoundaryChartEquiv_X (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) (i : Fin 3) :
    homogeneousBoundaryChartEquiv b w z hdet (X i) =
      C (b i) * X none + C (w i) * X (some 0) + C (z i) * X (some 1) := by
  have h0 : finSuccEquiv' (Fin.last 2) (0 : Fin 3) = some 0 :=
    finSuccEquiv'_last_apply_castSucc 0
  have h1 : finSuccEquiv' (Fin.last 2) (1 : Fin 3) = some 1 :=
    finSuccEquiv'_last_apply_castSucc 1
  have h2 : finSuccEquiv' (Fin.last 2) (2 : Fin 3) = none := finSuccEquiv'_at _
  rw [homogeneousBoundaryChartEquiv_apply]
  simp only [linearPolynomialPullback, aeval_X, linearPolynomialMap]
  change rename (finSuccEquiv' (Fin.last 2))
    (∑ j : Fin 3, C (rulingBoundaryCoordinateMatrix w z b i j) * X j) = _
  rw [Fin.sum_univ_three]
  simp only [map_add, map_mul, rename_C, rename_X, h0, h1, h2,
    rulingBoundaryCoordinateMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  change C (w i) * X (some 0) + C (z i) * X (some 1) + C (b i) * X none = _
  ring

/-- The actual invertible chart preserves each homogeneous degree. -/
theorem homogeneousBoundaryChartEquiv_homogeneous (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0)
    (P : MvPolynomial (Fin 3) F) {d : ℕ} (hP : P.IsHomogeneous d) :
    (homogeneousBoundaryChartEquiv b w z hdet P).IsHomogeneous d := by
  rw [homogeneousBoundaryChartEquiv_apply]
  exact (linearPolynomialPullback_homogeneous _ P hP).rename_isHomogeneous

/-- The constructed inverse also preserves the actual degree;
surjectivity therefore holds on every homogeneous piece. -/
theorem homogeneousBoundaryChartEquiv_symm_homogeneous (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0)
    (P : MvPolynomial (Option (Fin 2)) F) {d : ℕ} (hP : P.IsHomogeneous d) :
    ((homogeneousBoundaryChartEquiv b w z hdet).symm P).IsHomogeneous d := by
  change (linearPolynomialPullback (LinearMap.toMatrix'
    (rulingBoundaryLinearEquiv w z b hdet).symm.toLinearMap)
    (rename (finSuccEquiv' (Fin.last 2)).symm P)).IsHomogeneous d
  exact linearPolynomialPullback_homogeneous _ _ hP.rename_isHomogeneous

/-- Every target homogeneous form has an actual homogeneous preimage
under the constructed infinity-coordinate equivalence. -/
theorem homogeneousBoundaryChartEquiv_homogeneous_surjective (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) (d : ℕ) :
    Function.Surjective (homogeneousPolynomialAlgebraMap
      (homogeneousBoundaryChartEquiv b w z hdet).toAlgHom
      (fun _ P hP => homogeneousBoundaryChartEquiv_homogeneous b w z hdet P hP) d) := by
  intro P
  refine ⟨⟨(homogeneousBoundaryChartEquiv b w z hdet).symm P,
    homogeneousBoundaryChartEquiv_symm_homogeneous b w z hdet P P.property⟩, ?_⟩
  apply Subtype.ext
  exact (homogeneousBoundaryChartEquiv b w z hdet).apply_symm_apply P

/-- Setting the old infinity coordinate to zero and then using the
constructed homogeneous chart gives exactly the old affine chart
after dehomogenization. -/
theorem homogeneousBoundaryChartEquiv_dehomogenize (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    (projectiveDehomogenize (R := F) (σ := Fin 2)).comp
      ((homogeneousBoundaryChartEquiv b w z hdet).toAlgHom.comp
        (projectiveInfinityCoordinateProjection (F := F) (sigma := Fin 3))) =
      projectiveInfinityChartHom b w z := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | none => simp [projectiveInfinityCoordinateProjection_none, projectiveInfinityChartHom]
  | some i =>
    simp [projectiveInfinityCoordinateProjection_some, homogeneousBoundaryChartEquiv_X,
      projectiveInfinityChartHom, boundaryAffineChartCoordinate,
      projectiveDehomogenize_X_none, projectiveDehomogenize_X_some]

end DimensionFourDependence
