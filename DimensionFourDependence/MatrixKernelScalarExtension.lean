import DimensionFourDependence.MatrixRankFieldMap

/-! # Kernel inclusions persist through coefficient-field extension

A linear map whose kernel contains another kernel factors through the
other map: descend to its quotient, identify that quotient with its
range, and extend from the range. The resulting matrix factorization
persists after every field extension.
-/

namespace DimensionFourDependence

open Matrix

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {m n r : ℕ}

/-- A kernel inclusion for matrices over a field gives an actual
matrix factorization, with no surjectivity hypothesis. -/
theorem matrix_exists_mul_of_ker_le
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin r) (Fin n) F)
    (h : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin') :
    ∃ T : Matrix (Fin r) (Fin m) F, B = T * A := by
  let q := (LinearMap.ker A.toLin').liftQ B.toLin' h
  let l := q.comp A.toLin'.quotKerEquivRange.symm.toLinearMap
  obtain ⟨t, ht⟩ := l.exists_extend
  have he : t.comp A.toLin' = B.toLin' := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun ht (A.toLin'.rangeRestrict x)
    change t (A.toLin' x) = q (A.toLin'.quotKerEquivRange.symm (A.toLin'.rangeRestrict x)) at hx
    have hre : A.toLin'.quotKerEquivRange.symm (A.toLin'.rangeRestrict x) =
        (LinearMap.ker A.toLin').mkQ x :=
      A.toLin'.quotKerEquivRange.symm_apply_apply ((LinearMap.ker A.toLin').mkQ x)
    rw [hre] at hx
    exact hx
  refine ⟨LinearMap.toMatrix' t, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', he]

/-- Every original-field matrix-kernel inclusion remains true after
an arbitrary coefficient-field extension. -/
theorem matrix_kernel_le_after_scalar_extension
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin r) (Fin n) F)
    (h : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin') :
    LinearMap.ker (A.map (algebraMap F E)).toLin' ≤
      LinearMap.ker (B.map (algebraMap F E)).toLin' := by
  obtain ⟨T, hT⟩ := matrix_exists_mul_of_ker_le A B h
  intro x hx
  change A.map (algebraMap F E) *ᵥ x = 0 at hx
  change B.map (algebraMap F E) *ᵥ x = 0
  rw [hT, Matrix.map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

end DimensionFourDependence
