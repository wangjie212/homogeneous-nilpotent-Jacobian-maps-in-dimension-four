import DimensionFourDependence.GaussImageDimension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-! # Projective ratio fields under invertible constant linear coordinates -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 1500000

universe u v

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Constant linear combinations give no new projective ratios. -/
theorem projectiveRatioField_vecMul_le
    (nu : Fin n → F) (A : Matrix (Fin n) (Fin n) K) (a b : Fin n)
    (ha : nu a ≠ 0) (hb : (nu ᵥ* A.map (algebraMap K F)) b ≠ 0) :
    projectiveRatioField (K := K) (nu ᵥ* A.map (algebraMap K F)) b ≤
      projectiveRatioField (K := K) nu a := by
  let L := projectiveRatioField (K := K) nu a
  have hcoord (i : Fin n) : (nu ᵥ* A.map (algebraMap K F)) i / nu a ∈ L := by
    have he : (nu ᵥ* A.map (algebraMap K F)) i / nu a =
        ∑ j, (nu j / nu a) * algebraMap K F (A j i) := by
      dsimp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    apply L.sum_mem
    intro j _
    exact L.mul_mem (IntermediateField.subset_adjoin K _ ⟨j, rfl⟩) (L.algebraMap_mem _)
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i, rfl⟩
  change (nu ᵥ* A.map (algebraMap K F)) i / (nu ᵥ* A.map (algebraMap K F)) b ∈ L
  have he : (nu ᵥ* A.map (algebraMap K F)) i / (nu ᵥ* A.map (algebraMap K F)) b =
      ((nu ᵥ* A.map (algebraMap K F)) i / nu a) /
        ((nu ᵥ* A.map (algebraMap K F)) b / nu a) := by field_simp [ha, hb]
  rw [he]
  exact L.div_mem (hcoord i) (hcoord b)

/-- Inverse constant coordinate matrices preserve the entire
projective image field, with arbitrary nonzero chart pivots. -/
theorem projectiveRatioField_vecMul_eq
    (nu : Fin n → F) (A B : Matrix (Fin n) (Fin n) K) (hAB : A * B = 1)
    (a b : Fin n) (ha : nu a ≠ 0) (hb : (nu ᵥ* A.map (algebraMap K F)) b ≠ 0) :
    projectiveRatioField (K := K) (nu ᵥ* A.map (algebraMap K F)) b =
      projectiveRatioField (K := K) nu a := by
  have hmap : A.map (algebraMap K F) * B.map (algebraMap K F) = 1 := by
    rw [← Matrix.map_mul, hAB]
    ext i j
    simp [Matrix.one_apply]
  have hrestore : (nu ᵥ* A.map (algebraMap K F)) ᵥ* B.map (algebraMap K F) = nu := by
    rw [Matrix.vecMul_vecMul, hmap, Matrix.vecMul_one]
  apply le_antisymm (projectiveRatioField_vecMul_le nu A a b ha hb)
  have he := projectiveRatioField_vecMul_le (nu ᵥ* A.map (algebraMap K F)) B b a hb
    (by rw [hrestore]; exact ha)
  simpa only [hrestore] using he

variable {G : Type v} [Field G] [Algebra K G]

/-- An actual coefficient embedding carries the full ratio field to
exactly the ratio field of the embedded normal. -/
theorem projectiveRatioField_map (f : F →ₐ[K] G) (nu : Fin n → F) (a : Fin n) :
    (projectiveRatioField (K := K) nu a).map f =
      projectiveRatioField (K := K) (f ∘ nu) a := by
  unfold projectiveRatioField
  rw [IntermediateField.adjoin_map]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  exact map_div₀ f (nu i) (nu a)

/-- The dimension of a projective normal image is preserved by the
same actual coefficient embedding. -/
theorem projectiveRatioField_trdeg_map (f : F →ₐ[K] G) (nu : Fin n → F) (a : Fin n) :
    Algebra.trdeg K (projectiveRatioField (K := K) (f ∘ nu) a) =
      Algebra.trdeg K (projectiveRatioField (K := K) nu a) := by
  have he := (IntermediateField.equivMap (projectiveRatioField (K := K) nu a) f).trdeg_eq
  rw [projectiveRatioField_map] at he
  exact he.symm

end DimensionFourDependence
