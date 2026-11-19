import DimensionFourDependence.ProjectiveOutputField
import DimensionFourDependence.LineChartPivots

/-! # An independent linear pencil recovers exactly its projective output field -/

namespace DimensionFourDependence

universe u v

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {E : Type u} {F : Type v} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- An independent linear pencil with nonzero common scale has a
genuine nonzero output coordinate, over every coefficient extension. -/
theorem independent_linear_pencil_has_nonzero_coordinate
    (V W : Fin n → E) (hVW : LinearIndependent E ![V, W])
    (s t : F) (hs : s ≠ 0) (Y : Fin n → F)
    (hY : ∀ i, Y i = s * (t * algebraMap E F (V i) + algebraMap E F (W i))) :
    ∃ a, Y a ≠ 0 := by
  obtain ⟨i, j, hij⟩ := independent_pair_exists_nonzero_coordinate_minor V W hVW
  have hdet : algebraMap E F (V i) * algebraMap E F (W j) -
      algebraMap E F (V j) * algebraMap E F (W i) ≠ 0 := by
    simpa only [← map_mul, ← map_sub] using (map_ne_zero (algebraMap E F)).mpr hij
  by_contra hn
  push Not at hn
  have he : s * (algebraMap E F (V i) * algebraMap E F (W j) -
      algebraMap E F (V j) * algebraMap E F (W i)) = 0 := by
    calc
      _ = algebraMap E F (V i) * Y j - algebraMap E F (V j) * Y i := by rw [hY i, hY j]; ring
      _ = 0 := by rw [hn i, hn j]; ring
  exact mul_ne_zero hs hdet he

/-- Any nonzero output chart recovers the original pencil parameter
from two original projective coordinate ratios. -/
theorem independent_linear_pencil_parameter_mem_projective_field
    (V W : Fin n → E) (hVW : LinearIndependent E ![V, W])
    (s t : F) (hs : s ≠ 0) (Y : Fin n → F)
    (hY : ∀ i, Y i = s * (t * algebraMap E F (V i) + algebraMap E F (W i)))
    (a : Fin n) (ha : Y a ≠ 0) :
    t ∈ projectiveRatioField (K := E) Y a := by
  let L := projectiveRatioField (K := E) Y a
  obtain ⟨i, j, hij⟩ := independent_pair_exists_nonzero_coordinate_minor V W hVW
  have hdet : algebraMap E F (V i) * algebraMap E F (W j) -
      algebraMap E F (V j) * algebraMap E F (W i) ≠ 0 := by
    simpa only [← map_mul, ← map_sub] using (map_ne_zero (algebraMap E F)).mpr hij
  have hratio (i : Fin n) : Y i / Y a ∈ L := IntermediateField.subset_adjoin E _ ⟨i, rfl⟩
  let B := algebraMap E F (V i) * (Y j / Y a) - algebraMap E F (V j) * (Y i / Y a)
  let A := (Y i / Y a) * algebraMap E F (W j) - (Y j / Y a) * algebraMap E F (W i)
  have hB : B = s * (algebraMap E F (V i) * algebraMap E F (W j) -
      algebraMap E F (V j) * algebraMap E F (W i)) / Y a := by
    dsimp only [B]
    rw [hY i, hY j]
    ring
  have hB0 : B ≠ 0 := hB ▸ div_ne_zero (mul_ne_zero hs hdet) ha
  have hA : A = t * B := by
    dsimp only [A, B]
    rw [hY i, hY j]
    ring
  have hAmem : A ∈ L := L.sub_mem
    (L.mul_mem (hratio i) (L.algebraMap_mem _))
    (L.mul_mem (hratio j) (L.algebraMap_mem _))
  have hBmem : B ∈ L := L.sub_mem
    (L.mul_mem (L.algebraMap_mem _) (hratio j))
    (L.mul_mem (L.algebraMap_mem _) (hratio i))
  have he : t = A / B := by rw [hA, mul_div_cancel_right₀ _ hB0]
  rw [he]
  exact L.div_mem hAmem hBmem

/-- The entire original projective output field is exactly E(t),
independently of the nonzero common scale and chosen output chart. -/
theorem independent_linear_pencil_projective_field_eq_adjoin
    (V W : Fin n → E) (hVW : LinearIndependent E ![V, W])
    (s t : F) (hs : s ≠ 0) (Y : Fin n → F)
    (hY : ∀ i, Y i = s * (t * algebraMap E F (V i) + algebraMap E F (W i)))
    (a : Fin n) (ha : Y a ≠ 0) :
    projectiveRatioField (K := E) Y a = IntermediateField.adjoin E {t} := by
  let J := IntermediateField.adjoin E {t}
  have hJ (i : Fin n) : t * algebraMap E F (V i) + algebraMap E F (W i) ∈ J :=
    J.add_mem (J.mul_mem (IntermediateField.subset_adjoin E {t} rfl) (J.algebraMap_mem _))
      (J.algebraMap_mem _)
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change Y i / Y a ∈ J
    have he : Y i / Y a =
        (t * algebraMap E F (V i) + algebraMap E F (W i)) /
          (t * algebraMap E F (V a) + algebraMap E F (W a)) := by
      rw [hY i, hY a, mul_div_mul_left _ _ hs]
    rw [he]
    exact J.div_mem (hJ i) (hJ a)
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact independent_linear_pencil_parameter_mem_projective_field V W hVW s t hs Y hY a ha

end DimensionFourDependence
