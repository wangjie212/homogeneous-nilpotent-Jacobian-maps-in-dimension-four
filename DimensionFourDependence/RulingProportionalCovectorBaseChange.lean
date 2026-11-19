import DimensionFourDependence.RulingFormCoordinateSpan

/-! # Proportional ruling covectors retain their zero kernel after coefficient extension -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {m n : ℕ}

/-- Replacing the second independent ruling form by a nonzero
proportional form preserves its independence from the first. -/
theorem independent_ruling_forms_of_nonzero_proportional_second
    (W : Submodule E (Fin n → E)) (M N S : Fin n → E)
    (hMN : LinearIndependent E ![rulingFormRestriction W M, rulingFormRestriction W N])
    (b : E) (hb : b ≠ 0) (hSN : rulingFormRestriction W S = b • rulingFormRestriction W N) :
    LinearIndependent E ![rulingFormRestriction W M, rulingFormRestriction W S] := by
  rw [hSN]
  simpa only [one_smul] using
    (LinearIndependent.pair_smul_smul_iff (isUnit_one : IsUnit (1 : E))
      (isUnit_iff_ne_zero.mpr hb)).mpr hMN

/-- A scalar-extended ruling point killed by a nonzero proportional
power form is killed by the original numerator form. The relation on
all original ruling vectors is transported by the actual matrix kernel. -/
theorem proportional_ruling_covector_zero_after_field_extension
    (A : Matrix (Fin m) (Fin n) E) (S N : Fin n → E)
    (b : E) (hb : b ≠ 0)
    (hSN : rulingFormRestriction (LinearMap.ker A.toLin') S =
      b • rulingFormRestriction (LinearMap.ker A.toLin') N)
    (x : Fin n → F) (hx : A.map (algebraMap E F) *ᵥ x = 0)
    (hS : (fun i => algebraMap E F (S i)) ⬝ᵥ x = 0) :
    (fun i => algebraMap E F (N i)) ⬝ᵥ x = 0 := by
  let B : Matrix (Fin 1) (Fin n) E := fun _ i => S i - b * N i
  have hker : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin' := by
    intro y hy
    have he := LinearMap.congr_fun hSN ⟨y, hy⟩
    change S ⬝ᵥ y = b * (N ⬝ᵥ y) at he
    change B *ᵥ y = 0
    funext j
    change (∑ i, (S i - b * N i) * y i) = 0
    simpa only [dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc] using
      (sub_eq_zero.mpr he : S ⬝ᵥ y - b * (N ⬝ᵥ y) = 0)
  have hBx := matrix_kernel_le_after_scalar_extension (E := F) A B hker
    (show x ∈ LinearMap.ker (A.map (algebraMap E F)).toLin' from hx)
  change B.map (algebraMap E F) *ᵥ x = 0 at hBx
  have he := congrFun hBx (0 : Fin 1)
  have he' : (fun i => algebraMap E F (S i)) ⬝ᵥ x -
      algebraMap E F b * ((fun i => algebraMap E F (N i)) ⬝ᵥ x) = 0 := by
    simpa only [B, Matrix.mulVec, Matrix.map_apply, dotProduct, map_sub, map_mul, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, Pi.zero_apply] using he
  rw [hS, zero_sub, neg_eq_zero] at he'
  exact (mul_eq_zero.mp he').resolve_left ((map_ne_zero (algebraMap E F)).mpr hb)

end DimensionFourDependence
