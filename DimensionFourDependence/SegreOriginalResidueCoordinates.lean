import DimensionFourDependence.SegreOriginalSourceChart

/-! # The original radial chart supplies its own residue coordinates and derivative values -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

/-- A regular realization of the actual first-coordinate inverse
constructs its nonzero residue and the exact residue ruling ratio. -/
theorem segre_original_regular_coordinates_construct_residue_ratios
    {O κ : Type*} [CommRing O] [Field κ]
    (φ : O →+* F₀) (hφ : Function.Injective φ) (σ : O →+* κ)
    (x y z s : O) (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1)
    (hz : φ z = ((X₀) 0)⁻¹) (hs : φ s = (X₀) 1 / (X₀) 0) :
    σ x ≠ 0 ∧ σ z = (σ x)⁻¹ ∧ σ s = σ y / σ x := by
  have hunit : x * z = 1 := by
    apply hφ
    rw [map_mul, map_one, hx, hz, mul_inv_cancel₀ segre_original_source_first_coordinate_ne_zero]
  have hres : σ x * σ z = 1 := by simpa only [map_mul, map_one] using congrArg σ hunit
  have hxκ : σ x ≠ 0 := by
    intro he
    rw [he, zero_mul] at hres
    exact zero_ne_one hres
  have hzκ : σ z = (σ x)⁻¹ := by
    apply mul_left_cancel₀ hxκ
    exact hres.trans (mul_inv_cancel₀ hxκ).symm
  have hratio : x * s = y := by
    apply hφ
    rw [map_mul, hx, hs, hy]
    field_simp [segre_original_source_first_coordinate_ne_zero (K := K)]
  have hresS : σ x * σ s = σ y := by simpa only [map_mul] using congrArg σ hratio
  refine ⟨hxκ, hzκ, ?_⟩
  apply (eq_div_iff hxκ).mpr
  exact (mul_comm _ _).trans hresS

/-- Compatible local and residue derivations retain the actual source
coordinate derivative values. In particular `partial_y x = 0` and
`partial_y y = 1` are derived, not imposed on unrelated residue variables. -/
theorem segre_original_regular_derivations_construct_residue_coordinates
    {O κ : Type*} [CommRing O] [Field κ] [Algebra K O] [Algebra K κ]
    (φ : O →+* F₀) (hφ : Function.Injective φ) (σ : O →+* κ)
    (D : Fin 4 → Derivation K O O)
    (hD : ∀ i v, φ (D i v) = (D₀) i (φ v))
    (Dx Dy : Derivation K κ κ)
    (hDx : ∀ v, Dx (σ v) = σ (D 0 v)) (hDy : ∀ v, Dy (σ v) = σ (D 1 v))
    (x y : O) (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1) :
    Dx (σ x) = 1 ∧ Dx (σ y) = 0 ∧ Dy (σ x) = 0 ∧ Dy (σ y) = 1 := by
  have hxx : D 0 x = 1 := by
    apply hφ
    rw [hD, hx, segre_original_source_chart_derivation_coordinate]
    simp [segreSourceChartMatrix]
  have hxy : D 0 y = 0 := by
    apply hφ
    rw [hD, hy, segre_original_source_chart_derivation_coordinate]
    simp [segreSourceChartMatrix]
  have hyx : D 1 x = 0 := by
    apply hφ
    rw [hD, hx, segre_original_source_chart_derivation_coordinate]
    simp [segreSourceChartMatrix]
  have hyy : D 1 y = 1 := by
    apply hφ
    rw [hD, hy, segre_original_source_chart_derivation_coordinate]
    simp [segreSourceChartMatrix]
  simp only [hDx, hDy, hxx, hxy, hyx, hyy, map_one, map_zero, and_self]

end DimensionFourDependence
