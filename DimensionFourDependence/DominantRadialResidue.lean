import DimensionFourDependence.RadialValuationExclusion
import DimensionFourDependence.QuadraticPoleOrders

/-! # A strictly dominant radial coordinate gives the forbidden residue direction

The integral normalized tuple is constructed directly from a radial term
plus strictly smaller errors. This is the residue step in the pole argument.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- Normalize a radial term plus smaller errors. The residue of the
homogenizing coordinate is zero and the affine residue is exactly `Y`. -/
theorem dominant_radial_term_has_radial_residue
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]
    (x error : Fin n → F) (Y : Fin n → E) (τ : F)
    (hτ : 1 < V.valuation τ) (herr : ∀ i, V.valuation (error i) < V.valuation τ)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + error i) :
    ∃ z : Option (Fin n) → V,
      (∀ j, algebraMap V F (z j) = τ⁻¹ * j.elim 1 x) ∧
      (∀ j, IsLocalRing.residue V (z j) =
        algebraMap E (IsLocalRing.ResidueField V) (j.elim 0 Y)) := by
  have hτ0 : τ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hτ
    exact (not_lt_of_ge zero_le_one) hτ
  have hnot : τ ∉ V := fun h => (not_le_of_gt hτ) ((V.valuation_le_one_iff _).mpr h)
  have hinv : τ⁻¹ ∈ V := (V.mem_or_inv_mem τ).resolve_left hnot
  let b : V := ⟨τ⁻¹, hinv⟩
  have hb : IsLocalRing.residue V b = 0 := by
    apply (valuation_residue_zero_iff V b).mpr
    change V.valuation (τ⁻¹) < 1
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hτ
  have hsmall (i : Fin n) : V.valuation (error i / τ) < 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ (zero_lt_one.trans hτ)).mpr (herr i)
  let r : Fin n → V := fun i => ⟨error i / τ, (V.valuation_le_one_iff _).mp (hsmall i).le⟩
  have hr (i : Fin n) : IsLocalRing.residue V (r i) = 0 :=
    (valuation_residue_zero_iff V (r i)).mpr (hsmall i)
  let z : Option (Fin n) → V := fun j => j.elim b (fun i => algebraMap E V (Y i) + r i)
  refine ⟨z, ?_, ?_⟩
  · intro j
    cases j with
    | none => change (τ⁻¹ : F) = τ⁻¹ * 1; rw [mul_one]
    | some i =>
      change algebraMap V F (algebraMap E V (Y i) + r i) = τ⁻¹ * x i
      rw [map_add, ← IsScalarTower.algebraMap_apply E V F, hx i]
      change algebraMap E F (Y i) + error i / τ = τ⁻¹ * (τ * algebraMap E F (Y i) + error i)
      field_simp [hτ0]
  · intro j
    cases j with
    | none =>
      change IsLocalRing.residue V b = algebraMap E (IsLocalRing.ResidueField V) 0
      rw [map_zero]
      exact hb
    | some i =>
      change IsLocalRing.residue V (algebraMap E V (Y i) + r i) =
        algebraMap E (IsLocalRing.ResidueField V) (Y i)
      rw [map_add, hr, add_zero]
      exact (IsScalarTower.algebraMap_apply E V (IsLocalRing.ResidueField V) (Y i)).symm

/-- The lower terms of the three-coordinate quadratic normal form are
strictly smaller than a strictly dominant radial coordinate. -/
theorem affine_isotropic_errors_below_radial
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]
    (Z W c : Fin n → E) (τ s t : F)
    (hτ : 1 < V.valuation τ) (hs : V.valuation s < V.valuation τ) (ht : V.valuation t < V.valuation τ) :
    ∀ i, V.valuation (s * algebraMap E F (Z i) + t * algebraMap E F (W i) + algebraMap E F (c i)) <
      V.valuation τ := by
  have hc (a : E) : V.valuation (algebraMap E F a) ≤ 1 := by
    apply (V.valuation_le_one_iff _).mpr
    have he : algebraMap V F (algebraMap E V a) = algebraMap E F a :=
      (IsScalarTower.algebraMap_apply E V F a).symm
    rw [← he]
    exact (algebraMap E V a).property
  intro i
  apply V.valuation.map_add_lt
  · apply V.valuation.map_add_lt
    · rw [map_mul]
      exact (mul_le_mul_of_nonneg_left (hc (Z i)) (show 0 ≤ V.valuation s from zero_le)).trans_lt
        (by simpa only [mul_one] using hs)
    · rw [map_mul]
      exact (mul_le_mul_of_nonneg_left (hc (W i)) (show 0 ≤ V.valuation t from zero_le)).trans_lt
        (by simpa only [mul_one] using ht)
  · exact (hc (c i)).trans_lt hτ

end DimensionFourDependence
