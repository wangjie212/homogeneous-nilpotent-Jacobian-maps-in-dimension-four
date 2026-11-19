import DimensionFourDependence.RadialPoleBound

/-! # The residue direction at a single isotropic-coordinate pole

Once `tau` has at most the pole order of `s` and `t` is finite,
normalizing by `s` gives the residue direction `Z+rY`.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- Integral normalization at a pole of `s`, including the actual
residue scalar `r` arising from `tau/s`. -/
theorem single_pole_radial_shift_residue
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]
    (x : Fin n → F) (Y Z W c : Fin n → E) (τ s t : F)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i))
    (hs : 1 < V.valuation s) (hτ : V.valuation τ ≤ V.valuation s) (ht : V.valuation t ≤ 1) :
    ∃ (r : IsLocalRing.ResidueField V) (z : Option (Fin n) → V),
      (∀ j, algebraMap V F (z j) = s⁻¹ * j.elim 1 x) ∧
      IsLocalRing.residue V (z none) = 0 ∧
      ∀ i, IsLocalRing.residue V (z (some i)) =
        algebraMap E (IsLocalRing.ResidueField V) (Z i) +
          r * algebraMap E (IsLocalRing.ResidueField V) (Y i) := by
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hs
    exact (not_lt_of_ge zero_le_one) hs
  have hsnot : s ∉ V := fun h => (not_le_of_gt hs) ((V.valuation_le_one_iff _).mpr h)
  let b : V := ⟨s⁻¹, (V.mem_or_inv_mem s).resolve_left hsnot⟩
  have hb : IsLocalRing.residue V b = 0 := by
    apply (valuation_residue_zero_iff V b).mpr
    change V.valuation (s⁻¹) < 1
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hs
  have hrle : V.valuation (τ / s) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_one.trans hs)).mpr hτ
  have hwlt : V.valuation (t / s) < 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ (zero_lt_one.trans hs)).mpr (ht.trans_lt hs)
  let r : V := ⟨τ / s, (V.valuation_le_one_iff _).mp hrle⟩
  let w : V := ⟨t / s, (V.valuation_le_one_iff _).mp hwlt.le⟩
  have hw : IsLocalRing.residue V w = 0 := (valuation_residue_zero_iff V w).mpr hwlt
  let z : Option (Fin n) → V := fun j => j.elim b (fun i =>
    r * algebraMap E V (Y i) + algebraMap E V (Z i) +
      w * algebraMap E V (W i) + b * algebraMap E V (c i))
  refine ⟨IsLocalRing.residue V r, z, ?_, hb, ?_⟩
  · intro j
    cases j with
    | none => change (s⁻¹ : F) = s⁻¹ * 1; rw [mul_one]
    | some i =>
      change algebraMap V F (r * algebraMap E V (Y i) + algebraMap E V (Z i) +
        w * algebraMap E V (W i) + b * algebraMap E V (c i)) = s⁻¹ * x i
      simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply E V F]
      change τ / s * algebraMap E F (Y i) + algebraMap E F (Z i) +
        t / s * algebraMap E F (W i) + s⁻¹ * algebraMap E F (c i) = s⁻¹ * x i
      rw [hx i]
      field_simp [hs0]
  · intro i
    have hc (a : E) : IsLocalRing.residue V (algebraMap E V a) =
        algebraMap E (IsLocalRing.ResidueField V) a :=
      (IsScalarTower.algebraMap_apply E V (IsLocalRing.ResidueField V) a).symm
    change IsLocalRing.residue V (r * algebraMap E V (Y i) + algebraMap E V (Z i) +
      w * algebraMap E V (W i) + b * algebraMap E V (c i)) = _
    simp only [map_add, map_mul, hc, hw, hb, zero_mul, add_zero]
    ring

end DimensionFourDependence
