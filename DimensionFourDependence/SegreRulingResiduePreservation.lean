import DimensionFourDependence.SegreDominantNormalizedOutputs

/-! # Polynomial ruling preservation descends to the actual normalized outputs -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option quotPrecheck false

universe u
variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
  (hSegre : H 0 * H 3 - H 1 * H 2 = 0)

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "Q₀" => segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
local notation "O₀" => Localization.AtPrime (Q₀).asIdeal
local notation "κ₀" => (Q₀).asIdeal.ResidueField
local notation "F₀" => FractionRing R₀
local notation "Φ₀" => primeLocalizationFractionHom (F := F₀) (Q₀).asIdeal
local notation "ρ₀" => algebraMap R₀ κ₀
local notation "σ₀" => IsLocalRing.residue (O₀)

/-- The polynomial cross relation for the preserved first ruling gives
exactly the residue slope identity used in the original local contradiction. -/
theorem segre_original_cross_relation_constructs_residue_preservation
    (P : Fin 4 → R₀) (hcross : P 2 * X 0 - P 0 * X 2 ∈ (Q₀).asIdeal)
    (t : O₀) (ht : (Φ₀) t = segreOriginalSourceRulingParameter (K := K))
    (v u : (O₀)ˣ) (p : Fin 4 → O₀)
    (hp : ∀ i, p i = (v : O₀) * algebraMap R₀ (O₀) (P i))
    (hfirst : p 0 = (u : O₀)) :
    (σ₀) (p 2 * (↑u⁻¹ : O₀)) = (σ₀) t := by
  have hx : (ρ₀) (X 0) ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact segre_original_source_first_coordinate_not_mem_determinant_prime H hd hH hrank hind I hSegre
  have hxt : algebraMap R₀ (O₀) (X 0) * t = algebraMap R₀ (O₀) (X 2) := by
    apply segre_original_source_divisor_fraction_map_injective H hd hH hrank hind I hSegre
    rw [map_mul, ht, primeLocalizationFractionHom_algebraMap, primeLocalizationFractionHom_algebraMap]
    dsimp only [segreOriginalSourceRulingParameter]
    exact mul_div_cancel₀ _ segre_original_source_first_coordinate_ne_zero
  have hbase : ∀ z : R₀, (σ₀) (algebraMap R₀ (O₀) z) = (ρ₀) z := fun z =>
    (IsScalarTower.algebraMap_apply R₀ (O₀) κ₀ z).symm
  have hxtκ : (ρ₀) (X 0) * (σ₀) t = (ρ₀) (X 2) := by
    simpa only [map_mul, hbase] using congrArg (σ₀) hxt
  have hc : (ρ₀) (P 2) * (ρ₀) (X 0) = (ρ₀) (P 0) * (ρ₀) (X 2) := by
    have he := Ideal.algebraMap_residueField_eq_zero.mpr hcross
    simpa only [map_sub, map_mul, sub_eq_zero] using he
  have hP : (ρ₀) (P 2) = (σ₀) t * (ρ₀) (P 0) := by
    apply mul_right_cancel₀ hx
    rw [hc, ← hxtκ]
    ring
  have hpκ : (σ₀) (p 2) = (σ₀) t * (σ₀) (p 0) := by
    simp only [hp, map_mul, hbase]
    rw [hP]
    ring
  rw [map_mul, hpκ, hfirst, mul_assoc, ← map_mul]
  simp

end DimensionFourDependence
