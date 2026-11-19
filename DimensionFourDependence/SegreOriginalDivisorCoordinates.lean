import DimensionFourDependence.SegreOriginalSourceDivisor

/-! # The actual source determinant DVR constructs every regular ruling-chart coordinate -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option quotPrecheck false

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
  (hSegre : H 0 * H 3 - H 1 * H 2 = 0)

local notation "Q₀" => segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
local notation "O₀" => Localization.AtPrime (Q₀).asIdeal
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "Φ₀" => primeLocalizationFractionHom (F := F₀) (Q₀).asIdeal

/-- The given original nonplanar Segre map constructs regular realizations
of all six ruling-chart values in its actual source divisor ring. The
uniformizer is the exact original determinant divided by `x1`, and its
principal ideal is the actual local maximal ideal. -/
theorem segre_original_source_divisor_constructs_regular_coordinates :
    ∃ x y π t z s : O₀,
      (Φ₀) x = (X₀) 0 ∧ (Φ₀) y = (X₀) 1 ∧
      (Φ₀) π = segreOriginalSourceUniformizer (K := K) ∧
      (Φ₀) t = segreOriginalSourceRulingParameter (K := K) ∧
      (Φ₀) z = ((X₀) 0)⁻¹ ∧ (Φ₀) s = (X₀) 1 / (X₀) 0 ∧
      IsLocalRing.maximalIdeal (O₀) = Ideal.span {π} := by
  let u : (O₀)ˣ := (segre_original_source_first_coordinate_local_unit H hd hH hrank hind I hSegre).unit
  have hu : (u : O₀) = algebraMap (MvPolynomial (Fin 4) K) (O₀) (MvPolynomial.X 0) := IsUnit.unit_spec _
  let x : O₀ := algebraMap (MvPolynomial (Fin 4) K) (O₀) (MvPolynomial.X 0)
  let y : O₀ := algebraMap (MvPolynomial (Fin 4) K) (O₀) (MvPolynomial.X 1)
  let z : O₀ := (↑u⁻¹ : O₀)
  let t : O₀ := algebraMap (MvPolynomial (Fin 4) K) (O₀) (MvPolynomial.X 2) * z
  let s : O₀ := y * z
  let π : O₀ := algebraMap (MvPolynomial (Fin 4) K) (O₀) (standardRulingPolynomial (F := K)) * z
  have hx : (Φ₀) x = (X₀) 0 := primeLocalizationFractionHom_algebraMap _ _
  have hy : (Φ₀) y = (X₀) 1 := primeLocalizationFractionHom_algebraMap _ _
  have hz : (Φ₀) z = ((X₀) 0)⁻¹ := by
    change (Φ₀) (↑u⁻¹ : O₀) = _
    rw [map_units_inv, hu, primeLocalizationFractionHom_algebraMap]
    rfl
  have ht : (Φ₀) t = segreOriginalSourceRulingParameter (K := K) := by
    dsimp only [t]
    rw [map_mul, primeLocalizationFractionHom_algebraMap, hz]
    rfl
  have hs : (Φ₀) s = (X₀) 1 / (X₀) 0 := by
    dsimp only [s]
    rw [map_mul, hy, hz]
    rfl
  have hπ : (Φ₀) π = segreOriginalSourceUniformizer (K := K) := by
    dsimp only [π]
    rw [map_mul, primeLocalizationFractionHom_algebraMap, hz,
      segre_original_source_uniformizer_eq_determinant]
    rfl
  have hmax : IsLocalRing.maximalIdeal (O₀) = Ideal.span {π} := by
    calc
      _ = (Q₀).asIdeal.map (algebraMap (MvPolynomial (Fin 4) K) (O₀)) :=
        (Localization.AtPrime.map_eq_maximalIdeal (I := (Q₀).asIdeal)).symm
      _ = Ideal.span {algebraMap (MvPolynomial (Fin 4) K) (O₀) (standardRulingPolynomial (F := K))} := by
        change (Ideal.span {standardRulingPolynomial (F := K)}).map _ = _
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span {π} :=
        (Ideal.span_singleton_mul_right_unit (u⁻¹).isUnit
          (algebraMap (MvPolynomial (Fin 4) K) (O₀) (standardRulingPolynomial (F := K)))).symm
  exact ⟨x, y, π, t, z, s, hx, hy, hπ, ht, hz, hs, hmax⟩

end DimensionFourDependence
