import DimensionFourDependence.SegreProjectiveRestrictionKernel
import DimensionFourDependence.SegreOriginalDivisorDerivations

/-! # The dominant primitive restriction constructs unit-normalized original outputs -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option quotPrecheck false

universe u
variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
  (hSegre : H 0 * H 3 - H 1 * H 2 = 0)

local notation "Q₀" => segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
local notation "O₀" => Localization.AtPrime (Q₀).asIdeal
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Φ₀" => primeLocalizationFractionHom (F := F₀) (Q₀).asIdeal
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "δ₀" => standardRulingPolynomial (F := K)

/-- The original common scalar factor and actual projective dominance
construct their own exact determinant order, unit common remainder and
unit first normalized output in the actual source divisor DVR. -/
theorem segre_dominant_primitive_restriction_constructs_normalized_outputs
    (hH0 : H ≠ 0) (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => G * P i)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim)
    (x π : O₀) (hx : (Φ₀) x = (X₀) 0)
    (hπ : (Φ₀) π = segreOriginalSourceUniformizer (K := K)) :
    ∃ (j : ℕ) (v u : (O₀)ˣ) (p : Fin 4 → O₀),
      (∀ i, p i = (v : O₀) * algebraMap (MvPolynomial (Fin 4) K) (O₀) (P i)) ∧
      (∀ i, algebraMap (MvPolynomial (Fin 4) K) (O₀) (H i) = π ^ j * p i) ∧
      p 0 = (u : O₀) ∧ (δ₀) ^ j ∣ G := by
  have hδprime := (original_segre_image_constructs_determinant_irreducible H hd hH hrank hind I hSegre).prime
  obtain ⟨j, B, hBnot, hGB⟩ := WfDvdMonoid.max_power_factor hG hδprime.irreducible
  have hBunit : IsUnit (algebraMap (MvPolynomial (Fin 4) K) (O₀) B) :=
    IsLocalization.map_units (O₀) (⟨B, fun he => hBnot (Ideal.mem_span_singleton.mp he)⟩ : (Q₀).asIdeal.primeCompl)
  have hxval : x = algebraMap (MvPolynomial (Fin 4) K) (O₀) (MvPolynomial.X 0) := by
    apply segre_original_source_divisor_fraction_map_injective H hd hH hrank hind I hSegre
    exact hx.trans (primeLocalizationFractionHom_algebraMap _ _).symm
  have hxunit : IsUnit x := by
    rw [hxval]
    exact segre_original_source_first_coordinate_local_unit H hd hH hrank hind I hSegre
  have hδ : algebraMap (MvPolynomial (Fin 4) K) (O₀) (δ₀) = π * x := by
    apply segre_original_source_divisor_fraction_map_injective H hd hH hrank hind I hSegre
    rw [primeLocalizationFractionHom_algebraMap, map_mul, hπ, hx,
      segre_original_source_uniformizer_eq_determinant, div_mul_cancel₀ _ segre_original_source_first_coordinate_ne_zero]
  have hv : IsUnit (x ^ j * algebraMap (MvPolynomial (Fin 4) K) (O₀) B) := (hxunit.pow j).mul hBunit
  let v : (O₀)ˣ := hv.unit
  have hvval : (v : O₀) = x ^ j * algebraMap (MvPolynomial (Fin 4) K) (O₀) B := hv.unit_spec
  let p : Fin 4 → O₀ := fun i => (v : O₀) * algebraMap (MvPolynomial (Fin 4) K) (O₀) (P i)
  have hp0 : IsUnit (p 0) := v.isUnit.mul
    (segre_dominant_primitive_first_output_local_unit H hd hH hrank hind I hSegre hH0 P hD hP hprim hdom)
  refine ⟨j, v, hp0.unit, p, fun _ => rfl, ?_, hp0.unit_spec.symm, ⟨B, hGB⟩⟩
  intro i
  rw [congrFun hHP i, hGB, map_mul, map_mul, map_pow, hδ, mul_pow]
  dsimp only [p]
  rw [hvval]
  ring

end DimensionFourDependence
