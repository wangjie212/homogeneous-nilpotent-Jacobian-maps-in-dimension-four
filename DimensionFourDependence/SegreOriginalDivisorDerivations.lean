import DimensionFourDependence.PrimeLocalizationPartials
import DimensionFourDependence.SegreOriginalDivisorCoordinates

/-! # The actual original source determinant DVR constructs its regular chart derivations -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option quotPrecheck false

variable {K : Type*} [Field K]

/-- The regular chart vector field is formed from the localized original
coordinate partials with the actual regular chart coefficients. -/
noncomputable def segrePrimeLocalChartDerivation
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime]
    (x y t : Localization.AtPrime Q) (i : Fin 4) :
    Derivation K (Localization.AtPrime Q) (Localization.AtPrime Q) :=
  ∑ r : Fin 4, segreSourceChartMatrix t x y r i • primeLocalizationPartial Q r

/-- Values of the constructed regular chart operator. -/
theorem segrePrimeLocalChartDerivation_apply
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime]
    (x y t : Localization.AtPrime Q) (i : Fin 4) (v : Localization.AtPrime Q) :
    segrePrimeLocalChartDerivation Q x y t i v =
      ∑ r : Fin 4, segreSourceChartMatrix t x y r i * primeLocalizationPartial Q r v := by
  simp [segrePrimeLocalChartDerivation, Derivation.smul_apply, smul_eq_mul]

/-- The constructed local operator agrees with the original rational
chart operator on every actual regular element. -/
theorem segrePrimeLocalChartDerivation_compatible_source
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime]
    (x y t : Localization.AtPrime Q)
    (hx : primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin 4) K)) Q x = rationalCoordinate 0)
    (hy : primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin 4) K)) Q y = rationalCoordinate 1)
    (ht : primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin 4) K)) Q t =
      segreOriginalSourceRulingParameter (K := K))
    (i : Fin 4) (v : Localization.AtPrime Q) :
    primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin 4) K)) Q
        (segrePrimeLocalChartDerivation Q x y t i v) =
      segreOriginalSourceChartDerivation (K := K) i
        (primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin 4) K)) Q v) := by
  rw [segrePrimeLocalChartDerivation_apply, map_sum, segreOriginalSourceChartDerivation, sourceVectorDerivation_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_mul, primeLocalizationPartial_compatible_source]
  congr 1
  fin_cases r <;> fin_cases i <;> simp [segreSourceChartMatrix, hx, hy, ht]

variable [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
  (hSegre : H 0 * H 3 - H 1 * H 2 = 0)

local notation "Q₀" => segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
local notation "O₀" => Localization.AtPrime (Q₀).asIdeal
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "Φ₀" => primeLocalizationFractionHom (F := F₀) (Q₀).asIdeal

/-- The actual original Segre map constructs its regular source chart
and all four base-linear chart derivatives on its actual determinant DVR.
Every derivative retains its original source-field realization; no
regularity or existence of chart derivations is supplied as a hypothesis. -/
theorem segre_original_source_divisor_constructs_chart_and_derivations :
    ∃ (x y π t z s : O₀) (D : Fin 4 → Derivation K (O₀) (O₀)),
      (Φ₀) x = (X₀) 0 ∧ (Φ₀) y = (X₀) 1 ∧
      (Φ₀) π = segreOriginalSourceUniformizer (K := K) ∧
      (Φ₀) t = segreOriginalSourceRulingParameter (K := K) ∧
      (Φ₀) z = ((X₀) 0)⁻¹ ∧ (Φ₀) s = (X₀) 1 / (X₀) 0 ∧
      IsLocalRing.maximalIdeal (O₀) = Ideal.span {π} ∧
      ∀ i v, (Φ₀) (D i v) = segreOriginalSourceChartDerivation (K := K) i ((Φ₀) v) := by
  obtain ⟨x, y, π, t, z, s, hx, hy, hπ, ht, hz, hs, hmax⟩ :=
    segre_original_source_divisor_constructs_regular_coordinates H hd hH hrank hind I hSegre
  exact ⟨x, y, π, t, z, s, (fun i => segrePrimeLocalChartDerivation (Q₀).asIdeal x y t i),
    hx, hy, hπ, ht, hz, hs, hmax,
    fun i v => segrePrimeLocalChartDerivation_compatible_source (Q₀).asIdeal x y t hx hy ht i v⟩

end DimensionFourDependence
