import DimensionFourDependence.SegreOriginalSourceChart
import DimensionFourDependence.CoveringTransversalQuadric
import DimensionFourDependence.SourceDivisorLocalization
import DimensionFourDependence.PrimeLocalizationFunctionField

/-! # The original Segre equation constructs its actual source divisor local ring -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option quotPrecheck false

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
  (hSegre : H 0 * H 3 - H 1 * H 2 = 0)

include H hd hH hrank hind I hSegre

/-- The actual nonplanar rank-three image equation proves that the
original determinant polynomial is irreducible. No source-divisor prime
or irreducibility assumption is supplied. -/
theorem original_segre_image_constructs_determinant_irreducible :
    Irreducible (standardRulingPolynomial (F := K)) := by
  have hvan : aeval H (standardRulingPolynomial (F := K)) = 0 := by
    simpa [standardRulingPolynomial] using hSegre
  obtain ⟨_hdegree, c, hc, he⟩ := I.quadratic_relation_scalar_multiple H hd hH hrank hind
    (standardRulingPolynomial (F := K)) standardRulingPolynomial_homogeneous standardRulingPolynomial_ne_zero hvan
  have hunit : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 4) K) :=
    (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  rw [he]
  exact (irreducible_isUnit_mul hunit).mpr I.irreducible

/-- The prime of the actual original source determinant divisor. -/
noncomputable def segreOriginalSourceDeterminantPrime : PrimeSpectrum (MvPolynomial (Fin 4) K) :=
  ⟨Ideal.span {standardRulingPolynomial (F := K)}, Ideal.isPrime_span_singleton_of_prime
    (original_segre_image_constructs_determinant_irreducible H hd hH hrank hind I hSegre).prime⟩

local notation "Q₀" => segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
local notation "O₀" => Localization.AtPrime (Q₀).asIdeal
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual source determinant prime constructs the DVR needed for
the ruling calculation in the original coefficient field and coordinates. -/
theorem segre_original_source_determinant_localization_isDVR : IsDiscreteValuationRing (O₀) :=
  principal_prime_localization_isDVR (Q₀).asIdeal (standardRulingPolynomial (F := K))
    (original_segre_image_constructs_determinant_irreducible H hd hH hrank hind I hSegre).prime rfl

/-- The first source coordinate avoids the determinant prime, by the
actual degree-two versus degree-one polynomial divisibility bound. -/
theorem segre_original_source_first_coordinate_not_mem_determinant_prime :
    (MvPolynomial.X 0 : MvPolynomial (Fin 4) K) ∉ (Q₀).asIdeal := by
  intro he
  have hdiv : standardRulingPolynomial (F := K) ∣ (MvPolynomial.X 0 : MvPolynomial (Fin 4) K) :=
    Ideal.mem_span_singleton.mp he
  have hdeg := totalDegree_le_of_dvd_of_isDomain hdiv (MvPolynomial.X_ne_zero (R := K) (0 : Fin 4))
  rw [(standardRulingPolynomial_homogeneous (F := K)).totalDegree standardRulingPolynomial_ne_zero] at hdeg
  have hXdeg : (MvPolynomial.X 0 : MvPolynomial (Fin 4) K).totalDegree = 1 := by simp
  omega

/-- The chosen radial coordinate is an actual unit in the constructed
source divisor ring, so its inverse has a regular source realization. -/
theorem segre_original_source_first_coordinate_local_unit :
    IsUnit (algebraMap (MvPolynomial (Fin 4) K) (O₀) (MvPolynomial.X 0)) :=
  IsLocalization.map_units (O₀)
    (⟨MvPolynomial.X 0, segre_original_source_first_coordinate_not_mem_determinant_prime
      H hd hH hrank hind I hSegre⟩ : (Q₀).asIdeal.primeCompl)

/-- The actual determinant localization embeds faithfully in the same
original rational source field, retaining the original source map. -/
theorem segre_original_source_divisor_fraction_map_injective :
    Function.Injective (primeLocalizationFractionHom (F := F₀) (Q₀).asIdeal) := by
  letI : Algebra (O₀) F₀ := primeLocalizationFractionAlgebra (Q₀).asIdeal
  letI : IsFractionRing (O₀) F₀ := primeLocalizationFraction_isFractionRing (Q₀).asIdeal
  exact IsFractionRing.injective (O₀) F₀

end DimensionFourDependence
