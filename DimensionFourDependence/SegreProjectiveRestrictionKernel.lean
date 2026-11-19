import DimensionFourDependence.SegreOriginalSourceDivisor
import DimensionFourDependence.Lemma43ProjectiveRestriction

/-! # Actual projective dominance constructs the original Segre restriction kernel -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option quotPrecheck false

universe u
variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
  (hSegre : H 0 * H 3 - H 1 * H 2 = 0)

local notation "Q₀" => segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
local notation "O₀" => Localization.AtPrime (Q₀).asIdeal

include H hd hH hrank hind I hSegre

/-- The image relation prime is exactly the original source determinant
prime, derived from the actual defining equation and its nonzero scalar. -/
theorem original_segre_image_relation_ideal_eq_determinant_prime :
    imageRelationIdeal H = (Q₀).asIdeal := by
  have hvan : aeval H (standardRulingPolynomial (F := K)) = 0 := by
    simpa [standardRulingPolynomial] using hSegre
  obtain ⟨_hdegree, c, hc, he⟩ := I.quadratic_relation_scalar_multiple H hd hH hrank hind
    (standardRulingPolynomial (F := K)) standardRulingPolynomial_homogeneous standardRulingPolynomial_ne_zero hvan
  have hunit : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 4) K) :=
    (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  rw [I.ideal_eq_span H hrank]
  change Ideal.span {I.equation} = Ideal.span {standardRulingPolynomial (F := K)}
  rw [he, Ideal.span_singleton_mul_left_unit hunit]

variable (hH0 : H ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K)
  {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P)

/-- Equality of the actual projective image closures supplies the exact
source determinant substitution kernel of the primitive restriction. -/
theorem segre_projective_restriction_dominance_constructs_kernel
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim)
    (z : MvPolynomial (Fin 4) K) :
    aeval P z ∈ (Q₀).asIdeal ↔ z ∈ (Q₀).asIdeal := by
  have he := original_projective_restriction_dominance_constructs_cone_kernel
    H hd hH hH0 hrank I P hD hP hprim hdom z
  rw [Ideal.algebraMap_residueField_eq_zero] at he
  rwa [original_segre_image_relation_ideal_eq_determinant_prime H hd hH hrank hind I hSegre] at he

/-- Dominance of the actual projective restriction forces its first
primitive output to remain nonzero at the original determinant divisor. -/
theorem segre_dominant_primitive_first_output_not_mem_source_prime
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim) :
    P 0 ∉ (Q₀).asIdeal := by
  intro he
  have hX := (segre_projective_restriction_dominance_constructs_kernel H hd hH hrank hind I hSegre
    hH0 P hD hP hprim hdom (MvPolynomial.X 0)).mp (by simpa using he)
  exact segre_original_source_first_coordinate_not_mem_determinant_prime H hd hH hrank hind I hSegre hX

/-- The primitive first output is an actual unit of the constructed
source divisor DVR. This is derived from projective dominance, rather
than assumed as a regular normalized-output condition. -/
theorem segre_dominant_primitive_first_output_local_unit
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim) :
    IsUnit (algebraMap (MvPolynomial (Fin 4) K) (O₀) (P 0)) :=
  IsLocalization.map_units (O₀)
    (⟨P 0, segre_dominant_primitive_first_output_not_mem_source_prime H hd hH hrank hind I hSegre
      hH0 P hD hP hprim hdom⟩ : (Q₀).asIdeal.primeCompl)

end DimensionFourDependence
