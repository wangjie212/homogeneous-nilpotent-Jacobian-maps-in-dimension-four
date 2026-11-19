import DimensionFourDependence.IteratedPrimeLocalizationRegularity
import DimensionFourDependence.AffineStalkDimension
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Stalk primes construct actual affine points with the same regular fractions -/

namespace DimensionFourDependence

open AlgebraicGeometry

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A prime in an actual stalk constructs a point in any specified affine
neighborhood. Its height, section vanishing, and regular fractions in the
scheme's own function field are preserved by this construction. -/
theorem affine_stalk_prime_constructs_point_with_same_regular_fractions
    {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    (z : X) (hz : z ∈ U) (Q : PrimeSpectrum (X.presheaf.stalk z)) :
    ∃ (y : X) (hy : y ∈ U),
      Order.coheight y = Q.asIdeal.height ∧
      (∀ s : Γ(X, U), X.presheaf.germ U z hz s ∈ Q.asIdeal ↔
        X.presheaf.germ U y hy s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)) ∧
      (∀ f : X.functionField,
        f ∈ fractionPrimeLocalAlgebra (X.presheaf.stalk z) Q.asIdeal ↔
          IsLocalization.IsInteger (X.presheaf.stalk y) f) := by
  letI : Nonempty U := ⟨⟨z, hz⟩⟩
  let A := Γ(X, U)
  let R := X.presheaf.stalk z
  letI : Algebra A R := X.presheaf.algebra_section_stalk ⟨z, hz⟩
  letI : IsLocalization.AtPrime R (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hz⟩
  letI : IsFractionRing A X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsScalarTower A R X.functionField := functionField_isScalarTower X U ⟨z, hz⟩
  let p : PrimeSpectrum A := ⟨Q.asIdeal.comap (algebraMap A R), inferInstance⟩
  let y := hU.fromSpec p
  have hy : y ∈ U := by
    change y ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self p
  letI : Algebra A (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal := hU.isLocalization_stalk' p hy
  letI : IsScalarTower A (X.presheaf.stalk y) X.functionField :=
    functionField_isScalarTower X U ⟨y, hy⟩
  have hpheight : p.asIdeal.height = Q.asIdeal.height :=
    localized_prime_under_height_eq (hU.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl Q.asIdeal
  have hyheight : Order.coheight y = p.asIdeal.height := by
    have he := IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk y)
    rw [ringKrullDim_stalk_eq_coheight] at he
    exact_mod_cast he
  refine ⟨y, hy, hyheight.trans hpheight, ?_, ?_⟩
  · intro s
    change s ∈ p.asIdeal ↔ algebraMap A (X.presheaf.stalk y) s ∈ _
    have he := IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y) p.asIdeal
    change Ideal.comap (algebraMap A (X.presheaf.stalk y))
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) = p.asIdeal at he
    rw [← he]
    rfl
  · intro f
    exact (iterated_prime_fraction_membership_iff_under
      (hU.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl Q.asIdeal f).trans
      (prime_localization_integer_iff_fraction_subalgebra
        (T := X.presheaf.stalk y) p.asIdeal f).symm

end DimensionFourDependence
