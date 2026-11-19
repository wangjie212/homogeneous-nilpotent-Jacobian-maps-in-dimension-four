import DimensionFourDependence.NormalHeightOneLevel
import DimensionFourDependence.ZeroPoleLocalReciprocal

/-! # Level closure at an intersection of a zero and a pole

The level locus is defined on the maximal regular domain of a rational
function, using actual original-ring numerators and denominators. It
does not depend on an arbitrarily chosen quotient presentation. At a
normal Noetherian local point where a zero branch and a pole branch
meet, the closed point is in the closure of every constant level.
The proof constructs a height-one level prime below the closed point.
-/

namespace DimensionFourDependence

variable (R : Type*) {F : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- The rational level on the whole regular domain of the function.
The multiplier is required to be invertible at the specified prime,
and both numerator and level relation belong to the original ring. -/
def rationalLevelLocus (f : F) (c : R) : Set (PrimeSpectrum R) :=
  {p | ∃ a s : R, s ∉ p.asIdeal ∧
    algebraMap R F s * f = algebraMap R F a ∧ a - c * s ∈ p.asIdeal}

/-- A local value of the level difference vanishing at an actual
prime constructs an original numerator/denominator presentation of
the level at that same prime. -/
theorem rationalLevelLocus_mem_of_local_difference
    (f : F) (c : R) (p : PrimeSpectrum R)
    (z : fractionPrimeLocalAlgebra (F := F) R p.asIdeal)
    (hz : (z : F) = f - algebraMap R F c)
    (hvan : z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R p.asIdeal)) :
    p ∈ rationalLevelLocus R f c := by
  let T := fractionPrimeLocalAlgebra (F := F) R p.asIdeal
  obtain ⟨a, s, hs, hzs⟩ : ∃ (a s : R) (_ : s ∈ p.asIdeal.primeCompl),
      (z : F) = algebraMap R F a * (algebraMap R F s)⁻¹ := z.property
  have hs0 : algebraMap R F s ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
    intro he
    exact hs (he ▸ p.asIdeal.zero_mem)
  have he : algebraMap R T a = algebraMap R T s * z := by
    apply Subtype.ext
    change algebraMap R F a = algebraMap R F s * (z : F)
    rw [hzs]
    field_simp
  have haP : a ∈ p.asIdeal := by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff T p.asIdeal a).mp
    rw [he]
    exact (IsLocalRing.maximalIdeal T).mul_mem_left _ hvan
  refine ⟨a + c * s, s, hs, ?_, ?_⟩
  · have heF := congrArg (fun t : T => (t : F)) he
    change algebraMap R F a = algebraMap R F s * (z : F) at heF
    rw [hz] at heF
    rw [map_add, map_mul]
    linear_combination -heF
  · simpa only [add_sub_cancel_right] using haP

variable [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- A nonregular translated reciprocal constructs a height-one
prime in the rational level locus. -/
theorem normal_nonregular_reciprocal_constructs_height_one_level_point
    (f : F) (c : R)
    (hreg : ¬IsLocalization.IsInteger R ((f - algebraMap R F c)⁻¹)) :
    ∃ p : PrimeSpectrum R, p.asIdeal.height = 1 ∧ p ∈ rationalLevelLocus R f c := by
  obtain ⟨P, hP, hh, z, hz, hvan⟩ :=
    normal_nonregular_reciprocal_constructs_height_one_level R f (algebraMap R F c) hreg
  exact ⟨⟨P, hP⟩, hh,
    rationalLevelLocus_mem_of_local_difference R f c ⟨P, hP⟩ z hz hvan⟩

variable [IsLocalRing R]

/-- A nonregular translated reciprocal puts the actual closed point
in the Zariski closure of the rational level locus. -/
theorem normal_local_closed_point_mem_level_closure_of_nonregular_reciprocal
    (f : F) (c : R)
    (hreg : ¬IsLocalization.IsInteger R ((f - algebraMap R F c)⁻¹)) :
    (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈
      closure (rationalLevelLocus R f c) := by
  obtain ⟨p, hh, hp⟩ := normal_nonregular_reciprocal_constructs_height_one_level_point R f c hreg
  have hle : p ≤ (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) :=
    IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  exact closure_mono (Set.singleton_subset_iff.mpr hp)
    ((PrimeSpectrum.le_iff_mem_closure _ _).mp hle)

/-- The local zero/pole intersection argument of Section 4.4.2:
branches containing the original local ring and seeing a zero and
a pole force its closed point into the closure of every original-ring
level. A height-one level prime is constructed by normality. -/
theorem zero_pole_closed_point_mem_rational_level_closure
    (f : F) (c : R) (V₀ Vinf : ValuationSubring F)
    (hR₀ : ∀ a : R, algebraMap R F a ∈ V₀)
    (hRinf : ∀ a : R, algebraMap R F a ∈ Vinf)
    (hzero : f ∈ V₀.nonunits) (hpole : f⁻¹ ∈ Vinf.nonunits) (hf : f ≠ 0) :
    (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈
      closure (rationalLevelLocus R f c) :=
  normal_local_closed_point_mem_level_closure_of_nonregular_reciprocal R f c
    (zero_pole_level_reciprocal_not_isInteger R f c V₀ Vinf hR₀ hRinf hzero hpole hf)

end DimensionFourDependence
