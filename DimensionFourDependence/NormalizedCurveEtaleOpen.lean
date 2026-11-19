import DimensionFourDependence.FiniteNormalization
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Smooth.Fiber

/-! # A finite normalized curve cover is etale over a nonempty base open

For a finite extension of the fraction field of a characteristic-zero PID,
the integral closure is finite. A nonzero element upstairs divides a nonzero
base element. Applying this to a generic etale neighborhood produces an
actual nonzero denominator on the base, so all points above its complement
are etale. This is the affine parameter-line step of Lemma 4.2.
-/

namespace DimensionFourDependence

variable {R k L : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
  [Field k] [CharZero k] [Field L] [Algebra R k] [IsFractionRing R k]
  [Algebra k L] [Algebra R L] [IsScalarTower R k L] [Module.Finite k L]

include k in
omit [CharZero R] in
/-- The normalized affine curve of a finite parameter-field extension
is finite over the original parameter ring. -/
theorem normalized_curve_cover_finite : Module.Finite R (integralClosure R L) :=
  IsIntegralClosure.finite R k L (integralClosure R L)

include k in
omit [CharZero R] [CharZero k] [IsPrincipalIdealRing R] in
/-- Any nonzero regular function upstairs divides a nonzero original
base function in the actual normalized curve ring. -/
theorem normalized_curve_nonzero_divides_base_element
    (s : integralClosure R L) (hs : s ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ s ∣ algebraMap R (integralClosure R L) a := by
  classical
  have hsL : (s : L) ≠ 0 := fun hz => hs (Subtype.ext hz)
  obtain ⟨a, ha, hi⟩ := exists_integral_multiples R k (L := L) {(s : L)⁻¹}
  have hb : IsIntegral R (a • (s : L)⁻¹) := hi _ (by simp)
  refine ⟨a, ha, ⟨⟨a • (s : L)⁻¹, hb⟩, ?_⟩⟩
  apply Subtype.ext
  change algebraMap R L a = (s : L) * (a • (s : L)⁻¹)
  rw [Algebra.smul_def]
  field_simp

include k in
/-- There is an actual nonzero base denominator above whose basic open
the entire finite normalized curve cover is etale. -/
theorem normalized_curve_cover_etale_over_base_open :
    ∃ a : R, a ≠ 0 ∧ ∀ q : PrimeSpectrum (integralClosure R L),
      algebraMap R (integralClosure R L) a ∉ q.asIdeal → Algebra.IsEtaleAt R q.asIdeal := by
  let S := integralClosure R L
  let : Module.Finite R S := normalized_curve_cover_finite (k := k)
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R k L]
    exact (algebraMap k L).injective.comp (IsFractionRing.injective R k))
  let : Module.IsTorsionFree R S := inferInstance
  let : Module.Free R S := inferInstance
  let : Module.Flat R S := inferInstance
  let : Algebra.IsUnramifiedAt R (⊥ : Ideal S) := Algebra.isUnramifiedAt_bot
  obtain ⟨s, hs, hunr⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) (⊥ : Ideal S)
  have hs0 : s ≠ 0 := by simpa only [Ideal.mem_bot] using hs
  obtain ⟨a, ha, r, har⟩ := normalized_curve_nonzero_divides_base_element (k := k) s hs0
  refine ⟨a, ha, ?_⟩
  intro q haq
  have hsq : s ∉ q.asIdeal := by
    intro h
    apply haq
    rw [har]
    exact q.asIdeal.mul_mem_right r h
  let : Algebra.IsUnramifiedAt R q.asIdeal :=
    (Algebra.basicOpen_subset_unramifiedLocus_iff (R := R) (f := s)).mpr hunr hsq
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q.asIdeal

include k in
/-- Inverting an actual nonzero base element makes the normalized curve
cover etale. The denominator is chosen downstairs on the parameter curve. -/
theorem normalized_curve_cover_etale_base_localization :
    ∃ a : R, a ≠ 0 ∧ Algebra.Etale R
      (Localization.Away (algebraMap R (integralClosure R L) a)) := by
  let S := integralClosure R L
  let : Module.Finite R S := normalized_curve_cover_finite (k := k)
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨a, ha, hq⟩ := normalized_curve_cover_etale_over_base_open (R := R) (k := k) (L := L)
  refine ⟨a, ha, (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R)).mp ?_⟩
  intro q hqa
  exact hq q hqa

/-- Every finite extension of the actual rational parameter field has a
finite normalized affine parameter-curve model and an actual nonzero
original parameter polynomial over whose basic open it is etale. -/
theorem finite_rational_parameter_cover_etale_open
    {K₀ E₀ : Type*} [Field K₀] [CharZero K₀] [Field E₀]
    [Algebra (RatFunc K₀) E₀] [Module.Finite (RatFunc K₀) E₀] :
    letI : Algebra (Polynomial K₀) E₀ :=
      ((algebraMap (RatFunc K₀) E₀).comp (algebraMap (Polynomial K₀) (RatFunc K₀))).toAlgebra
    ∃ a : Polynomial K₀, a ≠ 0 ∧
      Module.Finite (Polynomial K₀) (integralClosure (Polynomial K₀) E₀) ∧
      Algebra.Etale (Polynomial K₀)
        (Localization.Away (algebraMap (Polynomial K₀) (integralClosure (Polynomial K₀) E₀) a)) := by
  let : Algebra (Polynomial K₀) E₀ :=
    ((algebraMap (RatFunc K₀) E₀).comp (algebraMap (Polynomial K₀) (RatFunc K₀))).toAlgebra
  let : IsScalarTower (Polynomial K₀) (RatFunc K₀) E₀ :=
    IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  obtain ⟨a, ha, het⟩ := normalized_curve_cover_etale_base_localization
    (R := Polynomial K₀) (k := RatFunc K₀) (L := E₀)
  exact ⟨a, ha, normalized_curve_cover_finite (k := RatFunc K₀), het⟩

end DimensionFourDependence
