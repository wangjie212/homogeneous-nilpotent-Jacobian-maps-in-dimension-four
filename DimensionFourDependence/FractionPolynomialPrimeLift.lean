import DimensionFourDependence.PowerRemainderUniqueness
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # Lifting a fraction-field polynomial prime to an actual primitive prime -/

namespace DimensionFourDependence

open Polynomial IsLocalization

set_option maxHeartbeats 2000000

variable {R F : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [Field F] [Algebra R F] [IsFractionRing R F]

/-- Clear the actual denominators and remove the actual content of a
nonzero fraction-field polynomial. Its resulting primitive polynomial
has an associated image, rather than a supplied primitive representative. -/
theorem fraction_polynomial_constructs_primitive_associate
    (p : Polynomial F) (hp : p ≠ 0) :
    ∃ P : Polynomial R, P.IsPrimitive ∧ Associated (P.map (algebraMap R F)) p := by
  let I := integerNormalization (nonZeroDivisors R) p
  have hI : I ≠ 0 := by
    exact fun h => hp ((IsFractionRing.integerNormalization_eq_zero_iff (A := R)).mp h)
  obtain ⟨b, hb, hden⟩ := integerNormalization_spec (nonZeroDivisors R) p
  have hb0 : algebraMap R F b ≠ 0 := by
    exact fun h => (nonZeroDivisors.ne_zero hb) ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
  have hc0 : algebraMap R F I.content ≠ 0 := by
    intro h
    have hz : I.content = 0 := (IsFractionRing.injective R F) (h.trans (map_zero _).symm)
    exact hI (Polynomial.content_eq_zero_iff.mp hz)
  have he : Polynomial.C (algebraMap R F I.content) * I.primPart.map (algebraMap R F) =
      Polynomial.C (algebraMap R F b) * p := by
    calc
      _ = I.map (algebraMap R F) := by rw [← Polynomial.map_C, ← Polynomial.map_mul, ← I.eq_C_content_mul_primPart]
      _ = _ := by simpa only [I, Algebra.smul_def, Polynomial.algebraMap_apply] using hden
  have hcunit : IsUnit (Polynomial.C (algebraMap R F I.content)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  have hbunit : IsUnit (Polynomial.C (algebraMap R F b)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0)
  exact ⟨I.primPart, I.isPrimitive_primPart,
    (associated_unit_mul_right _ _ hcunit).trans ((Associated.of_eq he).trans
      (associated_unit_mul_left _ _ hbunit))⟩

/-- Every actual irreducible fraction-field polynomial lifts to an
actual primitive irreducible polynomial over the coefficient domain. -/
theorem fraction_polynomial_irreducible_constructs_primitive_prime
    (p : Polynomial F) (hp : Irreducible p) :
    ∃ P : Polynomial R, P.IsPrimitive ∧ Irreducible P ∧
      Associated (P.map (algebraMap R F)) p := by
  obtain ⟨P, hprim, hmap⟩ := fraction_polynomial_constructs_primitive_associate (R := R) p hp.ne_zero
  refine ⟨P, hprim, ?_, hmap⟩
  exact hprim.irreducible_iff_irreducible_map_fraction_map.mpr (hmap.symm.irreducible hp)

/-- Every power of an actual primitive polynomial remains primitive. -/
theorem primitive_polynomial_power (P : Polynomial R) (hP : P.IsPrimitive) (n : ℕ) :
    (P ^ n).IsPrimitive := by
  induction n with
  | zero => simpa using (Polynomial.isPrimitive_one : (1 : Polynomial R).IsPrimitive)
  | succ n ih => simpa only [pow_succ] using ih.mul hP

end DimensionFourDependence
