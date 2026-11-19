import DimensionFourDependence.NormalizationResidueDimension
import DimensionFourDependence.TranscendenceDegreeSpecialization

/-! # Exact dimension of residue fraction fields of normalization divisors -/

namespace DimensionFourDependence

universe u

variable {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- The canonical fraction field retains the transcendence degree of
its original domain, with the original coefficient action. -/
theorem fractionRing_trdeg_eq_base :
    Algebra.trdeg k (FractionRing A) = Algebra.trdeg k A := by
  let : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have h := trdeg_add_eq (A := FractionRing A) k A
  simpa only [trdeg_eq_zero, add_zero] using h.symm

variable [CharZero k] [Algebra.FiniteType k A]

/-- The canonical finite birational normalization retains the whole
transcendence degree of the original affine domain. -/
theorem normalizationRing_trdeg_eq_source :
    Algebra.trdeg k (normalizationRing A) = Algebra.trdeg k A := by
  let : Module.Finite A (normalizationRing A) := normalizationRing_finite A (K := k)
  have h := trdeg_add_eq (A := normalizationRing A) k A
  simpa only [trdeg_eq_zero, add_zero] using h.symm

/-- A nonzero prime of the actual canonical normalization has residue
fraction field of strictly smaller dimension than the original affine
domain. No auxiliary projection or selected residue coordinate is used. -/
theorem normalization_nonzero_prime_residue_trdeg_lt_source
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Algebra.trdeg k (FractionRing (normalizationRing A ⧸ Q)) < Algebra.trdeg k A := by
  have hnorm := normalizationRing_trdeg_eq_source (k := k) (A := A)
  have hfin : Algebra.trdeg k (normalizationRing A) < Cardinal.aleph0 :=
    hnorm.trans_lt (trdeg_lt_aleph0_of_finiteType (R := k) (S := A))
  have hlt := prime_quotient_trdeg_lt (K' := k) Q hQ hfin
  exact ((fractionRing_trdeg_eq_base (k := k) (A := normalizationRing A ⧸ Q)).trans_lt hlt).trans_eq hnorm

/-- Every height-one prime on the canonical normalization of an
actual affine surface has residue fraction field of dimension exactly
one over the surface's coefficient field. -/
theorem normalization_surface_divisor_residue_trdeg_eq_one
    (htr : Algebra.trdeg k A = 2)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1) :
    Algebra.trdeg k (FractionRing (normalizationRing A ⧸ Q)) = 1 := by
  have hQne : Q ≠ ⊥ := by
    intro he
    have hz := Ideal.height_eq_zero_iff_eq_bot.mpr he
    rw [hQ] at hz
    exact one_ne_zero hz
  have hlt : Algebra.trdeg k (FractionRing (normalizationRing A ⧸ Q)) < 2 :=
    (normalization_nonzero_prime_residue_trdeg_lt_source (k := k) Q hQne).trans_eq htr
  have hle : Algebra.trdeg k (FractionRing (normalizationRing A ⧸ Q)) ≤ 1 :=
    (Cardinal.lt_natCast_add_one_iff (n := 1)).mp (by convert hlt using 1; norm_num)
  exact le_antisymm hle
    (normalization_divisor_residue_trdeg_at_least_one (by rw [htr]) Q hQ)

end DimensionFourDependence
