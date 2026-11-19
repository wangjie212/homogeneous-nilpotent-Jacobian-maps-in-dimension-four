import DimensionFourDependence.NormalizationResidueDimension
import DimensionFourDependence.GeneratedPointPrimeDimension

/-! # Normalization divisors cannot be supported only at a finite-type cone vertex -/

namespace DimensionFourDependence

universe u

variable {E A : Type u} [Field E] [CharZero E] [CommRing A] [IsDomain A]
  [Algebra E A] [Algebra.FiniteType E A]

/-- On the actual finite normalization of an affine algebra of
dimension at least two, every height-one prime avoids some original
algebra generator. If all generators vanished, its residue field would
be algebraic over the original constants, contradicting divisor dimension. -/
theorem normalization_divisor_avoids_some_original_generator
    {σ : Type*} (z : σ → A) (hgen : Algebra.adjoin E (Set.range z) = ⊤)
    (htr : 2 ≤ Algebra.trdeg E A)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1) :
    ∃ i, algebraMap A (normalizationRing A) (z i) ∉ Q := by
  classical
  by_contra hnone
  push Not at hnone
  let L := FractionRing (normalizationRing A ⧸ Q)
  have hdim : 1 ≤ Algebra.trdeg E L := normalization_divisor_residue_trdeg_at_least_one htr Q hQ
  have hz (i : σ) : algebraMap A L (z i) = 0 := by
    have hm := congrArg (fun J : Ideal (normalizationRing A) =>
      algebraMap A (normalizationRing A) (z i) ∈ J) (prime_quotient_fraction_algebraMap_ker Q)
    have he : algebraMap (normalizationRing A) L
        (algebraMap A (normalizationRing A) (z i)) = 0 := hm.to_iff.mpr (hnone i)
    exact (normalization_prime_residue_source_value Q (z i)).symm.trans he
  let : Algebra.IsAlgebraic E L := normalization_prime_residue_fraction_field_isAlgebraic
    (E := E) (J := E) Q z hgen (fun c => isAlgebraic_algebraMap c) (fun i => by
      rw [hz i]
      exact isAlgebraic_zero)
  have hzero : Algebra.trdeg E L = 0 := trdeg_eq_zero
  rw [hzero] at hdim
  exact one_ne_zero (le_antisymm hdim zero_le)

end DimensionFourDependence
