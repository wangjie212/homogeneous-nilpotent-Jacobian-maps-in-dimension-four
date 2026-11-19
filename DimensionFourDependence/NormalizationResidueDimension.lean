import DimensionFourDependence.NormalizationResidueCoordinateField
import DimensionFourDependence.AffineMaximalHeight

/-! # Normalization divisors on affine surfaces have nonalgebraic residue fields -/

namespace DimensionFourDependence

universe u

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- The actual residue fraction field of a height-one normalization
prime on a finite-type surface has a transcendental element over the
coefficient field. A maximal contraction is excluded by the original
surface dimension, not assumed absent. -/
theorem normalization_divisor_residue_trdeg_at_least_one
    (htr : 2 ≤ Algebra.trdeg k A)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1) :
    1 ≤ Algebra.trdeg k (FractionRing (normalizationRing A ⧸ Q)) := by
  let S := normalizationRing A
  let B := S ⧸ Q
  let L := FractionRing B
  let : Module.Finite A S := normalizationRing_finite A (K := k)
  let : Algebra.FiniteType k S :=
    (inferInstance : Algebra.FiniteType k A).trans (inferInstance : Algebra.FiniteType A S)
  have htrS : 2 ≤ Algebra.trdeg k S := htr.trans
    (trdeg_le_of_injective (IsScalarTower.toAlgHom k A S)
      (FaithfulSMul.algebraMap_injective A S))
  have hnot := height_one_prime_not_isMaximal_finiteType (k := k) htrS Q hQ
  apply Cardinal.one_le_iff_ne_zero.mpr
  intro hz
  let : Algebra.IsAlgebraic k L := trdeg_eq_zero_iff.mp hz
  let : Algebra.IsAlgebraic k B := Algebra.IsAlgebraic.of_injective
    (IsScalarTower.toAlgHom k B L) (IsFractionRing.injective B L)
  apply hnot
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mpr
    (isField_of_isIntegral_of_isField' (R := k) (S := B)
      (inferInstance : Field k).toIsField)

end DimensionFourDependence
