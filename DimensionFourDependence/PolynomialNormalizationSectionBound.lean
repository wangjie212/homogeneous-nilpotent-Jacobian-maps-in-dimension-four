import DimensionFourDependence.PolynomialNormOrderBound
import DimensionFourDependence.RationalNormDegree
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # The projection-degree bound for a general regular normalization section

The section is an arbitrary element of the actual polynomial-ring
normalization in its specified finite function field. Its regularity in
the infinity frame constructs the norm-degree bound. The relative ideal
norm then bounds its local order at every finite normalization prime.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k L : Type u} [Field k] [CharZero k] [Field L]
  [Algebra (RatFunc k) L] [Module.Finite (RatFunc k) L]
  [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- On the actual normalization of the polynomial base in its specified
finite function field, every nonzero regular section that is regular in
the infinity frame has local order at most the actual field degree.
No assumption that the section is an original linear form is used. -/
theorem polynomial_normalization_section_order_le_projection_degree
    (p : Polynomial k) (hp : Irreducible p)
    (q : Ideal (integralClosure (Polynomial k) L)) [q.IsPrime]
    [q.LiesOver (Ideal.span {p})]
    (z : integralClosure (Polynomial k) L) (hz : z ≠ 0)
    (hinfinity : IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * (z : L)))
    (a : ℕ) (horder : algebraMap (integralClosure (Polynomial k) L)
      (Localization.AtPrime q) z ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) :
    a ≤ Module.finrank (RatFunc k) L := by
  let R := Polynomial k
  let K := RatFunc k
  let S := integralClosure R L
  let : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  let : Module.Finite R S := IsIntegralClosure.finite R K L S
  let : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain R K L S
  let : Module.Free R S := IsIntegralClosure.module_free R K L S
  have hzL : (z : L) ≠ 0 := by
    intro hzero
    exact hz (Subtype.ext hzero)
  obtain ⟨P, hP0, hP, hdegree⟩ := field_norm_polynomial_degree_le_of_two_regularities
    (z : L) hzL z.property hinfinity
  have hnorm : algebraMap R K (Algebra.norm R z) = Algebra.norm K (z : L) := by
    rw [← Algebra.intNorm_eq_norm]
    exact Algebra.algebraMap_intNorm (A := R) (K := K) (L := L) (B := S) z
  have hpoly : Algebra.norm R z = P :=
    (IsFractionRing.injective R K) (hnorm.trans hP.symm)
  have hlocal := polynomial_normalization_local_order_le_norm_degree p hp q z hz a horder
  rw [hpoly] at hlocal
  exact hlocal.trans hdegree

end DimensionFourDependence
