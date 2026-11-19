import DimensionFourDependence.PolynomialNormalizationSectionBound
import DimensionFourDependence.DedekindLocalOverring
import DimensionFourDependence.SourceLocalNormalization
import DimensionFourDependence.LocalEquivOrderTransport

/-! # Arbitrary section orders in the given normal geometric local ring

The polynomial normalization prime and its local-ring comparison are
constructed from the given local ring and the common function field.
The resulting bound applies to the given section value itself, without
assuming a coordinate expression or supplying an auxiliary local model.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k B L : Type u} [Field k] [CharZero k]
  [CommRing B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Field L] [Algebra (RatFunc k) L] [Module.Finite (RatFunc k) L]
  [Algebra (Polynomial k) B] [Algebra (Polynomial k) L]
  [Algebra B L] [IsFractionRing B L]
  [IsScalarTower (Polynomial k) (RatFunc k) L]
  [IsScalarTower (Polynomial k) B L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- A nonzero section regular over the finite base and in the infinity
frame has order at most the actual projection degree in the given normal
local ring. Its polynomial-normalization prime and local comparison are
constructed from that ring, and every section value is preserved. -/
theorem normal_local_section_order_le_projection_degree
    (p : Polynomial k) (hp : Irreducible p)
    (hpB : algebraMap (Polynomial k) B p ∈ IsLocalRing.maximalIdeal B)
    (b : B) (hb : b ≠ 0)
    (hfinite : IsIntegral (Polynomial k) (algebraMap B L b))
    (hinfinity : IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * algebraMap B L b))
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ Module.finrank (RatFunc k) L := by
  let R := Polynomial k
  let K := RatFunc k
  let S := integralClosure R L
  let : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  let : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr
    (IsFractionRing.injective B L)
  let : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain R K L S
  let : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let g : S →ₐ[R] B := integralClosureToNormalLocalHom (S := R) (A := B) (F := L)
  let : Algebra S B := g.toRingHom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  let : IsScalarTower S B L := IsScalarTower.of_algebraMap_eq (fun z =>
    (integralClosureToNormalLocalHom_source (S := R) (A := B) (F := L) z).symm)
  let q : Ideal S := (IsLocalRing.maximalIdeal B).under S
  let : q.IsPrime := inferInstance
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  have hbase : Ideal.span {p} = (IsLocalRing.maximalIdeal B).under R := by
    apply Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance)
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact hpB
  let : q.LiesOver (Ideal.span {p}) := (Ideal.liesOver_iff q (Ideal.span {p})).mpr (by
    change Ideal.span {p} = ((IsLocalRing.maximalIdeal B).under S).under R
    rw [Ideal.under_under]
    exact hbase)
  have hq0 : q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero) q
  let e := dedekindLocalOverringEquiv (S := S) (B := B) L q rfl hq0
  let z : S := ⟨algebraMap B L b, hfinite⟩
  have hz : z ≠ 0 := by
    intro hzero
    apply hb
    apply IsFractionRing.injective B L
    exact (congrArg Subtype.val hzero).trans (map_zero _).symm
  have hgb : g z = b := by
    apply IsFractionRing.injective B L
    exact integralClosureToNormalLocalHom_source (S := R) (A := B) (F := L) z
  have hmodel : algebraMap S (Localization.AtPrime q) z ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a := by
    apply (local_equiv_maximalIdeal_pow_mem_iff e.toRingEquiv _ a).mp
    change e (algebraMap S (Localization.AtPrime q) z) ∈ (IsLocalRing.maximalIdeal B) ^ a
    rw [e.commutes]
    exact Eq.mp (congrArg (fun t : B => t ∈ (IsLocalRing.maximalIdeal B) ^ a) hgb.symm) horder
  exact polynomial_normalization_section_order_le_projection_degree p hp q z hz hinfinity a hmodel

end DimensionFourDependence
