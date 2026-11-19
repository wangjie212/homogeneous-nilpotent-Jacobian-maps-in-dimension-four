import DimensionFourDependence.ProjectiveChartPolynomialSections
import DimensionFourDependence.ComponentGenericPoint

/-! # Actual homogeneous equations characterize projective chart germs -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K]

local notation "𝒢" => homogeneousSubmodule (Fin 4) K
local notation "Pₖ" => AlgebraicGeometry.Proj 𝒢
local notation "Uₐ" a:max => Proj.basicOpen 𝒢 (X a)
local notation "hUₐ" a:max => Proj.isAffineOpen_basicOpen 𝒢 (X a) (isHomogeneous_X (R := K) a) (by omega)

/-- Membership of the actual regular polynomial coefficient in
the chart prime is exactly its original homogeneous equation at the
same projective point. -/
theorem projectiveChartPolynomialSection_mem_prime_iff
    (z : ProjectiveSpectrum 𝒢) (a : Fin 4) (ha : X a ∉ z.asHomogeneousIdeal)
    (P : MvPolynomial (Fin 4) K) {D : ℕ} (hP : P.IsHomogeneous D) :
    projectiveChartPolynomialSectionHom K a P ∈ ((hUₐ a).primeIdealOf ⟨z, ha⟩).asIdeal ↔
      P ∈ z.asHomogeneousIdeal := by
  let Q := z.asHomogeneousIdeal.toIdeal
  let : Q.IsPrime := z.isPrime
  let F := FractionRing (MvPolynomial (Fin 4) K ⧸ Q)
  let x : Fin 4 → F := primeQuotientCoordinate Q
  have hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom := by
    exact (primeQuotientCoordinate_relations Q).symm
  have hxa : x a ≠ 0 := by
    intro hz
    apply ha
    have he : aeval (R := K) x (X a) = 0 := (aeval_X x a).trans hz
    change X a ∈ z.asHomogeneousIdeal.toIdeal
    rw [hrel]
    exact he
  let e := projectiveSourceAffineSectionQuotientEquiv x a hxa z hrel ha
  let ψ := projectiveAmbientSectionToSource (C := K) x a hxa
  let S := projectiveChartPolynomialSectionHom K a P
  have hker : S ∈ ((hUₐ a).primeIdealOf ⟨z, ha⟩).asIdeal ↔ ψ S = 0 := by
    have he := projectiveSourceAffineSectionQuotientEquiv_mk x a hxa z hrel ha S
    constructor
    · intro h
      have hz := congrArg e (Ideal.Quotient.eq_zero_iff_mem.mpr h)
      rw [map_zero] at hz
      exact he.symm.trans hz
    · intro h
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply e.injective
      rw [map_zero]
      exact he.trans h
  have hvalue : (ψ S : F) = aeval x P / (x a) ^ D := by
    rw [projectiveChartPolynomialSectionHom_source_value]
    have he : ((aeval (fun i => projectiveChartTransition (C := K) x a i) P :
        projectiveCoordinateChartAlgebra (C := K) x a) : F) =
        aeval (fun i => x i / x a) P := MvPolynomial.comp_aeval_apply
          (fun i => projectiveChartTransition (C := K) x a i)
          (projectiveCoordinateChartAlgebra (C := K) x a).val P
    rw [he]
    have hs := homogeneous_aeval_scale P hP x (x a)⁻¹
    have hc : (fun i => (x a)⁻¹ * x i) = (fun i => x i / x a) := by
      funext i
      rw [div_eq_mul_inv, mul_comm]
    rw [hc] at hs
    rw [hs, div_eq_mul_inv, inv_pow, mul_comm]
  rw [hker]
  have hz : ψ S = 0 ↔ (ψ S : F) = 0 := by
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hz, hvalue, div_eq_zero_iff, or_iff_left (pow_ne_zero D hxa)]
  change aeval x P = 0 ↔ P ∈ z.asHomogeneousIdeal.toIdeal
  rw [hrel]
  rfl

/-- The actual chart coefficient germ vanishes exactly when the
original homogeneous polynomial belongs to the projective point. -/
theorem projectiveChartPolynomialSection_germ_mem_maximal_iff
    (z : ProjectiveSpectrum 𝒢) (a : Fin 4) (ha : X a ∉ z.asHomogeneousIdeal)
    (P : MvPolynomial (Fin 4) K) {D : ℕ} (hP : P.IsHomogeneous D) :
    (Pₖ).presheaf.germ (Uₐ a) z ha (projectiveChartPolynomialSectionHom K a P) ∈
      IsLocalRing.maximalIdeal ((Pₖ).presheaf.stalk z) ↔ P ∈ z.asHomogeneousIdeal := by
  rw [← projectiveChartPolynomialSection_mem_prime_iff z a ha P hP,
    IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  rfl

/-- Actual pullback germs preserve the same polynomial vanishing
test through the local stalk map of the specified geometric morphism. -/
theorem projective_pullback_polynomial_germ_mem_maximal_iff
    (Y : Scheme.{u}) (f : Y ⟶ Pₖ) (y : Y) (a : Fin 4)
    (ha : X a ∉ (f y).asHomogeneousIdeal)
    (P : MvPolynomial (Fin 4) K) {D : ℕ} (hP : P.IsHomogeneous D) :
    Y.presheaf.germ (f ⁻¹ᵁ Uₐ a) y ha
        (projectivePullbackChartPolynomialHom Y f a P) ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ↔ P ∈ (f y).asHomogeneousIdeal := by
  rw [projectivePullbackChartPolynomialHom_eq_app,
    ← Scheme.Hom.germ_stalkMap_apply]
  rw [← projectiveChartPolynomialSection_germ_mem_maximal_iff (f y) a ha P hP]
  change _ ∈ (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (f.stalkMap y).hom ↔ _
  rw [IsLocalRing.maximalIdeal_comap]

end DimensionFourDependence
