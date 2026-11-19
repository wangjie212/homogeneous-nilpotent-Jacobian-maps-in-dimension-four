import DimensionFourDependence.AffineSourceConeForm

/-! # Actual affine source identities extend across the pencil base

The source fraction field inverts the original pencil denominator, but
its polynomial relations are exactly the extended principal pencil
ideal. Every such identity therefore restricts to the entire original
base V(p,q), even where that denominator vanishes. This is the bridge
needed to restrict the scaled-plane power identity to the base curve.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₜ" => extendedClosedGaussSourceTensorCoordinate H I E
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

local instance affinePencilBaseRelationsDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

variable (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : MvPolynomial (Fin 4) K)
    (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)

include e hq hrel hparameter

/-- Every polynomial identity in the actual affine tensor source
belongs to the original coefficient-extended base ideal. -/
theorem affine_tensor_relation_mem_pencil_base_ideal
    (P : MvPolynomial (Fin 4) E) (hP : aeval (xₐ) P = 0) :
    P ∈ Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
      Set (MvPolynomial (Fin 4) E)) := by
  have ht : aeval (xₜ) P = 0 := by
    apply IsFractionRing.injective T₀ F₀
    have he := comp_aeval_apply (xₜ) (IsScalarTower.toAlgHom E T₀ F₀) P
    change algebraMap T₀ F₀ (aeval (xₜ) P) = aeval (xₐ) P at he
    rw [he, hP, map_zero]
  have hmem := (extendedClosedGaussSourceTensorCoordinate_zero_iff H I E P).mp ht
  have hJ : extendedClosedGaussPencilIdeal H I E =
      Ideal.span {MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilEquation H I e p q)} := by
    change (fiberVanishingIdeal (L := C₀) (rationalCoordinate (K := K) (n := 4))).map
      (MvPolynomial.map (algebraMap C₀ E)) = _
    rw [actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel hparameter,
      Ideal.map_span, Set.image_singleton]
  rw [hJ] at hmem
  apply (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)) hmem
  have he : MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilEquation H I e p q) =
      MvPolynomial.map (ι) p - C (algebraMap C₀ E (e RatFunc.X)) * MvPolynomial.map (ι) q := by
    rw [closedGaussPencilEquation_eq]
    simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_map]
    rfl
  rw [he]
  exact Ideal.sub_mem _ (Ideal.subset_span (by simp))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- An actual polynomial source identity vanishes at every point
of the coefficient-extended pencil base, including denominator zeros. -/
theorem affine_tensor_relation_vanishes_at_pencil_base
    {L : Type*} [CommRing L] [Algebra E L]
    (P : MvPolynomial (Fin 4) E) (hP : aeval (xₐ) P = 0)
    (ψ : MvPolynomial (Fin 4) E →ₐ[E] L)
    (hpψ : ψ (MvPolynomial.map (ι) p) = 0)
    (hqψ : ψ (MvPolynomial.map (ι) q) = 0) : ψ P = 0 := by
  have hmem := affine_tensor_relation_mem_pencil_base_ideal H I E e p q hq hrel hparameter P hP
  apply (show Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
      Set (MvPolynomial (Fin 4) E)) ≤ RingHom.ker ψ.toRingHom from ?_) hmem
  apply Ideal.span_le.mpr
  intro Q hQ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
  rcases hQ with rfl | rfl
  · exact hpψ
  · exact hqψ

/-- The scaled-plane output power identity restricts to the entire
original coefficient-extended base without assuming a nonzero source
pencil denominator there. -/
theorem affine_scaled_plane_power_identity_on_pencil_base
    (S L : MvPolynomial (Fin 4) E) (a : E) (d : ℕ)
    (hpower : aeval (xₐ) S = algebraMap E F₀ a * (aeval (xₐ) L) ^ d)
    {F : Type*} [CommRing F] [Algebra E F]
    (ψ : MvPolynomial (Fin 4) E →ₐ[E] F)
    (hpψ : ψ (MvPolynomial.map (ι) p) = 0)
    (hqψ : ψ (MvPolynomial.map (ι) q) = 0) :
    ψ S = algebraMap E F a * (ψ L) ^ d := by
  have hz : aeval (xₐ) (S - C a * L ^ d) = 0 := by
    simp only [map_sub, map_mul, aeval_C, map_pow, hpower, sub_self]
  have he := affine_tensor_relation_vanishes_at_pencil_base
    H I E e p q hq hrel hparameter (S - C a * L ^ d) hz ψ hpψ hqψ
  have hψC : ψ (C a) = algebraMap E F a := ψ.commutes a
  simpa only [map_sub, map_mul, map_pow, hψC, sub_eq_zero] using he

end DimensionFourDependence
