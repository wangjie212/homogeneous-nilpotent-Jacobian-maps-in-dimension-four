import DimensionFourDependence.ExtendedGaussPointAtlas
import DimensionFourDependence.GlobalSourceCodimension

/-! # Actual source orders at every global normalization point

The source-divisor hypothesis is intrinsic: the actual original
projective source stalk has dimension one. No chart prime or affine
height comparison is supplied by the caller.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e

/-- The actual source-image stalk is a domain at every global point. -/
theorem extendedClosedGaussNormalizationPoint_source_stalk_isDomain
    (y : Nₑ) : IsDomain ((Pₖ).presheaf.stalk ((mₑ) y)) := by
  obtain ⟨a, q, rfl⟩ := extendedClosedGaussNormalizationPoint_exists_tensor_prime H I E hH e y
  exact extendedClosedGaussNormalization_source_stalk_isDomain H I E hH e (finSuccEquiv' a) q

/-- The actual normalization stalk is a domain at every global point. -/
theorem extendedClosedGaussNormalizationPoint_stalk_isDomain
    (y : Nₑ) : IsDomain ((Nₑ).presheaf.stalk y) := by
  let : IsIntegral Nₑ := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
  infer_instance

/-- Intrinsic codimension one makes the actual source-image stalk a DVR,
at an arbitrary point of the global normalization. -/
theorem extendedClosedGaussNormalizationPoint_source_stalk_isDVR
    (y : Nₑ) (hdim : ringKrullDim ((Pₖ).presheaf.stalk ((mₑ) y)) = 1) :
    letI : IsDomain ((Pₖ).presheaf.stalk ((mₑ) y)) :=
      extendedClosedGaussNormalizationPoint_source_stalk_isDomain H I E hH e y
    IsDiscreteValuationRing ((Pₖ).presheaf.stalk ((mₑ) y)) := by
  obtain ⟨a, q, rfl⟩ := extendedClosedGaussNormalizationPoint_exists_tensor_prime H I E hH e y
  have hheight := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff
    H I E hH e (finSuccEquiv' a) q).mp hdim
  exact extendedClosedGaussNormalization_source_stalk_isDiscreteValuationRing
    H I E hH e (finSuccEquiv' a) q hheight

/-- All locally regular source functions retain every order bound at
every global normalization point lying over an original source divisor. -/
theorem actual_global_point_source_stalk_regular_order_iff
    [Module.Finite (closedGaussParameterField H I) E]
    (y : Nₑ) (hdim : ringKrullDim ((Pₖ).presheaf.stalk ((mₑ) y)) = 1)
    (z : (Pₖ).presheaf.stalk ((mₑ) y)) (n : ℕ) :
    (mₑ).stalkMap y z ∈ (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk y)) ^ n ↔
      z ∈ (IsLocalRing.maximalIdeal ((Pₖ).presheaf.stalk ((mₑ) y))) ^ n := by
  obtain ⟨a, q, rfl⟩ := extendedClosedGaussNormalizationPoint_exists_tensor_prime H I E hH e y
  have hheight := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff
    H I E hH e (finSuccEquiv' a) q).mp hdim
  exact actual_global_projective_source_stalk_regular_order_iff
    H I E hH e (finSuccEquiv' a) q hheight z n

end DimensionFourDependence
