import DimensionFourDependence.GlobalPointRegularOrders
import DimensionFourDependence.IntrinsicDivisorPullback

/-! # Intrinsic divisor-order comparison on the entire global normalization

Every point over an original source point of codimension one has the
same regular and rational source orders. This constructs both DVRs and
the source-compatible rational pullback without specifying a chart prime.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e

/-- At every point of the actual global normalization whose source
image has codimension one, the entire geometric source stalk map has
the intrinsic regular, rational and compatible-frame order comparison. -/
theorem actual_global_point_source_divisor_order_comparison
    [Module.Finite (closedGaussParameterField H I) E]
    (y : Nₑ) (hcodim : Order.coheight ((mₑ) y) = 1) :
    IntrinsicDivisorPullbackComparison ((mₑ).stalkMap y).hom := by
  have hdim : ringKrullDim ((Pₖ).presheaf.stalk ((mₑ) y)) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hcodim]
    rfl
  let : IsDomain ((Pₖ).presheaf.stalk ((mₑ) y)) :=
    extendedClosedGaussNormalizationPoint_source_stalk_isDomain H I E hH e y
  let : IsDomain ((Nₑ).presheaf.stalk y) :=
    extendedClosedGaussNormalizationPoint_stalk_isDomain H I E hH e y
  let : IsDiscreteValuationRing ((Pₖ).presheaf.stalk ((mₑ) y)) :=
    extendedClosedGaussNormalizationPoint_source_stalk_isDVR H I E hH e y hdim
  obtain ⟨a, q, rfl⟩ := extendedClosedGaussNormalizationPoint_exists_tensor_prime H I E hH e y
  let s := finSuccEquiv' a
  let z := extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
  let Q := extendedClosedGaussTensorNormalizationSourcePrime H I E s q
  let L := projectiveCoordinateChartField (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  have hheight := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff
    H I E hH e s q).mp hdim
  let hheight' := extendedClosedGaussNormalization_source_image_height_one H I E hH e s q hheight
  let : IsDiscreteValuationRing (Localization.AtPrime Q.asIdeal) :=
    projective_source_height_one_isDVR s Q.asIdeal hheight'
  let : Algebra (Localization.AtPrime Q.asIdeal) L := primeLocalizationFractionAlgebra Q.asIdeal
  let : IsFractionRing (Localization.AtPrime Q.asIdeal) L := projective_source_divisor_isFractionRing s Q.asIdeal
  have hraw := actual_global_projective_source_rational_stalk_orders H I E hH e s q hheight
  have hregular := actual_global_point_source_stalk_regular_order_iff H I E hH e z hdim
  let es : (Pₖ).presheaf.stalk ((mₑ) z) ≃+* Localization.AtPrime Q.asIdeal :=
    extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q
  let g : (Pₖ).presheaf.stalk ((mₑ) z) →+* (Nₑ).presheaf.stalk z := ((mₑ).stalkMap z).hom
  have hraw' : RationalStalkPullbackComparison
    (S := (Pₖ).presheaf.stalk ((mₑ) z)) (O := Localization.AtPrime Q.asIdeal)
    (A := (Nₑ).presheaf.stalk z) (F := L) es g := hraw
  have hregular' : ∀ (x : (Pₖ).presheaf.stalk ((mₑ) z)) (n : ℕ),
      g x ∈ (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk z)) ^ n ↔
        x ∈ (IsLocalRing.maximalIdeal ((Pₖ).presheaf.stalk ((mₑ) z))) ^ n := hregular
  let : Algebra ((Pₖ).presheaf.stalk ((mₑ) z))
      (FractionRing ((Pₖ).presheaf.stalk ((mₑ) z))) := OreLocalization.instAlgebra
  let : Algebra ((Nₑ).presheaf.stalk z)
      (FractionRing ((Nₑ).presheaf.stalk z)) := OreLocalization.instAlgebra
  have hcanonical := @rational_stalk_comparison_intrinsic_source
    ((Pₖ).presheaf.stalk ((mₑ) z)) (Localization.AtPrime Q.asIdeal)
    ((Nₑ).presheaf.stalk z) L
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance es g hraw'
  have hrawIntrinsic := canonical_rational_comparison_to_stalk_pullback
    (S := (Pₖ).presheaf.stalk ((mₑ) z)) (O := (Pₖ).presheaf.stalk ((mₑ) z))
    (A := (Nₑ).presheaf.stalk z) (F := FractionRing ((Pₖ).presheaf.stalk ((mₑ) z)))
    (RingEquiv.refl _) g g (fun _ => rfl) hcanonical
  have hframed := rational_stalk_pullback_comparison_all_frames
    (S := (Pₖ).presheaf.stalk ((mₑ) z)) (O := (Pₖ).presheaf.stalk ((mₑ) z))
    (A := (Nₑ).presheaf.stalk z) (F := FractionRing ((Pₖ).presheaf.stalk ((mₑ) z)))
    (RingEquiv.refl _) g hrawIntrinsic
  exact ⟨inferInstance, inferInstance, inferInstance, hframed, hregular'⟩

end DimensionFourDependence
