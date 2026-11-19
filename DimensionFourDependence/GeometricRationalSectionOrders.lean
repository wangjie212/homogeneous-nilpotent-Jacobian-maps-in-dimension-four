import DimensionFourDependence.GeometricRationalSourceOrders
import DimensionFourDependence.FramedRationalStalkComparison

/-! # Geometric rational-section orders in every compatible local frame

At the actual source-image divisor, every regular local-frame transition
unit lies in the actual source stalk. The constructed rational pullback
has the same normalized order in every such frame.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "N₀" => normalizationRing (S₀ ⊗[C₀] E)
local notation "L₀" => projectiveCoordinateChartField (C := K) x₀ (s.symm none)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Q₀" q:max => extendedClosedGaussTensorNormalizationSourcePrime H I E s q
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- Every original rational source coefficient has its original divisor
order after actual global geometric pullback, in every compatible regular
local frame. The source-divisor hypothesis is imposed on the actual
projective source-image point, and the target global stalk is a DVR. -/
theorem actual_global_projective_source_rational_section_orders
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀)
    (hheight : ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1) :
    let hheight' := extendedClosedGaussNormalization_source_image_height_one H I E hH e s q hheight
    letI : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
      projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight'
    letI : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
    letI : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
    letI : IsDomain ((Nₑ).presheaf.stalk (zₑ q)) := extendedClosedGaussNormalization_global_stalk_isDomain H I E hH e s q
    FramedRationalStalkPullbackComparison
      (S := (Pₖ).presheaf.stalk ((mₑ) (zₑ q))) (O := Localization.AtPrime (Q₀ q).asIdeal)
      (A := (Nₑ).presheaf.stalk (zₑ q)) (F := L₀)
      (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q)
      ((mₑ).stalkMap (zₑ q)).hom := by
  let hheight' := extendedClosedGaussNormalization_source_image_height_one H I E hH e s q hheight
  let : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
    projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight'
  let : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
  let : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
  let : IsDomain ((Nₑ).presheaf.stalk (zₑ q)) := extendedClosedGaussNormalization_global_stalk_isDomain H I E hH e s q
  have hraw := actual_global_projective_source_rational_stalk_orders H I E hH e s q hheight
  rcases hraw with ⟨hdvr, j, hj, hv⟩
  let : IsDiscreteValuationRing ((Nₑ).presheaf.stalk (zₑ q)) := hdvr
  let : Algebra ((Nₑ).presheaf.stalk (zₑ q)) (FractionRing ((Nₑ).presheaf.stalk (zₑ q))) := OreLocalization.instAlgebra
  refine ⟨hdvr, j, hj, ?_⟩
  intro v w
  refine ⟨hv, ?_⟩
  intro u x
  exact rational_section_pullback_order_change_frame
    (O := Localization.AtPrime (Q₀ q).asIdeal) (F := L₀)
    (L := FractionRing ((Nₑ).presheaf.stalk (zₑ q))) v
    (w.valuation (FractionRing ((Nₑ).presheaf.stalk (zₑ q)))) j hv
    (u.map (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q).toMonoidHom) x

end DimensionFourDependence
