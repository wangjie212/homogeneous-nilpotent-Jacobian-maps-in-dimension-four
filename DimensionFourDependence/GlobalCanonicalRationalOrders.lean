import DimensionFourDependence.GeometricSourceStalkOrders
import DimensionFourDependence.OriginalSourceCanonicalRationalOrders
import DimensionFourDependence.LocalEquivCanonicalRationalOrders

/-! # Canonical rational source orders in the actual global normalization

The local normalized prime comparison transports to the actual global
normalization stalk through its checked original-coordinate isomorphism.
The resulting source-local map agrees with the entire geometric pullback.
-/

namespace DimensionFourDependence

open AlgebraicGeometry
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
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "L₀" => projectiveCoordinateChartField (C := K) x₀ (s.symm none)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "Pₖ" => AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Q₀" q:max => extendedClosedGaussTensorNormalizationSourcePrime H I E s q

/-- The actual global normalization stalk is a domain, from the
integrality of the normalization formed after coefficient extension. -/
theorem extendedClosedGaussNormalization_global_stalk_isDomain
    (q : PrimeSpectrum N₀) : IsDomain ((Nₑ).presheaf.stalk (zₑ q)) := by
  let : IsIntegral Nₑ := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
  infer_instance

/-- The specified original source-local map into the actual global
normalization stalk, using the actual normalized-coordinate isomorphism. -/
@[irreducible] noncomputable def extendedClosedGaussNormalizationSourceLocalHom
    (q : PrimeSpectrum N₀) :
    Localization.AtPrime (Q₀ q).asIdeal →+* (Nₑ).presheaf.stalk (zₑ q) :=
  (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q).symm.toRingHom.comp
    (Localization.localRingHom (Q₀ q).asIdeal q.asIdeal
      (extendedClosedGaussTensorNormalizationSourceHom H I E s)
      (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q))

/-- This source-local map is the actual geometric source stalk map
on every locally regular source function, in its original coordinates. -/
theorem extendedClosedGaussNormalizationSourceLocalHom_stalkMap
    (q : PrimeSpectrum N₀) (z : (Pₖ).presheaf.stalk ((mₑ) (zₑ q))) :
    extendedClosedGaussNormalizationSourceLocalHom H I E hH e s q
      (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q z) =
        (mₑ).stalkMap (zₑ q) z := by
  have h := congrArg
    (fun x : Localization.AtPrime q.asIdeal =>
      (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q).symm x)
    (extendedClosedGaussNormalizationSourceStalkEquiv_stalkMap H I E hH e s q z)
  unfold extendedClosedGaussNormalizationSourceLocalHom
  change (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q).symm
    (Localization.localRingHom (Q₀ q).asIdeal q.asIdeal
      (extendedClosedGaussTensorNormalizationSourceHom H I E s)
      (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q)
      (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q z)) = _
  simpa only [RingEquiv.symm_apply_apply] using h.symm

/-- The actual global normalization source-local map constructs a
rational pullback preserving every original normalized source valuation.
The actual global normalization stalk is itself a DVR. -/
theorem actual_global_normalization_source_canonical_rational_orders
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀) (hheight : (Q₀ q).asIdeal.height = 1) :
    letI : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
      projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight
    letI : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
    letI : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
    letI : IsDomain ((Nₑ).presheaf.stalk (zₑ q)) := extendedClosedGaussNormalization_global_stalk_isDomain H I E hH e s q
    CanonicalRationalSourceOrderComparison
      (O := Localization.AtPrime (Q₀ q).asIdeal) (A := (Nₑ).presheaf.stalk (zₑ q)) (F := L₀)
      (extendedClosedGaussNormalizationSourceLocalHom H I E hH e s q) := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : IsDomain T₀ := subalgebra_algebraic_base_change_isDomain
    (L := E) (closedGaussParameterField_relatively_closed H I) S₀
  let : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
    projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight
  let : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
  let : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
  let : IsDomain ((Nₑ).presheaf.stalk (zₑ q)) := extendedClosedGaussNormalization_global_stalk_isDomain H I E hH e s q
  have hlocal := actual_tensor_normalization_source_canonical_rational_orders H I E hH e s q hheight
  unfold extendedClosedGaussNormalizationSourceLocalHom
  apply canonical_rational_source_order_comparison_comp
    (O := Localization.AtPrime (Q₀ q).asIdeal) (A := Localization.AtPrime q.asIdeal)
    (B := (Nₑ).presheaf.stalk (zₑ q)) (F := L₀) _ _ hlocal
  intro hdvr
  let : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := hdvr
  let : Algebra (Localization.AtPrime q.asIdeal) (FractionRing (Localization.AtPrime q.asIdeal)) := OreLocalization.instAlgebra
  exact local_equiv_canonical_rational_order_comparison
    (A := (Nₑ).presheaf.stalk (zₑ q)) (B := Localization.AtPrime q.asIdeal)
    (F := FractionRing (Localization.AtPrime q.asIdeal))
    (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q)

end DimensionFourDependence
