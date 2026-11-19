import DimensionFourDependence.GlobalOriginalSectionMultiplicity
import DimensionFourDependence.NormalizedHyperplaneGluing
import DimensionFourDependence.ExtendedNormalizationDivisorDvr
import DimensionFourDependence.RegularSectionIntegerMultiplicity
import DimensionFourDependence.OriginalSectionGermNonzero

/-! # Actual integer multiplicities of hyperplane sections glued on normalized overlaps

The section is supplied by regular original-chart coefficients glued by
the actual overlap transition units. Its actual global stalk germ is
nonzero, its intrinsic divisor stalk is a DVR, and its integer order in
the scheme's own function field lies between zero and the pencil degree.
-/

namespace DimensionFourDependence

universe u

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
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
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q

/-- A nonzero section glued by the actual hyperplane transition units
has actual integer divisor multiplicity between zero and the original
pencil degree in the normalized pencil's own scheme function field. All
DVR, local-value, projection and maximal-ideal order data are derived. -/
theorem actual_global_pencil_glued_hyperplane_integer_multiplicity_bound
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (Q : PrimeSpectrum N₀) (hcodim : Order.coheight (zₑ Q) = 1) :
    let : IsIntegral Nₑ := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
    let : IsNoetherian Nₑ := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
    let : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
    let : Field (FractionRing T₀) := inferInstance
    ∀ (x : Fin 4 → FractionRing T₀) (hx : ∀ i, x i ≠ 0)
      (sectionValue : NormalizedHyperplaneGluingSection (k := E) x hx)
      (hbase : x (s.symm none) ≠ 0)
      (hratios : projectiveAffineRatioCoordinates x s =
        (fun i => algebraMap T₀ (FractionRing T₀) (originalTensorPencilCoordinate H I E s i)))
      (_hsection : (sectionValue.coefficient (s.symm none) : FractionRing T₀) ≠ 0),
      let z := originalChartSectionStalkGerm Q.asIdeal
        (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s Q)
        (originalTensorPencilCoordinate H I E s) x sectionValue.toProjective s hbase hratios
      0 ≤ (Nₑ).ord (algebraMap ((Nₑ).presheaf.stalk (zₑ Q)) (Nₑ).functionField z) (zₑ Q) ∧
        (Nₑ).ord (algebraMap ((Nₑ).presheaf.stalk (zₑ Q)) (Nₑ).functionField z) (zₑ Q) ≤ (D : ℤ) := by
  let X := Nₑ
  let y := zₑ Q
  let : IsIntegral X := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
  let : IsNoetherian X := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
  let : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
  let : Field (FractionRing T₀) := inferInstance
  let : IsDiscreteValuationRing (X.presheaf.stalk y) :=
    extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e y hcodim
  dsimp only
  intro x hx sectionValue hbase hratios hsection
  let β := extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s Q
  let z : X.presheaf.stalk y := originalChartSectionStalkGerm Q.asIdeal β
    (originalTensorPencilCoordinate H I E s) x sectionValue.toProjective s hbase hratios
  change 0 ≤ X.ord (algebraMap (X.presheaf.stalk y) X.functionField z) y ∧
    X.ord (algebraMap (X.presheaf.stalk y) X.functionField z) y ≤ (D : ℤ)
  have hz : z ≠ 0 := original_chart_section_stalk_germ_ne_zero Q.asIdeal β
    (originalTensorPencilCoordinate H I E s) x sectionValue.toProjective s hbase hratios hsection
  apply scheme_regular_integer_multiplicity_bounded y hcodim z hz D
  intro a horder
  exact @actual_global_pencil_original_chart_section_order_le_degree K
    (inferInstance : Field K) (inferInstance : CharZero K) H I E
    (inferInstance : Field E) (inferInstance : Algebra C₀ E)
    (inferInstance : Algebra.IsAlgebraic C₀ E) d hH e s hGauss
    p q D hq0 hrel hpH hqH ht Q hcodim
    x sectionValue.toProjective hbase hratios hsection a horder

end DimensionFourDependence
