import DimensionFourDependence.TensorPencilCanonicalSectionMultiplicity
import DimensionFourDependence.OriginalChartSectionStalkTransport
import DimensionFourDependence.GlobalPencilHyperplaneMultiplicity
import DimensionFourDependence.ProjectiveAffineRatioCoordinates

/-! # Original normalized-frame section bounds in the actual global pencil stalk

The canonical original-chart section coefficient supplies its actual
global normalization germ through the original tensor affine atlas.
Intrinsic codimension one selects the original height-one normalization
prime. The original pencil degree bounds every such nonzero coefficient's
order in that actual global stalk.
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

/-- The original pencil degree bounds arbitrary original-normalized-frame
section coefficients in their actual global normalization stalk. The
canonical coefficient supplies the germ; the intrinsic global point
supplies its divisor height. No auxiliary local value or projection data
is assumed. -/
theorem actual_global_pencil_original_chart_section_order_le_degree
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (Q : PrimeSpectrum N₀) (hcodim : Order.coheight (zₑ Q) = 1) :
    let : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
    let : Field (FractionRing T₀) := inferInstance
    ∀ (x : Fin 4 → FractionRing T₀)
      (sectionValue : ProjectiveNormalizedSection (k := E) x)
      (hbase : x (s.symm none) ≠ 0)
      (hratios : projectiveAffineRatioCoordinates x s =
        (fun i => algebraMap T₀ (FractionRing T₀) (originalTensorPencilCoordinate H I E s i)))
      (_hsection : (sectionValue.coefficient (s.symm none) : FractionRing T₀) ≠ 0)
      (a : ℕ)
      (_horder : originalChartSectionStalkGerm Q.asIdeal
        (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s Q)
        (originalTensorPencilCoordinate H I E s) x sectionValue s hbase hratios ∈
          (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ Q))) ^ a), a ≤ D := by
  let A := T₀
  let : IsDomain A := original_tensor_pencil_chart_isDomain H I E s
  let : Field (FractionRing A) := inferInstance
  dsimp only
  intro x sectionValue hbase hratios hsection a horder
  let β := extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s Q
  have hlocal := (original_chart_section_stalk_order_iff Q.asIdeal β
    (originalTensorPencilCoordinate H I E s) x sectionValue s hbase hratios a).mp horder
  have hQ := extendedClosedGaussNormalizationTensorChartPoint_height_one H I E hH e s Q hcodim
  exact @actual_original_tensor_pencil_canonical_section_order_le_degree K
    (inferInstance : Field K) (inferInstance : CharZero K) H I E
    (inferInstance : Field E) (inferInstance : Algebra C₀ E)
    (inferInstance : Algebra.IsAlgebraic C₀ E) d hH e hGauss
    p q D hq0 hrel hpH hqH ht s Q.asIdeal inferInstance hQ
    x sectionValue hbase hratios hsection a hlocal

end DimensionFourDependence
