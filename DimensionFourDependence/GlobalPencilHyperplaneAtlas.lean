import DimensionFourDependence.GlobalPencilHyperplaneMultiplicity
import DimensionFourDependence.ExtendedGaussPointAtlas

/-! # Hyperplane order bounds at every actual global codimension-one point

The original tensor affine atlas supplies the coordinate frame and prime
for every point. The same frame simultaneously bounds the orders of all
nonzero extended-field hyperplane sections; no chart choice or prime
representation is required from the caller.
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

local notation "C₀" => closedGaussParameterField H I
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "S₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm (finSuccEquiv' a) none)

/-- Every actual codimension-one normalization point has an original
coordinate frame in which every nonzero hyperplane section has order
bounded by the actual pencil degree. The frame and prime are constructed
from the global affine cover and work for all hyperplanes simultaneously. -/
theorem actual_global_pencil_point_exists_hyperplane_order_bounds
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (y : Nₑ) (hcodim : Order.coheight y = 1) :
    ∃ (i : Fin 4) (Q : PrimeSpectrum (normalizationRing (S₀ i ⊗[C₀] E))),
      extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' i) Q = y ∧
        ∀ (b : E) (c : Fin 3 → E),
          originalTensorPencilHyperplaneValue H I E (finSuccEquiv' i) b c ≠ 0 →
            ∀ a : ℕ,
              extendedClosedGaussNormalizationHyperplaneGerm H I E hH e (finSuccEquiv' i) Q b c ∈
                (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk
                  (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' i) Q))) ^ a →
              a ≤ D := by
  obtain ⟨i, Q, hy⟩ := extendedClosedGaussNormalizationPoint_exists_tensor_prime H I E hH e y
  refine ⟨i, Q, hy, ?_⟩
  intro b c hz0 a horder
  have hcodimQ : Order.coheight
      (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' i) Q) = 1 :=
    (congrArg (fun z : Nₑ => Order.coheight z) hy).trans hcodim
  exact actual_global_normalized_pencil_hyperplane_order_le_degree H I E hH e (finSuccEquiv' i)
    hGauss p q hq0 hrel hpH hqH ht Q hcodimQ b c hz0 a horder

end DimensionFourDependence
