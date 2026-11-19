import DimensionFourDependence.TensorPencilResidueDimension
import DimensionFourDependence.AffinePointFieldDimension

/-! # Moving-plane incidence forces actual pencil divisor source fields to vary in dimension two -/

namespace DimensionFourDependence

universe u

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra
  tensorPencilResidueGenerationClosedAlgebra tensorPencilResidueGenerationClosedSMul
  tensorPencilResidueGenerationExtendedSMul tensorPencilResidueGenerationClosedTower
  tensorPencilResidueGenerationOriginalSMul tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "M₀" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "T₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none) ⊗[C₀] E

noncomputable local instance (priority := 2000) tensorPencilResiduePointAddCommMonoid
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] :
    AddCommMonoid (FractionRing (normalizationRing (T₀ s) ⧸ Q)) :=
  (normalizationPrimeResidueFieldInstance Q).toAddCommGroup.toAddCommMonoid

noncomputable local instance (priority := 2000) tensorPencilResiduePointSemiring
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] :
    Semiring (FractionRing (normalizationRing (T₀ s) ⧸ Q)) :=
  (normalizationPrimeResidueFieldInstance Q).toSemiring

noncomputable local instance (priority := 2000) tensorPencilResiduePointOriginalModule
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] :
    Module K (FractionRing (normalizationRing (T₀ s) ⧸ Q)) :=
  @Algebra.toModule K (FractionRing (normalizationRing (T₀ s) ⧸ Q)) _ _
    (originalTensorPencilResidueOriginalAlgebra H I E s Q)

noncomputable local instance (priority := 2000) tensorPencilResiduePointOriginalMulAction
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] :
    MulAction K (FractionRing (normalizationRing (T₀ s) ⧸ Q)) :=
  (tensorPencilResiduePointOriginalModule H I E s Q).toDistribMulAction.toMulAction

/-- At an actual height-one prime on an original tensor normalization
chart, incidence in a polynomial plane family with at most one fixed
projective point forces the actual source point field to have dimension
at least two. The family field dimension, its algebraicity over the point
and Gauss parameter, and projective coordinate generation are all proved
from the original map and the actual prime. -/
theorem original_tensor_pencil_divisor_moving_plane_source_field_dimension
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1)
    (e₀ : RatFunc K ≃ₐ[K] M₀) (v : Fin 4 → Polynomial K)
    (hdim : Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hplane : ∑ i, (s i).elim 1 (originalTensorPencilResidueCoordinate H I E s Q) *
      Polynomial.aeval (originalTensorPencilResidueGaussParameter H I E s Q e₀) (v i) = 0) :
    IsAlgebraic (originalTensorPencilResiduePointField H I E s Q)
        (originalTensorPencilResidueGaussParameter H I E s Q e₀) ∧
      Algebra.trdeg K (originalTensorPencilResiduePointField H I E s Q) =
        Algebra.trdeg K (FractionRing (normalizationRing (T₀ s) ⧸ Q)) ∧
      2 ≤ Algebra.trdeg K (originalTensorPencilResiduePointField H I E s Q) := by
  let : Algebra.IsAlgebraic
      (IntermediateField.adjoin
        (IntermediateField.adjoin K (Set.range (originalTensorPencilResidueCoordinate H I E s Q)))
        {originalTensorPencilResidueGaussParameter H I E s Q e₀})
      (FractionRing (normalizationRing (T₀ s) ⧸ Q)) :=
    original_tensor_pencil_residue_isAlgebraic_over_point_and_parameter H I E s Q e₀
  exact affine_point_field_dimension_of_moving_plane
    (originalTensorPencilResidueCoordinate H I E s Q) s v hdim
    (originalTensorPencilResidueGaussParameter H I E s Q e₀)
    (original_tensor_pencil_divisor_residue_trdeg_at_least_two H I E hH e hGauss s Q hQ) hplane

end DimensionFourDependence
