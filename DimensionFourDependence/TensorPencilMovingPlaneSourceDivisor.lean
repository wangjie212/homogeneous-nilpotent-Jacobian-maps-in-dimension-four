import DimensionFourDependence.TensorPencilResidueSourcePrime
import DimensionFourDependence.TensorPencilResidueDimensionExact
import DimensionFourDependence.ProjectiveSourceImageDivisor
import DimensionFourDependence.ExtendedGaussSourcePoint

/-! # Actual moving-plane incidence gives a source divisor at every pencil divisor prime -/

namespace DimensionFourDependence

universe u

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra tensorPencilResidueGenerationClosedAlgebra
  tensorPencilResidueGenerationClosedSMul tensorPencilResidueGenerationExtendedSMul
  tensorPencilResidueGenerationClosedTower tensorPencilResidueGenerationOriginalSMul
  tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra
attribute [local instance 2000] tensorPencilResiduePointAddCommMonoid
  tensorPencilResiduePointSemiring tensorPencilResiduePointOriginalModule
  tensorPencilResiduePointOriginalMulAction

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "M₀" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "T₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none) ⊗[C₀] E

/-- Actual polynomial moving-plane incidence makes the original
source contraction of every actual tensor normalization divisor a
height-one prime. Source codimension is a conclusion, rather than an
additional field or geometric image hypothesis. -/
theorem original_tensor_pencil_divisor_moving_plane_source_prime_height_one
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1)
    (e₀ : RatFunc K ≃ₐ[K] M₀) (v : Fin 4 → Polynomial K)
    (hdim : Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hplane : ∑ i, (s i).elim 1 (originalTensorPencilResidueCoordinate H I E s Q) *
      Polynomial.aeval (originalTensorPencilResidueGaussParameter H I E s Q e₀) (v i) = 0) :
    (Q.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)).height = 1 := by
  have hF := original_tensor_pencil_divisor_moving_plane_source_field_trdeg_eq_two
    H I E hH e hGauss s Q hQ e₀ v hdim hplane
  have hp := coordinate_relation_prime_height_one_of_generated_field_trdeg_two
    (originalTensorPencilResidueCoordinate H I E s Q) hF
  exact (original_tensor_pencil_residue_source_prime_height_eq H I E s Q).trans hp

/-- The actual affine source-image closure of a normalization
divisor satisfying moving-plane incidence is an irreducible source
hypersurface. Its equation and the image assertion are both derived. -/
theorem original_tensor_pencil_divisor_moving_plane_source_image_hypersurface
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1)
    (e₀ : RatFunc K ≃ₐ[K] M₀) (v : Fin 4 → Polynomial K)
    (hdim : Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hplane : ∑ i, (s i).elim 1 (originalTensorPencilResidueCoordinate H I E s Q) *
      Polynomial.aeval (originalTensorPencilResidueGaussParameter H I E s Q e₀) (v i) = 0) :
    ∃ δ : MvPolynomial (Fin 3) K, Irreducible δ ∧
      projectiveSourceChartImageClosure s (extendedClosedGaussTensorNormalizationSourceHom H I E s) Q =
        PrimeSpectrum.zeroLocus
          (Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ} :
            Set (projectiveCoordinateChartAlgebra (C := K)
              (rationalCoordinate (K := K) (n := 4)) (s.symm none))) :=
  (projective_source_image_divisor_iff_height_one s
    (extendedClosedGaussTensorNormalizationSourceHom H I E s) Q).mpr
      (original_tensor_pencil_divisor_moving_plane_source_prime_height_one
        H I E hH e hGauss s Q hQ e₀ v hdim hplane)

/-- The same derived codimension-one condition holds at the actual
projective source image of the actual global tensor normalization point. -/
theorem original_tensor_pencil_divisor_moving_plane_global_source_height_one
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (q : PrimeSpectrum (normalizationRing (T₀ s))) (hq : q.asIdeal.height = 1)
    (e₀ : RatFunc K ≃ₐ[K] M₀) (v : Fin 4 → Polynomial K)
    (hdim : Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hplane : ∑ i, (s i).elim 1 (originalTensorPencilResidueCoordinate H I E s q.asIdeal) *
      Polynomial.aeval (originalTensorPencilResidueGaussParameter H I E s q.asIdeal e₀) (v i) = 0) :
    ((Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
      (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)).primeIdealOf
        ⟨extendedClosedGaussNormalizationSourceMorphism H I E hH e
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q),
          extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1 :=
  (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff H I E hH e s q).mpr
    (original_tensor_pencil_divisor_moving_plane_source_prime_height_one
      H I E hH e hGauss s q.asIdeal hq e₀ v hdim hplane)

end DimensionFourDependence
