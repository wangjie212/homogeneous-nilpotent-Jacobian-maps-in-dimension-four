import DimensionFourDependence.TensorPencilMovingPlaneSourceDivisor
import DimensionFourDependence.ActualGaussPlaneSpecialization

/-! # Actual Gauss-plane incidence forces the original source image to be a divisor -/

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
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "M₀" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[C₀] E

variable (Q : Ideal (normalizationRing
  (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[closedGaussParameterField H I] E)))
  [Q.IsPrime]

local notation "L₀" => FractionRing (normalizationRing T₀ ⧸ Q)
local notation "y₀" => originalTensorPencilResidueCoordinate H I E s Q

/-- The actual Gauss parameter embeds in the actual normalization-prime
residue fraction field through the original closed Gauss constants. -/
noncomputable def originalTensorPencilResidueGaussHom
    (e₀ : RatFunc K ≃ₐ[K] M₀) : RatFunc K →ₐ[K] L₀ :=
  (IsScalarTower.toAlgHom K C₀ L₀).comp
    ((IsScalarTower.toAlgHom K M₀ C₀).comp e₀.toAlgHom)

/-- The rational-parameter homomorphism retains exactly the original
Gauss parameter, rather than an unspecified transcendental element. -/
theorem original_tensor_pencil_residue_gauss_hom_X
    (e₀ : RatFunc K ≃ₐ[K] M₀) :
    originalTensorPencilResidueGaussHom H I E s Q e₀ RatFunc.X =
      originalTensorPencilResidueGaussParameter H I E s Q e₀ := rfl

/-- Its original normal coordinates agree with the first row of the
actual extended Gauss ruling, inside the actual residue field. -/
theorem original_tensor_pencil_residue_gauss_hom_normal
    (e₀ : RatFunc K ≃ₐ[K] M₀) (i : Fin 4) :
    originalTensorPencilResidueGaussHom H I E s Q e₀ (gaussParameterNormal H I e₀ i) =
      algebraMap E L₀ (extendedClosedGaussRulingMatrix H I E e₀ 0 i) := by
  change algebraMap C₀ L₀ (algebraMap M₀ C₀ (e₀ (gaussParameterNormal H I e₀ i))) =
    algebraMap E L₀ (algebraMap C₀ E (algebraMap M₀ C₀ (e₀ (gaussParameterNormal H I e₀ i))))
  exact IsScalarTower.algebraMap_apply C₀ E L₀ _

variable {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
  (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- Actual tangent-plane incidence constructs its own polynomial
representative and constant-intersection bound. No polynomial-family,
normal-span, or coefficient-kernel hypothesis is supplied. -/
theorem original_tensor_pencil_actual_gauss_plane_polynomial_incidence
    (hplane : ∑ i, (s i).elim 1 y₀ *
      algebraMap E L₀ (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0 i) = 0) :
    ∃ v : Fin 4 → Polynomial K,
      Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1 ∧
      ∑ i, (s i).elim 1 y₀ * Polynomial.aeval
        (originalTensorPencilResidueGaussParameter H I E s Q
          (actualGaussRulingParameterChoice H I hH hd hind hGauss)) (v i) = 0 := by
  let e₀ := actualGaussRulingParameterChoice H I hH hd hind hGauss
  have hnormal : ∑ i, (s i).elim 1 y₀ *
      originalTensorPencilResidueGaussHom H I E s Q e₀ (gaussParameterNormal H I e₀ i) = 0 := by
    calc
      _ = ∑ i, (s i).elim 1 y₀ *
          algebraMap E L₀ (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0 i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg ((s i).elim 1 y₀ * ·)
          (original_tensor_pencil_residue_gauss_hom_normal H I E s Q e₀ i)
      _ = 0 := hplane
  exact actual_gauss_plane_polynomial_incidence_of_parameter_embedding H I hH hd hind hGauss
    (originalTensorPencilResidueGaussHom H I E s Q e₀) (fun i => (s i).elim 1 y₀) hnormal

/-- A divisor in the actual tensor normalization lying in the actual
Gauss tangent plane has an original source image of codimension one. -/
theorem original_tensor_pencil_actual_gauss_plane_source_prime_height_one
    (e : RatFunc K ≃ₐ[K] C₀) (hQ : Q.height = 1)
    (hplane : ∑ i, (s i).elim 1 y₀ *
      algebraMap E L₀ (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0 i) = 0) :
    (Q.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)).height = 1 := by
  obtain ⟨v, hdim, hp⟩ := original_tensor_pencil_actual_gauss_plane_polynomial_incidence
    H I E s Q hH hd hind hGauss hplane
  exact original_tensor_pencil_divisor_moving_plane_source_prime_height_one
    H I E hH e hGauss s Q hQ (actualGaussRulingParameterChoice H I hH hd hind hGauss) v hdim hp

/-- Its actual affine source-image closure is an irreducible
hypersurface, with its equation derived from actual Gauss-plane incidence. -/
theorem original_tensor_pencil_actual_gauss_plane_source_image_hypersurface
    (e : RatFunc K ≃ₐ[K] C₀) (hQ : Q.height = 1)
    (hplane : ∑ i, (s i).elim 1 y₀ *
      algebraMap E L₀ (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0 i) = 0) :
    ∃ δ : MvPolynomial (Fin 3) K, Irreducible δ ∧
      projectiveSourceChartImageClosure s (extendedClosedGaussTensorNormalizationSourceHom H I E s) Q =
        PrimeSpectrum.zeroLocus
          (Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ} :
            Set (projectiveCoordinateChartAlgebra (C := K)
              (rationalCoordinate (K := K) (n := 4)) (s.symm none))) :=
  (projective_source_image_divisor_iff_height_one s
    (extendedClosedGaussTensorNormalizationSourceHom H I E s) Q).mpr
      (original_tensor_pencil_actual_gauss_plane_source_prime_height_one
        H I E s Q hH hd hind hGauss e hQ hplane)

end DimensionFourDependence
