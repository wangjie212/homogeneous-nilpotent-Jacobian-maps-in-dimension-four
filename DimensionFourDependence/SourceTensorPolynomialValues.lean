import DimensionFourDependence.ScalarExtendedSourceRelations
import DimensionFourDependence.BoundaryRationalRootTensor
import DimensionFourDependence.ExtendedHomogeneousPowerSections
import DimensionFourDependence.ProjectiveSourceParameterField

/-! # Original source polynomials and selected output forms retain their tensor values -/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T" => S₀ ⊗[C₀] E
local notation "xₜ" => extendedClosedGaussSourceTensorCoordinate H I E

/-- Original polynomial coefficients pass through the actual closed
Gauss field and retain their exact original value in the source tensor. -/
theorem extendedClosedGaussSourceTensorCoordinate_original_constant_polynomial_value
    (P : MvPolynomial (Fin 4) K) :
    aeval (xₜ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P) =
      algebraMap (MvPolynomial (Fin 4) K) S₀ P ⊗ₜ[C₀] (1 : E) := by
  have he : MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P =
      MvPolynomial.map (algebraMap C₀ E) (MvPolynomial.map (algebraMap K C₀) P) := by
    rw [MvPolynomial.map_map]
    rfl
  rw [he, extendedClosedGaussSourceTensorCoordinate_original_polynomial_value,
    aeval_map_algebra_extension, rationalCoordinate_aeval]
  rfl

/-- A selected output covector is the original source polynomial
obtained from exactly those three original map components. -/
noncomputable def selectedOutputLinearPolynomial (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) :
    MvPolynomial (Fin 4) E :=
  ∑ i, MvPolynomial.C (n i) * MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H (p i.castSucc))

/-- Selected output linear forms retain the original homogeneous degree. -/
theorem selectedOutputLinearPolynomial_homogeneous
    {d : ℕ} (hH : IsHomogMap H d) (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) :
    (selectedOutputLinearPolynomial H I E p n).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro i hi
  exact ((hH (p i.castSucc)).map (extendedClosedGaussSourceCoefficientHom H I E)).C_mul (n i)

/-- The selected source polynomial has exactly its original
coefficient-extended output-linear value in the source tensor. -/
theorem selectedOutputLinearPolynomial_source_tensor_value
    (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) :
    aeval (xₜ) (selectedOutputLinearPolynomial H I E p n) =
      coefficientTensorLinearValue (C := C₀) n
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) := by
  simp only [selectedOutputLinearPolynomial, map_sum, map_mul, aeval_C,
    extendedClosedGaussSourceTensorCoordinate_original_constant_polynomial_value,
    coefficientTensorLinearValue]

end DimensionFourDependence
