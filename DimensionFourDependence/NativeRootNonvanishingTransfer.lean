import DimensionFourDependence.SourceTensorPolynomialValues
import DimensionFourDependence.NativeHomogeneousSourceRelations

/-! # Nonzero boundary linear forms and native rational root numerators

Nonvanishing transfers first from the boundary realization to the source
tensor and then, for homogeneous forms, to the native pencil field.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Boundary

variable {C L F E κ : Type*} [Field C] [Field L] [Field F] [Field E] [Field κ]
    [CharZero C] [Algebra C L] [Algebra C F] [Algebra C E] [Algebra.IsAlgebraic C E]
    [Algebra C κ] [Algebra L κ] [IsScalarTower C L κ]
    [Algebra E κ] [IsScalarTower C E κ]

/-- Nonvanishing of an actual boundary linear form implies
nonvanishing of that same form in the original source tensor. -/
theorem boundary_linear_form_source_tensor_ne_zero
    (f : L →ₐ[C] F) {r : ℕ} (n : Fin r → E) (y : Fin r → L)
    (hn : (∑ i, algebraMap E κ (n i) * algebraMap L κ (y i)) ≠ 0) :
    coefficientTensorLinearValue (C := C) n (fun i => f (y i)) ≠ 0 := by
  have hcoeff : coefficientTensorLinearValue (C := C) n y ≠ 0 := by
    intro hz
    apply hn
    rw [← coefficientTensorRealization_linear_value (C := C) (κ := κ), hz, map_zero]
  rw [← coefficientSourceTensorMap_linear_value f n y]
  exact (map_ne_zero_iff _ (coefficientSourceTensorMap_injective f)).mpr hcoeff

end Boundary

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "xₜ" => extendedClosedGaussSourceTensorCoordinate H I E

local instance nativeRootNonvanishingTransferIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeRootNonvanishingTransferAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- A rational root formula with nonzero homogeneous numerator
factors and denominator in the original source tensor remains nonzero
in the actual normalized pencil function field. -/
theorem extendedClosedGauss_native_rational_formula_ne_zero
    (N M Q : MvPolynomial (Fin 4) E) {a b c : ℕ}
    (hN : N.IsHomogeneous a) (hM : M.IsHomogeneous b) (hQ : Q.IsHomogeneous c)
    (hn : aeval (xₜ) N ≠ 0) (hm : aeval (xₜ) M ≠ 0) (hq : aeval (xₜ) Q ≠ 0) :
    aeval (w) N * aeval (w) Q / aeval (w) M ≠ 0 := by
  have hn' : aeval (w) N ≠ 0 := fun hz =>
    hn ((extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e N hN).mpr hz)
  have hm' : aeval (w) M ≠ 0 := fun hz =>
    hm ((extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e M hM).mpr hz)
  have hq' : aeval (w) Q ≠ 0 := fun hz =>
    hq ((extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e Q hQ).mpr hz)
  exact div_ne_zero (mul_ne_zero hn' hq') hm'

end DimensionFourDependence
