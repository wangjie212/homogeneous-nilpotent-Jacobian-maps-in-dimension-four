import DimensionFourDependence.NativeHomogeneousSourceRelations

/-! # Rational roots transfer from the actual source tensor to the native pencil

Clearing the ruling denominator gives one homogeneous polynomial
identity. The exact native relation ideal transfers that identity and
the denominator's nonvanishing, producing the rational root in the
native normalized pencil field.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The rational root equation is equivalent to its cleared identity
whenever the original ruling denominator is nonzero. -/
theorem rational_root_power_iff_cleared
    {F : Type*} [Field F] (n m s q : F) (d : ℕ) (hm : m ≠ 0) :
    (n * q / m) ^ d = s ↔ (n * q) ^ d = s * m ^ d := by
  rw [div_pow, div_eq_iff (pow_ne_zero d hm)]

/-- Clearing the rational root denominator produces a homogeneous
source equation of the expected degree d(d+1). -/
theorem rationalRootClearedPolynomial_homogeneous
    {E : Type*} [Field E] {σ : Type*} (N M S Q : MvPolynomial σ E)
    {d : ℕ} (hN : N.IsHomogeneous d) (hM : M.IsHomogeneous d)
    (hS : S.IsHomogeneous d) (hQ : Q.IsHomogeneous 1) :
    ((N * Q) ^ d - S * M ^ d).IsHomogeneous (d * (d + 1)) := by
  have hleft : ((N * Q) ^ d).IsHomogeneous (d * (d + 1)) := by
    convert (hN.mul hQ).pow d using 1 <;> ring
  have hright : (S * M ^ d).IsHomogeneous (d * (d + 1)) := by
    convert hS.mul (hM.pow d) using 1 <;> ring
  exact hleft.sub hright

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
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

local instance nativeRationalRootTransferIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeRationalRootTransferAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual rational formula and its power equation transfer
to the native normalized pencil field, retaining the original denominator.
The root itself is constructed by that formula. -/
theorem extendedClosedGauss_native_rational_root_of_source_tensor
    (N M S Q : MvPolynomial (Fin 4) E)
    (hN : N.IsHomogeneous d) (hM : M.IsHomogeneous d)
    (hS : S.IsHomogeneous d) (hQ : Q.IsHomogeneous 1)
    (hclear : (aeval (xₜ) N * aeval (xₜ) Q) ^ d =
      aeval (xₜ) S * aeval (xₜ) M ^ d)
    (hm : aeval (xₜ) M ≠ 0) :
    aeval (w) M ≠ 0 ∧
      (aeval (w) N * aeval (w) Q / aeval (w) M) ^ d = aeval (w) S := by
  have hm' : aeval (w) M ≠ 0 := by
    intro hz
    exact hm ((extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e M hM).mpr hz)
  refine ⟨hm', (rational_root_power_iff_cleared _ _ _ _ d hm').mpr ?_⟩
  have hsource : aeval (xₜ) ((N * Q) ^ d - S * M ^ d) = 0 := by
    simpa only [map_sub, map_pow, map_mul, sub_eq_zero] using hclear
  have hnative := (extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e
    ((N * Q) ^ d - S * M ^ d)
    (rationalRootClearedPolynomial_homogeneous N M S Q hN hM hS hQ)).mp hsource
  simpa only [map_sub, map_pow, map_mul, sub_eq_zero] using hnative

end DimensionFourDependence
