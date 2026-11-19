import DimensionFourDependence.CoefficientSourceTensor

/-! # Actual boundary root equations give the source tensor root equation

The boundary root is eliminated by its power equation and its actual
rational formula. Faithfulness gives the cleared equation before boundary
realization. The coefficient-field source inclusion then retains that
equation and the nonzero original denominator in the actual source tensor.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {C L F E κ : Type*} [Field C] [Field L] [Field F] [Field E] [Field κ]
    [Algebra C L] [Algebra C F] [Algebra C E]

/-- An actual output linear form with extended coefficients in
the tensor of its original coefficient field. -/
noncomputable def coefficientTensorLinearValue {r : ℕ} (n : Fin r → E) (y : Fin r → L) : L ⊗[C] E :=
  ∑ i, algebraMap E (L ⊗[C] E) (n i) * (y i ⊗ₜ[C] (1 : E))

/-- The original source inclusion retains the value of every
output linear form over the extended coefficient field. -/
theorem coefficientSourceTensorMap_linear_value
    (f : L →ₐ[C] F) {r : ℕ} (n : Fin r → E) (y : Fin r → L) :
    coefficientSourceTensorMap f (coefficientTensorLinearValue (C := C) n y) =
      coefficientTensorLinearValue (C := C) n (fun i => f (y i)) := by
  simp only [coefficientTensorLinearValue, map_sum, map_mul, AlgHom.commutes]
  rfl

variable [CharZero C] [Algebra.IsAlgebraic C E]
    [Algebra C κ] [Algebra L κ] [IsScalarTower C L κ]
    [Algebra E κ] [IsScalarTower C E κ]

/-- The actual compatible boundary realization recovers the
original output linear form with its actual boundary coefficients. -/
theorem coefficientTensorRealization_linear_value
    {r : ℕ} (n : Fin r → E) (y : Fin r → L) :
    coefficientTensorRealization (C := C) (κ := κ) (coefficientTensorLinearValue (C := C) n y) =
      ∑ i, algebraMap E κ (n i) * algebraMap L κ (y i) := by
  simp only [coefficientTensorLinearValue, map_sum, map_mul, AlgHom.commutes,
    coefficientTensorRealization_left]

/-- The actual boundary product and root equations construct the
cleared root equation in the original source tensor. The original
denominator is proved nonzero from the nonzero numerator and invariant. -/
theorem boundary_rational_root_gives_source_tensor_equation
    (f : L →ₐ[C] F) (hclosed : algebraicClosure C L = ⊥)
    {r : ℕ} (n m s : Fin r → E) (y : Fin r → L) (c : L) (ρ : κ) (d : ℕ)
    (hn : (∑ i, algebraMap E κ (n i) * algebraMap L κ (y i)) ≠ 0)
    (hc : c ≠ 0)
    (hprod : (∑ i, algebraMap E κ (n i) * algebraMap L κ (y i)) * algebraMap L κ c =
      (∑ i, algebraMap E κ (m i) * algebraMap L κ (y i)) * ρ)
    (hroot : ρ ^ d = ∑ i, algebraMap E κ (s i) * algebraMap L κ (y i)) :
    coefficientTensorLinearValue (C := C) m (fun i => f (y i)) ≠ 0 ∧
      (coefficientTensorLinearValue (C := C) n (fun i => f (y i)) * (f c ⊗ₜ[C] (1 : E))) ^ d =
        coefficientTensorLinearValue (C := C) s (fun i => f (y i)) *
          coefficientTensorLinearValue (C := C) m (fun i => f (y i)) ^ d := by
  let φ := coefficientTensorRealization (C := C) (L := L) (E := E) (κ := κ)
  have hv (a : Fin r → E) : φ (coefficientTensorLinearValue (C := C) a y) =
      ∑ i, algebraMap E κ (a i) * algebraMap L κ (y i) :=
    coefficientTensorRealization_linear_value a y
  have hmκ : (∑ i, algebraMap E κ (m i) * algebraMap L κ (y i)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact mul_ne_zero hn ((map_ne_zero (algebraMap L κ)).mpr hc) hprod
  have hm : coefficientTensorLinearValue (C := C) m y ≠ 0 := by
    intro hz
    exact hmκ (by rw [← hv, hz, map_zero])
  have hclear : (coefficientTensorLinearValue (C := C) n y * (c ⊗ₜ[C] (1 : E))) ^ d =
      coefficientTensorLinearValue (C := C) s y * coefficientTensorLinearValue (C := C) m y ^ d := by
    apply coefficientTensorRealization_injective (κ := κ) hclosed
    change φ _ = φ _
    rw [map_pow, map_mul, map_mul, map_pow, hv, hv, hv, coefficientTensorRealization_left,
      hprod, mul_pow, hroot]
    exact mul_comm _ _
  let ψ := coefficientSourceTensorMap (E := E) f
  have hψ := congrArg ψ hclear
  simp only [ψ, map_pow, map_mul, coefficientSourceTensorMap_linear_value] at hψ
  refine ⟨?_, hψ⟩
  rw [← coefficientSourceTensorMap_linear_value f m y]
  exact (map_ne_zero_iff _ (coefficientSourceTensorMap_injective f)).mpr hm

end DimensionFourDependence
