import DimensionFourDependence.SourceTensorPolynomialValues
import DimensionFourDependence.ExtendedParameterOutputRelations

/-! # The actual three-output root forms retain their original four-coordinate covectors -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

section Covectors

variable {E : Type*} [Field E]

/-- A selected three-output form in the original four coordinate
labels, with zero coefficient on the remaining output. -/
noncomputable def selectedOutputCovector (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) : Fin 4 → E :=
  Fin.snoc n 0 ∘ p.symm

/-- A selected coefficient retains its exact original output label. -/
theorem selectedOutputCovector_castSucc (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) (i : Fin 3) :
    selectedOutputCovector p n (p i.castSucc) = n i := by
  simp only [selectedOutputCovector, Function.comp_apply, Equiv.symm_apply_apply, Fin.snoc_castSucc]

/-- The unselected fourth output has zero coefficient. -/
theorem selectedOutputCovector_last (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) :
    selectedOutputCovector p n (p (Fin.last 3)) = 0 := by
  simp only [selectedOutputCovector, Function.comp_apply, Equiv.symm_apply_apply, Fin.snoc_last]

/-- No nonzero selected output form is lost by returning to the
original four-coordinate covector representation. -/
theorem selectedOutputCovector_injective (p : Equiv.Perm (Fin 4)) :
    Function.Injective (selectedOutputCovector (E := E) p) := by
  intro n m he
  funext i
  simpa only [selectedOutputCovector_castSucc] using congrFun he (p i.castSucc)

/-- Nonzero selected forms remain nonzero original covectors. -/
theorem selectedOutputCovector_ne_zero (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) (hn : n ≠ 0) :
    selectedOutputCovector p n ≠ 0 := by
  intro hz
  apply hn
  funext i
  simpa only [selectedOutputCovector_castSucc, Pi.zero_apply] using congrFun hz (p i.castSucc)

end Covectors

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

/-- The lifted original covector gives exactly the previously
constructed selected-output source polynomial. -/
theorem selectedOutputCovector_output_polynomial
    (p : Equiv.Perm (Fin 4)) (n : Fin 3 → E) :
    extendedClosedGaussOutputLinearPolynomial H I E (selectedOutputCovector p n) =
      selectedOutputLinearPolynomial H I E p n := by
  unfold extendedClosedGaussOutputLinearPolynomial
  rw [← Equiv.sum_comp p (fun i => selectedOutputCovector p n i •
    MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)), Fin.sum_univ_castSucc]
  simp only [selectedOutputCovector_castSucc, selectedOutputCovector_last, Algebra.smul_def,
    map_zero, zero_mul, add_zero]
  rfl

/-- Scaling an actual output covector scales its original source
polynomial by the same coefficient. -/
theorem extendedClosedGaussOutputLinearPolynomial_smul (a : E) (c : Fin 4 → E) :
    extendedClosedGaussOutputLinearPolynomial H I E (a • c) =
      a • extendedClosedGaussOutputLinearPolynomial H I E c := by
  simp only [extendedClosedGaussOutputLinearPolynomial, Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

variable {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance selectedOutputCovectorsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance selectedOutputCovectorsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Scaling the original output form retains its exact scalar
value in the actual native normalized pencil field. -/
theorem extendedClosedGaussOutputLinearPolynomial_smul_native_value (a : E) (c : Fin 4 → E) :
    aeval (w) (extendedClosedGaussOutputLinearPolynomial H I E (a • c)) =
      algebraMap E (N).functionField a * aeval (w) (extendedClosedGaussOutputLinearPolynomial H I E c) := by
  rw [extendedClosedGaussOutputLinearPolynomial_smul, map_smul, Algebra.smul_def]

end DimensionFourDependence
