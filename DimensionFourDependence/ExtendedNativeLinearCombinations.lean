import DimensionFourDependence.ExtendedFrameIntegerOrders
import DimensionFourDependence.FiberPolynomialForms

/-! # Actual constant-linear combinations of the native hyperplane sections -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e

local instance extendedNativeLinearCombinationsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedNativeLinearCombinationsTopNonempty : Nonempty (⊤ : (N).Opens) :=
  ⟨⟨genericPoint N, trivial⟩⟩
noncomputable local instance extendedNativeLinearCombinationsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Extended field constants are actual global regular functions,
pulled back along the original projective map. -/
noncomputable def extendedClosedGaussGlobalConstantHom : E →+* Γ(N, ⊤) :=
  (f).appTop.hom.comp (projectiveConstantSectionHom E ⊤)

/-- The global regular constant has exactly the original extended
coefficient value in the scheme function field. -/
theorem extendedClosedGaussGlobalConstantHom_generic_value (c : E) :
    (N).germToFunctionField ⊤ (extendedClosedGaussGlobalConstantHom H I E hH e c) =
      algebraMap E (N).functionField c := by
  let : Nonempty ((f) ⁻¹ᵁ ⊤) := ⟨⟨genericPoint N, trivial⟩⟩
  exact (projectivePullbackScalarHom_chart E N f ⊤ c).symm

/-- Every nonzero extended constant is an actual global regular unit. -/
theorem extendedClosedGaussGlobalConstantHom_isUnit (c : E) (hc : c ≠ 0) :
    IsUnit (extendedClosedGaussGlobalConstantHom H I E hH e c) :=
  (isUnit_iff_ne_zero.mpr hc).map (extendedClosedGaussGlobalConstantHom H I E hH e)

/-- Constant multiplication is implemented using the actual global
regular function action on the native module sheaf. -/
noncomputable def extendedClosedGaussConstantSectionSmul
    (c : E) (s : Γ(M, ⊤)) : Γ(M, ⊤) :=
  extendedClosedGaussGlobalConstantHom H I E hH e c • s

/-- Actual constant multiplication retains the original rational
numerator and its specified coefficient-field action. -/
theorem extendedClosedGaussConstantSectionSmul_value (c : E) (s : Γ(M, ⊤)) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussConstantSectionSmul H I E hH e c s) =
      algebraMap E (N).functionField c * extendedClosedGaussHyperplaneGlobalValue H I E hH e s := by
  exact (rationalFrameGlobalSectionValue_smul N (fun a : Fin 4 => V a) w
    (extendedClosedGaussGlobalConstantHom H I E hH e c) s).trans
      (congrArg (fun v => v * extendedClosedGaussHyperplaneGlobalValue H I E hH e s)
        (extendedClosedGaussGlobalConstantHom_generic_value H I E hH e c))

/-- The original input linear form is homogeneous of degree one. -/
theorem extendedClosedGaussInputLinearPolynomial_homogeneous (ν : Fin 4 → E) :
    (linearFormPolynomial ν).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i hi
  exact isHomogeneous_C_mul_X (ν i) i

/-- The input hyperplane form defines an actual native global
section in the original, unpowered regular frames. -/
noncomputable def extendedClosedGaussInputLinearSection (ν : Fin 4 → E) : Γ(M, ⊤) :=
  rationalFrameGlobalSectionOfRegular N (fun a : Fin 4 => V a) w
    (aeval w (linearFormPolynomial ν)) (by
      simpa only [pow_one] using extendedClosedGaussHomogeneousPolynomial_regular H I E hH e
        (linearFormPolynomial ν) (extendedClosedGaussInputLinearPolynomial_homogeneous E ν))

/-- The actual input hyperplane section has its original rational
linear-form value. -/
theorem extendedClosedGaussInputLinearSection_value (ν : Fin 4 → E) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e ν) =
        ∑ i, algebraMap E (N).functionField (ν i) * w i := by
  change aeval w (linearFormPolynomial ν) = _
  simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]

/-- The section U in the product-power argument is an actual sum
of a regular input linear section and the actual extended rational root. -/
noncomputable def extendedClosedGaussRootCombinationSection
    (ν c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c))
    (α β : E) : Γ(M, ⊤) :=
  extendedClosedGaussConstantSectionSmul H I E hH e α
      (extendedClosedGaussInputLinearSection H I E hH e ν) +
    extendedClosedGaussConstantSectionSmul H I E hH e β
      (extendedClosedGaussOutputLinearRootSection H I E hH e c r hd hroot)

/-- The actual regular section U retains the exact original
coefficient-linear combination used in the paper. -/
theorem extendedClosedGaussRootCombinationSection_value
    (ν c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) (α β : E) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) =
      algebraMap E (N).functionField α * (∑ i, algebraMap E (N).functionField (ν i) * w i) +
        algebraMap E (N).functionField β * r := by
  change extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussConstantSectionSmul H I E hH e α
          (extendedClosedGaussInputLinearSection H I E hH e ν)) +
      extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussConstantSectionSmul H I E hH e β
          (extendedClosedGaussOutputLinearRootSection H I E hH e c r hd hroot)) = _
  rw [extendedClosedGaussConstantSectionSmul_value, extendedClosedGaussConstantSectionSmul_value,
    extendedClosedGaussInputLinearSection_value, extendedClosedGaussOutputLinearRootSection_value]

end DimensionFourDependence
