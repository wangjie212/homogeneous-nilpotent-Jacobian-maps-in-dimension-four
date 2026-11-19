import DimensionFourDependence.ExtendedHomogeneousPowerSections

/-! # Powered source-form sections retain their actual regular coordinate-chart coefficients -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

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
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e

local instance extendedHomogeneousSectionCoefficientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedHomogeneousSectionCoefficientsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Actual regular original-frame coefficients of arbitrary actual
global sections of the native powered-frame sheaf. -/
noncomputable def extendedClosedGaussHyperplanePowerSectionCoefficient {n : ℕ}
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤)) (a : Fin 4) : Γ(N, U a) :=
  rationalFrameGlobalCoefficient N (fun a : Fin 4 => U a) (fun a => w a ^ n)
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (fun a => pow_ne_zero n (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a)) s a

/-- The actual regular original chart coefficient obtained by
evaluating an original source polynomial at actual pulled coordinate ratios. -/
noncomputable def extendedClosedGaussChartPolynomialCoefficient
    (P : MvPolynomial (Fin 4) E) (a : Fin 4) : Γ(N, U a) :=
  (N).presheaf.map (homOfLE (le_of_eq
    (extendedClosedGaussNormalizationProjectiveMap_preimage H I E hH e a).symm)).op
      (projectivePullbackChartPolynomialHom N f a P)

/-- Actual original chart coefficient functions of a homogeneous
form retain its exact numerator in the powered original frame. -/
theorem extendedClosedGaussChartPolynomialCoefficient_homogeneous_value
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (a : Fin 4) (p : U a) :
    w a ^ n * schemeRationalSectionFunction N (U a)
        (extendedClosedGaussChartPolynomialCoefficient H I E hH e P a) p = aeval w P := by
  unfold extendedClosedGaussChartPolynomialCoefficient
  rw [schemeRationalSectionFunction_res]
  exact projectivePullbackChartPolynomialHom_homogeneous_numerator N f
    (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) P hP a _

/-- Coefficients extracted from the actual homogeneous-form global
section are exactly the actual regular original chart-polynomial pullbacks. -/
theorem extendedClosedGaussHomogeneousPolynomialSection_coefficient
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) (a : Fin 4) :
    extendedClosedGaussHyperplanePowerSectionCoefficient H I E hH e
        (extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP) a =
      extendedClosedGaussChartPolynomialCoefficient H I E hH e P a := by
  apply schemeRationalSectionFunction_injective_all N (U a)
  funext p
  apply mul_left_cancel₀
    (pow_ne_zero n (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a))
  exact (rationalFrameGlobalCoefficient_value N (fun a : Fin 4 => U a) (fun a => w a ^ n)
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (fun a => pow_ne_zero n (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a))
    (extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP) a p).symm.trans
      (extendedClosedGaussChartPolynomialCoefficient_homogeneous_value H I E hH e P hP a p).symm

end DimensionFourDependence
