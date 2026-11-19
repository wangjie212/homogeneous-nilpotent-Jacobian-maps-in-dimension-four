import DimensionFourDependence.ProjectiveHomogeneousPullbackSections
import DimensionFourDependence.ExtendedNormalizedCoefficientValues
import DimensionFourDependence.ExtendedGaussSourceMorphism

/-! # Original homogeneous source forms are actual powered-frame sections on the pencil -/

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

local instance extendedHomogeneousPowerSectionsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedHomogeneousPowerSectionsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual powered original-frame sheaf on the normalization
formed after the algebraic coefficient extension. -/
noncomputable def extendedClosedGaussHyperplanePowerModuleSheaf (n : ℕ) : (N).Modules :=
  rationalFramePowerModuleSheaf N (fun a : Fin 4 => U a) w n

/-- The actual powered original-frame sheaves are locally free of
rank one, with their actual powered regular coordinate transitions. -/
theorem extendedClosedGaussHyperplanePowerModuleSheaf_locallyFreeRankOne (n : ℕ) :
    SchemeModuleIsLocallyFreeRankOne (extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n) :=
  rationalFramePowerModuleSheaf_locallyFreeRankOne N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneTransition H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneTransition_value H I E hH e) n

/-- Every original homogeneous source polynomial has an actually
regular numerator in the powered original frames of the actual pencil. -/
theorem extendedClosedGaussHomogeneousPolynomial_regular
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) :
    RationalFrameRegular N (fun a : Fin 4 => U a) (fun a => w a ^ n)
      (fun _ : (⊤ : (N).Opens) => aeval w P) := by
  exact rationalFrameRegular_of_open_eq N
    (fun a : Fin 4 => (f) ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a))
    (fun a : Fin 4 => U a) (fun a => w a ^ n)
    (extendedClosedGaussNormalizationProjectiveMap_preimage H I E hH e) _
    (projectiveHomogeneousPullback_regular N f
      (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) P hP)

/-- The actual regular powered-frame global section of any original
homogeneous source form over the extended coefficient field. -/
noncomputable def extendedClosedGaussHomogeneousPolynomialSection
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) :
    Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤) :=
  rationalFrameGlobalSectionOfRegular N (fun a : Fin 4 => U a) (fun a => w a ^ n)
    (aeval w P) (extendedClosedGaussHomogeneousPolynomial_regular H I E hH e P hP)

/-- The actual homogeneous source-form section has exactly the
original homogeneous rational numerator in the own scheme function field. -/
theorem extendedClosedGaussHomogeneousPolynomialSection_value
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) :
    rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n)
        (extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP) = aeval w P := rfl

/-- Original-field source forms enter the actual powered-frame
sheaf by the specified original source coefficient map. -/
noncomputable def extendedClosedGaussOriginalHomogeneousPolynomialSection
    (P : MvPolynomial (Fin 4) K) {n : ℕ} (hP : P.IsHomogeneous n) :
    Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤) :=
  extendedClosedGaussHomogeneousPolynomialSection H I E hH e
    (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P)
    (hP.map (extendedClosedGaussSourceCoefficientHom H I E))

/-- Each original homogeneous map component is an actual degree-d
powered-frame global section on the actual normalized extended pencil. -/
noncomputable def extendedClosedGaussMapComponentSection (i : Fin 4) :
    Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e d, ⊤) :=
  extendedClosedGaussOriginalHomogeneousPolynomialSection H I E hH e (H i) (hH i)

/-- The original linear combination of map components used by the
ruling forms, with its actual extended field coefficients. -/
noncomputable def extendedClosedGaussOutputLinearPolynomial (c : Fin 4 → E) :
    MvPolynomial (Fin 4) E :=
  ∑ i, c i • MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)

include hH in
/-- Original linear combinations of the homogeneous map components
retain the original homogeneous degree. -/
theorem extendedClosedGaussOutputLinearPolynomial_homogeneous (c : Fin 4 → E) :
    (extendedClosedGaussOutputLinearPolynomial H I E c).IsHomogeneous d := by
  apply (homogeneousSubmodule (Fin 4) E d).sum_mem
  intro i hi
  exact (homogeneousSubmodule (Fin 4) E d).smul_mem (c i)
    ((hH i).map (extendedClosedGaussSourceCoefficientHom H I E))

/-- The actual powered-frame global section of any ruling-linear
combination of the original homogeneous map components. -/
noncomputable def extendedClosedGaussOutputLinearSection (c : Fin 4 → E) :
    Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e d, ⊤) :=
  extendedClosedGaussHomogeneousPolynomialSection H I E hH e
    (extendedClosedGaussOutputLinearPolynomial H I E c)
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH c)

end DimensionFourDependence
