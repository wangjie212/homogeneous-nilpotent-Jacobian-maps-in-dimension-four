import DimensionFourDependence.ExtendedHomogeneousPowerSections
import DimensionFourDependence.ExtendedNativeNormalizedSections

/-! # The paper's rational positive-power roots are actual regular pencil sections -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

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
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedRationalRootSectionsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedRationalRootSectionsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual power of a native original-frame global section. -/
noncomputable def extendedClosedGaussHyperplaneSectionPower (s : Γ(M, ⊤)) (n : ℕ) :
    Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤) :=
  rationalFrameSectionPower N (fun a : Fin 4 => U a) w s n

/-- A rational section whose positive power is an actual regular
powered-frame section extends to an actual native global hyperplane
section, using the constructed normalization's own normal stalks. -/
noncomputable def extendedClosedGaussHyperplaneRationalRootSection
    (r : (N).functionField) {n : ℕ} (hn : 0 < n)
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤))
    (hs : rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s = r ^ n) :
    Γ(M, ⊤) :=
  rationalFrameGlobalRootSection N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed H I E hH e)
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) r hn s hs

/-- The actual regular root section retains the original rational
section value. -/
theorem extendedClosedGaussHyperplaneRationalRootSection_value
    (r : (N).functionField) {n : ℕ} (hn : 0 < n)
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤))
    (hs : rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s = r ^ n) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussHyperplaneRationalRootSection H I E hH e r hn s hs) = r :=
  rationalFrameGlobalRootSection_value N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed H I E hH e)
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) r hn s hs

/-- The actual power of the extended root is the originally supplied
regular global section of the actual powered-frame sheaf. -/
theorem extendedClosedGaussHyperplaneRationalRootSection_power
    (r : (N).functionField) {n : ℕ} (hn : 0 < n)
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤))
    (hs : rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s = r ^ n) :
    extendedClosedGaussHyperplaneSectionPower H I E hH e
      (extendedClosedGaussHyperplaneRationalRootSection H I E hH e r hn s hs) n = s :=
  rationalFrameGlobalRootSection_power N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed H I E hH e)
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) r hn s hs

/-- A nonzero original rational root gives a nonzero actual regular
global root section. -/
theorem extendedClosedGaussHyperplaneRationalRootSection_ne_zero
    (r : (N).functionField) (hr : r ≠ 0) {n : ℕ} (hn : 0 < n)
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤))
    (hs : rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s = r ^ n) :
    extendedClosedGaussHyperplaneRationalRootSection H I E hH e r hn s hs ≠ 0 := by
  intro hzero
  have hv := extendedClosedGaussHyperplaneRationalRootSection_value H I E hH e r hn s hs
  rw [hzero] at hv
  exact hr hv.symm

/-- Every actual regular original-frame coefficient of the extended
root has exactly its original rational value r/Xa in the own scheme field. -/
theorem extendedClosedGaussHyperplaneRationalRootSection_coefficient
    (r : (N).functionField) {n : ℕ} (hn : 0 < n)
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤))
    (hs : rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s = r ^ n)
    (a : Fin 4) :
    extendedClosedGaussHyperplaneOwnCoefficient H I E hH e
        (extendedClosedGaussHyperplaneRationalRootSection H I E hH e r hn s hs) a = r / w a := by
  apply (eq_div_iff (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a)).mpr
  exact (extendedClosedGaussHyperplaneOwnCoefficient_numerator H I E hH e _ a).trans
    (extendedClosedGaussHyperplaneRationalRootSection_value H I E hH e r hn s hs)

/-- A rational positive-power root of an original homogeneous source
form is an actual regular global hyperplane section on the normalized pencil. -/
noncomputable def extendedClosedGaussHomogeneousRationalRootSection
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (r : (N).functionField) (hn : 0 < n) (hroot : r ^ n = aeval w P) : Γ(M, ⊤) :=
  extendedClosedGaussHyperplaneRationalRootSection H I E hH e r hn
    (extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP)
    ((extendedClosedGaussHomogeneousPolynomialSection_value H I E hH e P hP).trans hroot.symm)

/-- The homogeneous-source root extension retains its exact original
rational root value. -/
theorem extendedClosedGaussHomogeneousRationalRootSection_value
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (r : (N).functionField) (hn : 0 < n) (hroot : r ^ n = aeval w P) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussHomogeneousRationalRootSection H I E hH e P hP r hn hroot) = r :=
  extendedClosedGaussHyperplaneRationalRootSection_value H I E hH e r hn _ _

/-- The actual powered root section equals the actual homogeneous
source-form section. -/
theorem extendedClosedGaussHomogeneousRationalRootSection_power
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (r : (N).functionField) (hn : 0 < n) (hroot : r ^ n = aeval w P) :
    extendedClosedGaussHyperplaneSectionPower H I E hH e
        (extendedClosedGaussHomogeneousRationalRootSection H I E hH e P hP r hn hroot) n =
      extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP :=
  extendedClosedGaussHyperplaneRationalRootSection_power H I E hH e r hn _ _

end DimensionFourDependence
