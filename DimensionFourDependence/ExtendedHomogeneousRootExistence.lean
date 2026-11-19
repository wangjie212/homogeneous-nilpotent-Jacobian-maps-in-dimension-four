import DimensionFourDependence.ExtendedRationalRootSections

/-! # A native homogeneous root has an actual regular global root section -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedHomogeneousRootExistenceIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedHomogeneousRootExistenceAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- An actual nonzero regular native root section, retaining its
rational value and exact positive-power source section. -/
noncomputable def ExtendedClosedGaussNonzeroRootSectionExists
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) (r : (N).functionField) : Prop :=
  ∃ t : Γ(extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e, ⊤), t ≠ 0 ∧
    extendedClosedGaussHyperplaneGlobalValue H I E hH e t = r ∧
    extendedClosedGaussHyperplaneSectionPower H I E hH e t n =
      extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP

/-- A positive-power equation in the native function field constructs
a regular global section with exactly that rational value and exactly
the original powered source-form section. -/
theorem extendedClosedGauss_homogeneous_root_has_regular_section
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (r : (N).functionField) (hn : 0 < n) (hroot : r ^ n = aeval (w) P) :
    ∃ t : Γ(extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e, ⊤),
      extendedClosedGaussHyperplaneGlobalValue H I E hH e t = r ∧
      extendedClosedGaussHyperplaneSectionPower H I E hH e t n =
        extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP :=
  ⟨extendedClosedGaussHomogeneousRationalRootSection H I E hH e P hP r hn hroot,
    extendedClosedGaussHomogeneousRationalRootSection_value H I E hH e P hP r hn hroot,
    extendedClosedGaussHomogeneousRationalRootSection_power H I E hH e P hP r hn hroot⟩

/-- A nonzero native root constructs a nonzero regular global
section, retaining both its value and its exact powered section. -/
theorem extendedClosedGauss_nonzero_homogeneous_root_has_regular_section
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (r : (N).functionField) (hr : r ≠ 0) (hn : 0 < n) (hroot : r ^ n = aeval (w) P) :
    ∃ t : Γ(extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e, ⊤), t ≠ 0 ∧
      extendedClosedGaussHyperplaneGlobalValue H I E hH e t = r ∧
      extendedClosedGaussHyperplaneSectionPower H I E hH e t n =
        extendedClosedGaussHomogeneousPolynomialSection H I E hH e P hP := by
  obtain ⟨t, ht, hpower⟩ := extendedClosedGauss_homogeneous_root_has_regular_section H I E hH e P hP r hn hroot
  refine ⟨t, ?_, ht, hpower⟩
  intro hz
  apply hr
  rw [← ht, hz]
  rfl

/-- The reusable actual section interface is constructed from the
nonzero native root and its positive-power equation. -/
theorem extendedClosedGauss_nonzero_homogeneous_root_constructs_section
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (r : (N).functionField) (hr : r ≠ 0) (hn : 0 < n) (hroot : r ^ n = aeval (w) P) :
    ExtendedClosedGaussNonzeroRootSectionExists H I E hH e P hP r :=
  extendedClosedGauss_nonzero_homogeneous_root_has_regular_section H I E hH e P hP r hr hn hroot

end DimensionFourDependence
