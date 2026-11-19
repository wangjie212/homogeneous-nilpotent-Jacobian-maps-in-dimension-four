import DimensionFourDependence.ExtendedOwnCoordinateCharts
import DimensionFourDependence.ExtendedNormalizationHyperplaneSections
import DimensionFourDependence.ProjectiveNormalizedSection

/-! # Actual native pencil sheaf sections construct their original normalized-frame representation -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

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
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)

local instance extendedNativeNormalizedSectionsIntegral : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedNativeNormalizedSectionsAlgebra : Algebra E (N).functionField := extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
local instance extendedNativeNormalizedSectionsNonempty (a : Fin 4) : Nonempty (U a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)

/-- The actual regular chart coefficient of a native global pencil
section, as its actual generic germ in the scheme's own function field. -/
noncomputable def extendedClosedGaussHyperplaneOwnCoefficient (s : Γ(M, ⊤)) (a : Fin 4) :
    (N).functionField :=
  (N).germToFunctionField (U a) (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)

/-- Every actual global pencil-sheaf coefficient is integral over
the actual original-frame ratio algebra in the own scheme function field. -/
theorem extendedClosedGaussHyperplaneOwnCoefficient_isIntegral (s : Γ(M, ⊤)) (a : Fin 4) :
    IsIntegral (projectiveCoordinateChartAlgebra (C := E) w a)
      (extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s a) := by
  have h := extendedClosedGaussNormalizedChartFunction_isIntegral_own_coordinates H I E hH e
    (finSuccEquiv' a) (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)
  rw [finSuccEquiv'_symm_none] at h
  exact h

/-- The native original-frame coefficients all have exactly the
actual global section's common rational numerator. -/
theorem extendedClosedGaussHyperplaneOwnCoefficient_numerator
    (s : Γ(M, ⊤)) (a : Fin 4) :
    extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s a * w a =
      extendedClosedGaussHyperplaneGlobalValue H I E hH e s := by
  let p : U a := Classical.choice (inferInstance : Nonempty (U a))
  have hg := schemeRationalSectionFunction_eq_generic N (U a)
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a) p
  exact (mul_comm _ _).trans ((congrArg (fun z => w a * z) hg.symm).trans
    (extendedClosedGaussHyperplaneGlobalCoefficient_value H I E hH e s a p).symm)

/-- A nonzero actual global pencil-sheaf section has nonzero
original-frame coefficients in the actual scheme function field. -/
theorem extendedClosedGaussHyperplaneOwnCoefficient_ne_zero
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4) :
    extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s a ≠ 0 := by
  intro hz
  apply extendedClosedGaussHyperplaneGlobalCoefficient_ne_zero H I E hH e s hs a
  exact (Scheme.germToFunctionField_injective N (U a)) (hz.trans (map_zero _).symm)

/-- The original normalized-coordinate section representation is
constructed from an actual global section of the actual native pencil sheaf. -/
noncomputable def extendedClosedGaussHyperplaneProjectiveNormalizedSection (s : Γ(M, ⊤)) :
    ProjectiveNormalizedSection (k := E) w where
  coefficient a := ⟨extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s a,
    extendedClosedGaussHyperplaneOwnCoefficient_isIntegral H I E hH e s a⟩
  transition i j := (extendedClosedGaussHyperplaneOwnCoefficient_numerator H I E hH e s i).trans
    (extendedClosedGaussHyperplaneOwnCoefficient_numerator H I E hH e s j).symm

/-- Every actual native global section is integral in any original
nonzero linear frame whose original coordinate ratios are integral over
the specified base. No coefficient integrality hypothesis is supplied. -/
theorem extendedClosedGaussHyperplaneGlobalSection_linear_frame_isIntegral
    {R : Type*} [CommRing R] [Algebra R (N).functionField]
    (s : Γ(M, ⊤)) (c : Fin 4 → E) (h : (N).functionField) (hh : h ≠ 0)
    (hlinear : h = ∑ i, algebraMap E (N).functionField (c i) * w i)
    (hconstants : ∀ z : E, IsIntegral R (algebraMap E (N).functionField z))
    (hcoordinates : ∀ i, IsIntegral R (w i / h)) (a : Fin 4) :
    IsIntegral R (extendedClosedGaussHyperplaneOwnCoefficient H I E hH e s a * w a / h) :=
  projective_normalized_section_linear_frame_isIntegral w
    (extendedClosedGaussHyperplaneProjectiveNormalizedSection H I E hH e s)
    c h hh hlinear hconstants hcoordinates a

end DimensionFourDependence
