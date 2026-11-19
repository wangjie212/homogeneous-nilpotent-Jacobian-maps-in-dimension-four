import DimensionFourDependence.AlgebraicSourceDerivationChain
import DimensionFourDependence.ParameterAlgebraicFieldExtension

/-! # The source and geometric constant realizations give the same actual parameter frame -/

namespace DimensionFourDependence

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Precomposing with a parameter equivalence retains the exact
range of the compatible closed coefficient-field embedding. -/
theorem algHom_parameter_equiv_fieldRange
    {K C E : Type*} [Field K] [Field C] [Field E] [Algebra K C] [Algebra K E]
    (e : RatFunc K ≃ₐ[K] C) (g : C →ₐ[K] E) :
    (g.comp e.toAlgHom).fieldRange = g.fieldRange := by
  ext a
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨e r, hr⟩
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    change g (e (e.symm c)) = a
    rw [e.apply_symm_apply]
    exact hc

variable {K E F : Type*} [Field K] [CharZero K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "D₀" => algebraicPartial (K := K) F

variable (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : closedGaussParameterField H I →ₐ[K] E)
    (hg : ∀ c : closedGaussParameterField H I, algebraMap E F (g c) =
      algebraMap (FractionRing (MvPolynomial (Fin 4) K)) F
        (c : FractionRing (MvPolynomial (Fin 4) K)))

local notation "p₀" => (IsScalarTower.toAlgHom K S₀ F).comp (closedGaussParameterSourceHom H I e)

include hg

/-- Compatibility identifies the entire actual source parameter
embedding with its geometric constant realization, at every rational function. -/
theorem compatible_closed_parameter_source_realization :
    (p₀) = (IsScalarTower.toAlgHom K E F).comp (g.comp e.toAlgHom) := by
  ext r
  exact (hg (e r)).symm

/-- All actual cone coefficients algebraic over the realized closed
Gauss constants stay algebraic over the identical source parameter
field range used by the source derivative frame. -/
theorem compatible_closed_parameter_coefficient_image_isAlgebraic
    (a : E) (ha : IsAlgebraic g.fieldRange a) :
    IsAlgebraic (p₀).fieldRange (algebraMap E F a) := by
  have ha' : IsAlgebraic (g.comp e.toAlgHom).fieldRange a := by
    rw [algHom_parameter_equiv_fieldRange e g]
    exact ha
  rw [compatible_closed_parameter_source_realization H I e g hg]
  exact parameter_algebraic_coefficient_map (g.comp e.toAlgHom)
    (IsScalarTower.toAlgHom K E F) a ha'

/-- The compatible actual parameter has a geometric constant value,
and its nonzero original vertex differential survives in the actual
algebraic source extension. Neither condition is assumed there. -/
theorem compatible_closed_parameter_constructs_constant_value_and_nonzero_vertex_partial
    (hvertex : rationalPartial (K := K) (Fin.last 3)
      (closedGaussParameterSourceHom H I e RatFunc.X) ≠ 0) :
    (∃ τ : E, (p₀) RatFunc.X = algebraMap E F τ) ∧
      (D₀) (Fin.last 3) ((p₀) RatFunc.X) ≠ 0 := by
  refine ⟨⟨g (e RatFunc.X), (hg (e RatFunc.X)).symm⟩, ?_⟩
  change (D₀) (Fin.last 3)
    (algebraMap S₀ F (closedGaussParameterSourceHom H I e RatFunc.X)) ≠ 0
  rw [algebraicPartial_extends]
  simpa only [map_zero] using (algebraMap S₀ F).injective.ne hvertex

end DimensionFourDependence
