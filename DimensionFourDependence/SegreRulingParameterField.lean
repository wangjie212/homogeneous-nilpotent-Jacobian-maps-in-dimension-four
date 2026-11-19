import DimensionFourDependence.SegreOriginalFiberInvariants
import DimensionFourDependence.IndependentGaussCoefficientRealization
import DimensionFourDependence.GaussParameterSurfaceDimension

/-! # The actual rational fields of the two Segre ruling parameters -/

namespace DimensionFourDependence

attribute [local instance] coefficientFieldScalarTower

universe u
variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- A ruling parameter as an actual element of the original coefficient field. -/
noncomputable def segreCoefficientRulingParameter (Y : Fin 3 → S₀) (j : Fin 3) :
    coefficientField (K := K) Y :=
  coefficientCoordinate (K := K) Y j / coefficientCoordinate (K := K) Y 0

theorem segreCoefficientRulingParameter_coe (Y : Fin 3 → S₀) (j : Fin 3) :
    (segreCoefficientRulingParameter Y j : S₀) = Y j / Y 0 := rfl

/-- The original output partial differentiates its own ruling
parameter to the nonzero reciprocal of the original radial output. -/
theorem segre_coefficient_ruling_parameter_partial
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    coefficientPartial Y hY j (segreCoefficientRulingParameter Y j) =
      (coefficientCoordinate (K := K) Y 0)⁻¹ := by
  have h0 : coefficientPartial Y hY j (coefficientCoordinate (K := K) Y 0) = 0 := by
    simpa only [coefficientCoordinate, Ne.symm hj, ite_false] using coefficientPartial_coordinate Y hY j 0
  have h1 : coefficientPartial Y hY j (coefficientCoordinate (K := K) Y j) = 1 := by
    simpa only [coefficientCoordinate, ite_true] using coefficientPartial_coordinate Y hY j j
  rw [segreCoefficientRulingParameter, (coefficientPartial Y hY j).leibniz_div_const _ _ h0,
    h1]
  simp

/-- Each actual Segre ruling parameter is transcendental over the
original constants, derived from the constructed coefficient derivation. -/
theorem segre_coefficient_ruling_parameter_transcendental
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    Transcendental K (segreCoefficientRulingParameter Y j) := by
  have h0 : coefficientCoordinate (K := K) Y 0 ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun a : coefficientField (K := K) Y => (a : S₀)) hz
  intro halg
  have he := derivation_zero_of_isAlgebraic (coefficientPartial Y hY j)
    (segreCoefficientRulingParameter Y j) halg
  rw [segre_coefficient_ruling_parameter_partial Y hY j hj] at he
  exact inv_ne_zero h0 he

/-- The actual rational ruling field embedded in the original
coefficient field, retaining its exact parameter value. -/
noncomputable def segreCoefficientRulingParameterHom
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    RatFunc K →ₐ[K] coefficientField (K := K) Y :=
  transcendentalParameterFieldHom (segreCoefficientRulingParameter Y j)
    (segre_coefficient_ruling_parameter_transcendental Y hY j hj)

theorem segreCoefficientRulingParameterHom_X
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    segreCoefficientRulingParameterHom Y hY j hj RatFunc.X = segreCoefficientRulingParameter Y j :=
  transcendentalParameterFieldHom_X _ _

/-- The same actual ruling field embedded in the original source,
preserving both the coefficient-field and original-source realizations. -/
noncomputable def segreSourceRulingParameterHom
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    RatFunc K →ₐ[K] S₀ :=
  (IsScalarTower.toAlgHom K (coefficientField (K := K) Y) S₀).comp
    (segreCoefficientRulingParameterHom Y hY j hj)

theorem segreSourceRulingParameterHom_X
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    segreSourceRulingParameterHom Y hY j hj RatFunc.X = Y j / Y 0 := by
  change algebraMap (coefficientField (K := K) Y) S₀
    (segreCoefficientRulingParameterHom Y hY j hj RatFunc.X) = Y j / Y 0
  rw [segreCoefficientRulingParameterHom_X]
  rfl

/-- The actual rational ruling field lies inside the original output
field, since its generating parameter is the original coordinate ratio. -/
theorem segre_source_ruling_parameter_fieldRange_le_output
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    (segreSourceRulingParameterHom Y hY j hj).fieldRange ≤ fullOutputField (K := K) Y := by
  rw [rational_function_algHom_fieldRange_eq_adjoin_parameter, segreSourceRulingParameterHom_X]
  apply IntermediateField.adjoin_le_iff.mpr
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  exact (fullOutputField (K := K) Y).div_mem
    (IntermediateField.subset_adjoin K _ ⟨j, rfl⟩) (IntermediateField.subset_adjoin K _ ⟨0, rfl⟩)

end DimensionFourDependence
