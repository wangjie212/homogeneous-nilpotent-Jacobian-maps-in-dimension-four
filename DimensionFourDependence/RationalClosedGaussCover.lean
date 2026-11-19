import DimensionFourDependence.ClosedGaussParameterField
import DimensionFourDependence.RationalSourceCurveField

/-! # A finite rational relatively closed cover of the actual Gauss curve

The actual Gauss field is finitely generated. Its finite relative
closure is therefore finitely generated too. Its actual transcendence
degree one and the source-line embedding give a rational-function-field
equivalence over the original coefficients. The image of its parameter
generates precisely this relatively closed source subfield and has
source Euler weight zero.
-/

namespace DimensionFourDependence

universe u

variable {K : Type u} [Field K]

/-- The actual Gauss field is finitely generated over the original
coefficient field, directly from its four normal-ratio coordinates. -/
theorem actual_gauss_field_essFiniteType
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    Algebra.EssFiniteType K
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)) := by
  apply IntermediateField.essFiniteType_iff.mpr
  exact IntermediateField.fg_adjoin_of_finite (Set.finite_range _)

/-- The actual finite relative closure is finitely generated over
the original coefficient field. -/
theorem closedGaussParameterField_fg
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    (closedGaussParameterField H I).FG := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let C := closedGaussParameterField H I
  let : Algebra.EssFiniteType K M := actual_gauss_field_essFiniteType H I
  let : Module.Finite M C := closedGaussParameterField_finite_over_gauss H I
  let : Algebra.EssFiniteType M C := inferInstance
  let : Algebra.EssFiniteType K C := Algebra.EssFiniteType.comp K M C
  exact IntermediateField.essFiniteType_iff.mp inferInstance

variable [CharZero K]

/-- The actual finite relatively closed cover of the dimension-one
Gauss curve is a rational-function field over the original field. -/
theorem actual_closed_gauss_parameter_rational_function_field
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    Nonempty (RatFunc K ≃ₐ[K] closedGaussParameterField H I) :=
  rational_function_equiv_of_fg_curve_subfield (closedGaussParameterField H I)
    (closedGaussParameterField_fg H I) (closedGaussParameterField_trdeg_one H I hGauss)

/-- The actual rational cover equivalence realized in the original
rational source field. -/
noncomputable def closedGaussParameterSourceHom
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    RatFunc K →ₐ[K] FractionRing (MvPolynomial (Fin 4) K) :=
  (closedGaussParameterField H I).val.comp e.toAlgHom

omit [CharZero K] in
/-- The entire realized range is the actual closed parameter field. -/
theorem closedGaussParameterSourceHom_fieldRange
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    (closedGaussParameterSourceHom H I e).fieldRange = closedGaussParameterField H I := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact (e r).property
  · intro hx
    obtain ⟨r, hr⟩ := e.surjective ⟨x, hx⟩
    exact ⟨r, congrArg Subtype.val hr⟩

omit [CharZero K] in
/-- The realized rational cover parameter generates the exact
relatively closed parameter field inside the original source. -/
theorem closedGaussParameterSourceHom_X_adjoin
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    IntermediateField.adjoin K {closedGaussParameterSourceHom H I e RatFunc.X} =
      closedGaussParameterField H I := by
  have he := congrArg (IntermediateField.map (closedGaussParameterSourceHom H I e)) (RatFunc.adjoin_X (K := K))
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
    closedGaussParameterSourceHom_fieldRange] at he
  exact he

omit [CharZero K] in
/-- The actual covering parameter is transcendental in the original
source field over the original coefficient field. -/
theorem closedGaussParameterSourceHom_X_transcendental
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    Transcendental K (closedGaussParameterSourceHom H I e RatFunc.X) := by
  intro ha
  exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff (closedGaussParameterSourceHom H I e)
    (closedGaussParameterSourceHom H I e).injective).mp ha)

/-- The original homogeneous map supplies its actual finite rational
Gauss cover with a transcendental source parameter generating a relatively
closed field and having source Euler weight zero. -/
theorem actual_gauss_curve_finite_rational_relatively_closed_cover
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I,
      let t := closedGaussParameterSourceHom H I e RatFunc.X
      Transcendental K t ∧
      IntermediateField.adjoin K {t} = closedGaussParameterField H I ∧
      Module.Finite
        (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
        (closedGaussParameterField H I) ∧
      algebraicClosure (IntermediateField.adjoin K {t}) (FractionRing (MvPolynomial (Fin 4) K)) = ⊥ ∧
      sourceEuler (K := K) (closedGaussParameterSourceHom H I e RatFunc.X) = 0 := by
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  have hgen := closedGaussParameterSourceHom_X_adjoin H I e
  refine ⟨e, closedGaussParameterSourceHom_X_transcendental H I e, hgen,
    closedGaussParameterField_finite_over_gauss H I, ?_, ?_⟩
  · rw [hgen]
    exact closedGaussParameterField_relatively_closed H I
  · exact closedGaussParameterField_le_sourceEuler_constants H hH I (e RatFunc.X).property

end DimensionFourDependence
