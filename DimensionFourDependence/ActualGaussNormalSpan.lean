import DimensionFourDependence.GaussNormalConstantSpan

/-! # Exact normal-span dimensions for the original polynomial map

The realization of the Gauss parameter and multiplication by the actual
nonzero normal pivot preserve original-field component-span dimensions.
Thus the constant-characteristic and varying-characteristic alternatives
give spans of exactly three and four for the original polynomial normal,
not only for its normalized rational parameter presentation.
-/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

section LinearAlgebra

variable {K F G : Type*} [Field K] [AddCommGroup F] [AddCommGroup G]
  [Module K F] [Module K G] {n : ℕ}

/-- An injective original-field linear map preserves the dimension
of the coordinate span of a finite family. -/
theorem finrank_coordinate_span_comp_injective
    (f : F →ₗ[K] G) (hf : Function.Injective f) (v : Fin n → F) :
    finrank K (Submodule.span K (Set.range (f ∘ v))) =
      finrank K (Submodule.span K (Set.range v)) := by
  have he := (Submodule.equivMapOfInjective f hf (Submodule.span K (Set.range v))).finrank_eq
  rw [Submodule.map_span, ← Set.range_comp] at he
  exact he.symm

end LinearAlgebra

universe u

variable {K : Type u} [Field K]

/-- Passing from normalized Gauss-parameter coordinates to the actual
original polynomial normal preserves the exact original-field span. -/
theorem actual_polynomial_normal_span_eq_parameter_normal_span
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) =
      finrank K (Submodule.span K (Set.range (gaussParameterNormal H I e))) := by
  let F := FractionRing (MvPolynomial (Fin 4) K)
  let f : RatFunc K →ₐ[K] F := gaussParameterSourceHom H I e
  let a := rationalImageNormal H I.equation (imageNormalPivot H I)
  have ha : a ≠ 0 := imageNormalPivot_ne_zero H I
  let g : RatFunc K →ₗ[K] F := a • f.toLinearMap
  have hg : Function.Injective g := by
    intro x y hxy
    apply f.injective
    exact mul_left_cancel₀ ha hxy
  have hcoord : g ∘ gaussParameterNormal H I e = rationalImageNormal H I.equation := by
    funext i
    change a * f (gaussParameterNormal H I e i) = rationalImageNormal H I.equation i
    rw [gaussParameterSourceHom_normal, mul_div_cancel₀ _ ha]
  let j := (IsScalarTower.toAlgHom K (MvPolynomial (Fin 4) K) F).toLinearMap
  have hj : Function.Injective j := IsFractionRing.injective _ _
  have hpoly := finrank_coordinate_span_comp_injective j hj (imageRelationNormal H I.equation)
  have hparam := finrank_coordinate_span_comp_injective g hg (gaussParameterNormal H I e)
  calc
    _ = finrank K (Submodule.span K (Set.range (rationalImageNormal H I.equation))) := hpoly.symm
    _ = _ := by rw [← hcoord]; exact hparam

variable [CharZero K]

/-- The actual original polynomial normal has span exactly three in
the fixed-characteristic case, and exactly four in the nonplanar
characteristic-tangent case. The rational parameter, characteristic,
independence, tangent span and original-field dimensions are constructed. -/
theorem actual_gauss_characteristic_alternative_exact_normal_spans
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let w := gaussParameterNormal H I e
      LinearIndependent (RatFunc K) (normalCharacteristicMatrix (rationalParameterDerivative K) w).row ∧
      ((∃ c : Fin 4 → K, c ≠ 0 ∧
        (fun i => algebraMap K (RatFunc K) (c i)) ∈ normalCharacteristicSubspace (rationalParameterDerivative K) w ∧
        finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) = 3) ∨
      ∃ b : Fin 4 → RatFunc K, b ≠ 0 ∧
        b ∈ normalCharacteristicSubspace (rationalParameterDerivative K) w ∧
        LinearIndependent (RatFunc K) ![b, fun i => rationalParameterDerivative K (b i)] ∧
        normalRulingSubspace (rationalParameterDerivative K) w =
          Submodule.span (RatFunc K) (Set.range ![b, fun i => rationalParameterDerivative K (b i)]) ∧
        (∀ c : Fin 4 → K, (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) ∧
        LinearIndependent K w ∧
        finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) = 4) := by
  obtain ⟨e, _, _, _, hLI⟩ := actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss
  have hLI' : LinearIndependent (RatFunc K)
      (normalCharacteristicMatrix (rationalParameterDerivative K) (gaussParameterNormal H I e)).row := hLI
  obtain ⟨b, hb0, hbC, _, halt⟩ :=
    rational_gauss_ruling_constant_vertex_or_characteristic_tangent (gaussParameterNormal H I e) hLI'
  refine ⟨e, hLI', ?_⟩
  rcases halt with ⟨c, hc, _, _, _, hcC⟩ | ⟨hpair, hspan⟩
  · left
    refine ⟨c, hc, hcC, ?_⟩
    rw [actual_polynomial_normal_span_eq_parameter_normal_span H I e]
    exact normal_component_span_finrank_three_of_constant_characteristic _ _ hLI' c hc hcC
  · right
    refine ⟨b, hb0, hbC, hpair, hspan,
      actual_characteristic_tangent_has_no_constant_hyperplane H hd hH hind I e b hspan,
      normal_components_independent_of_characteristic_tangent _ _ hLI' b hbC hpair, ?_⟩
    rw [actual_polynomial_normal_span_eq_parameter_normal_span H I e]
    exact normal_component_span_finrank_four_of_characteristic_tangent _ _ hLI' b hbC hpair

end DimensionFourDependence
