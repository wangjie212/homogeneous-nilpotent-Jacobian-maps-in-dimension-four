import DimensionFourDependence.GaussCharacteristicSubspaces

/-! # Constant characteristic points or actual characteristic tangents

A nonzero rational vector whose derivative is proportional to itself
has constant projective coordinates over the original coefficient field.
Otherwise the vector and its derivative are independent and span the
two-dimensional ruling. Applied to the constructed actual Gauss curve,
this constructs the constant-vertex or characteristic-tangent alternative.
-/

namespace DimensionFourDependence

open Matrix Module

section Constants

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- A vector with scalar-proportional derivative has an actual
constant projective representative when the derivation's constants
are exactly the original field. -/
theorem proportional_vector_derivative_constant_projective_representative
    (D : Derivation K F F)
    (hconstants : ∀ x : F, D x = 0 → ∃ c : K, x = algebraMap K F c)
    (b : Fin n → F) (hb : b ≠ 0) (a : F)
    (ha : a • b = fun i => D (b i)) :
    ∃ c : Fin n → K, c ≠ 0 ∧ ∃ s : F, s ≠ 0 ∧
      b = s • (fun i => algebraMap K F (c i)) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, b p ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hb
  have hquot (i : Fin n) : D (b i / b p) = 0 := by
    have hi : D (b i) = a * b i := (congrFun ha i).symm
    have hpp : D (b p) = a * b p := (congrFun ha p).symm
    rw [D.leibniz_div]
    simp only [smul_eq_mul, hi, hpp]
    ring
  choose c hc using fun i => hconstants (b i / b p) (hquot i)
  have he : b = b p • (fun i => algebraMap K F (c i)) := by
    funext i
    change b i = b p * algebraMap K F (c i)
    rw [← hc, mul_div_cancel₀ _ hp]
  refine ⟨c, ?_, b p, hp, he⟩
  intro hz
  have hh := hc p
  rw [hz, Pi.zero_apply, map_zero, div_self hp] at hh
  exact one_ne_zero hh

end Constants

variable {K : Type*} [Field K] [CharZero K]

/-- The characteristic of three independent rational normal covectors
is either a fixed original-field projective point, or its actual
derivative spans the ruling together with the characteristic vector. -/
theorem rational_gauss_ruling_constant_vertex_or_characteristic_tangent
    (w : Fin 4 → RatFunc K)
    (hLI : LinearIndependent (RatFunc K)
      (normalCharacteristicMatrix (rationalParameterDerivative K) w).row) :
    ∃ b : Fin 4 → RatFunc K, b ≠ 0 ∧
      b ∈ normalCharacteristicSubspace (rationalParameterDerivative K) w ∧
      (fun i => rationalParameterDerivative K (b i)) ∈ normalRulingSubspace (rationalParameterDerivative K) w ∧
      ((∃ c : Fin 4 → K, c ≠ 0 ∧ ∃ s : RatFunc K, s ≠ 0 ∧
        b = s • (fun i => algebraMap K (RatFunc K) (c i)) ∧
        (fun i => algebraMap K (RatFunc K) (c i)) ∈
          normalCharacteristicSubspace (rationalParameterDerivative K) w) ∨
      (LinearIndependent (RatFunc K) ![b, fun i => rationalParameterDerivative K (b i)] ∧
        normalRulingSubspace (rationalParameterDerivative K) w =
          Submodule.span (RatFunc K) (Set.range ![b, fun i => rationalParameterDerivative K (b i)]))) := by
  obtain ⟨b, hb0, hbC, hbD⟩ := exists_normal_characteristic_vector (rationalParameterDerivative K) w hLI
  refine ⟨b, hb0, hbC, hbD, ?_⟩
  by_cases hpair : LinearIndependent (RatFunc K) ![b, fun i => rationalParameterDerivative K (b i)]
  · right
    refine ⟨hpair, ?_⟩
    have hle : Submodule.span (RatFunc K)
        (Set.range ![b, fun i => rationalParameterDerivative K (b i)]) ≤
        normalRulingSubspace (rationalParameterDerivative K) w := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact normalCharacteristicSubspace_le_ruling _ _ hbC
      · exact hbD
    have hd : finrank (RatFunc K) (Submodule.span (RatFunc K)
        (Set.range ![b, fun i => rationalParameterDerivative K (b i)])) = 2 := by
      simpa using finrank_span_eq_card hpair
    exact (Submodule.eq_of_le_of_finrank_eq hle
      (hd.trans (normal_ruling_characteristic_subspace_dimensions _ _ hLI).1.symm)).symm
  · left
    rw [LinearIndependent.pair_iff' hb0] at hpair
    push Not at hpair
    obtain ⟨a, ha⟩ := hpair
    obtain ⟨c, hc, s, hs, he⟩ := proportional_vector_derivative_constant_projective_representative
      (rationalParameterDerivative K)
      (fun x hx => (rationalParameterDerivative_eq_zero_iff_scalar x).mp hx) b hb0 a ha
    refine ⟨c, hc, s, hs, he, ?_⟩
    rw [he] at hbC
    exact (Submodule.smul_mem_iff _ hs).mp hbC

universe u

variable {K' : Type u} [Field K'] [CharZero K']

/-- The original actual Gauss curve supplies the constant-vertex or
characteristic-tangent alternative, with all characteristic data constructed. -/
theorem actual_gauss_ruling_constant_vertex_or_characteristic_tangent
    (H : Fin 4 → MvPolynomial (Fin 4) K') {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K' ≃ₐ[K'] projectiveRatioField (K := K')
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let w : Fin 4 → RatFunc K' := fun i => e.symm (fullOutputCoordinate (K := K')
        (fun j => rationalImageNormal H I.equation j /
          rationalImageNormal H I.equation (imageNormalPivot H I)) i)
      ∃ b : Fin 4 → RatFunc K', b ≠ 0 ∧
        b ∈ normalCharacteristicSubspace (rationalParameterDerivative K') w ∧
        (fun i => rationalParameterDerivative K' (b i)) ∈ normalRulingSubspace (rationalParameterDerivative K') w ∧
        ((∃ c : Fin 4 → K', c ≠ 0 ∧ ∃ s : RatFunc K', s ≠ 0 ∧
          b = s • (fun i => algebraMap K' (RatFunc K') (c i)) ∧
          (fun i => algebraMap K' (RatFunc K') (c i)) ∈
            normalCharacteristicSubspace (rationalParameterDerivative K') w) ∨
        (LinearIndependent (RatFunc K') ![b, fun i => rationalParameterDerivative K' (b i)] ∧
          normalRulingSubspace (rationalParameterDerivative K') w =
            Submodule.span (RatFunc K') (Set.range ![b, fun i => rationalParameterDerivative K' (b i)]))) := by
  obtain ⟨e, _, _, _, hLI⟩ := actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss
  exact ⟨e, rational_gauss_ruling_constant_vertex_or_characteristic_tangent _ hLI⟩

end DimensionFourDependence
