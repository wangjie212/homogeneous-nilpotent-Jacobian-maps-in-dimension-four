import DimensionFourDependence.RationalParameterConstants

/-! # First and second parameter derivatives detect a fixed affine span

If every Wronskian of the first coordinate derivatives vanishes, their
ratios are actual constants. Integrating once more shows that every
coordinate is an original-field affine combination of one fixed function.
A normalized projective coordinate then turns a nonzero derivative
Wronskian into an actual nonzero three-column normal-jet determinant.
-/

namespace DimensionFourDependence

open Matrix

section Constants

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Vanishing Wronskians of the first derivatives force all original
coordinates into a fixed constant affine span when the derivation's
constant field is exactly the original coefficient field. -/
theorem derivative_wronskians_zero_constant_affine_span
    (D : Derivation K F F)
    (hconstants : ∀ x : F, D x = 0 → ∃ c : K, x = algebraMap K F c)
    (v : Fin n → F)
    (hW : ∀ i j, D (v i) * D (D (v j)) - D (v j) * D (D (v i)) = 0) :
    ∃ u : F, ∀ j, ∃ a b : K, v j = algebraMap K F a * u + algebraMap K F b := by
  classical
  by_cases hzero : ∀ i, D (v i) = 0
  · refine ⟨0, ?_⟩
    intro j
    obtain ⟨b, hb⟩ := hconstants (v j) (hzero j)
    exact ⟨0, b, by simpa only [map_zero, zero_mul, zero_add] using hb⟩
  · push Not at hzero
    obtain ⟨i, hi⟩ := hzero
    refine ⟨v i, ?_⟩
    intro j
    have hquot : D (D (v j) / D (v i)) = 0 := by
      rw [D.leibniz_div]
      change (D (v i))⁻¹ ^ 2 * (D (v i) * D (D (v j)) - D (v j) * D (D (v i))) = 0
      rw [hW i j, mul_zero]
    obtain ⟨a, ha⟩ := hconstants _ hquot
    have hDa : D (v j) = algebraMap K F a * D (v i) := (div_eq_iff hi).mp ha
    have hdiff : D (v j - algebraMap K F a * v i) = 0 := by
      rw [map_sub, D.leibniz, D.map_algebraMap]
      simp only [smul_eq_mul, mul_zero, add_zero, hDa, sub_self]
    obtain ⟨b, hb⟩ := hconstants _ hdiff
    exact ⟨a, b, by linear_combination hb⟩

/-- A nonzero square three-column minor proves independence of
the three actual rows of the original rectangular matrix. -/
theorem three_rows_independent_of_column_minor
    (A : Matrix (Fin 3) (Fin n) F) (c : Fin 3 → Fin n)
    (hdet : (A.submatrix id c).det ≠ 0) : LinearIndependent F A.row := by
  let r : (Fin n → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := fun v => v ∘ c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp r
  exact Matrix.linearIndependent_rows_of_det_ne_zero hdet

end Constants

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The vanishing-first-derivative-Wronskian criterion for the actual
rational parameter, with its exact original-field constants constructed. -/
theorem rational_parameter_derivative_wronskians_zero_affine_span
    (v : Fin n → RatFunc K)
    (hW : ∀ i j, rationalParameterDerivative K (v i) * rationalParameterDerivative K (rationalParameterDerivative K (v j)) -
      rationalParameterDerivative K (v j) * rationalParameterDerivative K (rationalParameterDerivative K (v i)) = 0) :
    ∃ u : RatFunc K, ∀ j, ∃ a b : K, v j = algebraMap K (RatFunc K) a * u + algebraMap K (RatFunc K) b :=
  derivative_wronskians_zero_constant_affine_span (rationalParameterDerivative K)
    (fun x hx => (rationalParameterDerivative_eq_zero_iff_scalar x).mp hx) v hW

/-- The actual parameter-normal matrix with rows the coordinate
vector, its first derivative, and its second derivative. -/
noncomputable def rationalParameterJetMatrix (v : Fin n → RatFunc K) : Matrix (Fin 3) (Fin n) (RatFunc K) :=
  fun r i => ![v i, rationalParameterDerivative K (v i),
    rationalParameterDerivative K (rationalParameterDerivative K (v i))] r

omit [CharZero K] in
/-- At a normalized coordinate equal to one, the actual three-column
jet determinant is exactly the Wronskian of the other first derivatives. -/
theorem rationalParameterJetMatrix_det_normalized_column
    (v : Fin n → RatFunc K) (a i j : Fin n) (ha : v a = 1) :
    ((rationalParameterJetMatrix v).submatrix id ![a, i, j]).det =
      rationalParameterDerivative K (v i) * rationalParameterDerivative K (rationalParameterDerivative K (v j)) -
        rationalParameterDerivative K (v j) * rationalParameterDerivative K (rationalParameterDerivative K (v i)) := by
  simp [rationalParameterJetMatrix, Matrix.det_fin_three, ha]

end DimensionFourDependence
