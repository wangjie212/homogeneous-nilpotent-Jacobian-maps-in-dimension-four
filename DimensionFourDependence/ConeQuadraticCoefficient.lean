import DimensionFourDependence.ConeRootSlopeIdentity
import DimensionFourDependence.RationalParameterAlgebraicDerivative
import DimensionFourDependence.TwoCovectorKernel

/-! # The slope identity constructs the nonzero quadratic coefficient kappa/r

Independence of the projected fiber direction from the directrix makes
the first normal derivative pairing nonzero. Parameter-algebraic
coefficients and their parameter derivatives are constant along the
fiber. Differentiating (4.9) therefore gives its exact acceleration and
the coefficient kappa/r, with kappa algebraic over the parameter field.
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

section Pairing

variable {F : Type*} [Field F]

/-- Independent ternary ruling covectors make the first normal
derivative pairing nonzero on a direction independent of the directrix. -/
theorem independent_cone_direction_first_normal_pairing_ne_zero
    (ν ν₁ V A : Fin 3 → F) (hν : LinearIndependent F ![ν, ν₁])
    (hVA : LinearIndependent F ![V, A])
    (hνV : ν ⬝ᵥ V = 0) (hν₁V : ν₁ ⬝ᵥ V = 0) (hνA : ν ⬝ᵥ A = 0) :
    ν₁ ⬝ᵥ A ≠ 0 := by
  intro hz
  have hV : V ≠ 0 := by simpa using hVA.ne_zero (0 : Fin 2)
  obtain ⟨s, hs⟩ := two_covector_common_kernel ν ν₁ V A hν hV hνV hν₁V hνA hz
  exact (LinearIndependent.pair_iff' hV).mp hVA s hs

end Pairing

variable {K F : Type*} [Field K] [CharZero K] [Field F] [CharZero F] [Algebra K F]

/-- The actual normal linear form and its parameter derivative have
the exact directional pairings along a fixed-parameter fiber direction. -/
theorem parameter_normal_linear_form_mixed_directional_values
    (p : RatFunc K →ₐ[K] F) (T D : Derivation K F F)
    (hT : T (p RatFunc.X) = 1) (hD : D (p RatFunc.X) = 0)
    (ν x A : Fin 3 → F) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (hTx : ∀ i, T (x i) = 0) (hDx : ∀ i, D (x i) = A i) :
    D (ν ⬝ᵥ x) = ν ⬝ᵥ A ∧ D (T (ν ⬝ᵥ x)) = (fun i => T (ν i)) ⬝ᵥ A := by
  have hDν (i : Fin 3) : D (ν i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p D hD _ (hν i)
  have hDTν (i : Fin 3) : D (T (ν i)) = 0 :=
    fixed_parameter_direction_kills_parameter_coefficient_derivative p T D hT hD _ (hν i)
  have hTL : T (ν ⬝ᵥ x) = (fun i => T (ν i)) ⬝ᵥ x := by
    rw [derivation_dotProduct]
    simp only [hTx, dotProduct, mul_zero, Finset.sum_const_zero, add_zero]
  constructor
  · rw [derivation_dotProduct]
    simp only [hDν, hDx, dotProduct, zero_mul, Finset.sum_const_zero, zero_add]
  · rw [hTL, derivation_dotProduct]
    simp only [hDTν, hDx, dotProduct, zero_mul, Finset.sum_const_zero, zero_add]

/-- Differentiating the exact cone slope gives its acceleration;
parameter derivative terms are proved constant from algebraicity. -/
theorem parameter_cone_slope_constructs_acceleration
    (p : RatFunc K →ₐ[K] F) (T D : Derivation K F F)
    (hT : T (p RatFunc.X) = 1) (hD : D (p RatFunc.X) = 0)
    {d : ℕ} (r w a b L α β θ : F) (hr : r ≠ 0) (hβ : β ≠ 0)
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hα : IsAlgebraic p.fieldRange α) (hβalg : IsAlgebraic p.fieldRange β)
    (hDr : D r = 0) (hDL : D L = 0) (hDTL : D (T L) = θ)
    (hslope : D w = (T a - α * a) / β +
      ((T b - α * ((d : F) - 1) * b / (d : F)) * L + b * T L) / (β * r)) :
    D (D w) = b * θ / (β * r) := by
  have hDa := parameter_algebraic_coefficient_direction_constant p D hD a ha
  have hDb := parameter_algebraic_coefficient_direction_constant p D hD b hb
  have hDα := parameter_algebraic_coefficient_direction_constant p D hD α hα
  have hDβ := parameter_algebraic_coefficient_direction_constant p D hD β hβalg
  have hDTa := fixed_parameter_direction_kills_parameter_coefficient_derivative p T D hT hD a ha
  have hDTb := fixed_parameter_direction_kills_parameter_coefficient_derivative p T D hT hD b hb
  let c₀ := (T a - α * a) / β
  let c₁ := T b - α * ((d : F) - 1) * b / (d : F)
  have hc₀ : D c₀ = 0 := by
    simp [c₀, D.leibniz_div, D.leibniz, smul_eq_mul, hDa, hDα, hDβ, hDTa]
  have hc₁ : D c₁ = 0 := by
    simp [c₁, D.leibniz_div, D.leibniz, smul_eq_mul, hDb, hDα, hDTb]
  have hden : D (β * r) = 0 := by simp [D.leibniz, hDβ, hDr]
  have hnum : D (c₁ * L + b * T L) = b * θ := by
    simp [D.leibniz, smul_eq_mul, hc₁, hDL, hDb, hDTL]
  change D (D w) = _
  rw [hslope]
  change D (c₀ + (c₁ * L + b * T L) / (β * r)) = _
  rw [map_add, hc₀, zero_add, D.leibniz_div, hnum, hden]
  simp only [smul_eq_mul, mul_zero, sub_zero]
  field_simp [hr, hβ]

/-- The actual quadratic acceleration constructs kappa != 0,
algebraic over the actual parameter field, and C = kappa/r. -/
theorem parameter_cone_quadratic_acceleration_constructs_nonzero_coefficient
    (p : RatFunc K →ₐ[K] F) (T D : Derivation K F F)
    (hT : T (p RatFunc.X) = 1) (hD : D (p RatFunc.X) = 0)
    {d : ℕ} (r w a b L α β θ C : F) (hr : r ≠ 0) (hb0 : b ≠ 0) (hβ : β ≠ 0) (hθ : θ ≠ 0)
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hα : IsAlgebraic p.fieldRange α) (hβalg : IsAlgebraic p.fieldRange β)
    (hθalg : IsAlgebraic p.fieldRange θ)
    (hDr : D r = 0) (hDL : D L = 0) (hDTL : D (T L) = θ)
    (hslope : D w = (T a - α * a) / β +
      ((T b - α * ((d : F) - 1) * b / (d : F)) * L + b * T L) / (β * r))
    (hacc : D (D w) = 2 * C) :
    ∃ κ : F, κ ≠ 0 ∧ IsAlgebraic p.fieldRange κ ∧ C = κ / r := by
  let κ := b * θ / (2 * β)
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hκ : κ ≠ 0 := div_ne_zero (mul_ne_zero hb0 hθ) (mul_ne_zero h2 hβ)
  have hκalg : IsAlgebraic p.fieldRange κ := by
    apply mem_algebraicClosure_iff.mp
    exact (algebraicClosure p.fieldRange F).div_mem
      ((algebraicClosure p.fieldRange F).mul_mem (mem_algebraicClosure_iff.mpr hb) (mem_algebraicClosure_iff.mpr hθalg))
      ((algebraicClosure p.fieldRange F).mul_mem ((algebraicClosure p.fieldRange F).natCast_mem 2)
        (mem_algebraicClosure_iff.mpr hβalg))
  have he : 2 * C = b * θ / (β * r) := hacc.symm.trans
    (parameter_cone_slope_constructs_acceleration p T D hT hD r w a b L α β θ hr hβ
      ha hb hα hβalg hDr hDL hDTL hslope)
  refine ⟨κ, hκ, hκalg, ?_⟩
  dsimp only [κ]
  field_simp [hr, hβ] at he ⊢
  linear_combination he

end DimensionFourDependence
