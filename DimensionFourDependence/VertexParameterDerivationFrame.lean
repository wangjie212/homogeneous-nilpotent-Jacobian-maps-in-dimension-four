import DimensionFourDependence.RulingDirectionAcceleration

/-! # Actual parameter and transverse derivations at a vertex-dependent parameter

The original vertex partial constructs the parameter derivative and the
three fixed-parameter transverse derivatives explicitly. Their values on
the original coordinates and parameter give the graph differential and
the full derivative chain rule, without an assumed inverse coordinate map.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option maxHeartbeats 3000000

/-- Differentiation in the actual parameter with transverse source
coordinates fixed, constructed from the original vertex partial. -/
noncomputable def vertexParameterPartial (D : Fin 4 → Derivation K F F) (t : F) : Derivation K F F :=
  (D (Fin.last 3) t)⁻¹ • D (Fin.last 3)

/-- The original transverse coordinate derivative with the actual
parameter held fixed. -/
noncomputable def transverseParameterPartial
    (D : Fin 4 → Derivation K F F) (t : F) (i : Fin 3) : Derivation K F F :=
  D i.castSucc - (D i.castSucc t / D (Fin.last 3) t) • D (Fin.last 3)

/-- The constructed parameter derivative sends t to one and the
fixed-parameter transverse derivatives send t to zero. -/
theorem vertex_parameter_derivation_frame_parameter_values
    (D : Fin 4 → Derivation K F F) (t : F) (ht : D (Fin.last 3) t ≠ 0) :
    vertexParameterPartial D t t = 1 ∧ ∀ i : Fin 3, transverseParameterPartial D t i t = 0 := by
  constructor
  · simp only [vertexParameterPartial, Derivation.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ ht
  · intro i
    simp only [transverseParameterPartial, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ ht, sub_self]

/-- The actual coordinate values of the new parameter frame,
including the full implicit graph derivatives of the original vertex. -/
theorem vertex_parameter_derivation_frame_coordinate_values
    (D : Fin 4 → Derivation K F F) (x : Fin 4 → F)
    (hcoord : ∀ i j, D i (x j) = if j = i then 1 else 0) (t : F) :
    (∀ j : Fin 3, vertexParameterPartial D t (x j.castSucc) = 0) ∧
      (∀ i j : Fin 3, transverseParameterPartial D t i (x j.castSucc) = if j = i then 1 else 0) ∧
      vertexParameterPartial D t (x (Fin.last 3)) = (D (Fin.last 3) t)⁻¹ ∧
      ∀ i : Fin 3, transverseParameterPartial D t i (x (Fin.last 3)) =
        -D i.castSucc t / D (Fin.last 3) t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simp only [vertexParameterPartial, Derivation.smul_apply, smul_eq_mul]
    rw [hcoord, if_neg (Fin.castSucc_ne_last j), mul_zero]
  · intro i j
    simp only [transverseParameterPartial, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hcoord]
    rw [if_neg (Fin.castSucc_ne_last j), mul_zero, sub_zero]
    simp only [Fin.castSucc_inj]
  · simp [vertexParameterPartial, Derivation.smul_apply, hcoord, smul_eq_mul]
  · intro i
    simp only [transverseParameterPartial, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]
    rw [hcoord, hcoord, if_neg (Fin.castSucc_ne_last i).symm, if_pos rfl]
    ring

/-- Every original source derivative has the full parameter-frame
chain rule, derived directly from the original nonzero vertex partial. -/
theorem vertex_parameter_derivation_frame_chain_rule
    (D : Fin 4 → Derivation K F F) (t : F) (ht : D (Fin.last 3) t ≠ 0)
    (u : F) (j : Fin 4) :
    D j u = (Fin.snoc (fun i : Fin 3 => transverseParameterPartial D t i u) (0 : F) : Fin 4 → F) j +
      vertexParameterPartial D t u * D j t := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    simp only [vertexParameterPartial, Derivation.smul_apply, smul_eq_mul, zero_add]
    field_simp [ht]
  · rw [Fin.snoc_castSucc]
    simp only [transverseParameterPartial, vertexParameterPartial, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]
    field_simp [ht]
    ring

/-- Every coefficient algebraic over the actual rational parameter
image is constant for the constructed fixed-parameter transverse frame. -/
theorem transverse_parameter_partial_kills_algebraic_coefficient [CharZero K]
    (D : Fin 4 → Derivation K F F) (p : RatFunc K →ₐ[K] F)
    (ht : D (Fin.last 3) (p RatFunc.X) ≠ 0) (a : F) (ha : IsAlgebraic p.fieldRange a)
    (i : Fin 3) : transverseParameterPartial D (p RatFunc.X) i a = 0 := by
  exact parameter_algebraic_coefficient_direction_constant p
    (transverseParameterPartial D (p RatFunc.X) i)
    ((vertex_parameter_derivation_frame_parameter_values D (p RatFunc.X) ht).2 i) a ha

end DimensionFourDependence
