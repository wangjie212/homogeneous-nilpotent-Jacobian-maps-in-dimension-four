import DimensionFourDependence.ImageNormalDerivation

/-! # A nonlinear affine curve has varying tangent direction

When the constants of a derivation are exactly the coefficient field,
a projectively fixed tangent direction places all coordinates on an
affine line. Consequently the tangent and its derivative are independent
for a nonlinear curve. Algebraically closed one-variable function fields
supply the required constant-field assertion.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- All coordinates lie on one affine line defined over the coefficient field. -/
def LiesInAffineLine (x : Fin n → F) : Prop :=
  ∃ a v : Fin n → E, v ≠ 0 ∧ ∃ t : F,
    ∀ i, x i = algebraMap E F (a i) + algebraMap E F (v i) * t

/-- Constant ratios of nonzero tangent coordinates integrate to an actual affine line. -/
theorem liesInAffineLine_of_derivative_ratios (D : Derivation E F F) (x : Fin n → F)
    (hconst : ∀ z : F, D z = 0 → ∃ c : E, algebraMap E F c = z)
    (j : Fin n) (hj : D (x j) ≠ 0)
    (hdir : ∀ i, ∃ c : E, D (x i) = algebraMap E F c * D (x j)) :
    LiesInAffineLine (E := E) x := by
  classical
  choose v hv using hdir
  have hv0 : v ≠ 0 := by
    intro hz
    have he := hv j
    rw [show v j = 0 from congrFun hz j, map_zero, zero_mul] at he
    exact hj he
  have hposition (i : Fin n) : D (x i - algebraMap E F (v i) * x j) = 0 := by
    rw [map_sub, D.leibniz, D.map_algebraMap, smul_zero, add_zero]
    simpa only [smul_eq_mul] using sub_eq_zero.mpr (hv i)
  choose a ha using fun i => hconst _ (hposition i)
  exact ⟨a, v, hv0, x j, fun i => sub_eq_iff_eq_add.mp (ha i).symm⟩

/-- If the tangent derivative is proportional to the tangent, all
direction ratios are constants and the coordinates lie on a line. -/
theorem liesInAffineLine_of_proportional_tangent_derivative
    (D : Derivation E F F) (x : Fin n → F)
    (hconst : ∀ z : F, D z = 0 → ∃ c : E, algebraMap E F c = z)
    (hu : (fun i => D (x i)) ≠ 0) (a : F)
    (ha : ∀ i, D (D (x i)) = a * D (x i)) : LiesInAffineLine (E := E) x := by
  obtain ⟨j, hj⟩ : ∃ j, D (x j) ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hu
  apply liesInAffineLine_of_derivative_ratios D x hconst j hj
  intro i
  have hz : D (D (x i) / D (x j)) = 0 := by
    rw [D.leibniz_div, ha i, ha j]
    simp only [smul_eq_mul]
    ring
  obtain ⟨c, hc⟩ := hconst _ hz
  exact ⟨c, by rw [hc, div_mul_cancel₀ _ hj]⟩

/-- Nonlinearity forces independence of the tangent derivative and tangent. -/
theorem nonlinear_curve_tangent_derivative_independent
    (D : Derivation E F F) (x : Fin n → F)
    (hconst : ∀ z : F, D z = 0 → ∃ c : E, algebraMap E F c = z)
    (hu : (fun i => D (x i)) ≠ 0) (hline : ¬ LiesInAffineLine (E := E) x) :
    LinearIndependent F ![(fun i => D (D (x i))), (fun i => D (x i))] := by
  apply linearIndependent_fin2.mpr
  constructor
  · exact hu
  · intro a he
    apply hline
    apply liesInAffineLine_of_proportional_tangent_derivative D x hconst hu a
    intro i
    have hi := congrFun he i
    simpa [Pi.smul_apply, smul_eq_mul] using hi.symm

/-- On an algebraically closed curve's function field every derivation
constant is an actual scalar. -/
theorem derivation_constant_scalar_of_algClosed_curve [CharZero E] [IsAlgClosed E]
    (D : Derivation E F F) (hD : D ≠ 0) (htr : Algebra.trdeg E F ≤ 1)
    (z : F) (hz : D z = 0) : ∃ c : E, algebraMap E F c = z := by
  have hAlg := (derivation_zero_iff_isAlgebraic_of_trdeg_le_one D hD htr z).mp hz
  have hm := mem_algebraicClosure_iff.mpr hAlg
  have hbot : algebraicClosure E F = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  rw [hbot] at hm
  exact hm

/-- The varying-tangent assertion used in Proposition 2.3 for a nonlinear
curve over algebraically closed constants, with its constants proved. -/
theorem algClosed_nonlinear_curve_tangent_independent [CharZero E] [IsAlgClosed E]
    (D : Derivation E F F) (hD : D ≠ 0) (htr : Algebra.trdeg E F ≤ 1) (x : Fin n → F)
    (hu : (fun i => D (x i)) ≠ 0) (hline : ¬ LiesInAffineLine (E := E) x) :
    LinearIndependent F ![(fun i => D (D (x i))), (fun i => D (x i))] :=
  nonlinear_curve_tangent_derivative_independent D x
    (derivation_constant_scalar_of_algClosed_curve D hD htr) hu hline

end DimensionFourDependence
