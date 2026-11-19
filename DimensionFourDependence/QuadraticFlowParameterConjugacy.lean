import DimensionFourDependence.QuadraticInvariantFlow

/-! # The actual auxiliary shear conjugacy in equation (6.4) -/

namespace DimensionFourDependence.QuadraticFlow

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

theorem quadratic4_notMem_auxiliary : (2 : Fin 4) ∉ (quadratic4 (K := K)).vars := by
  have h := Tame.notMem_vars_aeval (![X 3, X 0, X 1] : Fin 3 → MvPolynomial (Fin 4) K)
    (X 0 * X 1 - X 2 ^ 2) 2 (by intro i; fin_cases i <;> simp)
  simpa [quadratic4] using h

theorem auxiliary_shift_parameter_notMem (r : K) :
    (2 : Fin 4) ∉ (C r * quadratic4 : MvPolynomial (Fin 4) K).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
  · simpa using h
  · exact quadratic4_notMem_auxiliary h

/-- The actual elementary shear `u ↦ u+ρq`, fixing all other coordinates. -/
noncomputable def auxiliaryShift4 (r : K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  Tame.elementary 2 (C r * quadratic4) (auxiliary_shift_parameter_notMem r)

theorem auxiliaryShift4_X (r : K) (j : Fin 4) :
    auxiliaryShift4 r (X j) = X j + if j = 2 then C r * quadratic4 else 0 :=
  Tame.elementary_X _ _ _ j

theorem auxiliaryShift4_inv_X (r : K) (j : Fin 4) :
    (auxiliaryShift4 r)⁻¹ (X j) = X j + if j = 2 then -(C r * quadratic4) else 0 :=
  Tame.elementary_inv_X _ _ _ j

theorem auxiliaryShift4_quadratic (r : K) :
    auxiliaryShift4 r quadratic4 = quadratic4 :=
  Tame.elementary_fixed _ _ _ _ quadratic4_notMem_auxiliary

/-- The corresponding substitution on the polynomial parameter ring. -/
noncomputable def parameterShift3 (r : K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0, X 1 + C r * X 0, X 2]

/-- All actual parameter coefficients are transported by the shear. -/
theorem auxiliaryShift4_parameter (r : K) (h : MvPolynomial (Fin 3) K) :
    auxiliaryShift4 r (parameter4 h) = parameter4 (parameterShift3 r h) := by
  change (auxiliaryShift4 r).toAlgHom (aeval ![quadratic4, X 2, X 3] h) = _
  rw [Tame.algHom_aeval]
  unfold parameter4 parameterShift3
  rw [comp_aeval_apply]
  have he : (fun i : Fin 3 => auxiliaryShift4 r (![quadratic4, X 2, X 3] i)) =
      (fun i : Fin 3 => (aeval ![quadratic4, X 2, X 3]) (![X 0, X 1 + C r * X 0, X 2] i)) := by
    funext i
    fin_cases i <;> simp [auxiliaryShift4_quadratic, auxiliaryShift4_X]
  simpa only [AlgEquiv.coe_toAlgHom] using
    congrArg (fun g : Fin 3 → MvPolynomial (Fin 4) K => aeval g h) he

/-- Equation (6.4), with the point-map word reversed for pullbacks,
holds for every polynomial invariant parameter on the entire ring. -/
theorem automorphism4_parameter_shift_conjugacy
    (r : K) (h : MvPolynomial (Fin 3) K) :
    automorphism4 (parameterShift3 r h) =
      auxiliaryShift4 r * automorphism4 h * (auxiliaryShift4 r)⁻¹ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro j
  change automorphism4 (parameterShift3 r h) (X j) =
    (auxiliaryShift4 r * automorphism4 h * (auxiliaryShift4 r)⁻¹) (X j)
  have hC (c : K) : automorphism4 h (C c) = C c := (automorphism4 h).commutes c
  have hE (c : K) : auxiliaryShift4 r (C c) = C c := (auxiliaryShift4 r).commutes c
  have htwo : auxiliaryShift4 r (2 : MvPolynomial (Fin 4) K) = 2 := map_ofNat _ 2
  fin_cases j <;>
    simp [AlgEquiv.coe_toAlgHom, AlgEquiv.mul_apply, auxiliaryShift4_inv_X,
      automorphism4_X, auxiliaryShift4_X, automorphism4_quadratic,
      auxiliaryShift4_quadratic, auxiliaryShift4_parameter,
      map_add, map_mul, map_pow, map_neg, hC, hE, htwo]

/-- Tameness of a parameter survives its actual auxiliary shear. -/
theorem automorphism4_parameter_shift_tame
    (r : K) (h : MvPolynomial (Fin 3) K)
    (hh : automorphism4 h ∈ Tame.subgroup K 4) :
    automorphism4 (parameterShift3 r h) ∈ Tame.subgroup K 4 := by
  rw [automorphism4_parameter_shift_conjugacy]
  have he : auxiliaryShift4 r ∈ Tame.subgroup K 4 := Tame.elementary_mem _ _ _
  exact (Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem he hh)
    ((Tame.subgroup K 4).inv_mem he)

end DimensionFourDependence.QuadraticFlow
