import DimensionFourDependence.QuadraticInvariantFlow

/-! # Elementary factorizations for auxiliary-only quadratic flow parameters -/

namespace DimensionFourDependence.QuadraticFlow

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- A polynomial in the two fixed coordinates is independent of
both coordinates moved by the quadratic flow. -/
theorem auxiliary_parameter_notMem (f : MvPolynomial (Fin 2) K)
    (i : Fin 4) (hi2 : i ≠ 2) (hi3 : i ≠ 3) :
    i ∉ (aeval ![X 2, X 3] f : MvPolynomial (Fin 4) K).vars := by
  apply Tame.notMem_vars_aeval
  intro j
  fin_cases j <;> simp [vars_X, hi2, hi3]

/-- Auxiliary-only parameters in the three-variable parameter ring
evaluate to the corresponding actual fixed-coordinate polynomial. -/
theorem parameter4_auxiliary_only (f : MvPolynomial (Fin 2) K) :
    parameter4 (aeval ![X 1, X 2] f) =
      (aeval ![X 2, X 3] f : MvPolynomial (Fin 4) K) := by
  unfold parameter4
  rw [comp_aeval_apply]
  have hg : (fun i : Fin 2 =>
      (aeval (![quadratic4, X 2, X 3] : Fin 3 → MvPolynomial (Fin 4) K))
        ((![X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) K) i)) =
      (![X 2, X 3] : Fin 2 → MvPolynomial (Fin 4) K) := by
    funext i
    fin_cases i <;> simp
  exact congrArg (fun g : Fin 2 → MvPolynomial (Fin 4) K => aeval g f) hg

/-- The triangular quadratic flow with an arbitrary fixed-coordinate
parameter is the product of two actual elementary automorphisms. -/
theorem automorphism4_auxiliary_only_tame (f : MvPolynomial (Fin 2) K) :
    automorphism4 (aeval ![X 1, X 2] f) ∈ Tame.subgroup K 4 := by
  let p : MvPolynomial (Fin 4) K := aeval ![X 2, X 3] f
  have hp0 : (0 : Fin 4) ∉ p.vars := auxiliary_parameter_notMem f 0 (by decide) (by decide)
  have hp1 : (1 : Fin 4) ∉ p.vars := auxiliary_parameter_notMem f 1 (by decide) (by decide)
  have hr : (0 : Fin 4) ∉ (2 * X 1 * p - X 3 * p ^ 2).vars := by
    have h := Tame.notMem_vars_aeval (![X 1, p, X 3] : Fin 3 → MvPolynomial (Fin 4) K)
      (2 * X 0 * X 1 - X 2 * X 1 ^ 2) 0 (by
        intro j
        fin_cases j <;> simp [hp0])
    simpa [map_ofNat] using h
  have hv : (1 : Fin 4) ∉ (X 3 * p).vars := by
    intro h
    rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · simpa using h
    · exact hp1 h
  let er := Tame.elementary 0 (2 * X 1 * p - X 3 * p ^ 2) hr
  let ev := Tame.elementary 1 (X 3 * p) hv
  have heq : automorphism4 (aeval ![X 1, X 2] f) = ev * er := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro j
    change automorphism4 (aeval ![X 1, X 2] f) (X j) = (ev * er) (X j)
    have hfix : ev p = p := Tame.elementary_fixed _ _ _ _ hp1
    have hevr (i : Fin 4) : ev (X i) = X i + if i = 1 then X 3 * p else 0 :=
      Tame.elementary_X _ _ _ i
    have herr (i : Fin 4) : er (X i) = X i +
        if i = 0 then 2 * X 1 * p - X 3 * p ^ 2 else 0 :=
      Tame.elementary_X _ _ _ i
    have htwo : ev (2 : MvPolynomial (Fin 4) K) = 2 := by
      exact map_ofNat ev 2
    rw [automorphism4_X, parameter4_auxiliary_only]
    change (![X 0 + 2 * X 1 * p + X 3 * p ^ 2,
      X 1 + X 3 * p, X 2, X 3] : Fin 4 → MvPolynomial (Fin 4) K) j = ev (er (X j))
    rw [herr]
    fin_cases j
    · change X 0 + 2 * X 1 * p + X 3 * p ^ 2 = ev (X 0 + (2 * X 1 * p - X 3 * p ^ 2))
      rw [map_add, map_sub, map_mul, map_mul, map_mul, map_pow]
      rw [hevr, hevr, hevr, hfix, htwo]
      simp <;> ring
    · change X 1 + X 3 * p = ev (X 1 + 0)
      rw [add_zero, hevr]
      rfl
    · change X 2 = ev (X 2 + 0)
      rw [add_zero, hevr]
      simp
    · change X 3 = ev (X 3 + 0)
      rw [add_zero, hevr]
      simp
  rw [heq]
  exact (Tame.subgroup K 4).mul_mem (Tame.elementary_mem _ _ _) (Tame.elementary_mem _ _ _)

end DimensionFourDependence.QuadraticFlow
