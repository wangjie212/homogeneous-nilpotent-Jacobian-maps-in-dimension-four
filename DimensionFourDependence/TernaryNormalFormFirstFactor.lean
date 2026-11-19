import DimensionFourDependence.HomogenizedTernaryNormalForm
import DimensionFourDependence.Tame

/-! # The invariant-preserving factor A of Proposition 6.6 -/

namespace DimensionFourDependence.TernaryNormalForm

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "t" => (X (Fin.last 3))

theorem factorAx_parameter_notMem : (0 : Fin 4) ∉ ((t : R₄) * X 2).vars := by
  intro h
  have hh := vars_mul _ _ h
  simpa using hh

theorem factorAy_parameter_notMem :
    (1 : Fin 4) ∉ (-(2 : R₄) * X 0 * X 2 + t * X 2 ^ 2).vars := by
  have h := Tame.notMem_vars_aeval (![X 0, X 2, t] : Fin 3 → R₄)
    (-2 * X 0 * X 1 + X 2 * X 1 ^ 2) 1 (by intro j; fin_cases j <;> simp)
  simpa [map_ofNat] using h

noncomputable def factorAx4 : R₄ ≃ₐ[K] R₄ :=
  Tame.elementary 0 (t * X 2) factorAx_parameter_notMem

noncomputable def factorAy4 : R₄ ≃ₐ[K] R₄ :=
  Tame.elementary 1 (-2 * X 0 * X 2 + t * X 2 ^ 2) factorAy_parameter_notMem

/-- The pullback of `(x+tz,y-2xz-tz²,z,t)`. -/
noncomputable def factorA4 : R₄ ≃ₐ[K] R₄ := factorAx4 * factorAy4

theorem factorA4_X (j : Fin 4) : factorA4 (X j : R₄) =
    ![X 0 + t * X 2, X 1 - 2 * X 0 * X 2 - t * X 2 ^ 2, X 2, t] j := by
  have hx (i : Fin 4) : factorAx4 (X i : R₄) = X i + if i = 0 then t * X 2 else 0 :=
    Tame.elementary_X _ _ _ i
  have hy (i : Fin 4) : factorAy4 (X i : R₄) =
      X i + if i = 1 then -2 * X 0 * X 2 + t * X 2 ^ 2 else 0 :=
    Tame.elementary_X _ _ _ i
  have htwo : factorAx4 (2 : R₄) = 2 := map_ofNat _ 2
  have ht : (Fin.last 3 : Fin 4) = 3 := rfl
  rw [factorA4, AlgEquiv.mul_apply, hy]
  fin_cases j <;> simp [map_add, map_mul, map_pow, map_neg, hx, htwo, ht] <;> ring

theorem factorA4_inv_X (j : Fin 4) : factorA4⁻¹ (X j : R₄) =
    ![X 0 - t * X 2, X 1 + 2 * X 0 * X 2 - t * X 2 ^ 2, X 2, t] j := by
  apply (factorA4 (K := K)).injective
  have htwo : factorA4 (2 : R₄) = 2 := map_ofNat _ 2
  have ht : (Fin.last 3 : Fin 4) = 3 := rfl
  rw [show factorA4 (factorA4⁻¹ (X j : R₄)) = X j from factorA4.apply_symm_apply _]
  fin_cases j <;>
    simp [map_add, map_sub, map_mul, map_pow, factorA4_X, htwo, ht] <;> ring

theorem factorA4_tame : factorA4 (K := K) ∈ Tame.subgroup K 4 :=
  (Tame.subgroup K 4).mul_mem (Tame.elementary_mem _ _ _) (Tame.elementary_mem _ _ _)

theorem factorA4_invariant : factorA4 (quadratic4 (K := K)) = quadratic4 := by
  have ht : (Fin.last 3 : Fin 4) = 3 := rfl
  simp [quadratic4, factorA4_X, ht]
  ring

theorem factorA4_last : factorA4 (t : R₄) = t := factorA4_X (Fin.last 3)

theorem factorA4_inv_invariant : factorA4⁻¹ (quadratic4 (K := K)) = quadratic4 := by
  apply (factorA4 (K := K)).injective
  exact (factorA4.apply_symm_apply _).trans factorA4_invariant.symm

theorem factorA4_inv_last : factorA4⁻¹ (t : R₄) = t := by
  apply (factorA4 (K := K)).injective
  exact (factorA4.apply_symm_apply _).trans factorA4_last.symm

/-- Any coefficient-preserving substitution fixing the two inputs
of the homogeneous numerator also fixes both polynomial parameters. -/
theorem normal_parameters_fixed (E : R₄ →ₐ[K] R₄)
    (ht : E t = t) (hq : E quadratic4 = quadratic4) (P : Polynomial K) (d : ℕ) :
    E (q4 P d) = q4 P d ∧ E (correction4 P d) = correction4 P d := by
  have hn : E (numerator4 P) = numerator4 P := by
    rw [numerator4, homogeneousParameterPolynomialValue_algHom, hq, map_pow, ht]
  exact ⟨by simp only [q4, map_mul, map_pow, ht, hn],
    by simp only [correction4, map_mul, map_pow, ht, hn]⟩

end DimensionFourDependence.TernaryNormalForm
