import DimensionFourDependence.TernaryNormalFormFirstFactor

/-! # The elementary factors B, E_R and E_z in Proposition 6.6 -/

namespace DimensionFourDependence.TernaryNormalForm

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "t" => (X (Fin.last 3))

theorem quadratic4_notMem_z : (2 : Fin 4) ∉ (quadratic4 (K := K)).vars := by
  have h := Tame.notMem_vars_aeval (![X 0, X 1, t] : Fin 3 → R₄)
    (X 2 * X 1 + X 0 ^ 2) 2 (by intro j; fin_cases j <;> simp)
  simpa [quadratic4] using h

theorem numerator4_notMem_z (P : Polynomial K) : (2 : Fin 4) ∉ (numerator4 P).vars := by
  unfold numerator4 homogeneousParameterPolynomialValue
  apply Tame.notMem_vars_aeval
  intro i
  fin_cases i
  · exact quadratic4_notMem_z
  · intro h
    have hx := vars_pow (t : R₄) 2 h
    simpa using hx

theorem q4_notMem_z (P : Polynomial K) (d : ℕ) : (2 : Fin 4) ∉ (q4 P d).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
  · have hz := vars_pow (t : R₄) _ h
    simpa using hz
  · exact numerator4_notMem_z P h

theorem correction4_notMem_z (P : Polynomial K) (d : ℕ) :
    (2 : Fin 4) ∉ (correction4 P d).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
  · have hz := vars_pow (t : R₄) _ h
    simpa using hz
  · exact numerator4_notMem_z P (vars_pow _ 2 h)

theorem factorEz_parameter_notMem (d : ℕ) : (1 : Fin 4) ∉ ((t : R₄) ^ (d - 1) * X 2).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
  · have hz := vars_pow (t : R₄) _ h
    simpa using hz
  · simpa using h

noncomputable def factorB4 (P : Polynomial K) (d : ℕ) : R₄ ≃ₐ[K] R₄ :=
  Tame.elementary 2 (q4 P d) (q4_notMem_z P d)

noncomputable def factorER4 (P : Polynomial K) (d : ℕ) : R₄ ≃ₐ[K] R₄ :=
  Tame.elementary 2 (correction4 P d) (correction4_notMem_z P d)

noncomputable def factorEz4 (d : ℕ) : R₄ ≃ₐ[K] R₄ :=
  Tame.elementary 1 (t ^ (d - 1) * X 2) (factorEz_parameter_notMem d)

theorem factorB4_X (P : Polynomial K) (d : ℕ) (j : Fin 4) :
    factorB4 P d (X j) = X j + if j = 2 then q4 P d else 0 := Tame.elementary_X _ _ _ j

theorem factorB4_inv_X (P : Polynomial K) (d : ℕ) (j : Fin 4) :
    (factorB4 P d)⁻¹ (X j) = X j + if j = 2 then -q4 P d else 0 := Tame.elementary_inv_X _ _ _ j

theorem factorER4_X (P : Polynomial K) (d : ℕ) (j : Fin 4) :
    factorER4 P d (X j) = X j + if j = 2 then correction4 P d else 0 := Tame.elementary_X _ _ _ j

theorem factorEz4_X (d : ℕ) (j : Fin 4) :
    factorEz4 (K := K) d (X j) = X j + if j = 1 then t ^ (d - 1) * X 2 else 0 := Tame.elementary_X _ _ _ j

theorem factorB4_tame (P : Polynomial K) (d : ℕ) : factorB4 P d ∈ Tame.subgroup K 4 :=
  Tame.elementary_mem _ _ _

theorem factorER4_tame (P : Polynomial K) (d : ℕ) : factorER4 P d ∈ Tame.subgroup K 4 :=
  Tame.elementary_mem _ _ _

theorem factorEz4_tame (d : ℕ) : factorEz4 (K := K) d ∈ Tame.subgroup K 4 :=
  Tame.elementary_mem _ _ _

end DimensionFourDependence.TernaryNormalForm
