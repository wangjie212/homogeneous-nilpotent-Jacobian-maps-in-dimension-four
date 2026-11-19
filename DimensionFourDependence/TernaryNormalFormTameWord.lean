import DimensionFourDependence.TernaryNormalFormElementaryFactors
import DimensionFourDependence.TernaryNormalFormCommutatorIdentity

/-! # The actual tame word of Proposition 6.6 -/

namespace DimensionFourDependence.TernaryNormalForm

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "t" => (X (Fin.last 3))

/-- The polynomial pullback of the commutator in equation (6.13). -/
noncomputable def normalCommutator4 (P : Polynomial K) (d : ℕ) : R₄ ≃ₐ[K] R₄ :=
  (factorB4 P d)⁻¹ * factorA4⁻¹ * factorB4 P d * factorA4

theorem normalCommutator4_X (P : Polynomial K) (d : ℕ) (j : Fin 4) :
    normalCommutator4 P d (X j) =
      ![X 0 + t * q4 P d, X 1 - 2 * X 0 * q4 P d - t * q4 P d ^ 2, X 2, t] j := by
  have hi : factorA4⁻¹ (q4 P d) = q4 P d :=
    (normal_parameters_fixed ((factorA4 (K := K))⁻¹).toAlgHom
      factorA4_inv_last factorA4_inv_invariant P d).1
  have hj : (factorB4 P d)⁻¹ (q4 P d) = q4 P d :=
    Tame.elementary_inv_fixed _ _ _ _ (q4_notMem_z P d)
  have hv (i : Fin 4) : factorB4 P d (X i) = ![X 0, X 1, X 2 + q4 P d, t] i := by
    rw [factorB4_X]
    fin_cases i <;> simp
  have hjx (i : Fin 4) : (factorB4 P d)⁻¹ (X i) = ![X 0, X 1, X 2 - q4 P d, t] i := by
    rw [factorB4_inv_X]
    fin_cases i <;> simp [sub_eq_add_neg]
  exact normal_form_commutator_identity
    (factorA4 (K := K)).toAlgHom (factorB4 P d).toAlgHom
    ((factorA4 (K := K))⁻¹).toAlgHom ((factorB4 P d)⁻¹).toAlgHom
    X (q4 P d) factorA4_X hv factorA4_inv_X hjx hi hj j

theorem normalCommutator4_invariant (P : Polynomial K) (d : ℕ) :
    normalCommutator4 P d quadratic4 = quadratic4 := by
  have ht : (Fin.last 3 : Fin 4) = 3 := rfl
  simp [quadratic4, normalCommutator4_X, ht]
  ring

theorem normalCommutator4_correction (P : Polynomial K) (d : ℕ) :
    normalCommutator4 P d (correction4 P d) = correction4 P d :=
  (normal_parameters_fixed (normalCommutator4 P d).toAlgHom
    (normalCommutator4_X P d (Fin.last 3)) (normalCommutator4_invariant P d) P d).2

theorem normalCommutator4_tame (P : Polynomial K) (d : ℕ) :
    normalCommutator4 P d ∈ Tame.subgroup K 4 := by
  let G := Tame.subgroup K 4
  have hA : factorA4 (K := K) ∈ G := factorA4_tame
  have hB : factorB4 P d ∈ G := factorB4_tame P d
  exact G.mul_mem (G.mul_mem (G.mul_mem (G.inv_mem hB) (G.inv_mem hA)) hB) hA

/-- The reversed substitution word of equation (6.14). -/
noncomputable def normalFormAutomorphism4 (P : Polynomial K) (d : ℕ) : R₄ ≃ₐ[K] R₄ :=
  normalCommutator4 P d * factorER4 P d * factorEz4 d

theorem normalFormAutomorphism4_tame (P : Polynomial K) (d : ℕ) :
    normalFormAutomorphism4 P d ∈ Tame.subgroup K 4 :=
  (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem (normalCommutator4_tame P d) (factorER4_tame P d))
    (factorEz4_tame d)

theorem normal_form_word_coordinates (P : Polynomial K) (d : ℕ) (j : Fin 4) :
    (![X 0 + t * q4 P d, X 1 + (t ^ (d - 1) * X 2 - 2 * X 0 * q4 P d),
        X 2 + correction4 P d, t] : Fin 4 → R₄) j = X j + perturbation4 P d j := by
  exact normal_form_coordinatewise_addition (X : Fin 4 → R₄)
    (t * q4 P d) (t ^ (d - 1) * X 2 - 2 * X 0 * q4 P d) (correction4 P d) j

set_option maxHeartbeats 300000 in
/-- The last two elementary factors remove the quadratic correction
and give the exact four-variable perturbation of Proposition 6.6. -/
theorem normalFormAutomorphism4_X (P : Polynomial K) {d : ℕ}
    (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d) (j : Fin 4) :
    normalFormAutomorphism4 P d (X j) = X j + perturbation4 P d j := by
  have hu (i : Fin 4) : factorER4 P d (X i) = ![X 0, X 1, X 2 + correction4 P d, t] i := by
    rw [factorER4_X]
    fin_cases i <;> simp
  have hv (i : Fin 4) : factorEz4 (K := K) d (X i) = ![X 0, X 1 + t ^ (d - 1) * X 2, X 2, t] i := by
    rw [factorEz4_X]
    fin_cases i <;> simp
  have h := normal_form_finishing_identity (normalCommutator4 P d)
    (factorER4 P d) (factorEz4 (K := K) d)
    (X : Fin 4 → R₄) (q4 P d) (correction4 P d) (d - 1)
    (normalCommutator4_X P d) hu hv (normalCommutator4_correction P d)
    (q4_correction4_square_identity P hm hd) j
  exact h.trans (normal_form_word_coordinates P d j)

end DimensionFourDependence.TernaryNormalForm
