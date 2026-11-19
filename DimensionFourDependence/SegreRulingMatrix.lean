import DimensionFourDependence.NormalizedRulingAlgebraicity

/-! # The two original Segre ruling kernels and their exact dimensions -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 3000000

variable {R F E : Type*} [CommRing R] [Field F] [Field E]

/-- The two ruling equations in the original four-coordinate order.
Index one holds the first row ratio fixed; index two holds the second. -/
def segreRulingMatrix (j : Fin 3) (t : R) : Matrix (Fin 2) (Fin 4) R :=
  if j = 1 then !![-t, 1, 0, 0; 0, 0, -t, 1]
  else !![-t, 0, 1, 0; 0, -t, 0, 1]

theorem segreRulingMatrix_map (f : R →+* F) (j : Fin 3) (t : R) :
    (segreRulingMatrix j t).map f = segreRulingMatrix j (f t) := by
  by_cases hj : j = 1 <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [segreRulingMatrix, hj, Matrix.map_apply]

theorem segreRulingMatrix_mulVec (j : Fin 3) (t : F) (b : Fin 4 → F) :
    segreRulingMatrix j t *ᵥ b =
      if j = 1 then ![b 1 - t * b 0, b 3 - t * b 2]
      else ![b 2 - t * b 0, b 3 - t * b 1] := by
  by_cases hj : j = 1 <;> ext i <;> fin_cases i <;>
    simp [segreRulingMatrix, hj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Each ruling is an actual two-dimensional vector kernel. -/
theorem segreRulingMatrix_kernel_finrank (j : Fin 3) (t : F) :
    Module.finrank F (LinearMap.ker (segreRulingMatrix j t).toLin') = 2 := by
  have hLI : LinearIndependent F (segreRulingMatrix j t).row := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hcol (k : Fin 4) : (∑ l : Fin 2, c l * segreRulingMatrix j t l k) = 0 := by
      have he := congrFun hc k
      simpa [Fin.sum_univ_two, smul_eq_mul] using he
    by_cases hj : j = 1
    · have h0 : c 0 = 0 := by simpa [segreRulingMatrix, hj, Fin.sum_univ_two] using hcol 1
      have h1 : c 1 = 0 := by simpa [segreRulingMatrix, hj, Fin.sum_univ_two] using hcol 3
      fin_cases i <;> assumption
    · have h0 : c 0 = 0 := by simpa [segreRulingMatrix, hj, Fin.sum_univ_two] using hcol 2
      have h1 : c 1 = 0 := by simpa [segreRulingMatrix, hj, Fin.sum_univ_two] using hcol 3
      fin_cases i <;> assumption
  have hrank : (segreRulingMatrix j t).rank = 2 := by simpa using hLI.rank_matrix
  have hdim := LinearMap.finrank_range_add_finrank_ker (segreRulingMatrix j t).toLin'
  have hr : Module.finrank F (LinearMap.range (segreRulingMatrix j t).toLin') = 2 := hrank
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- The kernel equations recover the specified original ruling ratio. -/
theorem segreRulingMatrix_kernel_coordinate_relation
    (j : Fin 3) (hj : j ≠ 0) (t : F) (b : Fin 4 → F)
    (hb : segreRulingMatrix j t *ᵥ b = 0) : b j.castSucc = t * b 0 := by
  have he := congrFun hb 0
  fin_cases j
  · exact False.elim (hj rfl)
  · change b 1 = t * b 0
    simpa [segreRulingMatrix_mulVec, sub_eq_zero] using he
  · change b 2 = t * b 0
    simpa [segreRulingMatrix_mulVec, sub_eq_zero] using he

/-- The actual original determinant equation puts the output vector
on each original ruling through its own ratio, without a selected line. -/
theorem segre_output_mem_ruling_kernel
    (Q : Fin 4 → F) (hQ0 : Q 0 ≠ 0) (hquad : Q 0 * Q 3 - Q 1 * Q 2 = 0)
    (j : Fin 3) (hj : j ≠ 0) :
    segreRulingMatrix j (Q j.castSucc / Q 0) *ᵥ Q = 0 := by
  rw [segreRulingMatrix_mulVec]
  fin_cases j
  · exact False.elim (hj rfl)
  · ext i
    fin_cases i <;> simp <;> field_simp [hQ0] <;>
      first | (solve | ring) | (solve | simpa only [mul_comm, zero_mul] using hquad)
  · ext i
    fin_cases i <;> simp <;> field_simp [hQ0] <;>
      first | (solve | ring) | (solve | simpa only [mul_comm, zero_mul] using hquad)

end DimensionFourDependence
