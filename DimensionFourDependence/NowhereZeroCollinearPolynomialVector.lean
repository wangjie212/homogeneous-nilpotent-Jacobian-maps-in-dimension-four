import DimensionFourDependence.Defs

/-! # A polynomial vector without zeros on an affine line has constant tangent multiplier -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000

variable {E : Type*} [Field E] [IsAlgClosed E] {n : ℕ}

/-- A polynomial vector collinear with one fixed nonzero direction
and nonzero at every affine parameter is a nonzero constant multiple
of that direction. Algebraic closedness removes a possible nonconstant
polynomial multiplier. -/
theorem nowhere_zero_collinear_polynomial_vector_constant
    (U : Fin n → Polynomial E) (v : Fin n → E) (hv : v ≠ 0)
    (hcross : ∀ i j, U i * Polynomial.C (v j) = U j * Polynomial.C (v i))
    (hnozero : ∀ t : E, (fun i => (U i).eval t) ≠ 0) :
    ∃ c : E, c ≠ 0 ∧ ∀ i, U i = Polynomial.C (c * v i) := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  let μ := Polynomial.C ((v j)⁻¹) * U j
  have hC : Polynomial.C ((v j)⁻¹) * Polynomial.C (v j) = (1 : Polynomial E) := by
    rw [← map_mul, inv_mul_cancel₀ hj, map_one]
  have hU (i : Fin n) : U i = Polynomial.C (v i) * μ := by
    calc
      U i = Polynomial.C ((v j)⁻¹) * (U i * Polynomial.C (v j)) := by
        calc
          _ = U i * (Polynomial.C ((v j)⁻¹) * Polynomial.C (v j)) := by rw [hC, mul_one]
          _ = _ := by ring
      _ = Polynomial.C ((v j)⁻¹) * (U j * Polynomial.C (v i)) := by rw [hcross]
      _ = _ := by dsimp [μ]; ring
  have hμ (t : E) : μ.eval t ≠ 0 := by
    intro hz
    apply hnozero t
    funext i
    rw [hU, Polynomial.eval_mul, hz, mul_zero]
    rfl
  have hdegree : μ.natDegree = 0 := by
    by_contra hz
    have hpos : 0 < μ.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root μ hpos.ne'
    exact hμ t ht
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hc : μ.coeff 0 ≠ 0 := by
    intro hz
    apply hμ 0
    rw [hconstant, Polynomial.eval_C, hz]
  refine ⟨μ.coeff 0, hc, ?_⟩
  intro i
  calc
    U i = Polynomial.C (v i) * μ := hU i
    _ = Polynomial.C (v i) * Polynomial.C (μ.coeff 0) :=
      congrArg (fun P => Polynomial.C (v i) * P) hconstant
    _ = _ := by rw [← map_mul]; congr 1; ring

end DimensionFourDependence
