import DimensionFourDependence.AffineTangentCommutator

/-! # Constructing the quadratic potential of actual affine tangent lifts

The closed coefficient relation obtained from the invariant and P_w
constructs the original binary quadratic polynomial explicitly. Its two
partials are the full affine vertical coefficients; its degree bound is
proved without assuming any quadratic graph parameter in advance.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]

/-- The actual potential with zero constant coefficient. -/
noncomputable def affineTangentQuadraticPotential (b c : Fin 3 → K) : MvPolynomial (Fin 2) K :=
  C (b 1 / 2) * X 0 ^ 2 + C (b 2) * X 0 * X 1 + C (c 2 / 2) * X 1 ^ 2 +
    C (b 0) * X 0 + C (c 0) * X 1

/-- Its entire original transverse degree is at most two. -/
theorem affineTangentQuadraticPotential_degree_le_two (b c : Fin 3 → K) :
    (affineTangentQuadraticPotential b c).totalDegree ≤ 2 := by
  have hadd (p q : MvPolynomial (Fin 2) K) (hp : p.totalDegree ≤ 2) (hq : q.totalDegree ≤ 2) :
      (p + q).totalDegree ≤ 2 := (totalDegree_add p q).trans (max_le hp hq)
  have hquad (a : K) (i : Fin 2) : (C a * (X i : MvPolynomial (Fin 2) K) ^ 2).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simp)
  have hlinear (a : K) (i : Fin 2) : (C a * (X i : MvPolynomial (Fin 2) K)).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simp)
  have hmixed : (C (b 2) * (X (0 : Fin 2) : MvPolynomial (Fin 2) K) * X 1).totalDegree ≤ 2 := by
    apply (totalDegree_mul _ _).trans
    have he : (C (b 2) * (X (0 : Fin 2) : MvPolynomial (Fin 2) K)).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by simp)
    exact (Nat.add_le_add_right he _).trans (by simp)
  exact hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hquad _ _) hmixed) (hquad _ _))
    (hlinear _ _)) (hlinear _ _)

/-- The x derivative is the whole first affine vertical coefficient. -/
theorem affineTangentQuadraticPotential_pderiv_x (b c : Fin 3 → K) :
    pderiv (0 : Fin 2) (affineTangentQuadraticPotential b c) =
      C (b 0) + C (b 1) * X 0 + C (b 2) * X 1 := by
  have hcoeff (a : K) : C (a / 2) * (2 : MvPolynomial (Fin 2) K) = C a := by
    change C (a / 2) * C (2 : K) = C a
    rw [← map_mul, div_mul_cancel₀ _ (by norm_num : (2 : K) ≠ 0)]
  simp [affineTangentQuadraticPotential, Derivation.leibniz, smul_eq_mul, pderiv_pow]
  linear_combination X 0 * hcoeff (b 1)

/-- Closedness identifies the z derivative with the whole second
affine vertical coefficient. -/
theorem affineTangentQuadraticPotential_pderiv_z
    (b c : Fin 3 → K) (hclosed : b 2 = c 1) :
    pderiv (1 : Fin 2) (affineTangentQuadraticPotential b c) =
      C (c 0) + C (c 1) * X 0 + C (c 2) * X 1 := by
  have hcoeff (a : K) : C (a / 2) * (2 : MvPolynomial (Fin 2) K) = C a := by
    change C (a / 2) * C (2 : K) = C a
    rw [← map_mul, div_mul_cancel₀ _ (by norm_num : (2 : K) ≠ 0)]
  rw [← hclosed]
  simp [affineTangentQuadraticPotential, Derivation.leibniz, smul_eq_mul, pderiv_pow]
  linear_combination X 1 * hcoeff (c 2)

/-- Two normalized actual tangent lifts of an invariant with P_w
nonzero construct a quadratic binary potential for both complete vertical
coefficients. No closedness or potential is supplied as a hypothesis. -/
theorem invariant_affine_tangent_lifts_construct_quadratic_potential
    (P : MvPolynomial (Fin 3) K) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (b c : Fin 3 → K) (hx : affineTangentLiftX b P = 0) (hz : affineTangentLiftZ c P = 0) :
    ∃ Q : MvPolynomial (Fin 2) K, Q.totalDegree ≤ 2 ∧
      rename Fin.castSucc (pderiv (0 : Fin 2) Q) = affineTangentVerticalCoefficient b ∧
      rename Fin.castSucc (pderiv (1 : Fin 2) Q) = affineTangentVerticalCoefficient c := by
  have hclosed := invariant_affine_tangent_lifts_closed P hPw b c hx hz
  refine ⟨affineTangentQuadraticPotential b c, affineTangentQuadraticPotential_degree_le_two b c, ?_, ?_⟩
  · rw [affineTangentQuadraticPotential_pderiv_x]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl
  · rw [affineTangentQuadraticPotential_pderiv_z b c hclosed]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl

end DimensionFourDependence
