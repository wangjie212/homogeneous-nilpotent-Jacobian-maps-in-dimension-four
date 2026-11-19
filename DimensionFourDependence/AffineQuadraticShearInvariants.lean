import DimensionFourDependence.AffineTangentQuadraticPotential
import DimensionFourDependence.CommutativePolynomialChainRule
import DimensionFourDependence.QuadraticConeLevelSubstitution

/-! # The simultaneous affine tangent invariants are polynomials in w-Q

The constructed quadratic potential straightens both tangent lifts. The
existing level substitution sends their common invariants to coefficient
constants in K[t][x,z]. A constructed inverse substitution recovers the
entire original polynomial as a polynomial in the original w-Q.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- Reconstruct the original source from the independent level ring by
taking t=w-Q and retaining the original x,z coordinates. -/
noncomputable def affineConeLevelReconstruction (Q : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) (Polynomial K) →+* MvPolynomial (Fin 3) K :=
  MvPolynomial.eval₂Hom (Polynomial.aeval (X 2 - rename Fin.castSucc Q)).toRingHom
    (fun i : Fin 2 => X i.castSucc)

/-- Each coefficient polynomial is evaluated at the entire original w-Q. -/
theorem affineConeLevelReconstruction_C (Q : MvPolynomial (Fin 2) K) (F : Polynomial K) :
    affineConeLevelReconstruction Q (C F) = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F := by
  simp only [affineConeLevelReconstruction, MvPolynomial.eval₂Hom_C]
  rfl

/-- The transverse coordinates are reconstructed in their original positions. -/
theorem affineConeLevelReconstruction_X (Q : MvPolynomial (Fin 2) K) (i : Fin 2) :
    affineConeLevelReconstruction Q (X i) = X i.castSucc := by
  simp only [affineConeLevelReconstruction, MvPolynomial.eval₂Hom_X']

/-- Every original binary polynomial is reconstructed in its original
source coordinates, with all constant coefficients preserved. -/
theorem affineConeLevelReconstruction_binary (Q q : MvPolynomial (Fin 2) K) :
    affineConeLevelReconstruction Q (MvPolynomial.map Polynomial.C q) = rename Fin.castSucc q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, affineConeLevelReconstruction_C, Polynomial.aeval_C, rename_C]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, hp, rename_X, affineConeLevelReconstruction_X]

/-- Reconstruction after the level substitution is the identity on
every original affine polynomial. -/
theorem affineConeLevelReconstruction_substitution_inverse
    (Q : MvPolynomial (Fin 2) K) (P : MvPolynomial (Fin 3) K) :
    affineConeLevelReconstruction Q (affineConeLevelSubstitution Q P) = P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have ha : affineConeLevelSubstitution Q (C a) = C (Polynomial.C a) :=
      (affineConeLevelSubstitution Q).commutes a
    rw [ha, affineConeLevelReconstruction_C, Polynomial.aeval_C]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    rw [affineConeLevelSubstitution_X]
    fin_cases i
    · change affineConeLevelReconstruction Q (X (0 : Fin 2)) = X (0 : Fin 3)
      exact affineConeLevelReconstruction_X Q 0
    · change affineConeLevelReconstruction Q (X (1 : Fin 2)) = X (1 : Fin 3)
      exact affineConeLevelReconstruction_X Q 1
    · change affineConeLevelReconstruction Q
        (C Polynomial.X + MvPolynomial.map Polynomial.C Q) = X (2 : Fin 3)
      rw [map_add, affineConeLevelReconstruction_C, Polynomial.aeval_X,
        affineConeLevelReconstruction_binary]
      exact sub_add_cancel _ _

/-- The level substitution straightens the two actual gradient lifts
of Q to the ordinary transverse partials over K[t]. -/
theorem affineConeLevelSubstitution_transverse_partial
    (Q : MvPolynomial (Fin 2) K) (P : MvPolynomial (Fin 3) K) (i : Fin 2) :
    pderiv i (affineConeLevelSubstitution Q P) =
      affineConeLevelSubstitution Q (pderiv i.castSucc P +
        rename Fin.castSucc (pderiv i Q) * pderiv (2 : Fin 3) P) := by
  let v : Fin 3 → MvPolynomial (Fin 2) (Polynomial K) :=
    ![X 0, X 1, C Polynomial.X + MvPolynomial.map Polynomial.C Q]
  have he := derivation_commutative_aeval_chain_rule
    ((pderiv (R := Polynomial K) i).restrictScalars K) v P
  change pderiv i (affineConeLevelSubstitution Q P) =
    ∑ j : Fin 3, affineConeLevelSubstitution Q (pderiv j P) * pderiv i (v j) at he
  rw [map_add, map_mul, affineConeLevelSubstitution_binary, ← pderiv_map]
  fin_cases i <;> simpa [v, Fin.sum_univ_succ, mul_comm] using he

variable [CharZero K]

/-- A simultaneous invariant of the two gradient lifts of Q is exactly
a polynomial in the original source expression w-Q. -/
theorem quadratic_gradient_lifts_invariant_polynomial_in_graph
    (Q : MvPolynomial (Fin 2) K) (P : MvPolynomial (Fin 3) K)
    (hx : pderiv (0 : Fin 3) P + rename Fin.castSucc (pderiv (0 : Fin 2) Q) * pderiv (2 : Fin 3) P = 0)
    (hz : pderiv (1 : Fin 3) P + rename Fin.castSucc (pderiv (1 : Fin 2) Q) * pderiv (2 : Fin 3) P = 0) :
    ∃ F : Polynomial K, P = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F := by
  have hp (i : Fin 2) : pderiv i (affineConeLevelSubstitution Q P) = 0 := by
    rw [affineConeLevelSubstitution_transverse_partial]
    fin_cases i
    · change affineConeLevelSubstitution Q (pderiv (0 : Fin 3) P +
        rename Fin.castSucc (pderiv (0 : Fin 2) Q) * pderiv (2 : Fin 3) P) = 0
      rw [hx, map_zero]
    · change affineConeLevelSubstitution Q (pderiv (1 : Fin 3) P +
        rename Fin.castSucc (pderiv (1 : Fin 2) Q) * pderiv (2 : Fin 3) P) = 0
      rw [hz, map_zero]
  have hc := polynomial_all_partials_zero_eq_constant (affineConeLevelSubstitution Q P) hp
  refine ⟨(affineConeLevelSubstitution Q P).coeff 0, ?_⟩
  calc
    P = affineConeLevelReconstruction Q (affineConeLevelSubstitution Q P) :=
      (affineConeLevelReconstruction_substitution_inverse Q P).symm
    _ = affineConeLevelReconstruction Q (C ((affineConeLevelSubstitution Q P).coeff 0)) := congrArg _ hc
    _ = _ := affineConeLevelReconstruction_C _ _

/-- Every polynomial in the graph parameter is killed by both actual
gradient lifts, giving the reverse inclusion of the simultaneous invariant
ring as well. -/
theorem quadratic_graph_polynomial_gradient_lifts_invariant
    (Q : MvPolynomial (Fin 2) K) (F : Polynomial K) :
    (pderiv (0 : Fin 3) (Polynomial.aeval (X 2 - rename Fin.castSucc Q) F) +
      rename Fin.castSucc (pderiv (0 : Fin 2) Q) *
        pderiv (2 : Fin 3) (Polynomial.aeval (X 2 - rename Fin.castSucc Q) F) = 0) ∧
    (pderiv (1 : Fin 3) (Polynomial.aeval (X 2 - rename Fin.castSucc Q) F) +
      rename Fin.castSucc (pderiv (1 : Fin 2) Q) *
        pderiv (2 : Fin 3) (Polynomial.aeval (X 2 - rename Fin.castSucc Q) F) = 0) := by
  have h0 : pderiv (0 : Fin 3) (rename Fin.castSucc Q) = rename Fin.castSucc (pderiv (0 : Fin 2) Q) :=
    pderiv_rename (Fin.castSucc_injective 2) (0 : Fin 2) Q
  have h1 : pderiv (1 : Fin 3) (rename Fin.castSucc Q) = rename Fin.castSucc (pderiv (1 : Fin 2) Q) :=
    pderiv_rename (Fin.castSucc_injective 2) (1 : Fin 2) Q
  constructor <;>
    simp [affine_partial_polynomial_parameter_chain_rule, h0, h1, binary_rename_vertex_pderiv_zero] <;> ring

/-- The simultaneous polynomial invariants of the two gradient lifts
are exactly the polynomials in the original w-Q source expression. -/
theorem quadratic_gradient_lifts_invariant_iff_polynomial_in_graph
    (Q : MvPolynomial (Fin 2) K) (P : MvPolynomial (Fin 3) K) :
    ((pderiv (0 : Fin 3) P + rename Fin.castSucc (pderiv (0 : Fin 2) Q) * pderiv (2 : Fin 3) P = 0) ∧
      (pderiv (1 : Fin 3) P + rename Fin.castSucc (pderiv (1 : Fin 2) Q) * pderiv (2 : Fin 3) P = 0)) ↔
      ∃ F : Polynomial K, P = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F := by
  constructor
  · rintro ⟨hx, hz⟩
    exact quadratic_gradient_lifts_invariant_polynomial_in_graph Q P hx hz
  · rintro ⟨F, rfl⟩
    exact quadratic_graph_polynomial_gradient_lifts_invariant Q F

/-- Actual normalized affine tangent lifts of an invariant with P_w
nonzero construct both the quadratic potential and the nonconstant
univariate polynomial representing the entire original invariant. -/
theorem invariant_affine_tangent_lifts_construct_quadratic_composite_parameter
    (P : MvPolynomial (Fin 3) K) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (b c : Fin 3 → K) (hx : affineTangentLiftX b P = 0) (hz : affineTangentLiftZ c P = 0) :
    ∃ (Q : MvPolynomial (Fin 2) K) (F : Polynomial K),
      Q.totalDegree ≤ 2 ∧ 0 < F.natDegree ∧
      P = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F := by
  obtain ⟨Q, hQ, hQx, hQz⟩ := invariant_affine_tangent_lifts_construct_quadratic_potential P hPw b c hx hz
  have hx' : pderiv (0 : Fin 3) P + rename Fin.castSucc (pderiv (0 : Fin 2) Q) * pderiv (2 : Fin 3) P = 0 := by
    rw [hQx]
    exact (affineTangentLiftX_apply b P).symm.trans hx
  have hz' : pderiv (1 : Fin 3) P + rename Fin.castSucc (pderiv (1 : Fin 2) Q) * pderiv (2 : Fin 3) P = 0 := by
    rw [hQz]
    exact (affineTangentLiftZ_apply c P).symm.trans hz
  obtain ⟨F, hP⟩ := quadratic_gradient_lifts_invariant_polynomial_in_graph Q P hx' hz'
  have hF : 0 < F.natDegree := by
    by_contra! hzero
    have hc := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hzero)
    apply hPw
    rw [hP, hc, Polynomial.aeval_C]
    exact (pderiv (R := K) (2 : Fin 3)).map_algebraMap _
  exact ⟨Q, F, hQ, hF, hP⟩

end DimensionFourDependence
