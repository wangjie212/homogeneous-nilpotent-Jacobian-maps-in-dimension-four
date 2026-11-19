import DimensionFourDependence.LinearSubst

/-! # Nilpotent reductions for Sections 1 and 2 of the dimension-four paper -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-- The exact assertion of Theorem 1.1. This definition is a specification,
not a proof of the assertion. -/
def DependenceTheorem (K : Type*) [Field K] [CharZero K] : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ H : Fin 4 → MvPolynomial (Fin 4) K,
    IsHomogMap H d → IsNilpotent (jac H) → ComponentsDependent H

/-- The rank reduction at the start of Section 2.1. -/
theorem rank_at_most_three (H : Fin 4 → MvPolynomial (Fin 4) K)
    (hN : IsNilpotent (jac H)) : polyRank (jac H) ≤ 3 := by
  have := polyRank_lt_of_isNilpotent (jac H) hN (by norm_num)
  omega

/-- The equivalence stated immediately after Theorem 1.1 follows from
Cayley--Hamilton and the characteristic polynomial of a nilpotent matrix. -/
theorem nilpotent_iff_fourth_power_zero
    (N : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K)) :
    IsNilpotent N ↔ N ^ 4 = 0 := by
  constructor
  · intro hN
    have hc : N.charpoly = Polynomial.X ^ 4 := by
      exact sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
    simpa only [hc, map_pow, Polynomial.aeval_X] using Matrix.aeval_self_charpoly N
  · exact fun h => ⟨4, h⟩

/-- Nilpotence supplies the divergence identity used throughout the paper. -/
theorem trace_jac_zero (H : Fin 4 → MvPolynomial (Fin 4) K)
    (hN : IsNilpotent (jac H)) : Matrix.trace (jac H) = 0 :=
  (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero

/-- A constant left kernel of the Jacobian gives the required constant relation,
by Euler's identity. This is also the Gauss-image-point case of Section 5.5. -/
theorem dependent_of_constant_left_kernel [CharZero K] {n d : ℕ}
    (H : Fin n → MvPolynomial (Fin n) K) (hd : 0 < d) (hH : IsHomogMap H d)
    (c : Fin n → K) (hc : c ≠ 0)
    (hker : (fun i => C (c i)) ᵥ* jac H = 0) : ComponentsDependent H := by
  refine ⟨c, hc, ?_⟩
  simpa only [MvPolynomial.smul_eq_C_mul] using
    left_normal_dot_eq_zero H (fun i => C (c i)) (by omega) hH hker

/-- Theorem 1.1 in degree one, over the original coefficient field. -/
theorem dependence_degree_one [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (hH : IsHomogMap H 1) (hN : IsNilpotent (jac H)) : ComponentsDependent H := by
  let A : Matrix (Fin 4) (Fin 4) K := fun i j => ((jac H) i j).coeff 0
  have hA : ∀ i j, (jac H) i j = C (A i j) := fun i j =>
    eq_C_of_isHomogeneous_zero ((hH i).pderiv (i := j))
  have hdet : (jac H).det = 0 :=
    det_eq_zero_of_polyRank_lt _ (by have := rank_at_most_three H hN; omega)
  have hmap : (jac H).map constantCoeff = A := by
    ext i j
    rfl
  have hAdet : A.det = 0 := by
    have h := congrArg (fun p : MvPolynomial (Fin 4) K => p.coeff 0) hdet
    change constantCoeff (Matrix.det (jac H)) = 0 at h
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply, hmap] using h
  obtain ⟨c, hc, hker⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hAdet
  apply dependent_of_constant_left_kernel H (by norm_num) hH c hc
  funext j
  change (∑ i, C (c i) * (jac H) i j) = 0
  simp only [hA, ← map_mul, ← map_sum]
  have hz : ∑ i, c i * A i j = 0 := congrFun hker j
  rw [hz, map_zero]

/-- The rank-at-most-one part of the rank reduction, with no geometric
classification theorem required. -/
theorem dependence_rank_at_most_one [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ}
    (hd : 0 < d) (hH : IsHomogMap H d) (hr : polyRank (jac H) ≤ 1) :
    ComponentsDependent H := by
  by_cases hzero : H = 0
  · subst H
    exact ⟨fun _ => 1, by simp [funext_iff], by simp⟩
  obtain ⟨i, hi⟩ : ∃ i, H i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hzero
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨c, hc⟩ := lemma_2_1_rank_le_one H hd hH hr i j hi
  refine ⟨Pi.single j 1 - c • Pi.single i 1, ?_, ?_⟩
  · intro hz
    have h := congrFun hz j
    simp [Pi.single_apply, hji] at h
  · simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply,
      Finset.sum_ite_eq', hc]

/-- Nilpotence forbids any nonzero eigenvalue of a polynomial left covector.
This is the elementary obstruction used in Sections 2.2, 4.5 and 5.3. -/
theorem eigenvalue_zero_of_nilpotent {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (N : Matrix (Fin n) (Fin n) R) (hN : IsNilpotent N)
    (v : Fin n → R) (hv : v ≠ 0) (a : R) (he : v ᵥ* N = a • v) : a = 0 := by
  obtain ⟨k, hk⟩ := hN
  have hp : ∀ j : ℕ, v ᵥ* N ^ j = a ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← vecMul_vecMul, ih, smul_vecMul, he, smul_smul, pow_succ]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  have hz := congrFun (hp k) i
  rw [hk] at hz
  simp only [vecMul_zero, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hz
  have ha : a ^ k = 0 := (mul_eq_zero.mp hz.symm).resolve_right hi
  exact isNilpotent_iff_eq_zero.mp ⟨k, ha⟩

end DimensionFourDependence
