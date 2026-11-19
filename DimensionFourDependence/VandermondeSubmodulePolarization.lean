import DimensionFourDependence.Defs

/-! # Finite scalar polarization with actual Vandermonde inverses -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2000000

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A submodule containing every value at a finite set of distinct
scalar parameters contains every coefficient vector. The reconstruction
uses the actual inverse Vandermonde matrix. -/
theorem submodule_contains_vandermonde_coefficients {n : ℕ}
    (V : Submodule K M) (r : Fin n → K) (hr : Function.Injective r)
    (v : Fin n → M) (hv : ∀ i, (∑ j : Fin n, r i ^ (j : ℕ) • v j) ∈ V) :
    ∀ j, v j ∈ V := by
  classical
  let A := Matrix.vandermonde r
  have hdet : A.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hr
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
  intro j
  have he : (∑ i : Fin n, A⁻¹ j i • (∑ k : Fin n, A i k • v k)) = v j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hrow (k : Fin n) : (∑ i, A⁻¹ j i * A i k) = if j = k then 1 else 0 :=
      congrFun (congrFun hinv j) k
    simp only [hrow, ite_smul, one_smul, zero_smul]
    simp
  rw [← he]
  exact V.sum_mem (fun i _ => V.smul_mem _ (hv i))

variable [CharZero K]

/-- The integers `0,...,N` give an actual finite set of distinct
polarization parameters over every characteristic-zero field. -/
theorem submodule_contains_natural_parameter_coefficients {n : ℕ}
    (V : Submodule K M) (v : Fin n → M)
    (hv : ∀ r : K, (∑ j : Fin n, r ^ (j : ℕ) • v j) ∈ V) :
    ∀ j, v j ∈ V := by
  apply submodule_contains_vandermonde_coefficients V (fun i : Fin n => (i.val : K))
    (fun i j h => Fin.ext (Nat.cast_injective h)) v
  intro i
  exact hv (i.val : K)

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Binary monomials are finite scalar combinations of shifted
powers, even after multiplication by an arbitrary fixed coefficient.
This is the polarization step used twice in Lemma 6.2. -/
theorem submodule_contains_binary_monomial_of_shifted_powers
    (V : Submodule K A) (c u q : A) (N : ℕ)
    (hV : ∀ r : K, c * (u + algebraMap K A r * q) ^ N ∈ V)
    (k : ℕ) (hk : k ≤ N) : c * u ^ (N - k) * q ^ k ∈ V := by
  classical
  let v : Fin (N + 1) → A := fun j =>
    (N.choose j.val : K) • (c * u ^ (N - j.val) * q ^ j.val)
  have hv (r : K) : (∑ j : Fin (N + 1), r ^ (j : ℕ) • v j) ∈ V := by
    have he : (∑ j : Fin (N + 1), r ^ (j : ℕ) • v j) =
        c * (u + algebraMap K A r * q) ^ N := by
      rw [add_comm u, add_pow, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [v, smul_smul, Algebra.smul_def, map_mul, map_pow, map_natCast, mul_pow]
      ring
    rw [he]
    exact hV r
  have hm := submodule_contains_natural_parameter_coefficients V v hv ⟨k, by omega⟩
  have hchoose : (N.choose k : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk))
  have hcancel := V.smul_mem (N.choose k : K)⁻¹ hm
  simpa only [v, smul_smul, inv_mul_cancel₀ hchoose, one_smul] using hcancel

end DimensionFourDependence
