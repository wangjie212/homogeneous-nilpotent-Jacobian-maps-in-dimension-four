import DimensionFourDependence.Laplacian
import DimensionFourDependence.StandardRulingQuadric

/-! # The Section 5.4 Laplacian argument in the original determinant coordinates -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K

set_option maxHeartbeats 2500000

/-- The Laplacian for the split determinant form, in its original coordinates. -/
noncomputable def segreSplitLaplacian : R₀ →ₗ[K] R₀ :=
  (pderiv 0).toLinearMap.comp (pderiv 3).toLinearMap -
    (pderiv 1).toLinearMap.comp (pderiv 2).toLinearMap

theorem segreSplitLaplacian_apply (p : R₀) :
    segreSplitLaplacian p = pderiv 0 (pderiv 3 p) - pderiv 1 (pderiv 2 p) := rfl

/-- The original normal pairing for Delta=X0*X3-X1*X2. -/
noncomputable def segreNormalPairing (V : Fin 4 → R₀) : R₀ :=
  X 3 * V 0 - X 2 * V 1 - X 1 * V 2 + X 0 * V 3

theorem pderiv_segreSplitLaplacian (j : Fin 4) (p : R₀) :
    pderiv j (segreSplitLaplacian p) = segreSplitLaplacian (pderiv j p) := by
  simp only [segreSplitLaplacian_apply, map_sub]
  rw [pderiv_pderiv_comm j 0, pderiv_pderiv_comm j 3,
    pderiv_pderiv_comm j 1, pderiv_pderiv_comm j 2]

theorem segreSplitLaplacian_X_mul (j : Fin 4) (p : R₀) :
    segreSplitLaplacian (X j * p) = X j * segreSplitLaplacian p +
      (if j = 0 then pderiv 3 p else 0) + (if j = 3 then pderiv 0 p else 0) -
      (if j = 1 then pderiv 2 p else 0) - (if j = 2 then pderiv 1 p else 0) := by
  fin_cases j <;>
    simp [segreSplitLaplacian_apply, pderiv_mul, pderiv_X] <;> ring

/-- The split Laplacian of the normal pairing adds the original divergence. -/
theorem segreSplitLaplacian_normalPairing (V : Fin 4 → R₀) :
    segreSplitLaplacian (segreNormalPairing V) =
      segreNormalPairing (fun i => segreSplitLaplacian (V i)) + divergence V := by
  simp [segreNormalPairing, map_add, map_sub, segreSplitLaplacian_X_mul,
    divergence, Fin.sum_univ_succ]
  ring

theorem divergence_segreSplitLaplacian (V : Fin 4 → R₀) :
    divergence (fun i => segreSplitLaplacian (V i)) = segreSplitLaplacian (divergence V) := by
  simp only [divergence, map_sum, pderiv_segreSplitLaplacian]

/-- Both original vanishing constraints persist under every iterate. -/
theorem segreSplitLaplacian_preserves_constraints
    (V : Fin 4 → R₀) (hr : segreNormalPairing V = 0) (hd : divergence V = 0) (j : ℕ) :
    segreNormalPairing (fun i => (segreSplitLaplacian ^ j) (V i)) = 0 ∧
      divergence (fun i => (segreSplitLaplacian ^ j) (V i)) = 0 := by
  induction j with
  | zero => simpa using And.intro hr hd
  | succ j ih =>
    have hr' := segreSplitLaplacian_normalPairing (fun i => (segreSplitLaplacian ^ j) (V i))
    rw [ih.1, ih.2, map_zero, add_zero] at hr'
    have hd' := divergence_segreSplitLaplacian (fun i => (segreSplitLaplacian ^ j) (V i))
    rw [ih.2, map_zero] at hd'
    simpa only [pow_succ', Module.End.mul_apply] using And.intro hr'.symm hd'

theorem segreSplitLaplacian_homogeneous {p : R₀} {d : ℕ} (hp : p.IsHomogeneous d) :
    (segreSplitLaplacian p).IsHomogeneous (d - 2) := by
  rw [segreSplitLaplacian_apply]
  convert ((hp.pderiv (i := 3)).pderiv (i := 0)).sub
    ((hp.pderiv (i := 2)).pderiv (i := 1)) using 1

theorem segreSplitLaplacian_pow_homogeneous {p : R₀} {d : ℕ}
    (hp : p.IsHomogeneous d) (j : ℕ) :
    ((segreSplitLaplacian ^ j) p).IsHomogeneous (d - 2 * j) := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.mul_succ, Nat.sub_sub] using
      segreSplitLaplacian_homogeneous ih

theorem constant_vector_zero_of_segreNormalPairing
    (V : Fin 4 → R₀) (hV : IsHomogMap V 0) (hr : segreNormalPairing V = 0) : V = 0 := by
  have hc : ∀ i, V i = C ((V i).coeff 0) := fun i => eq_C_of_isHomogeneous_zero (hV i)
  have hz (i j : Fin 4) : pderiv j (V i) = 0 := by rw [hc i, pderiv_C]
  have h0 := congrArg (pderiv (3 : Fin 4)) hr
  have h1 := congrArg (pderiv (2 : Fin 4)) hr
  have h2 := congrArg (pderiv (1 : Fin 4)) hr
  have h3 := congrArg (pderiv (0 : Fin 4)) hr
  simp [segreNormalPairing, pderiv_mul, pderiv_X, hz] at h0 h1 h2 h3
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3]

/-- The half-degree iterate kills every component in the original split coordinates. -/
theorem segreSplitLaplacian_half_degree_zero
    (H : Fin 4 → R₀) (m : ℕ) (hH : IsHomogMap H (2 * m))
    (hr : segreNormalPairing H = 0) (hd : divergence H = 0) :
    (fun i => (segreSplitLaplacian ^ m) (H i)) = 0 := by
  apply constant_vector_zero_of_segreNormalPairing
  · intro i
    simpa using segreSplitLaplacian_pow_homogeneous (hH i) m
  · exact (segreSplitLaplacian_preserves_constraints H hr hd m).1

/-- The determinant version of the radial-power recurrence. -/
theorem segreSplitLaplacian_determinant_mul (p : R₀) :
    segreSplitLaplacian (standardRulingPolynomial * p) =
      standardRulingPolynomial * segreSplitLaplacian p +
        (∑ i : Fin 4, X i * pderiv i p) + 2 * p := by
  simp [segreSplitLaplacian_apply, standardRulingPolynomial,
    pderiv_mul, pderiv_X, Fin.sum_univ_succ]
  ring

theorem segreSplitLaplacian_determinant_pow (m : ℕ) :
    segreSplitLaplacian ((standardRulingPolynomial (F := K)) ^ (m + 1)) =
      ((m + 1) * (m + 2) : K) • standardRulingPolynomial ^ m := by
  induction m with
  | zero =>
    simp [segreSplitLaplacian_apply, standardRulingPolynomial, pderiv_mul,
      pderiv_X, smul_eq_C_mul]
    rw [show (2 : K) = 1 + 1 by ring, map_add, map_one]
  | succ m ih =>
    have heuler := ((standardRulingPolynomial_homogeneous (F := K)).pow (m + 1)).sum_X_mul_pderiv
    rw [show Nat.succ m + 1 = (m + 1) + 1 by omega, pow_succ',
      segreSplitLaplacian_determinant_mul, ih, heuler]
    simp only [smul_eq_C_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat, map_mul, map_add, map_natCast, map_ofNat, map_one]
    rw [pow_succ]
    ring

theorem segreSplitLaplacian_pow_determinant_pow (m : ℕ) :
    (segreSplitLaplacian ^ m) ((standardRulingPolynomial (F := K)) ^ m) =
      C ((m.factorial : K) * ((m + 1).factorial : K)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, segreSplitLaplacian_determinant_pow, map_smul, ih]
    simp only [smul_eq_C_mul, ← map_mul, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    congr 1
    ring

/-- The polynomial contradiction of Section 5.4 directly in the original
determinant coordinates; no change to a sum-of-squares form is required. -/
theorem no_segre_normal_determinant_power_identity [CharZero K]
    (H : Fin 4 → R₀) (m : ℕ) (hH : IsHomogMap H (2 * m))
    (hr : segreNormalPairing H = 0) (hd : divergence H = 0)
    (S : Fin 4 → K) (κ : K) (hκ : κ ≠ 0)
    (hs : ∑ i, S i • H i = κ • standardRulingPolynomial ^ m) : False := by
  have hzero := segreSplitLaplacian_half_degree_zero H m hH hr hd
  have he := congrArg (fun p => (segreSplitLaplacian ^ m) p) hs
  simp only [map_sum, map_smul, segreSplitLaplacian_pow_determinant_pow] at he
  have hzero' : ∀ i, (segreSplitLaplacian ^ m) (H i) = 0 := fun i => congrFun hzero i
  simp only [hzero', smul_zero, Finset.sum_const_zero, smul_eq_C_mul, ← map_mul] at he
  have hn : κ * ((m.factorial : K) * ((m + 1).factorial : K)) ≠ 0 :=
    mul_ne_zero hκ (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))))
  exact hn ((MvPolynomial.C_injective (Fin 4) K) (he.symm.trans (map_zero C).symm))

end DimensionFourDependence
