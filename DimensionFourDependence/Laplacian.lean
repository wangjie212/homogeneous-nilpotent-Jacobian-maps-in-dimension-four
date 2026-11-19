import DimensionFourDependence.Nilpotent

/-! # The polynomial Laplacian argument of Section 5.4

All statements here concern polynomial identities. The geometric construction
of the square identity (5.4) is a separate, still outstanding obligation.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

@[simp] theorem pderiv_natCast (i : Fin n) (m : ℕ) :
    pderiv i (m : MvPolynomial (Fin n) K) = 0 := by
  change pderiv i (C (m : K)) = 0
  exact pderiv_C

@[simp] theorem pderiv_two (i : Fin n) :
    pderiv i (2 : MvPolynomial (Fin n) K) = 0 := by
  change pderiv i (C (2 : K)) = 0
  exact pderiv_C

/-- The usual polynomial Laplacian, as a linear operator. -/
noncomputable def laplacian : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K :=
  ∑ i : Fin n, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

theorem laplacian_apply (p : MvPolynomial (Fin n) K) :
    laplacian p = ∑ i : Fin n, pderiv i (pderiv i p) := by
  simp [laplacian, LinearMap.sum_apply]

/-- The divergence of a polynomial vector field. -/
noncomputable def divergence (V : Fin n → MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K := ∑ i, pderiv i (V i)

/-- The radial pairing `XᵀV`. -/
noncomputable def radialPairing (V : Fin n → MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K := ∑ i, X i * V i

theorem divergence_eq_trace (V : Fin n → MvPolynomial (Fin n) K) :
    divergence V = Matrix.trace (jac V) := rfl

/-- Commutation of formal mixed partials, adapted from the foundation project's
`Lemma42.lean`; this proof imports no results about surfaces. -/
theorem pderiv_pderiv_comm (i j : Fin n) (p : MvPolynomial (Fin n) K) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, pderiv_X]
    rw [hp]
    by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2] <;> ring

theorem pderiv_laplacian (j : Fin n) (p : MvPolynomial (Fin n) K) :
    pderiv j (laplacian p) = laplacian (pderiv j p) := by
  simp only [laplacian_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_pderiv_comm j i, pderiv_pderiv_comm j i]

theorem laplacian_X_mul (j : Fin n) (p : MvPolynomial (Fin n) K) :
    laplacian (X j * p) = X j * laplacian p + 2 * pderiv j p := by
  have h : ∀ i : Fin n, pderiv i (pderiv i (X j * p)) =
      X j * pderiv i (pderiv i p) + if i = j then 2 * pderiv j p else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp only [pderiv_mul, pderiv_X_self, one_mul, map_add, ite_true]
      ring
    · simp [pderiv_X_of_ne (Ne.symm hij), hij]
  simp only [laplacian_apply, h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- The first displayed operator identity in Section 5.4. -/
theorem laplacian_radialPairing (V : Fin n → MvPolynomial (Fin n) K) :
    laplacian (radialPairing V) =
      radialPairing (fun i => laplacian (V i)) + 2 * divergence V := by
  simp only [radialPairing, map_sum, laplacian_X_mul,
    Finset.sum_add_distrib, divergence, Finset.mul_sum]

/-- The second displayed operator identity in Section 5.4. -/
theorem divergence_laplacian (V : Fin n → MvPolynomial (Fin n) K) :
    divergence (fun i => laplacian (V i)) = laplacian (divergence V) := by
  simp only [divergence, map_sum, pderiv_laplacian]

/-- Iterating the Laplacian preserves both vanishing conditions in Section 5.4. -/
theorem laplacian_preserves_constraints [CharZero K]
    (V : Fin n → MvPolynomial (Fin n) K)
    (hr : radialPairing V = 0) (hd : divergence V = 0) (j : ℕ) :
    radialPairing (fun i => (laplacian ^ j) (V i)) = 0 ∧
      divergence (fun i => (laplacian ^ j) (V i)) = 0 := by
  induction j with
  | zero => simpa using And.intro hr hd
  | succ j ih =>
    have hr' := laplacian_radialPairing (fun i => (laplacian ^ j) (V i))
    rw [ih.1, ih.2, map_zero, mul_zero, add_zero] at hr'
    have hd' := divergence_laplacian (fun i => (laplacian ^ j) (V i))
    rw [ih.2, map_zero] at hd'
    simpa only [pow_succ', Module.End.mul_apply] using And.intro hr'.symm hd'

theorem laplacian_homogeneous {p : MvPolynomial (Fin n) K} {d : ℕ}
    (hp : p.IsHomogeneous d) : (laplacian p).IsHomogeneous (d - 2) := by
  rw [laplacian_apply]
  apply IsHomogeneous.sum
  intro i _
  convert (hp.pderiv (i := i)).pderiv (i := i) using 1

theorem laplacian_pow_homogeneous {p : MvPolynomial (Fin n) K} {d : ℕ}
    (hp : p.IsHomogeneous d) (j : ℕ) :
    ((laplacian ^ j) p).IsHomogeneous (d - 2 * j) := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.mul_succ,
      Nat.sub_sub] using laplacian_homogeneous ih

/-- A constant vector whose radial pairing vanishes must be zero. -/
theorem constant_vector_zero_of_radialPairing
    (V : Fin n → MvPolynomial (Fin n) K)
    (hV : IsHomogMap V 0) (hr : radialPairing V = 0) : V = 0 := by
  funext j
  have h := congrArg (pderiv j) hr
  have hc : ∀ i, V i = C ((V i).coeff 0) := fun i => eq_C_of_isHomogeneous_zero (hV i)
  have hz : ∀ i, pderiv j (V i) = 0 := by
    intro i
    rw [hc i, pderiv_C]
  simp only [radialPairing, map_sum, pderiv_mul, hz, mul_zero, add_zero,
    pderiv_X, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, map_zero] at h
  exact h

/-- The assertion `L^m H = 0` in Section 5.4, proved from exactly the stated
homogeneity, radial and divergence conditions. -/
theorem laplacian_half_degree_zero [CharZero K]
    (H : Fin n → MvPolynomial (Fin n) K) (m : ℕ)
    (hH : IsHomogMap H (2 * m))
    (hr : radialPairing H = 0) (hd : divergence H = 0) :
    (fun i => (laplacian ^ m) (H i)) = 0 := by
  apply constant_vector_zero_of_radialPairing
  · intro i
    simpa using laplacian_pow_homogeneous (hH i) m
  · exact (laplacian_preserves_constraints H hr hd m).1

/-- The nondegenerate quadratic form chosen in Section 5.4. -/
noncomputable def sumSquares : MvPolynomial (Fin 4) K := ∑ i : Fin 4, X i ^ 2

theorem sumSquares_homogeneous : (sumSquares (K := K)).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_X_pow i 2

theorem pderiv_sumSquares (j : Fin 4) :
    pderiv j (sumSquares (K := K)) = 2 * X j := by
  simp [sumSquares, Pi.single_apply]

theorem laplacian_sumSquares_mul (p : MvPolynomial (Fin 4) K) :
    laplacian (sumSquares * p) =
      sumSquares * laplacian p + 4 * (∑ i : Fin 4, X i * pderiv i p) + 8 * p := by
  have h : ∀ i : Fin 4, pderiv i (pderiv i (sumSquares * p)) =
      sumSquares * pderiv i (pderiv i p) + 4 * X i * pderiv i p + 2 * p := by
    intro i
    simp only [pderiv_mul, pderiv_sumSquares, map_add]
    simp only [pderiv_two, pderiv_X_self, zero_mul, mul_one,
      zero_add]
    ring
  simp only [laplacian_apply, h, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- The recurrence `L(Q^i) = 4 i (i+1) Q^(i-1)` of Section 5.4,
indexed by `i = m + 1` to avoid truncated subtraction. -/
theorem laplacian_sumSquares_pow (m : ℕ) :
    laplacian ((sumSquares (K := K)) ^ (m + 1)) =
      (4 * (m + 1) * (m + 2) : K) • sumSquares ^ m := by
  induction m with
  | zero =>
    have h2 : C (2 : K) = (2 : MvPolynomial (Fin 4) K) := by
      rw [show (2 : K) = 1 + 1 by ring, map_add, map_one]
      ring
    have h4 : C (4 : K) = (4 : MvPolynomial (Fin 4) K) := by
      rw [show (4 : K) = 2 * 2 by ring, map_mul, h2]
      ring
    simp [laplacian_apply, pderiv_sumSquares, pderiv_two,
      smul_eq_C_mul, h2, h4]
  | succ m ih =>
    have he := (sumSquares_homogeneous (K := K)).pow (m + 1)
    have heuler := he.sum_X_mul_pderiv
    rw [show (Nat.succ m + 1) = (m + 1) + 1 by omega, pow_succ',
      laplacian_sumSquares_mul, ih, heuler]
    simp only [smul_eq_C_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat, map_mul, map_add, map_natCast, map_ofNat, map_one]
    rw [pow_succ]
    ring

/-- Iterating the radial-power recurrence gives the explicit nonzero scalar
in (5.5). -/
theorem laplacian_pow_sumSquares_pow (m : ℕ) :
    (laplacian ^ m) ((sumSquares (K := K)) ^ m) =
      C ((4 : K) ^ m * (m.factorial : K) * ((m + 1).factorial : K)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, laplacian_sumSquares_pow,
      map_smul, ih]
    simp only [smul_eq_C_mul, ← map_mul, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    congr 1
    ring

/-- The polynomial contradiction at the end of Section 5.4. In particular,
no nonzero constant covector can satisfy `S(H) = κ Q^m` under the two
vanishing conditions. Deriving that identity from the surface geometry
is not assumed to have been formalized by this theorem. -/
theorem no_radial_power_identity [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (m : ℕ)
    (hH : IsHomogMap H (2 * m))
    (hr : radialPairing H = 0) (hd : divergence H = 0)
    (s : Fin 4 → K) (κ : K) (hκ : κ ≠ 0)
    (hs : ∑ i, s i • H i = κ • sumSquares ^ m) : False := by
  have hzero := laplacian_half_degree_zero H m hH hr hd
  have h := congrArg (fun p => (laplacian ^ m) p) hs
  simp only [map_sum, map_smul, laplacian_pow_sumSquares_pow] at h
  have hzero' : ∀ i, (laplacian ^ m) (H i) = 0 := fun i => congrFun hzero i
  simp only [hzero', smul_zero, Finset.sum_const_zero, smul_eq_C_mul, ← map_mul] at h
  have hn : κ * ((4 : K) ^ m * (m.factorial : K) * ((m + 1).factorial : K)) ≠ 0 := by
    exact mul_ne_zero hκ (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))))
  exact hn ((MvPolynomial.C_injective (Fin 4) K) (h.symm.trans (map_zero C).symm))

end DimensionFourDependence
