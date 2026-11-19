/- Foundation adapted from the neighboring quartic project.
   Only the general-degree algebraic results are used for the present paper.
   The source theorem file with its admitted surface argument is not imported. -/
import DimensionFourDependence.Basic

/-!
# Linear changes of variables and Jacobians

Auxiliary material for the rank-two case of Lemma 2.5(a) of `quartic_dependence.pdf`
(the argument "after a linear change of coordinates, `p = x₁`, `q = x₂`, `g = x₃`").
Instead of changing coordinates we substitute linearly independent linear forms
`ℓ₀, …, ℓ_{r-1}` for the variables of a polynomial map `Φ` in `r` variables and compare
Jacobians via the chain rule.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-- The chain rule for a polynomial substitution `x ↦ ℓ(x)` (used for the linear changes of
coordinates in the proof of Lemma 2.5(a) of `quartic_dependence.pdf`). -/
theorem pderiv_aeval {n r : ℕ} (ℓ : Fin r → MvPolynomial (Fin n) K)
    (f : MvPolynomial (Fin r) K) (i : Fin n) :
    pderiv i (aeval ℓ f) = ∑ j, aeval ℓ (pderiv j f) * pderiv i (ℓ j) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, ← Finset.sum_add_distrib]; simp [add_mul]
  | mul_X p k hp =>
    have e : ∑ j, aeval ℓ (pderiv j (p * X k)) * pderiv i (ℓ j) =
        ℓ k * ∑ j, aeval ℓ (pderiv j p) * pderiv i (ℓ j) + aeval ℓ p * pderiv i (ℓ k) := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · simp [Pi.single_apply]
    rw [e, ← hp, map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring

/-- Substituting linearly independent linear forms is injective: if `ℓⱼ = ∑ᵢ Bᵢⱼ xᵢ` and `B`
has a left inverse, then `f ↦ f(ℓ)` is injective (auxiliary for the coordinate changes in
the proof of Lemma 2.5(a) of `quartic_dependence.pdf`). -/
theorem aeval_injective_of_mul_eq_one {n r : ℕ} (B : Matrix (Fin n) (Fin r) K)
    (D : Matrix (Fin r) (Fin n) K) (hDB : D * B = 1) (ℓ : Fin r → MvPolynomial (Fin n) K)
    (hℓ : ∀ j, ℓ j = ∑ i, C (B i j) * X i) : Function.Injective (aeval (R := K) ℓ) := by
  let ρ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin r) K :=
    aeval fun i => ∑ k, C (D k i) * X k
  have h : ρ.comp (aeval ℓ) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, aeval_X, hℓ, map_sum, map_mul, algHom_C, AlgHom.id_apply, ρ]
    simp only [algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k, ∑ i, C (B i j) * (C (D k i) * X k) =
        C ((D * B) k j) * (X k : MvPolynomial (Fin r) K) := by
      intro k
      rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [C_mul]; ring
    simp only [this, hDB, Matrix.one_apply]
    simp
  intro a b hab
  have ha := DFunLike.congr_fun h a
  have hb := DFunLike.congr_fun h b
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at ha hb
  rw [← ha, ← hb, hab]

/-- Composing the linear substitutions `x ↦ Bᵀx` and `z ↦ Dᵀz` with `D B = 1` gives the
identity. -/
theorem aeval_aeval_linear_of_mul_eq_one {n r : ℕ} (B : Matrix (Fin n) (Fin r) K)
    (D : Matrix (Fin r) (Fin n) K) (hDB : D * B = 1) (p : MvPolynomial (Fin r) K) :
    aeval (fun i => ∑ k, C (D k i) * X k) (aeval (fun j => ∑ i, C (B i j) * X i) p) = p := by
  have h : (aeval (R := K) fun i => ∑ k, C (D k i) * (X k : MvPolynomial (Fin r) K)).comp
      (aeval fun j => ∑ i, C (B i j) * X i) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply]
    simp only [algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k, ∑ i, C (B i j) * (C (D k i) * X k) =
        C ((D * B) k j) * (X k : MvPolynomial (Fin r) K) := by
      intro k
      rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [C_mul]; ring
    simp only [this, hDB, Matrix.one_apply]
    simp
  exact DFunLike.congr_fun h p

/-- Either the columns of `B` are linearly dependent, or `B` has a left inverse (auxiliary
for the case distinctions on linear forms in the proof of Lemma 2.5(a) of
`quartic_dependence.pdf`). -/
theorem linear_dichotomy {n r : ℕ} (B : Matrix (Fin n) (Fin r) K) :
    (∃ a : Fin r → K, a ≠ 0 ∧ B *ᵥ a = 0) ∨ ∃ D : Matrix (Fin r) (Fin n) K, D * B = 1 := by
  by_cases hinj : Function.Injective B.mulVecLin
  · right
    obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective B.mulVecLin
      (LinearMap.ker_eq_bot.mpr hinj)
    refine ⟨LinearMap.toMatrix' L, ?_⟩
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp]
    rw [show Matrix.toLin' B = B.mulVecLin from rfl, hL]
    exact LinearMap.toMatrix'_id
  · left
    rw [← LinearMap.ker_eq_bot] at hinj
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp hinj
    exact ⟨a, ha0, ha⟩

/-- `(BA)^{m+1} = B (AB)^m A` for rectangular matrices. -/
theorem mul_pow_succ_eq {R : Type*} [CommRing R] {n r : ℕ} (A : Matrix (Fin n) (Fin r) R)
    (B : Matrix (Fin r) (Fin n) R) (m : ℕ) : (B * A) ^ (m + 1) = B * (A * B) ^ m * A := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

/-- **Nilpotency under a linear change of coordinates.**  If `H = Φ(ℓ)` where
`ℓⱼ = ∑ᵢ Bᵢⱼ xᵢ` are linearly independent linear forms and `JH` is nilpotent, then the
Jacobian of `Bᵀ Φ` (an `r × r` matrix in the `r` new variables) is nilpotent.  This is the
formal counterpart of "put `p = x₁`, `q = x₂` (and `g = x₃`)" in the proof of the rank-two
case of Lemma 2.5(a) of `quartic_dependence.pdf`: by the chain rule `JH = A Bᵀ` and
`Bᵀ A = J(BᵀΦ)(ℓ)`. -/
theorem isNilpotent_jac_of_linear_subst {n r : ℕ} (B : Matrix (Fin n) (Fin r) K)
    (ℓ : Fin r → MvPolynomial (Fin n) K) (hℓ : ∀ j, ℓ j = ∑ i, C (B i j) * X i)
    (hinj : Function.Injective (aeval (R := K) ℓ))
    (Φ : Fin n → MvPolynomial (Fin r) K) (hN : IsNilpotent (jac fun i => aeval ℓ (Φ i))) :
    IsNilpotent (jac fun j => ∑ i, C (B i j) * Φ i) := by
  let A : Matrix (Fin n) (Fin r) (MvPolynomial (Fin n) K) :=
    of fun i k => aeval ℓ (pderiv k (Φ i))
  let Bt : Matrix (Fin r) (Fin n) (MvPolynomial (Fin n) K) := of fun j i => C (B i j)
  have h1 : (jac fun i => aeval ℓ (Φ i)) = A * Bt := by
    refine Matrix.ext fun a i => ?_
    simp only [jac, of_apply, pderiv_aeval, Matrix.mul_apply, A, Bt]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [hℓ k, map_sum]
    simp [Pi.single_apply]
  have h2 : Bt * A = (jac fun j => ∑ i, C (B i j) * Φ i).map (aeval ℓ) := by
    refine Matrix.ext fun j k => ?_
    simp [jac, Matrix.mul_apply, A, Bt, map_sum]
  obtain ⟨m, hm⟩ := hN
  refine ⟨m + 1, ?_⟩
  have h3 : ((jac fun j => ∑ i, C (B i j) * Φ i) ^ (m + 1)).map (aeval ℓ) = 0 := by
    rw [show ((jac fun j => ∑ i, C (B i j) * Φ i) ^ (m + 1)).map (aeval ℓ) =
      ((jac fun j => ∑ i, C (B i j) * Φ i).map (aeval ℓ)) ^ (m + 1) from
      Matrix.map_pow _ (aeval ℓ).toRingHom _]
    rw [← h2, mul_pow_succ_eq, ← h1, hm]; simp
  refine Matrix.ext fun a b => ?_
  have := congrFun (congrFun h3 a) b
  simp only [map_apply, Matrix.zero_apply] at this ⊢
  exact hinj (by rw [this, map_zero])

/-- A linear form is `∑ᵢ cᵢ xᵢ` with constant coefficients `cᵢ = ∂ᵢp`. -/
theorem eq_sum_of_isHomogeneous_one {n : ℕ} {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous 1) : p = ∑ i, C ((pderiv i p).coeff 0) * X i := by
  have := hp.sum_X_mul_pderiv
  rw [one_smul] at this
  conv_lhs => rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, ← eq_C_of_isHomogeneous_zero (hp.pderiv (i := i))]

end DimensionFourDependence
