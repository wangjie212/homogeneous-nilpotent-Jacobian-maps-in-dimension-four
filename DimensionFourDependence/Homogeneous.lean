/- Foundation adapted from the neighboring quartic project.
   Only the general-degree algebraic results are used for the present paper.
   The source theorem file with its admitted surface argument is not imported. -/
import DimensionFourDependence.Defs

/-!
# Auxiliary facts on homogeneous polynomials

Elementary facts about homogeneous polynomials that are used implicitly in
§2.1 of `quartic_dependence.pdf` (e.g. "For a homogeneous matrix, this generator may be
chosen homogeneous").  The key fact is that a factor of a nonzero homogeneous polynomial
is itself homogeneous.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*}

/-- The grading homomorphism `p ↦ ∑ₖ pₖ tᵏ`, where `pₖ` is the degree-`k` homogeneous
component of `p` (i.e. `p(t·X)`).  Auxiliary device for the implicit homogeneity facts of
§2.1 of `quartic_dependence.pdf`. -/
noncomputable def gradeHom : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval (fun i => Polynomial.C (X i) * Polynomial.X)

/-- `gradeHom` on a monomial (auxiliary; implicit in §2.1 of `quartic_dependence.pdf`). -/
theorem gradeHom_monomial (s : σ →₀ ℕ) (a : K) :
    gradeHom (monomial s a) = Polynomial.monomial (Finsupp.degree s) (monomial s a) := by
  simp only [gradeHom, aeval_monomial, mul_pow, Finsupp.prod_mul]
  have h1 : (s.prod fun i k => (Polynomial.X : Polynomial (MvPolynomial σ K)) ^ k) =
      Polynomial.X ^ Finsupp.degree s := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  have h2 : (s.prod fun i k => (Polynomial.C (X i) : Polynomial (MvPolynomial σ K)) ^ k) =
      Polynomial.C (s.prod fun i k => X i ^ k) := by
    rw [Finsupp.prod, Finsupp.prod, map_prod]; simp
  rw [h1, h2, ← Polynomial.C_mul_X_pow_eq_monomial, monomial_eq]
  simp [Polynomial.C_mul, mul_assoc]

/-- The `k`-th coefficient of `gradeHom p` is the degree-`k` homogeneous component of `p`
(auxiliary; implicit in §2.1 of `quartic_dependence.pdf`). -/
theorem coeff_gradeHom (p : MvPolynomial σ K) (k : ℕ) :
    (gradeHom p).coeff k = homogeneousComponent k p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [gradeHom_monomial, Polynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rw [homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]; simp
    · rw [homogeneousComponent_eq_zero']
      intro d hd
      have := support_monomial_subset hd
      simp at this; rw [this]; exact h
  | add p q hp hq => simp [hp, hq]

/-- A factor of a nonzero homogeneous polynomial is homogeneous.  This standard fact is
used implicitly in §2.1 of `quartic_dependence.pdf` (homogeneous choice of primitive
generators) and in §4.1 (the decomposition `H = gP`). -/
theorem isHomogeneous_of_mul_left {p q : MvPolynomial σ K} {d : ℕ}
    (h : (p * q).IsHomogeneous d) (h0 : p * q ≠ 0) : ∃ a, p.IsHomogeneous a := by
  classical
  have hp0 : p ≠ 0 := left_ne_zero_of_mul h0
  have hq0 : q ≠ 0 := right_ne_zero_of_mul h0
  have hP : gradeHom p ≠ 0 := by
    intro h'; apply hp0; rw [← sum_homogeneousComponent p]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← coeff_gradeHom, h']; simp
  have hQ : gradeHom q ≠ 0 := by
    intro h'; apply hq0; rw [← sum_homogeneousComponent q]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← coeff_gradeHom, h']; simp
  have hPQ : gradeHom p * gradeHom q = Polynomial.monomial d (p * q) := by
    rw [← map_mul]; refine Polynomial.ext fun k => ?_
    rw [coeff_gradeHom, Polynomial.coeff_monomial, homogeneousComponent_of_mem h]
    by_cases hk : k = d
    · simp [hk]
    · simp [hk, Ne.symm hk]
  have hdeg := Polynomial.natDegree_mul hP hQ
  have htr := Polynomial.natTrailingDegree_mul hP hQ
  rw [hPQ, Polynomial.natDegree_monomial] at hdeg
  simp only [h0, ite_false] at hdeg
  rw [hPQ, Polynomial.natTrailingDegree_monomial h0] at htr
  have h1 := Polynomial.natTrailingDegree_le_natDegree (p := gradeHom p)
  have h2 := Polynomial.natTrailingDegree_le_natDegree (p := gradeHom q)
  have hcoeff : ∀ k, k ≠ (gradeHom p).natDegree → homogeneousComponent k p = 0 := by
    intro k hk
    rw [← coeff_gradeHom]
    rcases lt_or_gt_of_ne hk with hk | hk
    · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt hk
  generalize (gradeHom p).natDegree = a at hcoeff
  refine ⟨a, ?_⟩
  rw [← sum_homogeneousComponent p]
  refine IsHomogeneous.sum _ _ _ fun k _ => ?_
  by_cases hk : k = a
  · subst hk; exact homogeneousComponent_isHomogeneous _ _
  · rw [hcoeff k hk]; exact isHomogeneous_zero _ _ _


/-- On a homogeneous polynomial of degree `d`, `gradeHom` is the monomial `f tᵈ`
(auxiliary; implicit in §2.1 of `quartic_dependence.pdf`). -/
theorem gradeHom_of_isHomogeneous {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    gradeHom f = Polynomial.monomial d f := by
  classical
  refine Polynomial.ext fun k => ?_
  rw [coeff_gradeHom, Polynomial.coeff_monomial, homogeneousComponent_of_mem hf]
  by_cases hk : k = d
  · simp [hk]
  · simp [hk, Ne.symm hk]

/-- Multiplication by a homogeneous polynomial of degree `d` shifts homogeneous components by
`d` (auxiliary; used for "this generator may be chosen homogeneous", §2.1 of
`quartic_dependence.pdf`). -/
theorem homogeneousComponent_mul_of_isHomogeneous {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (g : MvPolynomial σ K) (m : ℕ) :
    homogeneousComponent (m + d) (f * g) = f * homogeneousComponent m g := by
  rw [← coeff_gradeHom, map_mul, gradeHom_of_isHomogeneous hf,
    Polynomial.coeff_monomial_mul, coeff_gradeHom]

/-- A nonzero homogeneous polynomial of degree zero is a unit (auxiliary; §2.1 of
`quartic_dependence.pdf`). -/
theorem isUnit_of_isHomogeneous_zero {p : MvPolynomial σ K} (hp : p.IsHomogeneous 0)
    (h0 : p ≠ 0) : IsUnit p := by
  have := totalDegree_eq_zero_iff_eq_C.mp (hp.totalDegree h0)
  rw [this] at h0 ⊢
  exact (Ne.isUnit (fun h => h0 (by rw [h, C_0]))).map C

/-- Every nonzero homogeneous polynomial vector `w` of degree `d` factors as `w = g · P` with
`g` homogeneous of degree `c ≤ d` and `P` a primitive homogeneous vector of degree `d - c`.
This is the existence of the "primitive generator" in §2.1 of `quartic_dependence.pdf` and
of the decomposition `H = gP` (with `P` primitive) at the start of §4.1. -/
theorem exists_primitive_factorization {n : ℕ} : ∀ (d : ℕ) (w : Fin n → MvPolynomial σ K),
    IsHomogMap w d → w ≠ 0 →
    ∃ (g : MvPolynomial σ K) (P : Fin n → MvPolynomial σ K) (c : ℕ),
      c ≤ d ∧ g ≠ 0 ∧ g.IsHomogeneous c ∧ IsHomogMap P (d - c) ∧ IsPrimitiveVec P ∧
        w = fun i => g * P i := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro w hw h0
  by_cases hprim : IsPrimitiveVec w
  · exact ⟨1, w, 0, Nat.zero_le _, one_ne_zero, isHomogeneous_one _ _, by simpa using hw,
      hprim, by simp⟩
  simp only [IsPrimitiveVec, not_forall] at hprim
  obtain ⟨p, hdvd, hnu⟩ := hprim
  choose q hq using hdvd
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hne; push Not at hne; exact h0 (funext hne)
  have hpq0 : p * q i0 ≠ 0 := by rw [← hq]; exact hi0
  obtain ⟨a, ha⟩ := isHomogeneous_of_mul_left (hq i0 ▸ hw i0) hpq0
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hpq0
  have ha1 : 1 ≤ a := by
    by_contra h; push Not at h
    have : a = 0 := by omega
    subst this; exact hnu (isUnit_of_isHomogeneous_zero ha hp0)
  have hqh : ∀ i, (q i).IsHomogeneous (d - a) := by
    intro i
    by_cases hqi : q i = 0
    · rw [hqi]; exact isHomogeneous_zero _ _ _
    have hpqi : p * q i ≠ 0 := mul_ne_zero hp0 hqi
    obtain ⟨b, hb⟩ := isHomogeneous_of_mul_left (p := q i) (q := p)
      (by rw [mul_comm, ← hq]; exact hw i) (by rwa [mul_comm])
    have hab : a + b = d := (ha.mul hb).inj_right (hq i ▸ hw i) hpqi
    have : d - a = b := by omega
    rw [this]; exact hb
  have hadle : a ≤ d := by
    have := (hw i0).totalDegree hi0
    rw [hq i0, totalDegree_mul_of_isDomain hp0 (right_ne_zero_of_mul hpq0), ha.totalDegree hp0]
      at this
    omega
  have hq0 : q ≠ 0 := by
    intro h; apply hi0; rw [hq i0, h]; simp
  obtain ⟨g', P, c', hc', hg'0, hg', hP, hPp, hqgP⟩ := ih (d - a) (by omega) q hqh hq0
  refine ⟨p * g', P, a + c', by omega, mul_ne_zero hp0 hg'0, ha.mul hg', ?_, hPp, ?_⟩
  · have : d - (a + c') = d - a - c' := by omega
    rw [this]; exact hP
  · funext i; rw [hq i, hqgP]; ring


/-- A homogeneous polynomial of degree zero is a constant (auxiliary; used for the
constant left normal in (2.3) of `quartic_dependence.pdf`). -/
theorem eq_C_of_isHomogeneous_zero {p : MvPolynomial σ K} (hp : p.IsHomogeneous 0) :
    p = C (p.coeff 0) := by
  by_cases h : p = 0
  · simp [h]
  · exact totalDegree_eq_zero_iff_eq_C.mp (hp.totalDegree h)

/-- If a homogeneous polynomial divides one of its partial derivatives, that derivative
vanishes (auxiliary for the rank-one case of Lemma 2.1 of `quartic_dependence.pdf`). -/
theorem pderiv_eq_zero_of_dvd [Fintype σ] {f : MvPolynomial σ K} {e : ℕ} (hf : f.IsHomogeneous e)
    (k : σ) (hdvd : f ∣ pderiv k f) : pderiv k f = 0 := by
  by_contra hne
  obtain ⟨q, hq⟩ := hdvd
  have hf0 : f ≠ 0 := by rintro rfl; simp at hne
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact hne hq
  have h1 := (hf.pderiv (i := k)).totalDegree hne
  rw [hq, totalDegree_mul_of_isDomain hf0 hq0, hf.totalDegree hf0] at h1
  have he : e ≠ 0 := by
    rintro rfl
    have := totalDegree_eq_zero_iff_eq_C.mp (hf.totalDegree hf0)
    apply hne; rw [this]; simp
  omega

/-- A homogeneous polynomial of positive degree all of whose partial derivatives vanish is
zero, by Euler's identity in characteristic zero (auxiliary for Lemma 2.1 of
`quartic_dependence.pdf`). -/
theorem eq_zero_of_forall_pderiv_eq_zero [CharZero K] [Fintype σ] {f : MvPolynomial σ K} {e : ℕ}
    (hf : f.IsHomogeneous e) (he : e ≠ 0) (h : ∀ k, pderiv k f = 0) : f = 0 := by
  have := hf.sum_X_mul_pderiv
  simp only [h, mul_zero, Finset.sum_const_zero] at this
  rcases smul_eq_zero.mp this.symm with h | h
  · exact absurd h he
  · exact h

/-- If two homogeneous forms `f ≠ 0`, `g` of the same degree satisfy `f ∂ₖg = g ∂ₖf` for
all `k` (i.e. `d(g/f) = 0`), then `g` is a constant multiple of `f`.  This is the step
"`d(Fᵢ/Fⱼ) = 0`" of the rank-one case in the proof of Lemma 2.1 of
`quartic_dependence.pdf`. -/
theorem proportional_of_wronskian [CharZero K] [Fintype σ] {f g : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hf0 : f ≠ 0)
    (h : ∀ k, f * pderiv k g = g * pderiv k f) : ∃ c : K, g = c • f := by
  obtain ⟨hh, P, c, hc, hh0, -, hP, hPp, hfg⟩ :=
    exists_primitive_factorization (n := 2) d ![f, g] (by intro i; fin_cases i <;> assumption)
      (fun h0 => hf0 (by simpa using congrFun h0 0))
  have hf' : f = hh * P 0 := by simpa using congrFun hfg 0
  have hg' : g = hh * P 1 := by simpa using congrFun hfg 1
  have hP0 : P 0 ≠ 0 := by rintro h0; apply hf0; rw [hf', h0, mul_zero]
  have hW : ∀ k, P 0 * pderiv k (P 1) = P 1 * pderiv k (P 0) := by
    intro k
    have hk := h k
    rw [hf', hg'] at hk
    simp only [Derivation.leibniz, smul_eq_mul] at hk
    have : hh * hh * (P 0 * pderiv k (P 1) - P 1 * pderiv k (P 0)) = 0 := by
      linear_combination hk
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero hh0 hh0)
    exact sub_eq_zero.mp this
  have hrel : IsRelPrime (P 0) (P 1) := by
    intro p h0 h1
    exact hPp p (by intro i; fin_cases i <;> assumption)
  have hder : ∀ k, pderiv k (P 0) = 0 := by
    intro k
    apply pderiv_eq_zero_of_dvd (hP 0) k
    exact hrel.dvd_of_dvd_mul_left ⟨pderiv k (P 1), (hW k).symm⟩
  have he : d - c = 0 := by
    by_contra he
    exact hP0 (eq_zero_of_forall_pderiv_eq_zero (hP 0) he hder)
  have h0 := eq_C_of_isHomogeneous_zero (he ▸ hP 0)
  have h1 := eq_C_of_isHomogeneous_zero (he ▸ hP 1)
  have ha : (P 0).coeff 0 ≠ 0 := by
    intro ha; apply hP0; rw [h0, ha, C_0]
  generalize (P 0).coeff 0 = a at h0 ha
  generalize (P 1).coeff 0 = b at h1
  refine ⟨b / a, ?_⟩
  rw [hg', hf', h1, h0, smul_eq_C_mul]
  have : (C b : MvPolynomial σ K) = C (b / a) * C a := by
    rw [← C_mul, div_mul_cancel₀ _ ha]
  rw [this]; ring

end DimensionFourDependence
