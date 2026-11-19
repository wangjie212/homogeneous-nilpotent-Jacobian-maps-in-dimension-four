import DimensionFourDependence.BinaryQuadraticInfinityDirections
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # A quadratic relation of normalized independent polynomials has rank one -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K]

omit [CharZero K] in
/-- Every nonzero linear combination of two normalized independent
univariate polynomials is nonconstant. -/
theorem normalized_independent_polynomial_combination_pos_degree
    (f g : Polynomial K) (hf : f.eval 0 = 0) (hg : g.eval 0 = 0)
    (hind : ∀ u v : K, Polynomial.C u * f + Polynomial.C v * g = 0 → u = 0 ∧ v = 0)
    (u v : K) (hne : u ≠ 0 ∨ v ≠ 0) : 0 < (Polynomial.C u * f + Polynomial.C v * g).natDegree := by
  let P := Polynomial.C u * f + Polynomial.C v * g
  by_contra! h
  have hC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
  have h₀ : P.eval 0 = 0 := by simp [P, hf, hg]
  have he : P.coeff 0 = 0 := by rw [Polynomial.coeff_zero_eq_eval_zero, h₀]
  have hz : P = 0 := hC.trans (by rw [he, map_zero])
  exact hne.elim (fun hu => hu (hind u v hz).1) (fun hv => hv (hind u v hz).2)

/-- A binary quadratic with nonzero discriminant factors as two
independent linear forms over a closed field. -/
theorem nonsingular_binary_quadratic_has_independent_linear_factors [IsAlgClosed K]
    (A B C : K) (hD : B ^ 2 - 4 * A * C ≠ 0) :
    ∃ k u v s t : K, k ≠ 0 ∧ u * t - v * s ≠ 0 ∧
      A = k * u * s ∧ B = k * (u * t + v * s) ∧ C = k * v * t := by
  by_cases hA : A = 0
  · have hB : B ≠ 0 := by intro h; apply hD; simp [hA, h]
    refine ⟨1, 0, 1, B, C, one_ne_zero, ?_, ?_, ?_, ?_⟩ <;> simp [hA, hB]
  · obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (B ^ 2 - 4 * A * C) (n := 2) (by decide)
    have hd₀ : d ≠ 0 := fun h => hD (by rw [← hd, h]; simp)
    let v := (B + d) / (2 * A)
    let t := (B - d) / (2 * A)
    have hv : t - v = -d / A := by dsimp [v, t]; field_simp; ring
    refine ⟨A, 1, v, 1, t, hA, ?_, by ring, ?_, ?_⟩
    · simpa only [one_mul, mul_one, hv] using div_ne_zero (neg_ne_zero.mpr hd₀) hA
    · dsimp [v, t]
      field_simp
      ring
    · dsimp [v, t]
      field_simp
      linear_combination hd

omit [CharZero K] in
/-- Two nonconstant ordinary polynomials cannot have a nonzero
bilinear relation with only linear and constant corrections. -/
theorem nonconstant_polynomial_pair_excludes_unit_bilinear_relation
    (L M : Polynomial K) (hL : 0 < L.natDegree) (hM : 0 < M.natDegree)
    (k a b : K) (hk : k ≠ 0)
    (he : Polynomial.C k * L * M + Polynomial.C a * L + Polynomial.C b * M = 0) : False := by
  have hz : Polynomial.C k * (L + Polynomial.C (b / k)) * (M + Polynomial.C (a / k)) =
      Polynomial.C (b * a / k) := by
    have h₁ : Polynomial.C k * Polynomial.C (a / k) = Polynomial.C a := by
      rw [← map_mul, mul_div_cancel₀ _ hk]
    have h₂ : Polynomial.C k * Polynomial.C (b / k) = Polynomial.C b := by
      rw [← map_mul, mul_div_cancel₀ _ hk]
    have h₃ : Polynomial.C b * Polynomial.C (a / k) = Polynomial.C (b * a / k) := by
      rw [← map_mul, mul_div_assoc]
    linear_combination he + L * h₁ + (M + Polynomial.C (a / k)) * h₂ + h₃
  have hLd : (L + Polynomial.C (b / k)).natDegree = L.natDegree := Polynomial.natDegree_add_C
  have hMd : (M + Polynomial.C (a / k)).natDegree = M.natDegree := Polynomial.natDegree_add_C
  have hn (p : Polynomial K) (h : 0 < p.natDegree) : p ≠ 0 := by intro h0; simp [h0] at h
  have hL₀ := hn _ (hLd.symm ▸ hL)
  have hM₀ := hn _ (hMd.symm ▸ hM)
  have hCL : Polynomial.C k * (L + Polynomial.C (b / k)) ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hk) hL₀
  have hd := congrArg Polynomial.natDegree hz
  rw [Polynomial.natDegree_mul hCL hM₀, Polynomial.natDegree_C_mul hk, hLd, hMd, Polynomial.natDegree_C] at hd
  omega

/-- In a quadratic-plus-linear relation between normalized independent
univariate polynomials, the discriminant of the quadratic part vanishes. -/
theorem normalized_polynomial_relation_binary_discriminant_zero [IsAlgClosed K]
    (f g : Polynomial K) (hf : f.eval 0 = 0) (hg : g.eval 0 = 0)
    (hind : ∀ u v : K, Polynomial.C u * f + Polynomial.C v * g = 0 → u = 0 ∧ v = 0)
    (A B C d e : K)
    (he : Polynomial.C A * f ^ 2 + Polynomial.C B * f * g + Polynomial.C C * g ^ 2 +
      Polynomial.C d * f + Polynomial.C e * g = 0) : B ^ 2 - 4 * A * C = 0 := by
  by_contra hD
  obtain ⟨k, u, v, s, t, hk, hdet, hA, hB, hC⟩ := nonsingular_binary_quadratic_has_independent_linear_factors A B C hD
  let L := Polynomial.C u * f + Polynomial.C v * g
  let M := Polynomial.C s * f + Polynomial.C t * g
  have hLv : u ≠ 0 ∨ v ≠ 0 := by by_contra! h; exact hdet (by simp [h.1, h.2])
  have hMv : s ≠ 0 ∨ t ≠ 0 := by by_contra! h; exact hdet (by simp [h.1, h.2])
  have hL := normalized_independent_polynomial_combination_pos_degree f g hf hg hind u v hLv
  have hM := normalized_independent_polynomial_combination_pos_degree f g hf hg hind s t hMv
  let δ := u * t - v * s
  let a := (d * t - e * s) / δ
  let b := (e * u - d * v) / δ
  have hδ : δ ≠ 0 := hdet
  have ha : a * u + b * s = d := by
    dsimp only [a, b]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hδ]
    dsimp only [δ]
    ring
  have hb : a * v + b * t = e := by
    dsimp only [a, b]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hδ]
    dsimp only [δ]
    ring
  apply nonconstant_polynomial_pair_excludes_unit_bilinear_relation L M hL hM k a b hk
  rw [hA, hB, hC, ← ha, ← hb] at he
  simp only [L, M, map_add, map_mul] at he ⊢
  linear_combination he

/-- A nonzero singular binary quadratic is a scalar times the square
of an original linear form. No square-root extraction is needed. -/
theorem singular_nonzero_binary_quadratic_is_scalar_square
    (A B C : K) (hD : B ^ 2 - 4 * A * C = 0) (hQ : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∃ k u v : K, k ≠ 0 ∧ (u ≠ 0 ∨ v ≠ 0) ∧
      A = k * u ^ 2 ∧ B = 2 * k * u * v ∧ C = k * v ^ 2 := by
  by_cases hA : A = 0
  · have hB : B = 0 := by
      have hz : B ^ 2 = 0 := by simpa [hA] using hD
      exact not_ne_iff.mp (fun h => pow_ne_zero 2 h hz)
    refine ⟨C, 0, 1, ?_, Or.inr one_ne_zero, ?_, ?_, ?_⟩
    · simpa [hA, hB] using hQ
    all_goals simp [hA, hB]
  · let v := B / (2 * A)
    have hd : (2 : K) * A ≠ 0 := mul_ne_zero two_ne_zero hA
    refine ⟨A, 1, v, hA, Or.inl one_ne_zero, by simp, ?_, ?_⟩
    · simpa only [v, mul_one] using (mul_div_cancel₀ B hd).symm
    · dsimp only [v]
      field_simp
      linear_combination -hD

omit [CharZero K] in
/-- In the rank-one polynomial relation, the square direction and
the linear remainder give genuinely independent covectors. -/
theorem normalized_scalar_square_relation_transverse_covectors_independent
    (f g : Polynomial K) (u v a b k : K) (hk : k ≠ 0)
    (hP : 0 < (Polynomial.C u * f + Polynomial.C v * g).natDegree)
    (he : Polynomial.C k * (Polynomial.C u * f + Polynomial.C v * g) ^ 2 +
      Polynomial.C a * f + Polynomial.C b * g = 0) : u * b - v * a ≠ 0 := by
  intro h
  have huv : u ≠ 0 ∨ v ≠ 0 := by by_contra! hn; simp [hn.1, hn.2] at hP
  have hx := sub_eq_zero.mp h
  obtain ⟨s, hs, ht⟩ : ∃ s : K, a = s * u ∧ b = s * v := by
    rcases huv with hu | hv
    · refine ⟨a / u, (div_mul_cancel₀ _ hu).symm, ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff hu]
      linear_combination hx
    · refine ⟨b / v, ?_, (div_mul_cancel₀ _ hv).symm⟩
      rw [div_mul_eq_mul_div, eq_div_iff hv]
      linear_combination -hx
  let P := Polynomial.C u * f + Polynomial.C v * g
  apply nonconstant_polynomial_pair_excludes_unit_bilinear_relation P P hP hP k s 0 hk
  rw [hs, ht] at he
  simp only [P, map_mul, map_zero, pow_two] at he ⊢
  linear_combination he

end DimensionFourDependence
