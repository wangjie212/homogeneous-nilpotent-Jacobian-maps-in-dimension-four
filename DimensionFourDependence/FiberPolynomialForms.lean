import DimensionFourDependence.CubicDifferentiation

/-! # Polynomial forms of the three fiber equations of Lemma 2.2 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- The polynomial associated with a linear coefficient array. -/
noncomputable def linearFormPolynomial (a : Fin n → F) : MvPolynomial (Fin n) F :=
  ∑ i, C (a i) * X i

/-- The polynomial associated with a quadratic coefficient array. -/
noncomputable def quadraticFormPolynomial (T : Matrix (Fin n) (Fin n) F) : MvPolynomial (Fin n) F :=
  ∑ i, ∑ j, C (T i j) * X i * X j

/-- The polynomial associated with a cubic coefficient array. -/
noncomputable def cubicFormPolynomial (T : Fin n → Fin n → Fin n → F) : MvPolynomial (Fin n) F :=
  ∑ i, ∑ j, ∑ k, C (T i j k) * X i * X j * X k

/-- The affine hyperplane equation given by the first invariant. -/
noncomputable def affineFiberPolynomial (g : Fin n → F) (c : F) : MvPolynomial (Fin (n + 1)) F :=
  X (Fin.last n) - (∑ i : Fin n, C (g i) * X i.castSucc) - C c

/-- The quadratic equation given by the second invariant. -/
noncomputable def quadraticFiberPolynomial (a : Fin n → F)
    (T : Matrix (Fin n) (Fin n) F) (q : F) : MvPolynomial (Fin n) F :=
  linearFormPolynomial a + C ((2 : F)⁻¹) * quadraticFormPolynomial T - C q

/-- The cubic equation given by the third invariant. -/
noncomputable def cubicFiberPolynomial (a : Fin n → F) (S : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (k : F) : MvPolynomial (Fin n) F :=
  linearFormPolynomial a - C ((2 : F)⁻¹) * quadraticFormPolynomial S -
    C ((6 : F)⁻¹) * cubicFormPolynomial T - C k

theorem linearFormPolynomial_totalDegree (a : Fin n → F) :
    (linearFormPolynomial a).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using totalDegree_mul (C (a i)) (X i)

theorem quadraticFormPolynomial_totalDegree (T : Matrix (Fin n) (Fin n) F) :
    (quadraticFormPolynomial T).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  have h1 := totalDegree_mul (C (T i j)) (X i)
  have h2 := totalDegree_mul (C (T i j) * X i) (X j)
  simp only [totalDegree_C, totalDegree_X, zero_add] at h1 h2
  omega

theorem cubicFormPolynomial_totalDegree (T : Fin n → Fin n → Fin n → F) :
    (cubicFormPolynomial T).totalDegree ≤ 3 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  apply totalDegree_finsetSum_le
  intro k _
  have h1 := totalDegree_mul (C (T i j k)) (X i)
  have h2 := totalDegree_mul (C (T i j k) * X i) (X j)
  have h3 := totalDegree_mul (C (T i j k) * X i * X j) (X k)
  simp only [totalDegree_C, totalDegree_X, zero_add] at h1 h2 h3
  omega

/-- The first fiber equation is an affine hyperplane equation. -/
theorem affineFiberPolynomial_totalDegree (g : Fin n → F) (c : F) :
    (affineFiberPolynomial g c).totalDegree ≤ 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_X _).le
  · apply totalDegree_finsetSum_le
    intro i _
    simpa only [totalDegree_C, totalDegree_X, zero_add] using
      totalDegree_mul (C (g i)) (X i.castSucc)

/-- The quadratic equation has degree at most two, including degenerate cases. -/
theorem quadraticFiberPolynomial_totalDegree (a : Fin n → F)
    (T : Matrix (Fin n) (Fin n) F) (q : F) :
    (quadraticFiberPolynomial a T q).totalDegree ≤ 2 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (linearFormPolynomial_totalDegree a).trans (by decide)
  · have h := totalDegree_mul (C ((2 : F)⁻¹)) (quadraticFormPolynomial T)
    simp only [totalDegree_C, zero_add] at h
    exact h.trans (quadraticFormPolynomial_totalDegree T)

/-- The cubic equation has degree at most three, including degenerate cases. -/
theorem cubicFiberPolynomial_totalDegree (a : Fin n → F) (S : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (k : F) :
    (cubicFiberPolynomial a S T k).totalDegree ≤ 3 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (linearFormPolynomial_totalDegree a).trans (by decide)
    · have h := totalDegree_mul (C ((2 : F)⁻¹)) (quadraticFormPolynomial S)
      simp only [totalDegree_C, zero_add] at h
      exact h.trans ((quadraticFormPolynomial_totalDegree S).trans (by decide))
  · have h := totalDegree_mul (C ((6 : F)⁻¹)) (cubicFormPolynomial T)
    simp only [totalDegree_C, zero_add] at h
    exact h.trans (cubicFormPolynomial_totalDegree T)

variable {A : Type*} [Field A] [Algebra F A]

theorem affineFiberPolynomial_aeval (g : Fin n → F) (c : F) (x : Fin (n + 1) → A) :
    aeval x (affineFiberPolynomial g c) =
      x (Fin.last n) - (∑ i : Fin n, algebraMap F A (g i) * x i.castSucc) - algebraMap F A c := by
  simp [affineFiberPolynomial]

theorem quadraticFiberPolynomial_aeval (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F)
    (q : F) (x : Fin n → A) :
    aeval x (quadraticFiberPolynomial a T q) =
      quadraticExpression (fun i => algebraMap F A (a i))
        (Matrix.of fun i j => algebraMap F A (T i j)) x - algebraMap F A q := by
  simp [quadraticFiberPolynomial, linearFormPolynomial, quadraticFormPolynomial, quadraticExpression, map_ofNat]

theorem cubicFiberPolynomial_aeval (a : Fin n → F) (S : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (k : F) (x : Fin n → A) :
    aeval x (cubicFiberPolynomial a S T k) =
      cubicExpression (fun i => algebraMap F A (a i))
        (Matrix.of fun i j => algebraMap F A (S i j))
        (fun i j l => algebraMap F A (T i j l)) x - algebraMap F A k := by
  simp [cubicFiberPolynomial, linearFormPolynomial, quadraticFormPolynomial, cubicFormPolynomial, cubicExpression, map_ofNat]

end DimensionFourDependence
