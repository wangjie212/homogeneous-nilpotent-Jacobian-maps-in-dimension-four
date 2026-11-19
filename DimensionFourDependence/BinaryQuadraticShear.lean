import DimensionFourDependence.BinaryQuadraticExpansion

/-! # A quadratic relation surviving a quadratic shear is a parabola graph

The exact change Y to Y+s*T^2 is an invertible polynomial substitution.
If a polynomial and its negative-unit shear both have degree at most
two, their actual fourth and third T coefficients remove the Y-square
and Y*T terms. The remaining equation is linear in Y with constant
coefficient and quadratic in T.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L : Type*} [Field L]

/-- The actual polynomial quadratic shear fixing T. -/
noncomputable def binaryQuadraticShear (s : L) :
    MvPolynomial (Option Unit) L →ₐ[L] MvPolynomial (Option Unit) L :=
  aeval (fun j : Option Unit => j.elim (X none + C s * X (some ()) ^ 2) (fun _ => X (some ())))

/-- Applying the opposite quadratic shear recovers the entire original polynomial. -/
theorem binaryQuadraticShear_inverse (s : L) (P : MvPolynomial (Option Unit) L) :
    binaryQuadraticShear (-s) (binaryQuadraticShear s P) = P := by
  have he : (binaryQuadraticShear (-s)).comp (binaryQuadraticShear s) = AlgHom.id L _ := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simp [binaryQuadraticShear]
    | some u => cases u; simp [binaryQuadraticShear]
  exact DFunLike.congr_fun he P

/-- The actual quadratic shear preserves nonvanishing. -/
theorem binaryQuadraticShear_ne_zero (s : L) {P : MvPolynomial (Option Unit) L} (hP : P ≠ 0) :
    binaryQuadraticShear s P ≠ 0 := by
  intro he
  apply hP
  rw [← binaryQuadraticShear_inverse s P, he, map_zero]

/-- Each actual binary coordinate monomial has its specified exponent vector. -/
theorem binary_coordinate_monomial (a : L) (i j : ℕ) :
    C a * X (none : Option Unit) ^ i * X (some ()) ^ j =
      monomial (Finsupp.single none i + Finsupp.single (some ()) j) a := by
  rw [C_mul_X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one]

/-- Retaining degree at most two after the actual shear excludes
both quadratic Y terms, directly from the fourth and third T coefficients. -/
theorem binary_quadratic_shear_forces_graph_equation
    (P : MvPolynomial (Option Unit) L) (hP : P.totalDegree ≤ 2)
    (hshift : (binaryQuadraticShear (-1) P).totalDegree ≤ 2) :
    ∃ a b c f : L, P = C a + C b * X none + C c * X (some ()) + C f * X (some ()) ^ 2 := by
  classical
  obtain ⟨a, b, c, d, e, f, hcoeff⟩ := binary_quadratic_coordinate_expansion P hP
  have hexp : binaryQuadraticShear (-1) P =
      C a * X none ^ 0 * X (some ()) ^ 0 +
      C b * X none ^ 1 * X (some ()) ^ 0 +
      C c * X none ^ 0 * X (some ()) ^ 1 +
      C d * X none ^ 2 * X (some ()) ^ 0 +
      C e * X none ^ 1 * X (some ()) ^ 1 +
      C (f - b) * X none ^ 0 * X (some ()) ^ 2 +
      C (-2 * d) * X none ^ 1 * X (some ()) ^ 2 +
      C (-e) * X none ^ 0 * X (some ()) ^ 3 +
      C d * X none ^ 0 * X (some ()) ^ 4 := by
    rw [hcoeff]
    simp [binaryQuadraticShear, map_ofNat]
    ring
  have h4 := congrArg (fun Q : MvPolynomial (Option Unit) L => Q.coeff (Finsupp.single (some ()) 4)) hexp
  simp only [binary_coordinate_monomial] at h4
  norm_num [Finsupp.ext_iff, Option.forall] at h4
  have h4zero : (binaryQuadraticShear (-1) P).coeff (Finsupp.single (some ()) 4) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    apply hshift.trans_lt
    norm_num [Finsupp.degree_eq_sum, Fintype.sum_option]
  have hd : d = 0 := h4.symm.trans h4zero
  have h3 := congrArg (fun Q : MvPolynomial (Option Unit) L => Q.coeff (Finsupp.single (some ()) 3)) hexp
  simp only [binary_coordinate_monomial] at h3
  norm_num [Finsupp.ext_iff, Option.forall] at h3
  have h3zero : (binaryQuadraticShear (-1) P).coeff (Finsupp.single (some ()) 3) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    apply hshift.trans_lt
    norm_num [Finsupp.degree_eq_sum, Fintype.sum_option]
  have he : e = 0 := neg_eq_zero.mp (h3.symm.trans h3zero)
  refine ⟨a, b, c, f, ?_⟩
  simpa only [hd, he, map_zero, zero_mul, add_zero] using hcoeff

variable {F : Type*} [Field F] [Algebra L F]

/-- Evaluation of the quadratic shear is the original equation at
the correspondingly shifted actual affine point. -/
theorem binaryQuadraticShear_aeval (s : L) (t y : F) (P : MvPolynomial (Option Unit) L) :
    aeval (fun j : Option Unit => j.elim y (fun _ => t)) (binaryQuadraticShear s P) =
      aeval (fun j : Option Unit => j.elim (y + algebraMap L F s * t ^ 2) (fun _ => t)) P := by
  have he : (aeval (fun j : Option Unit => j.elim y (fun _ => t))).comp (binaryQuadraticShear s) =
      aeval (fun j : Option Unit => j.elim (y + algebraMap L F s * t ^ 2) (fun _ => t)) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simp [binaryQuadraticShear]
    | some u => cases u; simp [binaryQuadraticShear]
  exact DFunLike.congr_fun he P

end DimensionFourDependence
