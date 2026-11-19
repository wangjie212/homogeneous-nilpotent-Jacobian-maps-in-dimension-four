import DimensionFourDependence.HomogeneousAffineTangentCoefficient
import DimensionFourDependence.DirectionEquationMultiplicity

/-! # The leading affine term after removing the direction equation

If P = Φ^m R and Φ(A) = 0, its substituted degree is at most
m(deg Φ - 1) + deg R. The coefficient at that degree is exactly
R(A) times the m-th power of the tangent form at A. For the full
factor multiplicity this is the original homogeneous degree minus m.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

/-- The exact highest allowed affine-line coefficient of a homogeneous
equation power times a homogeneous cofactor, including cancellations. -/
theorem homogeneous_equation_power_affine_leading_term
    (Φ R : MvPolynomial (Fin n) K) {δ f : ℕ} (hδ : 0 < δ)
    (hΦ : Φ.IsHomogeneous δ) (hR : R.IsHomogeneous f)
    (x A : Fin n → E) (hzero : aeval A Φ = 0) (m : ℕ) :
    let s := fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X
    (aeval s (Φ ^ m * R)).natDegree ≤ m * (δ - 1) + f ∧
      (aeval s (Φ ^ m * R)).coeff (m * (δ - 1) + f) =
        (∑ i, aeval A (pderiv i Φ) * x i) ^ m * aeval A R := by
  dsimp only
  let s : Fin n → Polynomial E := fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X
  have hΦdeg : (aeval s Φ).natDegree ≤ δ - 1 :=
    homogeneous_affine_line_degree_drop Φ hΦ x A hzero
  have hs (i : Fin n) : (s i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simpa using (Polynomial.natDegree_X_le (R := E)))
  have hRdeg : (aeval s R).natDegree ≤ f :=
    (polynomial_natDegree_aeval_le_totalDegree s hs R).trans hR.totalDegree_le
  have hpow : ((aeval s Φ) ^ m).natDegree ≤ m * (δ - 1) :=
    Polynomial.natDegree_pow_le_of_le m hΦdeg
  constructor
  · change (aeval s (Φ ^ m * R)).natDegree ≤ _
    rw [map_mul, map_pow]
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hpow hRdeg)
  · change (aeval s (Φ ^ m * R)).coeff _ = _
    rw [map_mul, map_pow, Polynomial.coeff_mul_add_eq_of_natDegree_le hpow hRdeg,
      Polynomial.coeff_pow_of_natDegree_le hΦdeg,
      homogeneous_affine_line_tangent_coefficient Φ hδ hΦ x A,
      homogeneous_affine_line_coefficient_at_degree R hR x A]

/-- At the full factor multiplicity the original homogeneous degree
drops by exactly that multiplicity whenever its tangent value is nonzero.
The coefficient and its nonvanishing are both retained explicitly. -/
theorem direction_multiplicity_affine_exact_leading_term
    (A : Fin n → E) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (hzero : aeval A Φ = 0)
    (P : MvPolynomial (Fin n) K) {e : ℕ} (hP0 : P ≠ 0) (hP : P.IsHomogeneous e)
    (x : Fin n → E) (htangent : (∑ i, aeval A (pderiv i Φ) * x i) ≠ 0) :
    ∃ c : E, c ≠ 0 ∧
      (aeval (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) P).natDegree =
        e - multiplicity Φ P ∧
      (aeval (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X) P).coeff
        (e - multiplicity Φ P) = c * (∑ i, aeval A (pderiv i Φ) * x i) ^ multiplicity Φ P := by
  obtain ⟨R, hfactor, _hR0, _hnot, hR, hval, hbound, _hm⟩ :=
    direction_equation_multiplicity_cofactor A Φ hΦ hirr hI P hP0 hP
  have hδ := (principal_projective_equation_irreducible_degree_pos A Φ hirr.ne_zero hΦ hI).2
  have hindex : multiplicity Φ P * (δ - 1) + (e - δ * multiplicity Φ P) =
      e - multiplicity Φ P := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, mul_comm (multiplicity Φ P) δ]
    have hm := Nat.le_mul_of_pos_left (multiplicity Φ P) hδ
    omega
  obtain ⟨hdeg, hcoeff⟩ := homogeneous_equation_power_affine_leading_term Φ R hδ hΦ hR
    x A hzero (multiplicity Φ P)
  rw [hindex, ← hfactor] at hdeg hcoeff
  have hc : (∑ i, aeval A (pderiv i Φ) * x i) ^ multiplicity Φ P * aeval A R ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ htangent) hval
  refine ⟨aeval A R, hval, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg ?_, ?_⟩
  · rwa [hcoeff]
  · exact hcoeff.trans (mul_comm _ _)

end DimensionFourDependence
