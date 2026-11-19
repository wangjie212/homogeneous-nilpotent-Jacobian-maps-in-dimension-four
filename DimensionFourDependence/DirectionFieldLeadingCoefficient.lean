import DimensionFourDependence.GenericDirectionTangent

/-! # Affine leading coefficients stay in the actual direction field

The cofactor after removing the full original direction-equation
multiplicity is evaluated before extending the base-point field. Thus its
nonzero scalar lies in the direction field itself, while the tangent form
may be evaluated at any point of a larger field.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] {n : ℕ}

/-- The highest allowed affine coefficient has its nonzero scalar in
the original direction field. The bound holds even at tangent zeros. -/
theorem direction_field_affine_leading_coefficient
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial (Fin n) K) {e : ℕ} (hP0 : P ≠ 0) (hP : P.IsHomogeneous e)
    (x : Fin n → E) :
    ∃ c : F, c ≠ 0 ∧ multiplicity Φ P ≤ e ∧
      (aeval (fun i => Polynomial.C (x i) +
        Polynomial.C (algebraMap F E (A i)) * Polynomial.X) P).natDegree ≤ e - multiplicity Φ P ∧
      (aeval (fun i => Polynomial.C (x i) +
        Polynomial.C (algebraMap F E (A i)) * Polynomial.X) P).coeff (e - multiplicity Φ P) =
          algebraMap F E c *
            (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) ^ multiplicity Φ P := by
  obtain ⟨R, hfactor, _hR0, _hnot, hR, hval, hbound, hm⟩ :=
    direction_equation_multiplicity_cofactor A Φ hΦ hirr hI P hP0 hP
  have hδ := (principal_projective_equation_irreducible_degree_pos A Φ hirr.ne_zero hΦ hI).2
  have hI' : (projectiveFieldPointIdeal (E := K) (fun i => algebraMap F E (A i))).toIdeal =
      Ideal.span {Φ} := by
    have he := projectiveFieldPointIdeal_algHom A (IsScalarTower.toAlgHom K F E)
    change (projectiveFieldPointIdeal (E := K) (fun i => algebraMap F E (A i))).toIdeal =
      (projectiveFieldPointIdeal (E := K) A).toIdeal at he
    exact he.trans hI
  have hzero : aeval (fun i => algebraMap F E (A i)) Φ = 0 :=
    (principal_projective_equation_vanishing_iff_dvd _ Φ hI' Φ hΦ).mpr (dvd_refl Φ)
  have hindex : multiplicity Φ P * (δ - 1) + (e - δ * multiplicity Φ P) = e - multiplicity Φ P := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, mul_comm (multiplicity Φ P) δ]
    have hle := Nat.le_mul_of_pos_left (multiplicity Φ P) hδ
    omega
  obtain ⟨hdeg, hcoeff⟩ := homogeneous_equation_power_affine_leading_term Φ R hδ hΦ hR
    x (fun i => algebraMap F E (A i)) hzero (multiplicity Φ P)
  rw [hindex, ← hfactor] at hdeg hcoeff
  have hvalue : aeval (fun i => algebraMap F E (A i)) R = algebraMap F E (aeval A R) :=
    (comp_aeval_apply A (IsScalarTower.toAlgHom K F E) R).symm
  refine ⟨aeval A R, hval, hm, hdeg, ?_⟩
  rw [hcoeff, hvalue, mul_comm]

end DimensionFourDependence
