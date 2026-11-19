import DimensionFourDependence.DirectionMultiplicityLeadingTerm
import DimensionFourDependence.FiberPolynomialForms

/-! # The actual tangent form is nonzero at an independent generic base point

The nonzero evaluated gradient gives a nonzero original linear polynomial.
Algebraic independence of a generic base point prevents that tangent
polynomial from vanishing. Field extension also preserves the entire
projective point ideal, so its original equation and multiplicities apply.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F E σ : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]

/-- Injective field realization retains every original homogeneous
relation, and hence the entire original projective point ideal. -/
theorem projectiveFieldPointIdeal_algHom (A : σ → F) (f : F →ₐ[K] E) :
    (projectiveFieldPointIdeal (E := K) (fun i => f (A i))).toIdeal =
      (projectiveFieldPointIdeal (E := K) A).toIdeal := by
  ext P
  rw [projectiveFieldPointIdeal_mem_iff_components, projectiveFieldPointIdeal_mem_iff_components]
  apply forall_congr'
  intro d
  rw [← comp_aeval_apply A f (homogeneousComponent d P)]
  constructor
  · intro hz
    exact f.injective (hz.trans (map_zero f).symm)
  · intro hz
    rw [hz, map_zero]

variable {n : ℕ}

/-- A nonzero coefficient vector gives a nonzero original linear form. -/
theorem linearFormPolynomial_ne_zero_of_vector_ne_zero (a : Fin n → F) (ha : a ≠ 0) :
    linearFormPolynomial a ≠ 0 := by
  intro hz
  apply ha
  funext i
  have he := congrArg (fun P : MvPolynomial (Fin n) F => pderiv i P) hz
  have hd : pderiv i (linearFormPolynomial a) = C (a i) := by
    simp [linearFormPolynomial, Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply]
  rw [hd, map_zero] at he
  exact C_injective (Fin n) F (he.trans (map_zero C).symm)

variable [Algebra F E] [IsScalarTower K F E]

/-- At an algebraically independent base point, the actual nonzero
normal gives a nonzero tangent value in the actual ambient field. -/
theorem independent_base_point_tangent_ne_zero
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K)
    (hgrad : (fun i => aeval A (pderiv i Φ)) ≠ 0)
    (x : Fin n → E) (hx : AlgebraicIndependent F x) :
    (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) ≠ 0 := by
  let a : Fin n → F := fun i => aeval A (pderiv i Φ)
  have hlin : linearFormPolynomial a ≠ 0 := linearFormPolynomial_ne_zero_of_vector_ne_zero a hgrad
  have hinj := algebraicIndependent_iff_injective_aeval.mp hx
  have hval : aeval x (linearFormPolynomial a) ≠ 0 := by
    intro hz
    exact hlin (hinj (hz.trans (map_zero (aeval x)).symm))
  intro hz
  apply hval
  have he (i : Fin n) :
      aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) = algebraMap F E (a i) :=
    (comp_aeval_apply A (IsScalarTower.toAlgHom K F E) (pderiv i Φ)).symm
  simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X, ← he] using hz

/-- The paper's affine leading-degree formula holds at an actual
independent generic base point, with no nonvanishing tangent assumption
supplied. The original direction equation and multiplicity are retained. -/
theorem generic_direction_multiplicity_exact_leading_term [CharZero K]
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial (Fin n) K) {e : ℕ} (hP0 : P ≠ 0) (hP : P.IsHomogeneous e)
    (x : Fin n → E) (hx : AlgebraicIndependent F x) :
    ∃ c : E, c ≠ 0 ∧
      (aeval (fun i => Polynomial.C (x i) +
        Polynomial.C (algebraMap F E (A i)) * Polynomial.X) P).natDegree = e - multiplicity Φ P ∧
      (aeval (fun i => Polynomial.C (x i) +
        Polynomial.C (algebraMap F E (A i)) * Polynomial.X) P).coeff (e - multiplicity Φ P) =
          c * (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) ^ multiplicity Φ P := by
  have hI' : (projectiveFieldPointIdeal (E := K) (fun i => algebraMap F E (A i))).toIdeal =
      Ideal.span {Φ} := by
    have he := projectiveFieldPointIdeal_algHom A (IsScalarTower.toAlgHom K F E)
    change (projectiveFieldPointIdeal (E := K) (fun i => algebraMap F E (A i))).toIdeal =
      (projectiveFieldPointIdeal (E := K) A).toIdeal at he
    exact he.trans hI
  have hzero : aeval (fun i => algebraMap F E (A i)) Φ = 0 :=
    (principal_projective_equation_vanishing_iff_dvd _ Φ hI' Φ hΦ).mpr (dvd_refl Φ)
  have hgrad := principal_projective_equation_gradient_ne_zero A Φ hirr.ne_zero hΦ hI
  have htangent := independent_base_point_tangent_ne_zero A Φ hgrad x hx
  exact direction_multiplicity_affine_exact_leading_term _ Φ hΦ hirr hI' hzero P hP0 hP x htangent

end DimensionFourDependence
