import DimensionFourDependence.OriginalParabolicCoefficientFamily
import DimensionFourDependence.ParabolicCoefficientAlgebraicity

/-! # An original vertex-dependent invariant constrains the quadratic coefficient

Every coefficient and multiplicity comes from the original homogeneous
invariant and its actual direction equation. Constancy of its entire
formal parabolic substitution constructs a nonzero polynomial over the
direction field in T times the quadratic vertex coefficient.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] {n : ℕ}

/-- The actual original vertex-dependent invariant constructs its
polynomial constraint on the tangent-scaled quadratic coefficient.
No coefficient family, maximal degree or annihilating relation is supplied. -/
theorem original_invariant_tangent_quadratic_isAlgebraic
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial (Option (Fin n)) K) {e : ℕ}
    (hP0 : P ≠ 0) (hP : P.IsHomogeneous e) (hvertex : 0 < P.degreeOf none)
    (x : Fin n → E)
    (hT : (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) ≠ 0)
    (w : Polynomial E) (hw : w.natDegree ≤ 2)
    (a : E) (hconstant : aeval (fun j : Option (Fin n) => j.elim w
      (fun i => Polynomial.C (x i) + Polynomial.C (algebraMap F E (A i)) * Polynomial.X)) P = Polynomial.C a) :
    IsAlgebraic F ((∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) * w.coeff 2) := by
  classical
  let Q := optionEquivLeft K (Fin n) P
  let m : ℕ → ℕ := fun j => multiplicity Φ (Q.coeff j)
  let f : ℕ → Polynomial E := fun j => aeval (fun i => Polynomial.C (x i) +
    Polynomial.C (algebraMap F E (A i)) * Polynomial.X) (Q.coeff j)
  let T : E := ∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i
  obtain ⟨hpositive, c, hc⟩ := original_parabolic_coefficient_family A Φ hΦ hirr hI P hP0 hP hvertex x
  have hsum : (∑ j ∈ Q.support, f j * w ^ j) = Polynomial.C a := by
    rw [original_vertex_polynomial_evaluation_expansion] at hconstant
    exact hconstant
  obtain ⟨N, _hN, _htop, _hpoly, _hroot, halg⟩ :=
    constant_parabolic_invariant_constructs_algebraic_tangent_ratio Q.support e m c hpositive
      (fun j hj => (hc j hj).1) (fun j hj => (hc j hj).2.2.1)
      (fun j hj => (hc j hj).2.1) f T hT
      (fun j hj => (hc j hj).2.2.2.1) (fun j hj => (hc j hj).2.2.2.2)
      w hw a hsum
  exact halg

end DimensionFourDependence
