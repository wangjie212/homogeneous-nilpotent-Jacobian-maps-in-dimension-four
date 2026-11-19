import DimensionFourDependence.ActualGenericLinePairQuadric
import DimensionFourDependence.FiberInvariantDataForWitness
import DimensionFourDependence.GeometricLineAtlas

/-! # The Gauss-dimension-two quadric conclusion from the original map

Over algebraically closed coefficients, a nonlinear actual geometric
generic fiber and the actual Gauss-image dimension two give the two
distinct generic image lines. Their covering components, dimensions,
product relations and pairwise incidence are all constructed. The
actual defining equation is a nonzero scalar multiple of the smooth
determinant quadric after an actual invertible linear coordinate change.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [CharZero K] [IsAlgClosed K] [Field E] [Algebra K E]

/-- Equality with the determinant zero set gives an exact polynomial
scalar-multiple identity for the actual original image equation. -/
theorem ImageRelationWitness.ruling_polynomial_scalar_multiple_of_zero_set
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H)
    (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)))
    (hzero : ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0) :
    ∃ c : K, c ≠ 0 ∧ rulingPolynomialInCoordinates e = MvPolynomial.C c * I.equation := by
  have hvan : aeval H (rulingPolynomialInCoordinates e) = 0 := by
    apply MvPolynomial.funext
    intro x
    change aeval x (aeval H (rulingPolynomialInCoordinates e)) = 0
    rw [comp_aeval_apply, rulingPolynomialInCoordinates_eval]
    apply (hzero (fun i => aeval x (H i))).mp
    have he := congrArg (aeval x) I.vanishing
    rw [comp_aeval_apply, map_zero] at he
    exact he
  exact (I.quadratic_relation_scalar_multiple H hd hH hrank hind _
    (rulingPolynomialInCoordinates_homogeneous e) (rulingPolynomialInCoordinates_ne_zero e) hvan).2

/-- The Section 3.2 quadric classification over algebraically closed
coefficients, starting with the original homogeneous nilpotent rank-three
map and an actual nonlinear full-output geometric generic component.
All invariant coefficients, two generic lines, covering families and
incidence-density comparisons are constructed in the proof. -/
theorem gauss_dimension_two_nonlinear_geometric_fiber_image_quadric
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2)
    [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [IsScalarTower K (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    I.degree = 2 ∧
      ∃ (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K))) (c : K), c ≠ 0 ∧
        rulingPolynomialInCoordinates e = MvPolynomial.C c * I.equation ∧
        ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, k, hh, hc, hq, hk⟩ :=
    fiberEquationWitness_exists_invariant_coefficients H hN hrank W
  obtain ⟨s, t, _, hne, hs, ht⟩ := geometric_fiber_two_actual_line_atlas_points
    H hd hH hN hrank hind W h c q k hh hc hq hk E P hP hline I hGauss
  obtain ⟨hdeg, e, hzero⟩ := actual_generic_distinct_image_lines_force_quadric
    H hd hH hN hrank hind I hGauss s t hs ht hne
  obtain ⟨a, ha, he⟩ := I.ruling_polynomial_scalar_multiple_of_zero_set H hd hH hrank hind e hzero
  exact ⟨hdeg, e, a, ha, he, hzero⟩

end DimensionFourDependence
