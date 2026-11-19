import DimensionFourDependence.GaussDimensionTwoQuadric
import DimensionFourDependence.LinearPullbackGradient

/-! # The checked smooth-quadric conclusion over algebraically closed coefficients

The actual original defining equation is quadratic and becomes the
determinant polynomial up to a nonzero scalar in invertible linear
coordinates. The evaluated gradient is nonzero at every nonzero vector,
so nonsingularity is also checked for the actual original equation.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

section Coordinates

variable {F : Type*} [Field F]

/-- The determinant polynomial in any invertible actual linear
coordinates has nonzero gradient at every nonzero vector. -/
theorem rulingPolynomialInCoordinates_gradient_ne_zero
    (e : (Fin 4 → F) ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)))
    (x : Fin 4 → F) (hx : x ≠ 0) :
    (fun i => aeval x (pderiv i (rulingPolynomialInCoordinates e))) ≠ 0 := by
  let g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) := e.trans (fourCoordinateEquiv (F := F))
  have hgx : g x ≠ 0 := fun hz => hx ((map_eq_zero_iff g g.injective).mp hz)
  intro hz
  change (fun i => aeval x (pderiv i
    (linearPolynomialPullback (LinearMap.toMatrix' g.toLinearMap) standardRulingPolynomial))) = 0 at hz
  exact standardRulingPolynomial_projectively_nonsingular (g x) hgx
    ((linearPolynomialPullback_gradient_zero_iff g standardRulingPolynomial x).mp hz)

/-- Exact polynomial identification with that determinant gives
projective nonsingularity of the actual defining equation itself. -/
theorem polynomial_associated_ruling_projectively_nonsingular
    (R : MvPolynomial (Fin 4) F)
    (e : (Fin 4 → F) ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F))) (c : F)
    (heq : rulingPolynomialInCoordinates e = MvPolynomial.C c * R)
    (x : Fin 4 → F) (hx : x ≠ 0) :
    (fun i => aeval x (pderiv i R)) ≠ 0 := by
  intro hz
  apply rulingPolynomialInCoordinates_gradient_ne_zero e x hx
  funext i
  rw [heq]
  have hi := congrFun hz i
  simp only [Pi.zero_apply] at hi
  change MvPolynomial.eval x (pderiv i R) = 0 at hi
  simp [Derivation.leibniz, hi]

end Coordinates

universe u

variable {K E : Type u} [Field K] [CharZero K] [IsAlgClosed K] [Field E] [Algebra K E]

/-- Proposition 3.1 over algebraically closed coefficients: the
original actual equation is a projectively nonsingular quadratic,
identified polynomially with the determinant in invertible linear
coordinates. No auxiliary equations, directions, line families,
dimension, incidence or smoothness conclusions are assumed. -/
theorem proposition_3_1_over_algebraically_closed_field
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
      (∀ x : Fin 4 → K, x ≠ 0 → (fun i => aeval x (pderiv i I.equation)) ≠ 0) ∧
      ∃ (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K))) (c : K), c ≠ 0 ∧
        rulingPolynomialInCoordinates e = MvPolynomial.C c * I.equation ∧
        ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
  obtain ⟨hdeg, e, c, hc, he, hzero⟩ :=
    gauss_dimension_two_nonlinear_geometric_fiber_image_quadric H hd hH hN hrank hind I hGauss P hP hline
  exact ⟨hdeg, fun x hx => polynomial_associated_ruling_projectively_nonsingular I.equation e c he x hx,
    e, c, hc, he, hzero⟩

end DimensionFourDependence
