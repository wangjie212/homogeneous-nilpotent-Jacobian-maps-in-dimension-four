import DimensionFourDependence.ParabolaFromAffineSquare

/-! # Original function-field constancy gives an entire polynomial identity

Evaluation at a transcendental parameter is injective. Thus a polynomial
in the original coordinates which is constant on a specified polynomial
parametrization at the actual generic point has that same constant
polynomial as its entire substituted expression.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E F sigma : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra E F] [Algebra K F] [IsScalarTower K E F]

/-- Constancy at the actual transcendental generic parameter is
constancy of the entire original substituted polynomial. -/
theorem original_polynomial_parametrization_constant_of_transcendental
    (t : F) (ht : Transcendental E t) (x : sigma → F) (q : sigma → Polynomial E)
    (hx : ∀ i, Polynomial.aeval t (q i) = x i)
    (P : MvPolynomial sigma K) (c : E) (hvalue : aeval x P = algebraMap E F c) :
    aeval q P = Polynomial.C c := by
  apply (transcendental_iff_injective.mp ht)
  change Polynomial.aeval t (aeval q P) = Polynomial.aeval t (Polynomial.C c)
  rw [Polynomial.aeval_C]
  have he := comp_aeval_apply q ((Polynomial.aeval t).restrictScalars K) P
  have he' : Polynomial.aeval t (aeval q P) = aeval x P := by
    simpa only [AlgHom.restrictScalars_apply, hx] using he
  exact he'.trans hvalue

end DimensionFourDependence
