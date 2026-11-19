import DimensionFourDependence.ClosedParameterPolynomialDescent
import DimensionFourDependence.SegreNormalizedRulingPolynomial

/-! # Both original ruling polynomials are realized in one geometric constant field -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A bounded original normalized ruling polynomial in the common
geometric constant field, with every coefficient algebraic over the
specified original ruling parameter alone. -/
def SegreAlgebraicNormalizedRulingPolynomial
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3) : Prop :=
  ∃ P : Polynomial E, P ≠ 0 ∧ P.natDegree ≤ d + 1 ∧
    f ^ d / (Y 0) ^ (d + 1) = P.eval (Y (segreRulingRemainingIndex j).castSucc / Y 0) ∧
    ∀ i, IsAlgebraic (IntermediateField.adjoin K ({Y j.castSucc / Y 0} : Set E)) (P.coeff i)

/-- The actual finite boundary coefficient polynomial descends into
the original closed geometric constants, preserving its nonzero value,
degree bound and algebraicity over the original parameter alone. -/
theorem segre_normalized_ruling_polynomial_descends_to_geometric_constants
    [IsAlgClosed E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hpoly : SegreBoundedNormalizedRulingPolynomial K Y f d j p) :
    SegreAlgebraicNormalizedRulingPolynomial K Y f d j := by
  obtain ⟨a, _ha, C, hC, P, hP, hdegree, hvalue⟩ := hpoly
  exact finite_parameter_polynomial_descends_to_closed_constants
    (Y j.castSucc / Y 0) (Y (segreRulingRemainingIndex j).castSucc / Y 0)
      (f ^ d / (Y 0) ^ (d + 1)) C hC P hP hdegree (by
        simpa only [map_div₀, map_pow] using hvalue)

end DimensionFourDependence
