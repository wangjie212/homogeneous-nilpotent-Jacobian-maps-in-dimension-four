import DimensionFourDependence.FixedCoordinateTamenessReduction
import DimensionFourDependence.Proposition64

/-! # Exact specification of the still-open Theorem 1.2 -/

namespace DimensionFourDependence

open Matrix MvPolynomial

variable {K : Type*} [Field K]

/-- The independent branch in Theorem 1.2 is witnessed by actual
inverse constant coordinates making the last perturbation component
zero and by independence of their normalized ternary chart. -/
def HasIndependentNormalizedTernaryChart
    (H : Fin 4 → MvPolynomial (Fin 4) K) : Prop :=
  ∃ (T S : Matrix (Fin 4) (Fin 4) K)
    (B : Fin 3 → MvPolynomial (Fin 4) K),
    T * S = 1 ∧ S * T = 1 ∧
    linearPolynomialConjugate T S H = Fin.lastCases 0 B ∧
    ¬ComponentsDependent (normalizedFixedCoordinateChart B)

/-- The full original-field assertion of Theorem 1.2. This is only
a specification. It requires an actual polynomial automorphism with
the exact coordinates `X+H`, an actual tame extension fixing one
additional variable, and ordinary tameness both through degree five
and in the independent normalized ternary branch in every degree. -/
def TamenessTheorem (K : Type*) [Field K] [CharZero K] : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ H : Fin 4 → MvPolynomial (Fin 4) K,
    IsHomogMap H d → IsNilpotent (jac H) →
    ∃ e : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
      (∀ i, e (X i) = X i + H i) ∧
      Shear.IsOneStablyTame e ∧
      (HasIndependentNormalizedTernaryChart H → e ∈ Tame.subgroup K 4) ∧
      (d ≤ 5 → e ∈ Tame.subgroup K 4)

end DimensionFourDependence
