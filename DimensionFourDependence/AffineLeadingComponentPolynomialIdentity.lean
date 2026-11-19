import DimensionFourDependence.AffineSubstitutionLeadingValue
import DimensionFourDependence.ProjectiveSourceParameterField

/-! # Affine substitution preserves the highest allowed component by its linear part -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1550000

variable {L : Type u} [Field L] {n m : ℕ}

/-- The leading value identity gives an equality of the actual
polynomials, by evaluating in the rational field of their variables. -/
theorem homogeneousComponent_affine_substitution
    (g : Fin m → MvPolynomial (Fin n) L) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (P : MvPolynomial (Fin m) L) {d : ℕ} (hP : P.totalDegree ≤ d) :
    homogeneousComponent d (aeval g P) =
      aeval (fun i => homogeneousComponent 1 (g i)) (homogeneousComponent d P) := by
  let R₀ := MvPolynomial (Fin n) L
  let F := FractionRing R₀
  let x := rationalCoordinate (K := L) (n := n)
  apply IsFractionRing.injective R₀ F
  rw [← rationalCoordinate_aeval, ← rationalCoordinate_aeval, comp_aeval_apply]
  exact affine_substitution_homogeneous_value g hg P hP x

end DimensionFourDependence
