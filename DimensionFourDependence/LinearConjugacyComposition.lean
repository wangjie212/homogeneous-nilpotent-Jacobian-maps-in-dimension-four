import DimensionFourDependence.FixedCovectorCoordinateChoice

/-! # Composing the original linear source and target changes -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}
local notation "R" => MvPolynomial (Fin n) K
local notation "M" => Matrix (Fin n) (Fin n) K

theorem linearPolynomialPullback_compose (T U : M) (p : R) :
    linearPolynomialPullback U (linearPolynomialPullback T p) =
      linearPolynomialPullback (T * U) p := by
  let A : M → R →ₐ[K] R := fun S => aeval (linearPolynomialMap S)
  have he : (A U).comp (A T) = A (T * U) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [A, AlgHom.comp_apply, aeval_X]
    change linearPolynomialPullback U (linearFormPolynomial (T i)) =
      linearFormPolynomial ((T * U) i)
    rw [linearPolynomialPullback_linear_form]
    rfl
  exact AlgHom.congr_fun he p

theorem linearPolynomialConjugate_compose (T S U V : M) (H : Fin n → R) :
    linearPolynomialConjugate U V (linearPolynomialConjugate T S H) =
      linearPolynomialConjugate (T * U) (V * S) H := by
  let A : R →ₐ[K] R := aeval (linearPolynomialMap U)
  have hC (c : K) : A (C c) = C c := A.commutes _
  have hA (p : R) : A (linearPolynomialPullback T p) = linearPolynomialPullback (T * U) p :=
    linearPolynomialPullback_compose T U p
  funext i
  change (∑ j, C (V i j) * A (∑ k, C (S j k) * linearPolynomialPullback T (H k))) =
    ∑ k, C ((V * S) i k) * linearPolynomialPullback (T * U) (H k)
  simp only [map_sum, map_mul, hC, hA, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, mul_assoc]

end DimensionFourDependence
