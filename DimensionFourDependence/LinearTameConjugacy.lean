import DimensionFourDependence.LinearPolynomialConjugacy
import DimensionFourDependence.Tame

/-! # Actual constant-coordinate changes preserve polynomial automorphisms and tameness -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] {n : ℕ}

/-- Inverse original constant matrices give an affine polynomial
automorphism, hence an element of the actual tame subgroup. -/
theorem matrixPolynomialCoordinateEquiv_tame
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1) :
    matrixPolynomialCoordinateEquiv T S hTS hST ∈ Tame.subgroup K n := by
  apply Subgroup.subset_closure
  left
  intro i
  rw [matrixPolynomialCoordinateEquiv_apply]
  simp only [linearPolynomialPullback, aeval_X]
  change (linearPolynomialMap T i).totalDegree ≤ 1
  by_cases hz : linearPolynomialMap T i = 0
  · simp [hz]
  · exact ((linearPolynomialMap_homogeneous T i).totalDegree hz).le

/-- The actual pullback of the point map `X + H`. -/
noncomputable def perturbedPolynomialSubstitution
    (H : Fin n → MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (fun i => X i + H i)

theorem perturbedPolynomialSubstitution_X
    (H : Fin n → MvPolynomial (Fin n) K) (i : Fin n) :
    perturbedPolynomialSubstitution H (X i) = X i + H i := by
  simp [perturbedPolynomialSubstitution]

/-- Coordinate formulas identify an actual automorphism with the full
substitution, so tameness statements concern the whole polynomial ring. -/
theorem automorphism_eq_perturbedPolynomialSubstitution
    (H : Fin n → MvPolynomial (Fin n) K)
    (e : MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K)
    (he : ∀ i, e (X i) = X i + H i) :
    e.toAlgHom = perturbedPolynomialSubstitution H := by
  apply MvPolynomial.algHom_ext
  intro i
  exact (he i).trans (perturbedPolynomialSubstitution_X H i).symm

/-- The full algebra identity corresponding to constant linear
conjugacy of `X+H`, with the reversal caused by polynomial pullback. -/
theorem perturbedPolynomialSubstitution_linear_conjugacy
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) :
    perturbedPolynomialSubstitution (linearPolynomialConjugate T S H) =
      (matrixPolynomialCoordinateEquiv T S hTS hST).toAlgHom.comp
        ((perturbedPolynomialSubstitution H).comp
          (matrixPolynomialCoordinateEquiv S T hST hTS).toAlgHom) := by
  apply MvPolynomial.algHom_ext
  intro i
  have hF : perturbedPolynomialSubstitution H (linearPolynomialPullback S (X i)) =
      linearPolynomialPullback S (X i) + ∑ j, C (S i j) * H j := by
    simp only [linearPolynomialPullback, aeval_X, linearPolynomialMap,
      perturbedPolynomialSubstitution, map_sum, map_mul, aeval_C, algebraMap_eq,
      mul_add, Finset.sum_add_distrib]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    matrixPolynomialCoordinateEquiv_apply, perturbedPolynomialSubstitution_X, hF]
  change X i + linearPolynomialConjugate T S H i =
    (aeval (linearPolynomialMap T))
      (linearPolynomialPullback S (X i) + ∑ j, C (S i j) * H j)
  rw [map_add]
  change X i + linearPolynomialConjugate T S H i =
    linearPolynomialPullback T (linearPolynomialPullback S (X i)) + _
  rw [matrix_linear_polynomial_substitution_inverse S T hST]
  simp only [linearPolynomialConjugate, map_sum, map_mul, aeval_C, algebraMap_eq]
  rfl

/-- An actual tame automorphism for a constant conjugate gives an
actual tame automorphism of the original point map over the original
field. The coordinate changes are the ones constructed in the proof. -/
theorem tame_automorphism_descends_from_constant_linear_conjugacy
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (e : MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K)
    (he : ∀ i, e (X i) = X i + linearPolynomialConjugate T S H i)
    (het : e ∈ Tame.subgroup K n) :
    ∃ E : MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K,
      E ∈ Tame.subgroup K n ∧ ∀ i, E (X i) = X i + H i := by
  let t := matrixPolynomialCoordinateEquiv T S hTS hST
  let s := matrixPolynomialCoordinateEquiv S T hST hTS
  have hinv (p : MvPolynomial (Fin n) K) : s (t p) = p :=
    matrix_linear_polynomial_substitution_inverse T S hTS p
  have heq : e.toAlgHom = t.toAlgHom.comp ((perturbedPolynomialSubstitution H).comp s.toAlgHom) :=
    (automorphism_eq_perturbedPolynomialSubstitution _ e he).trans
      (perturbedPolynomialSubstitution_linear_conjugacy T S hTS hST H)
  refine ⟨s * e * t, ?_, ?_⟩
  · exact (Tame.subgroup K n).mul_mem
      ((Tame.subgroup K n).mul_mem
        (matrixPolynomialCoordinateEquiv_tame S T hST hTS) het)
      (matrixPolynomialCoordinateEquiv_tame T S hTS hST)
  · intro i
    change s (e (t (X i))) = X i + H i
    have hep := AlgHom.congr_fun heq (t (X i))
    change e (t (X i)) = t (perturbedPolynomialSubstitution H (s (t (X i)))) at hep
    rw [hep, hinv, hinv, perturbedPolynomialSubstitution_X]

end DimensionFourDependence
