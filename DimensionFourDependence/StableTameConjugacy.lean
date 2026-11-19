import DimensionFourDependence.LinearTameConjugacy
import DimensionFourDependence.StableTamenessComposition

/-! # Restoring constant coordinates while retaining stable and ordinary tameness -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

theorem actual_automorphisms_with_same_coordinate_perturbation_eq
    (H : Fin 4 → R₄) (e f : Aut₄)
    (he : ∀ i, e (X i) = X i + H i) (hf : ∀ i, f (X i) = X i + H i) :
    e = f := by
  apply AlgEquiv.ext
  exact AlgHom.congr_fun
    ((automorphism_eq_perturbedPolynomialSubstitution H e he).trans
      (automorphism_eq_perturbedPolynomialSubstitution H f hf).symm)

/-- The original automorphism is recovered using affine maps on both
sides, so its fixed-variable tame extension retains the same length of stabilization. -/
theorem one_stably_tame_automorphism_descends_from_constant_linear_conjugacy
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin 4 → R₄) (e : Aut₄)
    (he : ∀ i, e (X i) = X i + linearPolynomialConjugate T S H i)
    (hes : Shear.IsOneStablyTame e) :
    ∃ E : Aut₄, (∀ i, E (X i) = X i + H i) ∧ Shear.IsOneStablyTame E ∧
      (e ∈ Tame.subgroup K 4 → E ∈ Tame.subgroup K 4) := by
  let t := matrixPolynomialCoordinateEquiv T S hTS hST
  let s := matrixPolynomialCoordinateEquiv S T hST hTS
  have ht := matrixPolynomialCoordinateEquiv_tame T S hTS hST
  have hs := matrixPolynomialCoordinateEquiv_tame S T hST hTS
  have hinv (p : R₄) : s (t p) = p :=
    matrix_linear_polynomial_substitution_inverse T S hTS p
  have heq : e.toAlgHom = t.toAlgHom.comp ((perturbedPolynomialSubstitution H).comp s.toAlgHom) :=
    (automorphism_eq_perturbedPolynomialSubstitution _ e he).trans
      (perturbedPolynomialSubstitution_linear_conjugacy T S hTS hST H)
  refine ⟨s * e * t, ?_, ?_, ?_⟩
  · intro i
    change s (e (t (X i))) = X i + H i
    have hep := AlgHom.congr_fun heq (t (X i))
    change e (t (X i)) = t (perturbedPolynomialSubstitution H (s (t (X i)))) at hep
    rw [hep, hinv, hinv, perturbedPolynomialSubstitution_X]
  · exact Shear.oneStablyTame_mul _ _ (Shear.oneStablyTame_mul _ _
      (Shear.oneStablyTame_of_tame s hs) hes) (Shear.oneStablyTame_of_tame t ht)
  · exact fun h => (Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem hs h) ht

end DimensionFourDependence
