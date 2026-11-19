import DimensionFourDependence.CoprimeBinaryPencilSplitMember
import DimensionFourDependence.LinearTameConjugacy

/-! # Distinct split factors give the base coordinate frame of Lemma 6.8 -/

namespace DimensionFourDependence.Shear

open MvPolynomial Matrix

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

/-- The two root factors become the two coefficient variables under
an actual invertible linear substitution. -/
theorem split_binary_quadratic_factors_construct_base_frame
    (r s : K) (hrs : r ≠ s) :
    ∃ T S : M₂, T * S = 1 ∧ S * T = 1 ∧
      linearPolynomialPullback T (X 0 - C r * X 1 : R₂) = X 0 ∧
      linearPolynomialPullback T (X 0 - C s * X 1 : R₂) = X 1 := by
  let S : M₂ := !![1, -r; 1, -s]
  have hSdet : S.det = r - s := by
    simp [S, Matrix.det_fin_two, sub_eq_add_neg, add_comm]
  have hS : IsUnit S.det := by
    rw [hSdet]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hrs)
  have hST := Matrix.mul_nonsing_inv S hS
  have hTS := Matrix.nonsing_inv_mul S hS
  refine ⟨S⁻¹, S, hTS, hST, ?_, ?_⟩
  · have h : linearPolynomialPullback S (X 0 : R₂) = X 0 - C r * X 1 := by
      simp [linearPolynomialPullback, linearPolynomialMap, S, Fin.sum_univ_two,
        sub_eq_add_neg, neg_mul]
    rw [← h]
    exact matrix_linear_polynomial_substitution_inverse S S⁻¹ hST _
  · have h : linearPolynomialPullback S (X 1 : R₂) = X 0 - C s * X 1 := by
      simp [linearPolynomialPullback, linearPolynomialMap, S, Fin.sum_univ_two,
        sub_eq_add_neg, neg_mul]
    rw [← h]
    exact matrix_linear_polynomial_substitution_inverse S S⁻¹ hST _

/-- Substitution by an invertible constant matrix preserves relative
primality over the original polynomial coefficient ring. -/
theorem binary_base_frame_preserves_isRelPrime
    (T S : M₂) (hTS : T * S = 1) (hST : S * T = 1)
    (a b : R₂) (hc : IsRelPrime a b) :
    IsRelPrime (linearPolynomialPullback T a) (linearPolynomialPullback T b) := by
  let E := matrixPolynomialCoordinateEquiv T S hTS hST
  change IsRelPrime (E a) (E b)
  intro q hqa hqb
  have hqa' : E.symm q ∣ a := by
    have h := map_dvd E.symm.toRingHom hqa
    change E.symm q ∣ E.symm (E a) at h
    rwa [AlgEquiv.symm_apply_apply] at h
  have hqb' : E.symm q ∣ b := by
    have h := map_dvd E.symm.toRingHom hqb
    change E.symm q ∣ E.symm (E b) at h
    rwa [AlgEquiv.symm_apply_apply] at h
  have hu := (hc hqa' hqb').map E.toRingHom
  change IsUnit (E (E.symm q)) at hu
  rwa [AlgEquiv.apply_symm_apply] at hu

end DimensionFourDependence.Shear
