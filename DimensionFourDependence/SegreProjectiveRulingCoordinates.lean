import DimensionFourDependence.SegreFiniteProjectiveRulingPoint

/-! # Actual normalized original coordinates of projective Segre ruling points -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {E : Type u} [Field E]

/-- An original ruling equation gives its exact coordinate equation
in the actual normalized coordinate field of the original projective prime. -/
theorem segre_normalized_projective_ruling_linear_equation
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (a : Fin 4) (ha : X (some a) ∉ p.asHomogeneousIdeal) (t : E) (i k : Fin 4)
    (h : segreRulingLinearPolynomial t i k ∈ p.asHomogeneousIdeal) :
    projectivePrimeRatioCoordinate p (some a) (some i) -
      algebraMap E (projectivePrimeRatioField p (some a)) t *
        projectivePrimeRatioCoordinate p (some a) (some k) = 0 := by
  rw [← projectivePrimeRatioCoordinate_represents p (some a) ha] at h
  have he := (projectiveFieldPoint_homogeneous_mem _
    (projectivePrimeRatioCoordinate_ne_zero p (some a) ha) _
      (segreRulingLinearPolynomial_homogeneous t i k)).mp h
  simpa only [segreRulingLinearPolynomial, map_sub, map_mul, aeval_X, aeval_C] using he

/-- The two original projective ruling equations put the normalized
four-coordinate vector in the exact original ruling kernel. -/
theorem segre_normalized_projective_ruling_kernel
    (Y : Fin 4 → E) (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (a : Fin 4) (ha : X (some a) ∉ p.asHomogeneousIdeal)
    (hR0 : segreRulingLinearPolynomial (Y j.castSucc / Y 0) j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial (Y j.castSucc / Y 0) 3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal) :
    segreRulingMatrix j (algebraMap E (projectivePrimeRatioField p (some a)) (Y j.castSucc / Y 0)) *ᵥ
      (fun i => projectivePrimeRatioCoordinate p (some a) (some i)) = 0 := by
  have h0 := segre_normalized_projective_ruling_linear_equation p a ha _ _ _ hR0
  have h1 := segre_normalized_projective_ruling_linear_equation p a ha _ _ _ hR1
  rw [segreRulingMatrix_mulVec]
  fin_cases j
  · exact False.elim (hj rfl)
  · funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · funext i
    fin_cases i
    · simpa using h0
    · simpa using h1

/-- A nonzero point of either original ruling has a nonzero original
first-three-coordinate vector; the fourth coordinate is forced by the ruling. -/
theorem segre_ruling_kernel_first_three_ne_zero
    {F : Type u} [Field F] (j : Fin 3) (hj : j ≠ 0) (t : F)
    (b : Fin 4 → F) (hb : b ≠ 0) (hkernel : segreRulingMatrix j t *ᵥ b = 0) :
    (fun i : Fin 3 => b i.castSucc) ≠ 0 := by
  intro hz
  have h0 : b 0 = 0 := congrFun hz 0
  have h1 : b 1 = 0 := congrFun hz 1
  have h2 : b 2 = 0 := congrFun hz 2
  have h3 : b 3 = 0 := by
    have he := congrFun hkernel 1
    rw [segreRulingMatrix_mulVec] at he
    fin_cases j
    · exact False.elim (hj rfl)
    · simpa [h2] using he
    · simpa [h1] using he
  apply hb
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end DimensionFourDependence
