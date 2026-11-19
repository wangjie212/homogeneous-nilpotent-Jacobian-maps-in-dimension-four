import DimensionFourDependence.LinearConjugacyComposition

/-! # Evaluating the original linear frames after any coefficient extension -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

theorem linearPolynomialPullback_aeval_extension (T : Matrix (Fin m) (Fin n) K)
    (p : MvPolynomial (Fin m) K) (x : Fin n → F) :
    aeval x (linearPolynomialPullback T p) = aeval ((T.map (algebraMap K F)) *ᵥ x) p := by
  unfold linearPolynomialPullback
  rw [comp_aeval_apply]
  have he : (fun i => aeval x (linearPolynomialMap T i)) =
      (T.map (algebraMap K F)) *ᵥ x := by
    funext i
    simp [linearPolynomialMap, Matrix.mulVec, dotProduct]
  rw [he]

theorem linearPolynomialConjugate_aeval_extension
    (T S : Matrix (Fin n) (Fin n) K)
    (H : Fin n → MvPolynomial (Fin n) K) (x : Fin n → F) :
    (fun i => aeval x (linearPolynomialConjugate T S H i)) =
      (S.map (algebraMap K F)) *ᵥ (fun i => aeval ((T.map (algebraMap K F)) *ᵥ x) (H i)) := by
  funext i
  simp only [linearPolynomialConjugate, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    map_mul, aeval_C, linearPolynomialPullback_aeval_extension]

/-- A common zero of the original forms becomes a common zero after
the inverse constant frame, over the same field extension. -/
theorem linearPolynomialConjugate_aeval_extension_eq_zero
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (x : Fin n → F) (hx : ∀ i, aeval x (H i) = 0) :
    ∀ i, aeval ((S.map (algebraMap K F)) *ᵥ x) (linearPolynomialConjugate T S H i) = 0 := by
  let E : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) F :=
    (algebraMap K F).mapMatrix
  have he : E T * E S = 1 := by rw [← map_mul, hTS, map_one]
  have hm : E T *ᵥ (E S *ᵥ x) = x := by rw [mulVec_mulVec, he, one_mulVec]
  have hv := linearPolynomialConjugate_aeval_extension T S H (E S *ᵥ x)
  change (fun i => aeval (E S *ᵥ x) (linearPolynomialConjugate T S H i)) =
    E S *ᵥ (fun i => aeval (E T *ᵥ (E S *ᵥ x)) (H i)) at hv
  have hzero : (fun i => aeval x (H i)) = 0 := funext hx
  rw [hm, hzero, mulVec_zero] at hv
  exact fun i => congrFun hv i

end DimensionFourDependence
