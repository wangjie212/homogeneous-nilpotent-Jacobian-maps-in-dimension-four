import DimensionFourDependence.LinearPolynomialConjugacy

/-! # Primitivity of the actual polynomial kernel under inverse linear coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {n : ℕ}

/-- Invertible simultaneous source-target linear coordinates preserve
the original primitive polynomial-vector property. -/
theorem linearPolynomialConjugate_preserves_primitive_vector
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (u : Fin n → MvPolynomial (Fin n) K) (hprim : IsPrimitiveVec u) :
    IsPrimitiveVec (linearPolynomialConjugate T S u) := by
  let φ := matrixPolynomialCoordinateEquiv T S hTS hST
  have hTSC : T.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) * S.map MvPolynomial.C = 1 := by
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  have hrestore (i : Fin n) : φ (u i) =
      ∑ j, MvPolynomial.C (T i j) * linearPolynomialConjugate T S u j := by
    change (fun j => φ (u j)) i =
      (T.map MvPolynomial.C *ᵥ (S.map MvPolynomial.C *ᵥ fun j => φ (u j))) i
    rw [Matrix.mulVec_mulVec, hTSC, Matrix.one_mulVec]
  intro a ha
  have hsource (i : Fin n) : a ∣ φ (u i) := by
    rw [hrestore]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_right (ha j) _)
  have hprimitive : IsUnit (φ.symm a) := by
    apply hprim
    intro i
    have he := map_dvd φ.symm.toMonoidHom (hsource i)
    change φ.symm a ∣ φ.symm (φ (u i)) at he
    simpa only [AlgEquiv.symm_apply_apply] using he
  have he := hprimitive.map φ.toRingHom
  change IsUnit (φ (φ.symm a)) at he
  simpa only [AlgEquiv.apply_symm_apply] using he

end DimensionFourDependence
