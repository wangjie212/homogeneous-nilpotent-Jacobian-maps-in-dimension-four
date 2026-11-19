import DimensionFourDependence.FirstOrderTaylor

/-! # Evaluating homogeneous forms at a scaled polynomial point -/

namespace DimensionFourDependence

open MvPolynomial

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {n : ℕ}

/-- Homogeneous evaluation scales by the actual degree over any coefficient algebra. -/
theorem homogeneous_aeval_scale (P : MvPolynomial (Fin n) K) {d : ℕ}
    (hP : P.IsHomogeneous d) (x : Fin n → A) (r : A) :
    aeval (fun i => r * x i) P = r ^ d * aeval x P := by
  let e : Polynomial (MvPolynomial (Fin n) K) →ₐ[K] A :=
    ((Polynomial.aeval r).restrictScalars K).comp (Polynomial.mapAlgHom (aeval x))
  have hC (Q : MvPolynomial (Fin n) K) : e (Polynomial.C Q) = aeval x Q := by
    change Polynomial.aeval r (Polynomial.map (aeval x).toRingHom (Polynomial.C Q)) = _
    rw [Polynomial.map_C, Polynomial.aeval_C]
    rfl
  have hX : e Polynomial.X = r := by
    change Polynomial.aeval r (Polynomial.map (aeval x).toRingHom Polynomial.X) = r
    rw [Polynomial.map_X, Polynomial.aeval_X]
  have he : e.comp gradeHom = aeval (fun i => r * x i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X]
    change e (gradeHom (X i)) = r * x i
    have hg : gradeHom (X i : MvPolynomial (Fin n) K) = Polynomial.C (X i) * Polynomial.X := by
      simp only [gradeHom, aeval_X]
    rw [hg, map_mul, hC, hX, aeval_X]
    exact mul_comm _ _
  rw [← DFunLike.congr_fun he P, AlgHom.comp_apply, gradeHom_of_isHomogeneous hP]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  rw [map_mul, map_pow, hC, hX]
  exact mul_comm _ _

/-- Scaling the formal coordinates gives the usual homogeneous identity. -/
theorem homogeneous_aeval_scaled_coordinates (P : MvPolynomial (Fin n) K) {d : ℕ}
    (hP : P.IsHomogeneous d) (r : MvPolynomial (Fin n) K) :
    aeval (fun i : Fin n => r * X i) P = r ^ d * P := by
  simpa only [aeval_X_left_apply] using homogeneous_aeval_scale P hP X r

/-- The first differential scales with degree one less. -/
theorem homogeneous_directional_differential_scaled_coordinates
    (P : MvPolynomial (Fin n) K) {d : ℕ} (hP : P.IsHomogeneous d)
    (r : MvPolynomial (Fin n) K) (w : Fin n → MvPolynomial (Fin n) K) :
    evaluatedDirectionalDifferential (fun i : Fin n => r * X i) w P =
      r ^ (d - 1) * ∑ i, pderiv i P * w i := by
  unfold evaluatedDirectionalDifferential
  simp_rw [homogeneous_aeval_scaled_coordinates _ hP.pderiv]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end DimensionFourDependence
