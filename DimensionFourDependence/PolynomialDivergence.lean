import DimensionFourDependence.HomogeneousEvaluationScaling
import DimensionFourDependence.Laplacian

/-! # Divergence and gradient-pairing identities for the radial trace calculation -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- Pair a polynomial gradient with a polynomial vector field. -/
noncomputable def polynomialGradientPairing (P : MvPolynomial (Fin n) K)
    (V : Fin n → MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K :=
  ∑ i, pderiv i P * V i

theorem polynomialGradientPairing_add (P : MvPolynomial (Fin n) K)
    (V W : Fin n → MvPolynomial (Fin n) K) :
    polynomialGradientPairing P (V + W) = polynomialGradientPairing P V + polynomialGradientPairing P W := by
  simp only [polynomialGradientPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem polynomialGradientPairing_scalar (P a : MvPolynomial (Fin n) K)
    (V : Fin n → MvPolynomial (Fin n) K) :
    polynomialGradientPairing P (fun i => a * V i) = a * polynomialGradientPairing P V := by
  rw [polynomialGradientPairing, polynomialGradientPairing, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem polynomialGradientPairing_radial (P : MvPolynomial (Fin n) K) {d : ℕ}
    (hP : P.IsHomogeneous d) : polynomialGradientPairing P (fun i => X i) = d • P := by
  simpa only [polynomialGradientPairing, mul_comm] using hP.sum_X_mul_pderiv

theorem polynomialDivergence_add (V W : Fin n → MvPolynomial (Fin n) K) :
    divergence (V + W) = divergence V + divergence W := by
  simp only [divergence, Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- The full product rule, with the gradient term kept explicit. -/
theorem polynomialDivergence_scalar (a : MvPolynomial (Fin n) K)
    (V : Fin n → MvPolynomial (Fin n) K) :
    divergence (fun i => a * V i) = a * divergence V + polynomialGradientPairing a V := by
  simp only [divergence, polynomialGradientPairing, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Multiplication by a source coordinate adds exactly that vector component. -/
theorem polynomialDivergence_coordinate (j : Fin n) (V : Fin n → MvPolynomial (Fin n) K) :
    divergence (fun i => X j * V i) = X j * divergence V + V j := by
  rw [polynomialDivergence_scalar]
  simp [polynomialGradientPairing, Pi.single_apply]

/-- The radial field in four variables has divergence `(e+4) f`. -/
theorem polynomialDivergence_radial_four (f : MvPolynomial (Fin 4) K) {e : ℕ}
    (hf : f.IsHomogeneous e) : divergence (fun i => f * X i) = (e + 4) • f := by
  simp only [divergence, Derivation.leibniz, smul_eq_mul, pderiv_X_self,
    mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hf.sum_X_mul_pderiv]
  simp only [add_nsmul]
  abel

/-- Factoring a power through divergence, after the normal pairing is
known to contain the extra factor. This includes exponent zero. -/
theorem polynomialDivergence_power_factor (R S : MvPolynomial (Fin n) K)
    (V : Fin n → MvPolynomial (Fin n) K)
    (hG : polynomialGradientPairing R V = R * S) (m : ℕ) :
    divergence (fun i => R ^ m * V i) = R ^ m * (divergence V + m • S) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : (fun i => R ^ (m + 1) * V i) = fun i => R * (R ^ m * V i) := by
      funext i
      rw [pow_succ]
      ring
    rw [he, polynomialDivergence_scalar, ih, polynomialGradientPairing_scalar, hG,
      pow_succ, add_nsmul, one_nsmul]
    ring

end DimensionFourDependence
