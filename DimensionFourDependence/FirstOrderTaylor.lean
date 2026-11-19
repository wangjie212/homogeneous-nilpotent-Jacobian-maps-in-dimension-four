import DimensionFourDependence.GeometricPlanarFiber

/-! # First-order polynomial Taylor expansion with an explicit square remainder -/

namespace DimensionFourDependence

open MvPolynomial

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {n : ℕ}

/-- The first directional differential evaluated at a polynomial point. -/
noncomputable def evaluatedDirectionalDifferential (x w : Fin n → A)
    (P : MvPolynomial (Fin n) K) : A := ∑ i, aeval x (pderiv i P) * w i

theorem evaluatedDirectionalDifferential_add (x w : Fin n → A)
    (P Q : MvPolynomial (Fin n) K) :
    evaluatedDirectionalDifferential x w (P + Q) =
      evaluatedDirectionalDifferential x w P + evaluatedDirectionalDifferential x w Q := by
  simp only [evaluatedDirectionalDifferential, map_add, add_mul, Finset.sum_add_distrib]

theorem evaluatedDirectionalDifferential_mul_X (x w : Fin n → A)
    (P : MvPolynomial (Fin n) K) (j : Fin n) :
    evaluatedDirectionalDifferential x w (P * X j) =
      x j * evaluatedDirectionalDifferential x w P + aeval x P * w j := by
  simp only [evaluatedDirectionalDifferential, Derivation.leibniz, smul_eq_mul,
    map_add, map_mul, aeval_X, pderiv_X, add_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp [Pi.single_apply]

/-- Taylor expansion modulo the square of an arbitrary displacement
factor, with an actual polynomial-ring element as remainder. -/
theorem first_order_taylor_square_remainder (x w : Fin n → A) (r : A)
    (P : MvPolynomial (Fin n) K) :
    ∃ q : A, aeval (fun i => x i + r * w i) P =
      aeval x P + r * evaluatedDirectionalDifferential x w P + r ^ 2 * q := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [evaluatedDirectionalDifferential]⟩
  | add P Q hP hQ =>
    obtain ⟨p, hp⟩ := hP
    obtain ⟨q, hq⟩ := hQ
    refine ⟨p + q, ?_⟩
    rw [map_add, map_add, evaluatedDirectionalDifferential_add, hp, hq]
    ring
  | mul_X P j hP =>
    obtain ⟨q, hq⟩ := hP
    refine ⟨q * (x j + r * w j) + evaluatedDirectionalDifferential x w P * w j, ?_⟩
    rw [map_mul, map_mul, aeval_X, aeval_X, evaluatedDirectionalDifferential_mul_X, hq]
    ring

end DimensionFourDependence
