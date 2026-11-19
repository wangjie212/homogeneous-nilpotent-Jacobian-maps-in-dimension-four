import DimensionFourDependence.FirstOrderTaylor

/-! # Polynomial restriction to a parameterized affine line and its derivative -/

namespace DimensionFourDependence

open MvPolynomial

variable {K E G : Type*} [Field K] [Field E] [Field G]
  [Algebra K E] [Algebra E G] [Algebra K G] [IsScalarTower K E G] {n : ℕ}

/-- Restrict an original polynomial to a line over an extension field. -/
noncomputable def affineLinePolynomialRestriction (a v : Fin n → E)
    (P : MvPolynomial (Fin n) K) : Polynomial E :=
  aeval (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) P

/-- Restriction commutes with evaluation of the line parameter in any field extension. -/
theorem affineLinePolynomialRestriction_aeval (a v : Fin n → E) (t : G)
    (P : MvPolynomial (Fin n) K) :
    Polynomial.aeval t (affineLinePolynomialRestriction a v P) =
      aeval (fun i => algebraMap E G (a i) + algebraMap E G (v i) * t) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [affineLinePolynomialRestriction, IsScalarTower.algebraMap_apply K E (Polynomial E),
      ← IsScalarTower.algebraMap_apply K E G]
  | add P Q hP hQ =>
    simpa only [affineLinePolynomialRestriction, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simpa only [affineLinePolynomialRestriction, map_mul, aeval_X, map_add,
      Polynomial.aeval_C, Polynomial.aeval_X] using
      congrArg (· * (algebraMap E G (a i) + algebraMap E G (v i) * t)) hP

/-- The ordinary derivative of a line restriction is the evaluated directional differential. -/
theorem affineLinePolynomialRestriction_eval (a v : Fin n → E) (t : E)
    (P : MvPolynomial (Fin n) K) :
    (affineLinePolynomialRestriction a v P).eval t = aeval (fun i => a i + v i * t) P := by
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
    RingHom.id_apply] using affineLinePolynomialRestriction_aeval a v t P

/-- The ordinary derivative of a line restriction is the evaluated directional differential. -/
theorem affineLinePolynomialRestriction_derivative (a v : Fin n → E)
    (P : MvPolynomial (Fin n) K) :
    (affineLinePolynomialRestriction a v P).derivative =
      ∑ i, affineLinePolynomialRestriction a v (pderiv i P) * Polynomial.C (v i) := by
  classical
  change (affineLinePolynomialRestriction a v P).derivative =
    evaluatedDirectionalDifferential
      (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)
      (fun i => Polynomial.C (v i)) P
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [affineLinePolynomialRestriction, evaluatedDirectionalDifferential,
      IsScalarTower.algebraMap_apply K E (Polynomial E)]
  | add P Q hP hQ =>
    simpa only [affineLinePolynomialRestriction, map_add, Polynomial.derivative_add,
      evaluatedDirectionalDifferential_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    rw [show affineLinePolynomialRestriction a v (P * X i) =
      affineLinePolynomialRestriction a v P *
        (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) by
          simp only [affineLinePolynomialRestriction, map_mul, aeval_X],
      Polynomial.derivative_mul, hP, evaluatedDirectionalDifferential_mul_X]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_mul, Polynomial.derivative_X, zero_add, zero_mul, mul_one]
    change _ = _ + affineLinePolynomialRestriction a v P * Polynomial.C (v i)
    ring

end DimensionFourDependence
