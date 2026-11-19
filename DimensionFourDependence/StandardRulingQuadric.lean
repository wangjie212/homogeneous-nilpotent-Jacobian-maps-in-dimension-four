import DimensionFourDependence.QuadricTransversals

/-! # The smooth determinant quadric

An explicit homogeneous defining polynomial, its gradient, and the absence
of singular points away from the origin. These statements hold over every field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F : Type*} [Field F]

/-- The usual four-coordinate determinant polynomial. -/
noncomputable def standardRulingPolynomial : MvPolynomial (Fin 4) F :=
  X 0 * X 3 - X 1 * X 2

/-- The determinant equation is homogeneous of degree two. -/
theorem standardRulingPolynomial_homogeneous :
    (standardRulingPolynomial (F := F)).IsHomogeneous 2 := by
  exact ((isHomogeneous_X F 0).mul (isHomogeneous_X F 3)).sub
    ((isHomogeneous_X F 1).mul (isHomogeneous_X F 2))

/-- Its value agrees with the determinant in product coordinates. -/
theorem standardRulingPolynomial_eval_pair (x : (Fin 2 → F) × (Fin 2 → F)) :
    aeval ![x.1 0, x.1 1, x.2 0, x.2 1] (standardRulingPolynomial (F := F)) =
      standardRulingQuadric x := by
  simp [standardRulingPolynomial, standardRulingQuadric]

/-- The four partial derivatives of the determinant equation. -/
theorem standardRulingPolynomial_gradient (x : Fin 4 → F) :
    (fun i => aeval x (pderiv i (standardRulingPolynomial (F := F)))) =
      ![x 3, -x 2, -x 1, x 0] := by
  funext i
  fin_cases i <;>
    simp [standardRulingPolynomial, Derivation.leibniz, pderiv_X]

/-- The determinant polynomial has no singular vector except the origin. -/
theorem standardRulingPolynomial_gradient_zero_iff (x : Fin 4 → F) :
    (fun i => aeval x (pderiv i (standardRulingPolynomial (F := F)))) = 0 ↔ x = 0 := by
  rw [standardRulingPolynomial_gradient]
  constructor
  · intro h
    have h0 := congrFun h 3
    have h1 := congrFun h 2
    have h2 := congrFun h 1
    have h3 := congrFun h 0
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  · rintro rfl
    ext i
    fin_cases i <;> simp

/-- The quadric is projectively nonsingular, expressed by a nonzero gradient
at every nonzero vector (in particular at every projective zero). -/
theorem standardRulingPolynomial_projectively_nonsingular (x : Fin 4 → F) (hx : x ≠ 0) :
    (fun i => aeval x (pderiv i (standardRulingPolynomial (F := F)))) ≠ 0 := by
  exact mt (standardRulingPolynomial_gradient_zero_iff x).mp hx

/-- The displayed quadric is a nonzero polynomial. -/
theorem standardRulingPolynomial_ne_zero : standardRulingPolynomial (F := F) ≠ 0 := by
  intro h
  have he := congrArg (aeval (![1, 0, 0, 1] : Fin 4 → F)) h
  simp [standardRulingPolynomial] at he

end DimensionFourDependence
