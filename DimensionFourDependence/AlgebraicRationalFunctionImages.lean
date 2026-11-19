import DimensionFourDependence.AlgebraicConstantsCompatibleImages
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Algebraic coefficient and parameter images control an entire rational field -/

namespace DimensionFourDependence

variable {D E G : Type*} [Field D] [Field E] [Field G] [Algebra D G]

/-- If the original coefficient images and the free parameter image
are algebraic, then so is the image of every rational function. -/
theorem rational_function_images_algebraic_of_coefficients_and_parameter
    (φ : RatFunc E →+* G) (hC : ∀ c : E, IsAlgebraic D (φ (RatFunc.C c)))
    (hX : IsAlgebraic D (φ RatFunc.X)) (r : RatFunc E) : IsAlgebraic D (φ r) := by
  have hpoly (P : Polynomial E) : IsAlgebraic D (φ (algebraMap (Polynomial E) (RatFunc E) P)) := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => simpa only [map_add] using hP.add hQ
    | monomial n c =>
      rw [RatFunc.algebraMap_monomial, map_mul, map_pow]
      exact (hC c).mul (hX.pow n)
  rw [← RatFunc.num_div_denom r, map_div₀]
  simpa only [div_eq_mul_inv] using (hpoly r.num).mul (hpoly r.denom).inv

/-- For two nested free parameters, the exact original coefficient
images and those two parameter images suffice. No scalar specialization
of either parameter is used. -/
theorem two_parameter_rational_function_images_algebraic
    (φ : RatFunc (RatFunc E) →+* G)
    (hC : ∀ c : E, IsAlgebraic D (φ (RatFunc.C (RatFunc.C c))))
    (hlevel : IsAlgebraic D (φ (RatFunc.C RatFunc.X)))
    (hr : IsAlgebraic D (φ RatFunc.X)) (r : RatFunc (RatFunc E)) : IsAlgebraic D (φ r) := by
  apply rational_function_images_algebraic_of_coefficients_and_parameter φ _ hr r
  intro c
  exact rational_function_images_algebraic_of_coefficients_and_parameter (φ.comp RatFunc.C) hC hlevel c

end DimensionFourDependence
