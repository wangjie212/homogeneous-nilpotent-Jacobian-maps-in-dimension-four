import DimensionFourDependence.BoundaryLeadingEquations

/-! # Isotropy equations read from quadratic and cubic fiber boundaries

The leading parts of the actual fiber polynomial forms vanish in any
residue direction at infinity. The nonzero scalar factors `1/2` and
`-1/6` are removed using characteristic zero.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {E O F κ : Type*} [Field E] [CharZero E] [CommRing O] [Field F] [Field κ]
    [Algebra E O] [Algebra E F] [Algebra O F] [IsScalarTower E O F] [Algebra E κ] {n : ℕ}

/-- A residue direction at infinity of the quadratic fiber equation is
isotropic for its actual Hessian coefficient matrix. -/
theorem quadratic_fiber_residue_direction_isotropic
    (π : O →ₐ[E] κ) (hinj : Function.Injective (algebraMap O F))
    (x : Fin n → F) (s : F) (z : Option (Fin n) → O)
    (hz0 : algebraMap O F (z none) = s)
    (hz : ∀ i, algebraMap O F (z (some i)) = s * x i) (hres0 : π (z none) = 0)
    (a : Fin n → E) (T : Matrix (Fin n) (Fin n) E) (q : E)
    (hQ : aeval x (quadraticFiberPolynomial a T q) = 0) :
    matrixBilinearPairing (T.map (algebraMap E κ))
      (fun i => π (z (some i))) (fun i => π (z (some i))) = 0 := by
  have he := leading_equation_residue_specialization π hinj x s z hz0 hz hres0
    (quadraticFiberPolynomial a T q) 2 (quadraticFiberPolynomial_totalDegree a T q) hQ
  rw [quadraticFiberPolynomial_leading_component, map_mul, aeval_C] at he
  have hhalf : algebraMap E κ ((2 : E)⁻¹) ≠ 0 := by
    intro h
    have hz : (2 : E)⁻¹ = 0 := (algebraMap E κ).injective (by simpa only [map_zero] using h)
    exact inv_ne_zero (by norm_num) hz
  have hform := (mul_eq_zero.mp he).resolve_left hhalf
  simpa only [quadraticFormPolynomial, map_sum, map_mul, aeval_C, aeval_X,
    matrixBilinearPairing, Matrix.map_apply] using hform

/-- A residue direction at infinity of the cubic fiber equation kills
the actual third derivative self-contraction. -/
theorem cubic_fiber_residue_direction_isotropic
    (π : O →ₐ[E] κ) (hinj : Function.Injective (algebraMap O F))
    (x : Fin n → F) (s : F) (z : Option (Fin n) → O)
    (hz0 : algebraMap O F (z none) = s)
    (hz : ∀ i, algebraMap O F (z (some i)) = s * x i) (hres0 : π (z none) = 0)
    (a : Fin n → E) (S : Matrix (Fin n) (Fin n) E) (T : Fin n → Fin n → Fin n → E) (k : E)
    (hQ : aeval x (cubicFiberPolynomial a S T k) = 0) :
    tensorTrilinearPairing (fun i j l => algebraMap E κ (T i j l))
      (fun i => π (z (some i))) (fun i => π (z (some i))) (fun i => π (z (some i))) = 0 := by
  have he := leading_equation_residue_specialization π hinj x s z hz0 hz hres0
    (cubicFiberPolynomial a S T k) 3 (cubicFiberPolynomial_totalDegree a S T k) hQ
  rw [cubicFiberPolynomial_leading_component, map_neg, map_mul, aeval_C] at he
  have hsixth : algebraMap E κ ((6 : E)⁻¹) ≠ 0 := by
    intro h
    have hz : (6 : E)⁻¹ = 0 := (algebraMap E κ).injective (by simpa only [map_zero] using h)
    exact inv_ne_zero (by norm_num) hz
  have hform := (mul_eq_zero.mp (neg_eq_zero.mp he)).resolve_left hsixth
  simpa only [cubicFormPolynomial, map_sum, map_mul, aeval_C, aeval_X, tensorTrilinearPairing] using hform

end DimensionFourDependence
