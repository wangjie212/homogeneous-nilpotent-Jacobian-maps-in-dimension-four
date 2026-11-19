import DimensionFourDependence.RationalParameterAlgebraicDerivative
import DimensionFourDependence.ConeQuadraticCoefficient

/-! # A parameter-algebraic directrix decomposition supplies algebraic direction coefficients -/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [CharZero K] [Field F] [CharZero F] [Algebra K F]

/-- A nonzero transverse coefficient in the directrix derivative
decomposition forces every actual direction coordinate to be algebraic
over the parameter field. -/
theorem parameter_directrix_decomposition_direction_isAlgebraic
    (p : RatFunc K →ₐ[K] F) (T : Derivation K F F) (hT : T (p RatFunc.X) = 1)
    (V A : Fin 3 → F) (α β : F) (hβ : β ≠ 0)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i))
    (hα : IsAlgebraic p.fieldRange α) (hβalg : IsAlgebraic p.fieldRange β)
    (hdecomp : ∀ i, T (V i) = α * V i + β * A i) :
    ∀ i, IsAlgebraic p.fieldRange (A i) := by
  intro i
  have he : A i = (T (V i) - α * V i) / β := by
    apply (eq_div_iff hβ).mpr
    linear_combination -(hdecomp i)
  rw [he]
  apply mem_algebraicClosure_iff.mp
  exact (algebraicClosure p.fieldRange F).div_mem
    ((algebraicClosure p.fieldRange F).sub_mem
      (mem_algebraicClosure_iff.mpr
        (rational_parameter_derivative_preserves_algebraic_coefficients p T hT _ (hV i)))
      ((algebraicClosure p.fieldRange F).mul_mem (mem_algebraicClosure_iff.mpr hα)
        (mem_algebraicClosure_iff.mpr (hV i))))
    (mem_algebraicClosure_iff.mpr hβalg)

/-- The first normal derivative paired with a parameter-algebraic
direction is itself algebraic over the same actual parameter field. -/
theorem parameter_normal_derivative_direction_pairing_isAlgebraic
    (p : RatFunc K →ₐ[K] F) (T : Derivation K F F) (hT : T (p RatFunc.X) = 1)
    (ν A : Fin 3 → F) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (hA : ∀ i, IsAlgebraic p.fieldRange (A i)) :
    IsAlgebraic p.fieldRange ((fun i => T (ν i)) ⬝ᵥ A) := by
  apply mem_algebraicClosure_iff.mp
  apply (algebraicClosure p.fieldRange F).sum_mem
  intro i _hi
  exact (algebraicClosure p.fieldRange F).mul_mem
    (mem_algebraicClosure_iff.mpr
      (rational_parameter_derivative_preserves_algebraic_coefficients p T hT _ (hν i)))
    (mem_algebraicClosure_iff.mpr (hA i))

end DimensionFourDependence
