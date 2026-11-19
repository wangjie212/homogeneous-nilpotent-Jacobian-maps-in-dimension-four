import DimensionFourDependence.CoefficientChainRule
import DimensionFourDependence.RationalParameterCoefficientAlgebraicity
import DimensionFourDependence.RulingDirectionAcceleration

/-! # Parameter derivatives preserve algebraic parameter coefficients

The actual relative algebraic closure of K(t) carries its constructed
coordinate derivative. The coefficient chain rule identifies every
ambient derivative with value one on t with that derivative on the
closure. A direction fixing t therefore kills these parameter derivatives.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

set_option maxHeartbeats 3000000

/-- An actual parameter derivative preserves the algebraic closure
of the actual rational-parameter image inside the source field. -/
theorem rational_parameter_derivative_preserves_algebraic_coefficients
    (p : RatFunc K →ₐ[K] F) (T : Derivation K F F) (ht : T (p RatFunc.X) = 1)
    (a : F) (ha : IsAlgebraic p.fieldRange a) : IsAlgebraic p.fieldRange (T a) := by
  let Y : Fin 1 → F := fun _ => p RatFunc.X
  have hY : AlgebraicIndependent K Y :=
    (algebraicIndependent_singleton_iff (R := K) (x := Y) 0).mpr (by
      intro hx
      exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff p p.injective).mp hx))
  have hJ : IntermediateField.adjoin K (Set.range Y) = p.fieldRange := by
    have hrange : Set.range Y = {p RatFunc.X} := by ext x; simp [Y]
    rw [hrange, rational_parameter_hom_fieldRange]
  have ha' : IsAlgebraic (IntermediateField.adjoin K (Set.range Y)) a := by rw [hJ]; exact ha
  let c : coefficientField (K := K) Y := ⟨a, mem_algebraicClosure_iff.mpr ha'⟩
  have he := coefficient_chain_rule Y hY T c
  have he' : T a = (coefficientPartial (K := K) Y hY 0 c : F) := by
    simpa only [Y, Fin.sum_univ_one, ht, one_mul] using he
  rw [← hJ, he']
  exact mem_algebraicClosure_iff.mp (coefficientPartial (K := K) Y hY 0 c).property

/-- Every actual fixed-parameter direction also annihilates the
parameter derivative of every algebraic parameter coefficient. -/
theorem fixed_parameter_direction_kills_parameter_coefficient_derivative
    (p : RatFunc K →ₐ[K] F) (T D : Derivation K F F)
    (hT : T (p RatFunc.X) = 1) (hD : D (p RatFunc.X) = 0)
    (a : F) (ha : IsAlgebraic p.fieldRange a) : D (T a) = 0 := by
  exact parameter_algebraic_coefficient_direction_constant p D hD (T a)
    (rational_parameter_derivative_preserves_algebraic_coefficients p T hT a ha)

end DimensionFourDependence
