import DimensionFourDependence.ExtendedProductPowerMultiplicity

/-! # Actual source-form germs, their coefficient-linear relations and local ideal orders -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedSourceFormLocalIdealsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedSourceFormLocalIdealsNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance extendedSourceFormLocalIdealsNonempty (a : Fin 4) : Nonempty (V a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)
local instance extendedSourceFormLocalIdealsTopNonempty : Nonempty (⊤ : (N).Opens) :=
  ⟨⟨genericPoint N, trivial⟩⟩
noncomputable local instance extendedSourceFormLocalIdealsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual local original-frame coefficient of an original
source form, formed from its genuine regular chart-polynomial section. -/
noncomputable def extendedClosedGaussPolynomialCoefficientGerm
    (P : MvPolynomial (Fin 4) E) (z : N) (a : Fin 4) (ha : z ∈ V a) : (N).presheaf.stalk z :=
  (N).presheaf.germ (V a) z ha (extendedClosedGaussChartPolynomialCoefficient H I E hH e P a)

/-- The actual regular source-form germ retains the original
homogeneous numerator divided by the original powered frame. -/
theorem extendedClosedGaussPolynomialCoefficientGerm_value
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (z : N) (a : Fin 4) (ha : z ∈ V a) :
    algebraMap ((N).presheaf.stalk z) (N).functionField
        (extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha) = aeval w P / w a ^ n := by
  have hp := extendedClosedGaussChartPolynomialCoefficient_homogeneous_value H I E hH e P hP a ⟨z, ha⟩
  have hquot := (eq_div_iff
    (pow_ne_zero n (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a))).mpr
      ((mul_comm _ _).trans hp)
  exact (Scheme.algebraMap_germ_eq_germToFunctionField N ha _).trans
    ((schemeRationalSectionFunction_eq_generic N (V a) _ ⟨z, ha⟩).symm.trans hquot)

/-- Actual source-form germs vanish identically exactly when their
original rational numerators vanish. -/
theorem extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha = 0 ↔ aeval w P = 0 := by
  have heq : extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha = 0 ↔
      algebraMap ((N).presheaf.stalk z) (N).functionField
        (extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha) = 0 := by
    constructor
    · intro hzero
      rw [hzero, map_zero]
    · intro hzero
      exact (IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField)
        (hzero.trans (map_zero _).symm)
  rw [heq, extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e P hP z a ha]
  simp only [div_eq_zero_iff,
    pow_ne_zero n (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a), or_false]

/-- The actual regular source coefficient has maximal-ideal order
at least m exactly when it is zero or its actual integer order is at
least m. The statement includes identically zero components. -/
theorem extendedClosedGaussPolynomialCoefficientGerm_mem_maximalIdeal_pow_iff
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ V a) (m : ℕ) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ^ m ↔
      aeval w P = 0 ∨ (m : ℤ) ≤ (N).ord (aeval w P / w a ^ n) z := by
  let : IsDiscreteValuationRing ((N).presheaf.stalk z) :=
    extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  rw [← scheme_regular_order_bound_iff z hz _ m,
    extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff H I E hH e P hP z a ha,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e P hP z a ha]

/-- The original extended coefficient acts in the actual local ring
through the germ of its original global regular constant. -/
theorem extendedClosedGaussGlobalConstantHom_germ_value (c : E) (z : N) :
    algebraMap ((N).presheaf.stalk z) (N).functionField
        ((N).presheaf.germ ⊤ z (by trivial) (extendedClosedGaussGlobalConstantHom H I E hH e c)) =
      algebraMap E (N).functionField c :=
  (Scheme.algebraMap_germ_eq_germToFunctionField N (show z ∈ (⊤ : (N).Opens) from trivial) _).trans
    (extendedClosedGaussGlobalConstantHom_generic_value H I E hH e c)

/-- A coefficient-linear relation among homogeneous rational
source-form values is the same actual regular relation among their
original-frame local coefficients. -/
theorem extendedClosedGaussPolynomialCoefficientGerm_linear_combination
    (P S T : MvPolynomial (Fin 4) E) {n : ℕ}
    (hP : P.IsHomogeneous n) (hS : S.IsHomogeneous n) (hT : T.IsHomogeneous n)
    (α β : E)
    (hlinear : aeval w P = algebraMap E (N).functionField α * aeval w S +
      algebraMap E (N).functionField β * aeval w T)
    (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha =
      (N).presheaf.germ ⊤ z (by trivial) (extendedClosedGaussGlobalConstantHom H I E hH e α) *
          extendedClosedGaussPolynomialCoefficientGerm H I E hH e S z a ha +
        (N).presheaf.germ ⊤ z (by trivial) (extendedClosedGaussGlobalConstantHom H I E hH e β) *
          extendedClosedGaussPolynomialCoefficientGerm H I E hH e T z a ha := by
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  simp only [map_add, map_mul]
  rw [extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e P hP z a ha,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e S hS z a ha,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e T hT z a ha,
    extendedClosedGaussGlobalConstantHom_germ_value, extendedClosedGaussGlobalConstantHom_germ_value,
    hlinear]
  ring

/-- Every actual local ideal containing two homogeneous output
forms contains every original source form in their coefficient span,
including identically zero source components. -/
theorem extendedClosedGaussPolynomialCoefficientGerm_mem_ideal_of_linear_combination
    (P S T : MvPolynomial (Fin 4) E) {n : ℕ}
    (hP : P.IsHomogeneous n) (hS : S.IsHomogeneous n) (hT : T.IsHomogeneous n)
    (α β : E)
    (hlinear : aeval w P = algebraMap E (N).functionField α * aeval w S +
      algebraMap E (N).functionField β * aeval w T)
    (z : N) (a : Fin 4) (ha : z ∈ V a) (J : Ideal ((N).presheaf.stalk z))
    (hSJ : extendedClosedGaussPolynomialCoefficientGerm H I E hH e S z a ha ∈ J)
    (hTJ : extendedClosedGaussPolynomialCoefficientGerm H I E hH e T z a ha ∈ J) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha ∈ J := by
  rw [extendedClosedGaussPolynomialCoefficientGerm_linear_combination H I E hH e
    P S T hP hS hT α β hlinear z a ha]
  exact J.add_mem (J.mul_mem_left _ hSJ) (J.mul_mem_left _ hTJ)

end DimensionFourDependence
