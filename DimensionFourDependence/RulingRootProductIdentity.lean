import DimensionFourDependence.ExtendedNativeLinearCombinations

/-! # The original ruling root formula gives the actual section identity (4.5) -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

/-- The paper's root equation, binary-form relation and rational
root compatibility give the product-power identity by ring arithmetic. -/
theorem ruling_root_combination_product_identity
    {F : Type*} [CommRing F] (r L m n S α β : F) (d : ℕ)
    (hroot : r ^ d = S) (hlinear : S = α * m + β * n) (hcompat : m * r = n * L) :
    (α * L + β * r) * n = r ^ (d + 1) := by
  calc
    _ = α * (n * L) + β * (r * n) := by ring
    _ = α * (m * r) + β * (r * n) := by rw [← hcompat]
    _ = r * (α * m + β * n) := by ring
    _ = r * S := by rw [← hlinear]
    _ = r ^ (d + 1) := by rw [← hroot, pow_succ']

/-- The original rational formula r = n L / m supplies the root
compatibility, so the product identity needs no additional equation. -/
theorem ruling_rational_root_combination_product_identity
    {F : Type*} [Field F] (r L m n S α β : F) (d : ℕ)
    (hroot : r ^ d = S) (hlinear : S = α * m + β * n)
    (hm : m ≠ 0) (hformula : r = n * L / m) :
    (α * L + β * r) * n = r ^ (d + 1) := by
  apply ruling_root_combination_product_identity r L m n S α β d hroot hlinear
  exact (mul_comm m r).trans ((eq_div_iff hm).mp hformula)

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
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance rulingRootProductIdentityIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance rulingRootProductIdentityAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual regular section U = alpha L_t + beta rho satisfies
equation (4.5) from the original rational root formula and the original
binary ruling-form relation. No product-power identity is assumed. -/
theorem actual_native_root_combination_product_power_of_rational_root_formula
    (ν cS cM cN : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E)
    (hlinear : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) =
      algebraMap E (N).functionField α * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) +
        algebraMap E (N).functionField β * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN))
    (hm : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) ≠ 0)
    (hformula : r = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) *
      (∑ i, algebraMap E (N).functionField (ν i) * w i) /
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM)) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) *
      aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1) := by
  rw [extendedClosedGaussRootCombinationSection_value]
  exact ruling_rational_root_combination_product_identity r _ _ _ _ _ _ d hroot hlinear hm hformula

end DimensionFourDependence
