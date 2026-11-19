import DimensionFourDependence.AffineFullConeIndependentRootData
import DimensionFourDependence.ActualGaussRootFullCone

/-! # Both original finite root alternatives yield independent fixed-vertex root forms -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hN : IsNilpotent (jac H)) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "hd₀" => (lt_trans Nat.zero_lt_one hd)
local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH (hd₀) hind hGauss 0)

local instance actualGaussIndependentConeRootDataIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualGaussIndependentConeRootDataAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hrank hN hvertex

/-- The actual finite normal-form alternatives construct independent
root forms on the original chosen ruling, over their same finite
coefficient field. The retained original nonzero root proves both the
canonical numerator and input plane nonzero before the new forms are
constructed. No cone presentation or independence is supplied. -/
theorem actual_chosen_root_normal_forms_construct_independent_fixed_vertex_root_data
    (hdata : ActualChosenGaussRootNormalForms H I E hH e (hd₀) hind hGauss) :
    ActualChosenIndependentGaussRootData H I E hH e (hd₀) hind hGauss := by
  obtain ⟨rA, hrA, hcone⟩ := actual_chosen_gauss_root_normal_forms_construct_full_affine_cone
    H hrank hN I E hd hH hind hGauss hvertex e hdata
  obtain ⟨_cS, cM, cN, r, _hS, _hM, _hNc, hr, _hpower, _hm, hformula, _halt, hnumerator⟩ := hdata
  have hLvalue : aeval (w) (L₀) = ∑ i, algebraMap E (N₀).functionField
      (extendedClosedGaussChosenRulingMatrix H I E hH (hd₀) hind hGauss 0 i) * (w) i := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  have hformula' : r = aeval (w) ((O) cN) * aeval (w) (L₀) / aeval (w) ((O) cM) := by
    rw [hLvalue]
    exact hformula
  have hn : aeval (w) ((O) cN) ≠ 0 := by
    intro hz
    exact hr (by rw [hformula', hz, zero_mul, zero_div])
  have hL : aeval (w) (L₀) ≠ 0 := by
    intro hz
    exact hr (by rw [hformula', hz, mul_zero, zero_div])
  exact actual_affine_full_cone_constructs_independent_native_root_data
    H I E hH e (hd₀) hind hGauss hvertex cN hnumerator hn hL rA hrA hcone

end DimensionFourDependence
