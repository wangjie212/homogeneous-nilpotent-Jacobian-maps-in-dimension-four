import DimensionFourDependence.ConeNormalGaussField
import DimensionFourDependence.ClosedGaussHomogeneousParameter

/-! # The actual closed Gauss realization constructs the moving normal

The normalized original normal has coefficients in the actual closed
Gauss field. A compatible realization places them in its exact field
range. The specified zero vertex coordinate and Gauss dimension one
then construct a nonconstant ternary normal chart in that same range.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type*} [Field K] [CharZero K] [Field E] [Field G]
    [Algebra K E] [Algebra E G] [Algebra K G] [IsScalarTower K E G]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

omit [CharZero K] in
/-- Every compatible actual closed Gauss realization constructs its
own ternary normal over its exact constant-field range, with a nonzero
chart and positive-dimensional original projective image. -/
theorem compatible_closed_gauss_realization_constructs_ternary_moving_normal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (f : S₀ →ₐ[K] G) (g : closedGaussParameterField H I →ₐ[K] E)
    (hg : ∀ c : closedGaussParameterField H I, algebraMap E G (g c) = f (c : S₀)) :
    ∃ (ν : Fin 3 → g.fieldRange) (k : Fin 3), ν k ≠ 0 ∧
      Algebra.trdeg K (projectiveRatioField (K := K) ν k) ≠ 0 ∧
      (∀ i : Fin 3, (ν i : E) = g (e (closedGaussParameterNormal H I e i.castSucc))) ∧
      (∀ i : Fin 3, algebraMap E G (ν i : E) =
        f (rationalImageNormal H I.equation i.castSucc /
          rationalImageNormal H I.equation (imageNormalPivot H I))) := by
  classical
  let ν : Fin 3 → g.fieldRange := fun i =>
    ⟨g (e (closedGaussParameterNormal H I e i.castSucc)),
      ⟨e (closedGaussParameterNormal H I e i.castSucc), rfl⟩⟩
  have hν (i : Fin 3) : algebraMap E G (ν i : E) =
      f (rationalImageNormal H I.equation i.castSucc /
        rationalImageNormal H I.equation (imageNormalPivot H I)) := by
    change algebraMap E G (g (e (closedGaussParameterNormal H I e i.castSucc))) = _
    rw [hg]
    change f (closedGaussParameterSourceHom H I e
      (closedGaussParameterNormal H I e i.castSucc)) = _
    rw [closedGaussParameterSourceHom_normal]
  let ψ : g.fieldRange →ₐ[K] G := (IsScalarTower.toAlgHom K E G).comp g.fieldRange.val
  let c : G := (f (rationalImageNormal H I.equation (imageNormalPivot H I)))⁻¹
  have hc : c ≠ 0 := by
    apply inv_ne_zero
    intro hz
    apply imageNormalPivot_ne_zero H I
    apply f.injective
    exact hz.trans (map_zero f).symm
  have hrealize (i : Fin 3) : ψ (ν i) = c * f (rationalImageNormal H I.equation i.castSucc) := by
    change algebraMap E G (ν i : E) = _
    rw [hν, map_div₀]
    change _ = (f (rationalImageNormal H I.equation (imageNormalPivot H I)))⁻¹ * _
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨k, hk, hdim⟩ := original_vertex_gauss_compatible_normal_realization_positive
    H I hGauss hvertex g.fieldRange f ψ ν c hc hrealize
  exact ⟨ν, k, hk, hdim, fun _ => rfl, hν⟩

end DimensionFourDependence
