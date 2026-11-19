import DimensionFourDependence.ActualRootCharacteristicComparison
import DimensionFourDependence.FixedVertexCharacteristicAxis

/-! # The actual root numerator annihilates the specified vertex

The root numerator is the original second-normal derivative after its
proved graph-pivot normalization. Its kernel on the ruling is the actual
characteristic line. In the fixed-vertex case this line is the specified
fourth axis, so the original numerator has zero fourth coefficient.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

include hH hd hind hGauss

/-- The actual second-normal numerator, with its original source
provenance, vanishes on the fixed vertex without a supplied incidence
or numerator-coordinate hypothesis. -/
theorem actual_gauss_root_numerator_fixed_vertex_coordinate_zero
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (cN : Fin 4 → E) (hN : HasActualGaussRootNumerator H I E e cN) :
    cN (Fin.last 3) = 0 := by
  let a : Fin 4 → E := Fin.snoc (0 : Fin 3 → E) 1
  have hruling : a ∈ LinearMap.ker
      (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin' := by
    change extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss *ᵥ a = 0
    funext r
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, a, Fin.snoc_castSucc,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Fin.snoc_last, mul_one, zero_add]
    exact extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex r
  have hchar : a ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss := by
    rw [← extended_chosen_characteristic_fixed_vertex_axis_span H I E hH hd hind hGauss hvertex]
    exact Submodule.subset_span rfl
  have hn := (actual_gauss_root_numerator_zero_iff_characteristic
    H I E e hH hd hind hGauss cN hN a hruling).mpr hchar
  simpa only [dotProduct, Fin.sum_univ_castSucc, a, Fin.snoc_castSucc,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, Fin.snoc_last, mul_one, zero_add] using hn

end DimensionFourDependence
