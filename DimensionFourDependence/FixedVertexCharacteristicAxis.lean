import DimensionFourDependence.ExtendedChosenGaussCharacteristic

/-! # The specified fixed vertex is the actual characteristic axis

A zero fourth normal coordinate has zero successive parameter derivatives.
The fourth axis therefore lies in the actual characteristic kernel. That
kernel is a line, so every nonzero characteristic vector has zero first
three coordinates and a nonzero fourth coordinate after coefficient extension.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]

omit [CharZero K] in
/-- The specified fourth-axis vertex makes the actual normalized
normal's fourth coordinate vanish in every original Gauss parameter. -/
theorem gaussParameterNormal_fixed_vertex_coordinate_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e₀ : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    gaussParameterNormal H I e₀ (Fin.last 3) = 0 := by
  apply (gaussParameterSourceHom H I e₀).injective
  change gaussParameterSourceHom H I e₀ (gaussParameterNormal H I e₀ (Fin.last 3)) =
    gaussParameterSourceHom H I e₀ 0
  rw [gaussParameterSourceHom_normal, hvertex, zero_div, map_zero]

variable (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- Both actual chosen ruling equations have zero fourth coefficient
when the original normal has the specified fourth-axis vertex. -/
theorem extended_chosen_ruling_fixed_vertex_last_column
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) (r : Fin 2) :
    extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss r (Fin.last 3) = 0 := by
  have hn := gaussParameterNormal_fixed_vertex_coordinate_zero H I
    (actualGaussRulingParameterChoice H I hH hd hind hGauss) hvertex
  change gaussParameterNormal H I
    (actualGaussRulingParameterChoice H I hH hd hind hGauss) (3 : Fin 4) = 0 at hn
  fin_cases r <;> simp [extendedClosedGaussChosenRulingMatrix, extendedClosedGaussRulingMatrix,
    actualGaussRulingMatrix, normalRulingMatrix, hn]

/-- The actual extended characteristic line is exactly the specified
fourth axis, derived from the original normal's zero fourth entry. -/
theorem extended_chosen_characteristic_fixed_vertex_axis_span
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    Submodule.span E {(Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E)} =
      extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss := by
  let a : Fin 4 → E := Fin.snoc (0 : Fin 3 → E) 1
  have ha : a ≠ 0 := by
    intro hz
    have he := congrFun hz (Fin.last 3)
    exact one_ne_zero (by simpa only [a, Fin.snoc_last, Pi.zero_apply] using he)
  have hn := gaussParameterNormal_fixed_vertex_coordinate_zero H I
    (actualGaussRulingParameterChoice H I hH hd hind hGauss) hvertex
  change gaussParameterNormal H I
    (actualGaussRulingParameterChoice H I hH hd hind hGauss) (3 : Fin 4) = 0 at hn
  have hcol (r : Fin 3) :
      extendedClosedGaussChosenCharacteristicMatrix H I E hH hd hind hGauss r (Fin.last 3) = 0 := by
    fin_cases r <;>
      simp [extendedClosedGaussChosenCharacteristicMatrix, normalCharacteristicMatrix, hn]
  have hmem : a ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss := by
    change extendedClosedGaussChosenCharacteristicMatrix H I E hH hd hind hGauss *ᵥ a = 0
    funext r
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, a, Fin.snoc_castSucc,
      Pi.zero_apply, Fin.snoc_last, mul_zero, Finset.sum_const_zero, zero_add, mul_one, hcol]
  exact extendedClosedGaussChosenCharacteristic_span_of_nonzero H I E hH hd hind hGauss a ha hmem

/-- A nonzero actual characteristic vector has zero first three
coordinates and a nonzero fourth coordinate; its full vector is the
fourth-axis vector with that scalar coefficient. -/
theorem extended_chosen_characteristic_fixed_vertex_coordinates
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (b : Fin 4 → E) (hb : b ≠ 0)
    (hmem : b ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss) :
    (∀ i : Fin 3, b i.castSucc = 0) ∧ b (Fin.last 3) ≠ 0 ∧
      b = Fin.snoc (0 : Fin 3 → E) (b (Fin.last 3)) := by
  have hspan := extended_chosen_characteristic_fixed_vertex_axis_span H I E hH hd hind hGauss hvertex
  have hm : b ∈ Submodule.span E {(Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E)} := by
    rw [hspan]
    exact hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hfirst (i : Fin 3) : b i.castSucc = 0 := by
    simpa only [Pi.smul_apply, Fin.snoc_castSucc, Pi.zero_apply, smul_zero] using
      (congrFun hc i.castSucc).symm
  have heq : b = Fin.snoc (0 : Fin 3 → E) (b (Fin.last 3)) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc, hfirst]
      rfl
  refine ⟨hfirst, ?_, heq⟩
  intro hz
  apply hb
  have hc0 : c = 0 := by
    simpa only [Pi.smul_apply, Fin.snoc_last, smul_eq_mul, mul_one, hz] using congrFun hc (Fin.last 3)
  rw [← hc, hc0, zero_smul]

end DimensionFourDependence
