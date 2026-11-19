import DimensionFourDependence.OriginalConeScalarDirection
import DimensionFourDependence.ClosedGaussHomogeneousParameter

/-! # The constructed scalar directrix on any actual closed Gauss cover

The original Gauss field includes in its actual closed cover. Substitution
through that inclusion transports the constructed directrix and its source
values. The rational chain rule transports both tangent-normal incidences.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual relatively closed Gauss cover constructs a normalized
rational directrix, its nonzero original output scalar, and both normal
incidences. This holds for every chosen rational parameter of that cover. -/
theorem closed_fixed_vertex_cone_constructs_rational_scalar_direction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ∃ (V : Fin 3 → RatFunc K) (j : Fin 3),
      V j = 1 ∧ H j.castSucc ≠ 0 ∧ LinearIndependent K V ∧
      (∀ i : Fin 3, algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
        closedGaussParameterSourceHom H I e (V i) *
          algebraMap (MvPolynomial (Fin 4) K) S₀ (H j.castSucc)) ∧
      (fun i : Fin 3 => closedGaussParameterNormal H I e i.castSucc) ⬝ᵥ V = 0 ∧
      (fun i : Fin 3 => rationalParameterDerivative K
        (closedGaussParameterNormal H I e i.castSucc)) ⬝ᵥ V = 0 ∧
      (fun i : Fin 3 => closedGaussParameterNormal H I e i.castSucc) ⬝ᵥ
        (fun i => rationalParameterDerivative K (V i)) = 0 := by
  classical
  obtain ⟨e₀, V₀, j, hj, hHj, hLI, hvalues, hnormal, hderivative, _htangent⟩ :=
    original_fixed_vertex_cone_constructs_rational_scalar_direction H hd hH hind I hGauss hvertex
  let ι := IntermediateField.inclusion (actual_gauss_field_le_closed_parameter_field H I)
  let φ : RatFunc K →ₐ[K] RatFunc K := e.symm.toAlgHom.comp (ι.comp e₀.toAlgHom)
  let V : Fin 3 → RatFunc K := fun i => φ (V₀ i)
  have hsource (r : RatFunc K) :
      closedGaussParameterSourceHom H I e (φ r) = gaussParameterSourceHom H I e₀ r := by
    change (e (e.symm (ι (e₀ r))) : S₀) = (e₀ r : S₀)
    rw [e.apply_symm_apply]
    rfl
  have hν (i : Fin 4) : φ (gaussParameterNormal H I e₀ i) = closedGaussParameterNormal H I e i := by
    apply (closedGaussParameterSourceHom H I e).injective
    change closedGaussParameterSourceHom H I e (φ (gaussParameterNormal H I e₀ i)) =
      closedGaussParameterSourceHom H I e (closedGaussParameterNormal H I e i)
    rw [hsource, gaussParameterSourceHom_normal, closedGaussParameterSourceHom_normal]
  have hnormal' : (fun i : Fin 3 => closedGaussParameterNormal H I e i.castSucc) ⬝ᵥ V = 0 := by
    simpa only [dotProduct, map_sum, map_mul, map_zero, hν, V] using congrArg φ hnormal
  have hderivative' : (fun i : Fin 3 => rationalParameterDerivative K
      (closedGaussParameterNormal H I e i.castSucc)) ⬝ᵥ V = 0 := by
    have he : (fun i : Fin 3 => φ (rationalParameterDerivative K
        (gaussParameterNormal H I e₀ i.castSucc))) ⬝ᵥ V = 0 := by
      simpa only [dotProduct, map_sum, map_mul, map_zero, V] using congrArg φ hderivative
    have hchain (i : Fin 3) : rationalParameterDerivative K
        (closedGaussParameterNormal H I e i.castSucc) =
        φ (rationalParameterDerivative K (gaussParameterNormal H I e₀ i.castSucc)) *
          rationalParameterDerivative K (φ RatFunc.X) := by
      rw [← hν]
      exact rational_parameter_chain_rule φ (rationalParameterDerivative K) _
    simp only [hchain, dotProduct]
    simp only [dotProduct] at he
    calc
      (∑ i : Fin 3, (φ (rationalParameterDerivative K
          (gaussParameterNormal H I e₀ i.castSucc)) *
          rationalParameterDerivative K (φ RatFunc.X)) * V i) =
          (∑ i : Fin 3, φ (rationalParameterDerivative K
            (gaussParameterNormal H I e₀ i.castSucc)) * V i) *
              rationalParameterDerivative K (φ RatFunc.X) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = 0 := by rw [he, zero_mul]
  refine ⟨V, j, ?_, hHj, ?_, ?_, hnormal', hderivative', ?_⟩
  · change φ (V₀ j) = 1
    rw [hj, map_one]
  · exact hLI.map' φ.toLinearMap (LinearMap.ker_eq_bot.mpr φ.injective)
  · intro i
    rw [hvalues i, ← hsource]
  · have he := congrArg (rationalParameterDerivative K) hnormal'
    rw [derivation_dotProduct, hderivative', zero_add, map_zero] at he
    exact he

end DimensionFourDependence
