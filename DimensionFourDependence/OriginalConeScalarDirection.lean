import DimensionFourDependence.TernaryRulingDirection
import DimensionFourDependence.ActualGaussNormalSpan
import DimensionFourDependence.ConeNormalGaussField
import DimensionFourDependence.PrimitiveMapDegree

/-! # The original fixed vertex constructs the scalar directrix presentation

The actual Gauss curve constructs independent successive normal
covectors. Dropping the zero vertex coordinate gives two independent
ternary covectors. Their actual output incidences construct a normalized
rational directrix and the common scalar factor in all three original
projected output coordinates. Component independence also proves the
directrix is not contained in an original constant projective line.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- A nonplanar dimension-one Gauss image with the specified fourth-axis
vertex constructs its own rational directrix, normalized output scalar
and complete original source values. Both tangent-normal incidences are
conclusions, and no scalar cone-coordinate presentation is assumed. -/
theorem original_fixed_vertex_cone_constructs_rational_scalar_direction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
        (rationalImageNormal H I.equation) (imageNormalPivot H I),
      ∃ (V : Fin 3 → RatFunc K) (j : Fin 3),
        V j = 1 ∧ H j.castSucc ≠ 0 ∧ LinearIndependent K V ∧
        (∀ i : Fin 3, algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc) =
          gaussParameterSourceHom H I e (V i) * algebraMap (MvPolynomial (Fin 4) K) S₀ (H j.castSucc)) ∧
        (fun i : Fin 3 => gaussParameterNormal H I e i.castSucc) ⬝ᵥ V = 0 ∧
        (fun i : Fin 3 => rationalParameterDerivative K (gaussParameterNormal H I e i.castSucc)) ⬝ᵥ V = 0 ∧
        (fun i : Fin 3 => gaussParameterNormal H I e i.castSucc) ⬝ᵥ
          (fun i => rationalParameterDerivative K (V i)) = 0 := by
  classical
  obtain ⟨e, _i, _j, _hminor, hjet⟩ :=
    actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss
  let ν := gaussParameterNormal H I e
  let f := gaussParameterSourceHom H I e
  let Q : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  have hν4 : ν (Fin.last 3) = 0 := by
    apply f.injective
    change gaussParameterSourceHom H I e (gaussParameterNormal H I e (Fin.last 3)) = f 0
    rw [gaussParameterSourceHom_normal, hvertex, zero_div, map_zero]
  have hD4 : rationalParameterDerivative K (ν (Fin.last 3)) = 0 := by rw [hν4, map_zero]
  have hpair4 : LinearIndependent (RatFunc K) ![ν, fun i => rationalParameterDerivative K (ν i)] := by
    have he := hjet.comp (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2)
    convert he using 1
    funext r i
    fin_cases r <;> rfl
  have hpair := independent_covector_pair_drop_zero_vertex ν
    (fun i => rationalParameterDerivative K (ν i)) hν4 hD4 hpair4
  have hnormal4 : (fun i => f (ν i)) ⬝ᵥ Q = 0 := by
    simpa only [f, ν, Q, gaussParameterSourceHom_normal] using I.normalized_normal_dot_output_eq_zero H hd hH
  have hderivative4 : (fun i => f (rationalParameterDerivative K (ν i))) ⬝ᵥ Q = 0 :=
    I.parameter_normal_derivative_dot_output_eq_zero H hd hH e
  have hnormal3 : (fun i : Fin 3 => f (ν i.castSucc)) ⬝ᵥ (fun i => Q i.castSucc) = 0 := by
    change ν (3 : Fin 4) = 0 at hν4
    simpa [dotProduct, Fin.sum_univ_castSucc, hν4] using hnormal4
  have hderivative3 : (fun i : Fin 3 => f (rationalParameterDerivative K (ν i.castSucc))) ⬝ᵥ
      (fun i => Q i.castSucc) = 0 := by
    change rationalParameterDerivative K (ν (3 : Fin 4)) = 0 at hD4
    simpa [dotProduct, Fin.sum_univ_castSucc, hD4] using hderivative4
  have hQ3 : (fun i : Fin 3 => Q i.castSucc) ≠ 0 := by
    intro hz
    have hh := (linearIndependent_of_componentsIndependent H hind).ne_zero ((0 : Fin 3).castSucc)
    apply hh
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
    have he := congrFun hz (0 : Fin 3)
    simpa only [Q, Pi.zero_apply, map_zero] using he
  obtain ⟨V, j, hVj, hQj, hvalues, hνV, hDνV⟩ :=
    independent_ternary_covectors_construct_normalized_source_direction f.toRingHom
      (fun i : Fin 3 => ν i.castSucc) (fun i => rationalParameterDerivative K (ν i.castSucc))
      hpair (fun i : Fin 3 => Q i.castSucc) hQ3 hnormal3 hderivative3
  have hHj : H j.castSucc ≠ 0 := by
    intro hz
    exact hQj (by simp [Q, hz])
  have hLI : LinearIndependent K V := by
    let φ : RatFunc K →ₗ[K] S₀ := Q j.castSucc • f.toLinearMap
    have hsource := (linearIndependent_of_componentsIndependent H hind).map'
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin 4) K) S₀).toLinearMap
      (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀))
    apply LinearIndependent.of_comp φ
    convert hsource.comp Fin.castSucc (Fin.castSucc_injective 3) using 1
    funext i
    change Q j.castSucc * f (V i) = Q i.castSucc
    rw [mul_comm]
    exact (hvalues i).symm
  have htangent : (fun i : Fin 3 => ν i.castSucc) ⬝ᵥ
      (fun i => rationalParameterDerivative K (V i)) = 0 := by
    have he := congrArg (rationalParameterDerivative K) hνV
    rw [derivation_dotProduct, map_zero, hDνV, zero_add] at he
    exact he
  exact ⟨e, V, j, hVj, hHj, hLI, hvalues, hνV, hDνV, htangent⟩

end DimensionFourDependence
