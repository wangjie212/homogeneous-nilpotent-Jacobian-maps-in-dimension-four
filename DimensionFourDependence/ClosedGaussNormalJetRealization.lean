import DimensionFourDependence.RationalJetMinorTransfer
import DimensionFourDependence.ClosedConeScalarDirection

/-! # Every actual closed Gauss parameter constructs independent realized ternary normal jets -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- A common zero vertex coordinate can be dropped from all three
independent actual normal jets without losing independence. -/
theorem independent_normal_jet_drop_zero_vertex
    (T : Derivation K F F) (ν : Fin 4 → F) (hvertex : ν (Fin.last 3) = 0)
    (hjet : LinearIndependent F (normalCharacteristicMatrix T ν).row) :
    LinearIndependent F ![(fun i : Fin 3 => ν i.castSucc),
      (fun i : Fin 3 => T (ν i.castSucc)), (fun i : Fin 3 => T (T (ν i.castSucc)))] := by
  let N := normalCharacteristicMatrix T ν
  change ν (3 : Fin 4) = 0 at hvertex
  have hlast (r : Fin 3) : N r (Fin.last 3) = 0 := by
    fin_cases r <;> simp [N, normalCharacteristicMatrix, hvertex]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc r
  apply Fintype.linearIndependent_iff.mp hjet c ?_ r
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · change (∑ r : Fin 3, c r * N r (Fin.last 3)) = 0
    simp only [hlast, mul_zero, Finset.sum_const_zero]
  · have he := congrFun hc j
    simpa [N, normalCharacteristicMatrix, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul] using he

/-- Every rational parameter of the actual closed Gauss field
constructs its own nonzero normalized jet minor and independent normal
jets, preserving the original normal and its specified pivot. -/
theorem closed_gauss_parameter_constructs_independent_normal_jet_minor
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ∃ i j : Fin 4,
      ((rationalParameterJetMatrix (closedGaussParameterNormal H I e)).submatrix id
        ![imageNormalPivot H I, i, j]).det ≠ 0 ∧
      LinearIndependent (RatFunc K) (rationalParameterJetMatrix (closedGaussParameterNormal H I e)).row := by
  obtain ⟨e₀, i, j, hminor, _hjet⟩ :=
    actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss
  let ι := IntermediateField.inclusion (actual_gauss_field_le_closed_parameter_field H I)
  let φ : RatFunc K →ₐ[K] RatFunc K := e.symm.toAlgHom.comp (ι.comp e₀.toAlgHom)
  let v := gaussParameterNormal H I e₀
  have hsource (r : RatFunc K) :
      closedGaussParameterSourceHom H I e (φ r) = gaussParameterSourceHom H I e₀ r := by
    change (e (e.symm (ι (e₀ r))) : FractionRing (MvPolynomial (Fin 4) K)) = (e₀ r : FractionRing (MvPolynomial (Fin 4) K))
    rw [e.apply_symm_apply]
    rfl
  have hν (k : Fin 4) : φ (v k) = closedGaussParameterNormal H I e k := by
    apply (closedGaussParameterSourceHom H I e).injective
    change closedGaussParameterSourceHom H I e (φ (v k)) =
      closedGaussParameterSourceHom H I e (closedGaussParameterNormal H I e k)
    rw [hsource]
    exact (gaussParameterSourceHom_normal H I e₀ k).trans (closedGaussParameterSourceHom_normal H I e k).symm
  have hpivot : v (imageNormalPivot H I) = 1 := by
    apply (gaussParameterSourceHom H I e₀).injective
    change gaussParameterSourceHom H I e₀ (gaussParameterNormal H I e₀ (imageNormalPivot H I)) =
      gaussParameterSourceHom H I e₀ 1
    rw [gaussParameterSourceHom_normal, div_self (imageNormalPivot_ne_zero H I), map_one]
  have hspeed := rational_cover_parameter_derivative_ne_zero (AlgEquiv.refl : RatFunc K ≃ₐ[K] RatFunc K) φ
  change rationalParameterDerivative K (φ RatFunc.X) ≠ 0 at hspeed
  have hnew : ((normalCharacteristicMatrix (rationalParameterDerivative K)
      (fun k => φ (v k))).submatrix id ![imageNormalPivot H I, i, j]).det ≠ 0 := by
    rw [rational_normal_jet_minor_transfer φ (rationalParameterDerivative K) v _ i j hpivot]
    exact mul_ne_zero ((map_ne_zero φ).mpr hminor) (pow_ne_zero 3 hspeed)
  have hclosed : ((rationalParameterJetMatrix (closedGaussParameterNormal H I e)).submatrix id
      ![imageNormalPivot H I, i, j]).det ≠ 0 := by
    change ((rationalParameterJetMatrix (fun k => φ (v k))).submatrix id
      ![imageNormalPivot H I, i, j]).det ≠ 0 at hnew
    simpa only [hν] using hnew
  exact ⟨i, j, hclosed, three_rows_independent_of_column_minor _ _ hclosed⟩

/-- The original map's nonplanar dimension-one Gauss image and
specified fixed vertex construct independent ternary normal jets in
every actual normalized-parameter realization. Neither jet independence,
an original jet minor nor a parameter-speed assumption is supplied. -/
theorem realized_closed_gauss_fixed_vertex_normal_jets_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p : RatFunc K →ₐ[K] F) (T : Derivation K F F) (hT : T (p RatFunc.X) = 1) :
    let ν : Fin 3 → F := fun i => p (closedGaussParameterNormal H I e i.castSucc)
    LinearIndependent F ![ν, (fun i => T (ν i)), (fun i => T (T (ν i)))] := by
  obtain ⟨i, j, hminor, _hjet⟩ :=
    closed_gauss_parameter_constructs_independent_normal_jet_minor H hd hH hind I hGauss e
  have hpivot : closedGaussParameterNormal H I e (imageNormalPivot H I) = 1 := by
    apply (closedGaussParameterSourceHom H I e).injective
    change closedGaussParameterSourceHom H I e (closedGaussParameterNormal H I e (imageNormalPivot H I)) =
      closedGaussParameterSourceHom H I e 1
    rw [closedGaussParameterSourceHom_normal, div_self (imageNormalPivot_ne_zero H I), map_one]
  have hzero : closedGaussParameterNormal H I e (Fin.last 3) = 0 := by
    apply (closedGaussParameterSourceHom H I e).injective
    change closedGaussParameterSourceHom H I e (closedGaussParameterNormal H I e (Fin.last 3)) =
      closedGaussParameterSourceHom H I e 0
    rw [closedGaussParameterSourceHom_normal, hvertex, zero_div, map_zero]
  have hLI := rational_normal_jet_independent_after_parameter_realization p T
    (closedGaussParameterNormal H I e) _ i j hpivot hminor (by rw [hT]; exact one_ne_zero)
  exact independent_normal_jet_drop_zero_vertex T (fun k => p (closedGaussParameterNormal H I e k))
    (by rw [hzero, map_zero]) hLI

end DimensionFourDependence
