import DimensionFourDependence.ActualChosenGraphDualPair
import DimensionFourDependence.FixedVertexCharacteristicAxis

/-! # The constructed independent root forms give the original fixed-axis graph basis -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap (closedGaussParameterField H I) E (e ((A) i))
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'
local notation "Wg" => extendedClosedGaussGraphRuling H I p hY h hh e E

/-- The denominator's nonzero vertex value and the power form's
zero vertex value fix the longitudinal dual vector to the original
fourth axis. The second dual vector and both exact graph restrictions
are constructed on the same actual ruling and coefficient field. -/
theorem independent_fixed_vertex_root_forms_construct_original_axis_graph_dual_pair
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (M S : Fin 4 → E) (hM : M (Fin.last 3) ≠ 0) (hS : S (Fin.last 3) = 0)
    (hpair : LinearIndependent E ![rulingFormRestriction (W₀) M, rulingFormRestriction (W₀) S]) :
    let b : Fin 4 → E := (M (Fin.last 3))⁻¹ • (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E)
    ∃ a : Fin 4 → E, b ∈ (W₀) ∧ a ∈ (W₀) ∧
      (fun i => b (p i.castSucc)) ∈ (Wg) ∧ (fun i => a (p i.castSucc)) ∈ (Wg) ∧
      graphRestrictedCovector p (Aₑ) M ⬝ᵥ (fun i => b (p i.castSucc)) = 1 ∧
      graphRestrictedCovector p (Aₑ) S ⬝ᵥ (fun i => b (p i.castSucc)) = 0 ∧
      graphRestrictedCovector p (Aₑ) M ⬝ᵥ (fun i => a (p i.castSucc)) = 0 ∧
      graphRestrictedCovector p (Aₑ) S ⬝ᵥ (fun i => a (p i.castSucc)) = 1 ∧
      LinearIndependent E ![rulingFormRestriction (Wg) (graphRestrictedCovector p (Aₑ) M),
        rulingFormRestriction (Wg) (graphRestrictedCovector p (Aₑ) S)] := by
  classical
  let axis : Fin 4 → E := Fin.snoc (0 : Fin 3 → E) 1
  let b : Fin 4 → E := (M (Fin.last 3))⁻¹ • axis
  have haxis : axis ∈ (W₀) := by
    change extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss *ᵥ axis = 0
    funext q
    change (∑ i : Fin 4, extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss q i * axis i) = 0
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss q i.castSucc * axis i.castSucc) +
      extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss q (Fin.last 3) * axis (Fin.last 3) = 0
    simp only [axis, Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
    exact extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex q
  have hb : b ∈ (W₀) := (W₀).smul_mem _ haxis
  have haxis_pair (v : Fin 4 → E) : v ⬝ᵥ axis = v (Fin.last 3) := by
    change (∑ i : Fin 4, v i * axis i) = v (Fin.last 3)
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, v i.castSucc * axis i.castSucc) + v (Fin.last 3) * axis (Fin.last 3) = _
    simp only [axis, Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
  have hMb : M ⬝ᵥ b = 1 := by
    rw [show b = (M (Fin.last 3))⁻¹ • axis from rfl, dotProduct_smul, haxis_pair]
    exact inv_mul_cancel₀ hM
  have hSb : S ⬝ᵥ b = 0 := by
    rw [show b = (M (Fin.last 3))⁻¹ • axis from rfl, dotProduct_smul, haxis_pair, hS, smul_zero]
  obtain ⟨_b, a, _hLI, _hb, ha, _hMb, _hSb, hMa, hSa, _hspan⟩ :=
    two_dimensional_ruling_coordinate_basis (W₀)
      (extendedClosedGaussChosenRulingMatrix_kernel_finrank H I E hH hd hind hGauss) M S hpair
  obtain ⟨hblinear, hbgraph⟩ := actual_chosen_ruling_vector_constructs_original_graph_equations
    H I p hY h hh e E hH hd hind hGauss b hb
  obtain ⟨halinear, hagraph⟩ := actual_chosen_ruling_vector_constructs_original_graph_equations
    H I p hY h hh e E hH hd hind hGauss a ha
  have hMb' := (graphRestrictedCovector_pairing p (Aₑ) M b hblinear).trans hMb
  have hSb' := (graphRestrictedCovector_pairing p (Aₑ) S b hblinear).trans hSb
  have hMa' := (graphRestrictedCovector_pairing p (Aₑ) M a halinear).trans hMa
  have hSa' := (graphRestrictedCovector_pairing p (Aₑ) S a halinear).trans hSa
  exact ⟨a, hb, ha, hbgraph, hagraph, hMb', hSb', hMa', hSa',
    ruling_form_pair_independent_of_specified_dual_values (Wg) _ _ _ _
      hbgraph hagraph hMb' hSb' hMa' hSa'⟩

end DimensionFourDependence
