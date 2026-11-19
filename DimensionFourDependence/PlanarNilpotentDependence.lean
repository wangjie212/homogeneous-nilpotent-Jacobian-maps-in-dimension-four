import DimensionFourDependence.DerivationInvariantPlanarLine
import DimensionFourDependence.PlanarBinarySlopeAlgebraicity
import DimensionFourDependence.PlanarNilpotentSlopeIdentity
import DimensionFourDependence.CommutativePolynomialChainRule
import DimensionFourDependence.OriginalFieldTernaryDependence

/-! # The normalized planar nilpotent dependence input of Proposition 6.3 -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "F₂" => FractionRing R₂

theorem normalized_polynomial_eq_zero_of_partials_zero {n : ℕ}
    (p : MvPolynomial (Fin n) K) (h0 : aeval (fun _ : Fin n => (0 : K)) p = 0)
    (hp : ∀ i, pderiv i p = 0) : p = 0 := by
  have h := polynomial_all_partials_zero_eq_constant p hp
  have hc : p.coeff 0 = 0 := by
    rw [h, aeval_C, Algebra.algebraMap_self_apply] at h0
    exact h0
  rw [h, hc, map_zero]

section ClosedField

variable [IsAlgClosed K]

theorem closed_field_normalized_planar_trace_det_componentsDependent (u v : R₂)
    (hu0 : aeval (fun _ : Fin 2 => (0 : K)) u = 0)
    (hv0 : aeval (fun _ : Fin 2 => (0 : K)) v = 0)
    (htr : pderiv 0 u + pderiv 1 v = 0)
    (hdet : pderiv 0 u * pderiv 1 v - pderiv 1 u * pderiv 0 v = 0) :
    ComponentsDependent (![u,v] : Fin 2 → R₂) := by
  by_cases hu : pderiv 1 u = 0
  · have hx : pderiv 0 u = 0 := by
      have hy : pderiv 1 v = -pderiv 0 u := eq_neg_of_add_eq_zero_right htr
      rw [hu, zero_mul, sub_zero, hy, mul_neg, neg_eq_zero] at hdet
      exact (mul_eq_zero.mp hdet).elim id id
    have huz := normalized_polynomial_eq_zero_of_partials_zero u hu0 (by
      intro i
      fin_cases i
      · exact hx
      · exact hu)
    refine ⟨![1,0], ?_, ?_⟩
    · intro hz
      have he := congrFun hz (0 : Fin 2)
      exact one_ne_zero he
    · simp [Fin.sum_univ_two, huz]
  have hdeg : 0 < u.totalDegree := by
    by_contra! hd
    have he : u.totalDegree = 0 := by omega
    exact hu (by rw [totalDegree_eq_zero_iff_eq_C.mp he, pderiv_C])
  obtain ⟨s, hs, hui, hpart⟩ := planar_trace_determinant_construct_invariant_slope u v hu htr hdet
  let x := rationalCoordinate (K := K) (0 : Fin 2)
  let y := rationalCoordinate (K := K) (1 : Fin 2)
  have ha : aeval (![x,y] : Fin 2 → F₂) = IsScalarTower.toAlgHom K R₂ F₂ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [x, y, rationalCoordinate]
  have htop := invariant_planar_line_direction_annihilates_top_component
    (planarSlopeDerivation s) x y s (planarSlopeDerivation_first_coordinate s)
    (planarSlopeDerivation_second_coordinate s) hs u hdeg (by rw [ha]; exact hui)
  have halg := slope_isAlgebraic_of_homogeneous_binary_form_zero _
    (top_homogeneousComponent_ne_zero u (by intro hz; exact hu (by rw [hz, map_zero])))
    (homogeneousComponent_isHomogeneous _ _) s htop
  have hc : s ∈ algebraicClosure K F₂ := mem_algebraicClosure_iff.mpr halg
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure K F₂),
    IntermediateField.mem_bot] at hc
  obtain ⟨c, hc⟩ := hc
  have hdiff (i : Fin 2) : pderiv i (v - C c * u) = 0 := by
    have he := hpart i
    rw [rationalPartial_polynomial, rationalPartial_polynomial, ← hc] at he
    have hc' : algebraMap K F₂ c = algebraMap R₂ F₂ (C c) :=
      IsScalarTower.algebraMap_apply K R₂ F₂ c
    rw [hc', ← map_mul] at he
    have hpoly := (IsFractionRing.injective R₂ F₂) he
    rw [map_sub, pderiv_mul, hpoly, pderiv_C, zero_mul, zero_add, sub_self]
  have he : v - C c * u = 0 := normalized_polynomial_eq_zero_of_partials_zero _ (by
    simp only [map_sub, map_mul, hv0, hu0, mul_zero, sub_zero]) hdiff
  refine ⟨![-c,1], ?_, ?_⟩
  · intro hz
    have hz' := congrFun hz (1 : Fin 2)
    exact one_ne_zero hz'
  · rw [Fin.sum_univ_two]
    change (-c) • u + (1 : K) • v = 0
    rw [one_smul, MvPolynomial.smul_eq_C_mul, map_neg, neg_mul, add_comm, ← sub_eq_add_neg]
    exact he

theorem closed_field_normalized_planar_nilpotent_componentsDependent
    (H : Fin 2 → R₂) (h0 : ∀ i, aeval (fun _ : Fin 2 => (0 : K)) (H i) = 0)
    (hN : IsNilpotent (jac H)) : ComponentsDependent H := by
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have hdet : (jac H).det = 0 := by
    obtain ⟨j, hj⟩ := hN
    have he := congrArg Matrix.det hj
    rw [Matrix.det_pow, Matrix.det_zero] at he
    exact isNilpotent_iff_eq_zero.mp ⟨j, he⟩
  have h := closed_field_normalized_planar_trace_det_componentsDependent
    (H 0) (H 1) (h0 0) (h0 1)
    (by simpa [Matrix.trace, jac, Fin.sum_univ_two] using htr)
    (by simpa [Matrix.det_fin_two, jac] using hdet)
  have he : (![H 0,H 1] : Fin 2 → R₂) = H := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at h

end ClosedField

/-- The planar input of Section 6.3 over every original
characteristic-zero field, with no homogeneity hypothesis. -/
theorem normalized_planar_nilpotent_componentsDependent
    (H : Fin 2 → R₂) (h0 : ∀ i, aeval (fun _ : Fin 2 => (0 : K)) (H i) = 0)
    (hN : IsNilpotent (jac H)) : ComponentsDependent H := by
  let F := AlgebraicClosure K
  let G := fun i => MvPolynomial.map (algebraMap K F) (H i)
  apply componentsDependent_of_map F H
  apply closed_field_normalized_planar_nilpotent_componentsDependent G _
    (general_nilpotent_jacobian_map_coefficients H hN)
  intro i
  change aeval (fun _ : Fin 2 => (0 : F)) (MvPolynomial.map (algebraMap K F) (H i)) = 0
  have he : eval₂ (algebraMap K F) (fun _ : Fin 2 => (0 : F)) (H i) = 0 := by
    rw [← map_zero (algebraMap K F)]
    simpa [aeval_def, map_eval₂Hom, map_zero] using congrArg (algebraMap K F) (h0 i)
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHom.id_comp] using he

end DimensionFourDependence
