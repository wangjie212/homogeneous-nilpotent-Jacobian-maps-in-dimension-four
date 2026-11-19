import DimensionFourDependence.TernaryConicFrames
import DimensionFourDependence.QuadricAxisEvaluation
import DimensionFourDependence.TernaryGraphRankOneHessian

/-! # The conic with a repeated direction gives a dependent pair of outputs -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2400000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "Out₂" => (ternaryRationalOutputPair (K := K))
local notation "Coeff" => (coefficientField (K := K))

/-- A singular leading Hessian yields a constant frame in which a
linear combination of the last two outputs is algebraic over the first. -/
theorem TernaryConicWitness.singular_hessian_constructs_algebraic_pair_frame
    {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) (hdet : W.hessian.det = 0) :
    ∃ (T S : Matrix (Fin 3) (Fin 3) K) (μ : K), T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      AlgebraicIndependent K (Out₂ G) ∧ IsAlgebraic (IntermediateField.adjoin K {ι (G 0)})
        (ι (G 2 - C μ * G 1)) := by
  let L := Coeff (Out₂ H)
  have hd : W.hessian 0 0 * W.hessian 1 1 - (W.hessian 0 1) ^ 2 = 0 := by
    simpa only [Matrix.det_fin_two, W.hessian_symmetric 1 0, pow_two] using hdet
  obtain ⟨e, he, hroot⟩ := binaryQuadratic_degenerate_constructs_direction
    (W.hessian 0 0) (W.hessian 0 1) (W.hessian 1 1) hd
  have hzero : aeval e (quadraticFormPolynomial W.hessian) = 0 := by
    rw [quadraticFormPolynomial_aeval_fin_two_binary_value _ (W.hessian_symmetric 1 0)]
    simpa only [Algebra.algebraMap_self_apply] using hroot
  obtain ⟨l, hl, hlz⟩ := W.hessian_direction_has_constant_covector (A := L) e hzero
  have hj : ∃ j : Fin 2, e j ≠ 0 := by
    by_contra h
    push Not at h
    exact he (funext h)
  obtain ⟨j, hj⟩ := hj
  let r : Fin 3 → K := Pi.single j.castSucc 1
  have hr : aeval (W.liftDirection e) (linearFormPolynomial r) ≠ 0 := by
    have hv : W.liftDirection e j.castSucc = e j := by fin_cases j <;> rfl
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
    rw [Finset.sum_eq_single j.castSucc]
    · simpa only [r, Pi.single_eq_same, map_one, one_mul, hv] using hj
    · intro i _ hi
      simp [r, hi]
    · simp
  obtain ⟨T, S, hTS, hST, hS₀, hS₁, hA⟩ :=
    W.separating_covectors_construct_transverse_frame e l r hl hlz hr
  obtain ⟨V⟩ := W.rechart T S hTS hST hA
  obtain ⟨α, c, hc, h⟩ := W.hessian_linear_association T S hTS hST V hA
  let f := (W.restrictedFrame S).map (algebraMap L L) *ᵥ e
  have hf₀ : f 0 = 0 := by
    change ((W.restrictedFrame S).map (algebraMap L L) *ᵥ e) (0 : Fin 2) = 0
    rw [W.restrictedFrame_mulVec_coordinate]
    change aeval (W.liftDirection e) (linearFormPolynomial (S 0)) = 0
    rw [hS₀]
    exact hlz
  have hf₁ : f 1 ≠ 0 := by
    change ((W.restrictedFrame S).map (algebraMap L L) *ᵥ e) (1 : Fin 2) ≠ 0
    rw [W.restrictedFrame_mulVec_coordinate]
    change aeval (W.liftDirection e) (linearFormPolynomial (S 1)) ≠ 0
    rw [hS₁]
    exact hr
  have hz := quadraticFormPolynomial_associated_linear_direction_zero
    _ _ _ c h e hzero
  have hq := quadraticFormPolynomial_nonzero_axis_root_diagonal_zero
    (V.hessian.map α.symm) 1 f hf₁ (by
      intro i hi
      fin_cases i
      · exact hf₀
      · exact (hi rfl).elim) hz
  have hV₁₁ : V.hessian 1 1 = 0 := α.symm.injective (hq.trans (map_zero α.symm).symm)
  have hVdet := (W.hessian_det_zero_iff_of_linear_association V _ hA α c hc h).mpr hdet
  have hV₀₁ : V.hessian 0 1 = 0 := by
    rw [Matrix.det_fin_two, hV₁₁, mul_zero, V.hessian_symmetric 1 0,
      zero_sub, neg_eq_zero] at hVdet
    exact (mul_eq_zero.mp hVdet).elim id id
  let G := linearPolynomialConjugate T S H
  have hcol (i : Fin 2) : ternaryGraphHessian (Out₂ G) V.independent V.lastOutput i 1 = 0 := by
    let M := Coeff (Out₂ G)
    have ht : V.hessian i 1 = 0 := by
      fin_cases i
      · exact hV₀₁
      · exact hV₁₁
    change algebraMap M F (V.hessian i 1) = 0
    rw [ht, map_zero]
  obtain ⟨μ, hμ⟩ := ternary_graph_zero_second_hessian_column_constructs_algebraic_output_pair
    (Out₂ G) V.independent V.lastOutput hcol
  refine ⟨T, S, μ, hTS, hST, V.independent, ?_⟩
  change IsAlgebraic (IntermediateField.adjoin K {ι (G 0)})
    ((V.lastOutput : F) - algebraMap K F μ * ι (G 1)) at hμ
  rw [V.lastOutput_value] at hμ
  change IsAlgebraic (IntermediateField.adjoin K {ι (G 0)}) (ι (G 2 - C μ * G 1))
  simp only [map_sub, map_mul, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₃ F]
  exact hμ

end DimensionFourDependence
