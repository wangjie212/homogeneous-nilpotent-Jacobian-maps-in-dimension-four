import DimensionFourDependence.TernaryConicFrames
import DimensionFourDependence.QuadricAxisEvaluation
import DimensionFourDependence.TernaryGraphMixedHessian

/-! # Two distinct conic directions produce the mixed-product output -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2450000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "Out₂" => (ternaryRationalOutputPair (K := K))
local notation "Coeff" => (coefficientField (K := K))

/-- Two independent directions at infinity give an original frame
whose last output is a nonzero mixed product of the two independent
outputs, up to addition of an original affine linear combination. -/
theorem TernaryConicWitness.nonsingular_hessian_constructs_bilinear_output_frame
    {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) (hdet : W.hessian.det ≠ 0) :
    ∃ (T S : Matrix (Fin 3) (Fin 3) K) (γ a b c : K),
      T * S = 1 ∧ S * T = 1 ∧ γ ≠ 0 ∧
      let G := linearPolynomialConjugate T S H
      AlgebraicIndependent K (Out₂ G) ∧
        G 2 = C γ * G 0 * G 1 + C a * G 0 + C b * G 1 + C c := by
  let L := Coeff (Out₂ H)
  let E := AlgebraicClosure L
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap L E).injective
  let : Algebra K E := inferInstanceAs (Algebra K (AlgebraicClosure L))
  let : IsScalarTower K L E := inferInstanceAs (IsScalarTower K L (AlgebraicClosure L))
  let f := algebraMap L E
  have hd : f (W.hessian 0 0) * f (W.hessian 1 1) - (f (W.hessian 0 1)) ^ 2 ≠ 0 := by
    have he : f W.hessian.det ≠ 0 := (map_ne_zero f).mpr hdet
    simpa only [Matrix.det_fin_two, W.hessian_symmetric 1 0, map_sub, map_mul, pow_two] using he
  obtain ⟨u, v, huv, hu, hv⟩ := binaryQuadratic_nondegenerate_constructs_two_directions
    (f (W.hessian 0 0)) (f (W.hessian 0 1)) (f (W.hessian 1 1)) hd
  have hu₀ : aeval u (quadraticFormPolynomial W.hessian) = 0 :=
    (quadraticFormPolynomial_aeval_fin_two_binary_value W.hessian (W.hessian_symmetric 1 0) u).trans hu
  have hv₀ : aeval v (quadraticFormPolynomial W.hessian) = 0 :=
    (quadraticFormPolynomial_aeval_fin_two_binary_value W.hessian (W.hessian_symmetric 1 0) v).trans hv
  obtain ⟨l, hl, hlu⟩ := W.hessian_direction_has_constant_covector (A := E) u hu₀
  obtain ⟨r, hr, hrv⟩ := W.hessian_direction_has_constant_covector (A := E) v hv₀
  have hvu : v 0 * u 1 - v 1 * u 0 ≠ 0 := by
    have he : v 0 * u 1 - v 1 * u 0 = -(u 0 * v 1 - u 1 * v 0) := by ring
    rw [he]
    exact neg_ne_zero.mpr huv
  have hsep (k : Fin 3 → K) (hk : k ≠ 0) (e e' : Fin 2 → E)
      (hdet₀ : e 0 * e' 1 - e 1 * e' 0 ≠ 0)
      (hz : aeval (W.liftDirection e) (linearFormPolynomial k) = 0) :
      aeval (W.liftDirection e') (linearFormPolynomial k) ≠ 0 := by
    have ha := ternaryGraphRestrictedCovector_direction_value (W.gradient 0) (W.gradient 1) k e
    have hb := ternaryGraphRestrictedCovector_direction_value (W.gradient 0) (W.gradient 1) k e'
    have he := nonzero_binary_covector_cannot_kill_independent_directions
      (W.restrictedCovector k) (W.restrictedCovector_ne_zero k hk) e e' hdet₀ (ha.symm.trans hz)
    exact fun h => he (hb.symm.trans h)
  have hlv := hsep l hl u v huv hlu
  have hru := hsep r hr v u hvu hrv
  obtain ⟨T, S, hTS, hST, hS₀, hS₁, hA⟩ :=
    W.separating_covectors_construct_transverse_frame u l r hl hlu hru
  obtain ⟨V⟩ := W.rechart T S hTS hST hA
  obtain ⟨α, c, _, h⟩ := W.hessian_linear_association T S hTS hST V hA
  let B := W.restrictedFrame S
  let u' := B.map f *ᵥ u
  let v' := B.map f *ᵥ v
  have hu'₀ : u' 0 = 0 := by
    change ((W.restrictedFrame S).map (algebraMap L E) *ᵥ u) (0 : Fin 2) = 0
    rw [W.restrictedFrame_mulVec_coordinate]
    change aeval (W.liftDirection u) (linearFormPolynomial (S 0)) = 0
    rw [hS₀]
    exact hlu
  have hu'₁ : u' 1 ≠ 0 := by
    change ((W.restrictedFrame S).map (algebraMap L E) *ᵥ u) (1 : Fin 2) ≠ 0
    rw [W.restrictedFrame_mulVec_coordinate]
    change aeval (W.liftDirection u) (linearFormPolynomial (S 1)) ≠ 0
    rw [hS₁]
    exact hru
  have hv'₀ : v' 0 ≠ 0 := by
    change ((W.restrictedFrame S).map (algebraMap L E) *ᵥ v) (0 : Fin 2) ≠ 0
    rw [W.restrictedFrame_mulVec_coordinate]
    change aeval (W.liftDirection v) (linearFormPolynomial (S 0)) ≠ 0
    rw [hS₀]
    exact hlv
  have hv'₁ : v' 1 = 0 := by
    change ((W.restrictedFrame S).map (algebraMap L E) *ᵥ v) (1 : Fin 2) = 0
    rw [W.restrictedFrame_mulVec_coordinate]
    change aeval (W.liftDirection v) (linearFormPolynomial (S 1)) = 0
    rw [hS₁]
    exact hrv
  have hU := quadraticFormPolynomial_associated_linear_direction_zero _ _ _ c h u hu₀
  have hV := quadraticFormPolynomial_associated_linear_direction_zero _ _ _ c h v hv₀
  have h₀₀ := quadraticFormPolynomial_nonzero_axis_root_diagonal_zero
    (V.hessian.map α.symm) 0 v' hv'₀ (by
      intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact hv'₁) hV
  have h₁₁ := quadraticFormPolynomial_nonzero_axis_root_diagonal_zero
    (V.hessian.map α.symm) 1 u' hu'₁ (by
      intro i hi
      fin_cases i
      · exact hu'₀
      · exact (hi rfl).elim) hU
  have hV₀₀ : V.hessian 0 0 = 0 := α.symm.injective (h₀₀.trans (map_zero α.symm).symm)
  have hV₁₁ : V.hessian 1 1 = 0 := α.symm.injective (h₁₁.trans (map_zero α.symm).symm)
  let G := linearPolynomialConjugate T S H
  have hHess := closed_field_normalized_ternary_graph_hessian_ne_zero
    G V.origin_zero V.components_independent (Out₂ G) V.independent (fun _ => rfl)
    V.lastOutput V.lastOutput_value
  obtain ⟨γ, a, b, δ, hγ, he⟩ :=
    ternary_graph_zero_hessian_diagonal_constructs_bilinear_output
      (Out₂ G) V.independent V.lastOutput hV₀₀ hV₁₁ hHess
  refine ⟨T, S, γ, a, b, δ, hTS, hST, hγ, V.independent, ?_⟩
  apply IsFractionRing.injective R₃ F
  change (V.lastOutput : F) = algebraMap K F γ * ι (G 0) * ι (G 1) +
    algebraMap K F a * ι (G 0) + algebraMap K F b * ι (G 1) + algebraMap K F δ at he
  rw [V.lastOutput_value] at he
  simpa only [map_add, map_mul, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₃ F] using he

end DimensionFourDependence
