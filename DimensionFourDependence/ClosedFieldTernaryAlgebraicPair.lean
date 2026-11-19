import DimensionFourDependence.TernaryConicDistinctDirections
import DimensionFourDependence.TernaryConicSingularDirection
import DimensionFourDependence.TernaryBilinearOutputExclusion
import DimensionFourDependence.TernaryAlgebraicPairFrame

/-! # The normalized independent ternary map has an algebraically dependent pair after conjugacy -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2450000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "Out₂" => (ternaryRationalOutputPair (K := K))

/-- The rank-two conic and its actual directions construct a constant
conjugacy with an independent first pair and a third output algebraic
over the first. This is the dependent-pair conclusion of the cited
classification's geometric argument. -/
theorem closed_field_normalized_independent_ternary_constructs_algebraic_pair_chart
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H)) :
    ∃ T S : Matrix (Fin 3) (Fin 3) K, T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      AlgebraicIndependent K (Out₂ G) ∧
        IsAlgebraic (IntermediateField.adjoin K {ι (G 0)}) (ι (G 2)) := by
  have hR := closed_field_normalized_independent_ternary_nilpotent_rank_two H h0 hind hN
  obtain ⟨T, S, hTS, hST, hG₀, hGi, hGn, hYG⟩ :=
    ternary_rank_two_constructs_normalized_independent_output_chart H h0 hind hN hR
  let G := linearPolynomialConjugate T S H
  obtain ⟨W⟩ := exists_ternary_conic_witness G hG₀ hGi hGn hYG
  have hDet : W.hessian.det = 0 := by
    by_contra hne
    obtain ⟨A, B, γ, a, b, c, hAB, hBA, hγ, _, he⟩ :=
      W.nonsingular_hessian_constructs_bilinear_output_frame hne
    let Z := linearPolynomialConjugate A B G
    have hZi := linearPolynomialConjugate_componentsIndependent A B hAB hBA G hGi
    have hZn := linearPolynomialConjugate_nilpotent A B hAB hBA G hGn
    have hZ₀ : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (Z i) = 0 := by
      have he₀ := linearPolynomialConjugate_aeval_extension_eq_zero A B hAB G
        (fun _ : Fin 3 => (0 : K)) hG₀
      have hz : B.map (algebraMap K K) *ᵥ (fun _ : Fin 3 => (0 : K)) = 0 := mulVec_zero _
      rw [hz] at he₀
      exact he₀
    exact normalized_independent_ternary_nilpotent_bilinear_output_impossible Z hZ₀ hZi hZn γ a b c hγ he
  obtain ⟨A, B, μ, hAB, hBA, hYZ, hPair⟩ := W.singular_hessian_constructs_algebraic_pair_frame hDet
  let Z := linearPolynomialConjugate A B G
  obtain ⟨U, V, hUV, hVU, hFinY, hFinAlg⟩ :=
    ternary_conjugate_subtracts_second_from_algebraic_last_output Z μ hYZ hPair
  have hLeft : (T * (A * U)) * ((V * B) * S) = 1 := by
    calc
      _ = T * (A * (U * V) * B) * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUV, mul_one, hAB, mul_one, hTS]
  have hRight : ((V * B) * S) * (T * (A * U)) = 1 := by
    calc
      _ = V * (B * (S * T) * A) * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hST, mul_one, hBA, mul_one, hVU]
  have he : linearPolynomialConjugate U V Z =
      linearPolynomialConjugate (T * (A * U)) ((V * B) * S) H := by
    change linearPolynomialConjugate U V (linearPolynomialConjugate A B
      (linearPolynomialConjugate T S H)) = _
    rw [linearPolynomialConjugate_compose A B U V,
      linearPolynomialConjugate_compose T S (A * U) (V * B)]
  refine ⟨T * (A * U), (V * B) * S, hLeft, hRight, ?_, ?_⟩
  · change AlgebraicIndependent K (Out₂ (linearPolynomialConjugate (T * (A * U)) ((V * B) * S) H))
    rw [← he]
    exact hFinY
  · change IsAlgebraic
      (IntermediateField.adjoin K {ι (linearPolynomialConjugate (T * (A * U)) ((V * B) * S) H 0)})
      (ι (linearPolynomialConjugate (T * (A * U)) ((V * B) * S) H 2))
    rw [← he]
    exact hFinAlg

end DimensionFourDependence
