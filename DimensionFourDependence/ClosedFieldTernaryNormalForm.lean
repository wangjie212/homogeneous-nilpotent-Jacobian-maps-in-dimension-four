import DimensionFourDependence.TernaryQuadraticGraphIdentity
import DimensionFourDependence.TernaryRankOneGraphNormalForm

/-! # The canonical normalized ternary form over algebraically closed constants -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 5400000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "O" => (aeval (fun _ : Fin 3 => (0 : K)))
local notation "σ" => (rename (R := K) ternaryVerticalSwap)
local notation "ι" => (algebraMap R₃ (FractionRing R₃))

/-- The algebraically dependent pair gives the canonical form after
the graph's rank-one identity and one original constant conjugacy. -/
theorem closed_field_ternary_algebraic_pair_conjugates_to_normal_form
    (H : Fin 3 → R₃) (h₀ : ∀ i, O (H i) = 0) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hTrans : Transcendental K (ι (H 0)))
    (hAlg : IsAlgebraic (IntermediateField.adjoin K {ι (H 0)}) (ι (H 2))) :
    ∃ (T S : Matrix (Fin 3) (Fin 3) K) (P : Polynomial K), T * S = 1 ∧ S * T = 1 ∧
      0 < P.natDegree ∧ P.eval 0 = 0 ∧ linearPolynomialConjugate T S H = TernaryNormalForm.perturbation3 P := by
  obtain ⟨l, m, a, b, f, g, hclosed, hf₀, hg₀, hF, hG, hV⟩ :=
    ternary_algebraic_pair_constructs_quadratic_graph_chart H h₀ hN hind hTrans hAlg
  let Q := affineTangentQuadraticPotential l m
  let r := X 2 - rename Fin.castSucc Q
  let F := Polynomial.aeval r f
  let G := Polynomial.aeval r g
  let U := rename Fin.castSucc (pderiv (0 : Fin 2) Q)
  let V := rename Fin.castSucc (pderiv (1 : Fin 2) Q)
  change σ (H 0) = F at hF
  change σ (H 2) = G at hG
  change σ (H 1) = U * F + V * G + (C a * X 0 + C b * X 1) at hV
  have hf : H 0 = Polynomial.aeval (σ r) f := by
    have he := congrArg σ hF
    simpa only [ternaryVerticalSwap_rename_involutive, F, ← Polynomial.aeval_algHom_apply] using he
  have hg : H 2 = Polynomial.aeval (σ r) g := by
    have he := congrArg σ hG
    simpa only [ternaryVerticalSwap_rename_involutive, G, ← Polynomial.aeval_algHom_apply] using he
  have hindfg (u v : K) (he : Polynomial.C u * f + Polynomial.C v * g = 0) : u = 0 ∧ v = 0 := by
    have hpol := congrArg (Polynomial.aeval (σ r)) he
    have hrel : C u * H 0 + C v * H 2 = 0 := by
      simpa only [map_add, map_mul, map_zero, Polynomial.aeval_C, algebraMap_eq, ← hf, ← hg] using hpol
    by_contra h
    apply hind
    refine ⟨![u, 0, v], fun hz => h ⟨congrFun hz 0, congrFun hz 2⟩, ?_⟩
    rw [Fin.sum_univ_three]
    simp only [cons_val_zero, cons_val_one, cons_val_two, zero_smul, add_zero, smul_eq_C_mul]
    exact hrel
  obtain ⟨_, hminor⟩ := ternary_vertical_common_parameter_trace_and_minors H hN (σ r) f g hf hg
  have hminor' : (Polynomial.aeval r f.derivative * pderiv 0 r + Polynomial.aeval r g.derivative * pderiv 1 r) *
      pderiv 2 (σ (H 1)) - pderiv 2 r * (Polynomial.aeval r f.derivative * pderiv 0 (σ (H 1)) +
        Polynomial.aeval r g.derivative * pderiv 1 (σ (H 1))) = 0 := by
    simpa only [ternaryVerticalSwap_rename_involutive] using hminor
  have hrel := ternary_quadratic_graph_minor_forces_output_identity l m hclosed a b f g hf₀ hg₀ (σ (H 1)) ⟨hV, hminor'⟩
  have hU : U = affineTangentVerticalCoefficient l := by
    change rename Fin.castSucc (pderiv (0 : Fin 2) (affineTangentQuadraticPotential l m)) = _
    rw [affineTangentQuadraticPotential_pderiv_x]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl
  have hV' : V = affineTangentVerticalCoefficient m := by
    change rename Fin.castSucc (pderiv (1 : Fin 2) (affineTangentQuadraticPotential l m)) = _
    rw [affineTangentQuadraticPotential_pderiv_z l m hclosed]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl
  have hD := normalized_polynomial_relation_binary_discriminant_zero f g hf₀ hg₀ hindfg _ _ _ a b hrel
  have hQ : l 1 / 2 ≠ 0 ∨ l 2 ≠ 0 ∨ m 2 / 2 ≠ 0 := by
    by_contra! h
    have hℓ : l 1 = 0 := (div_eq_zero_iff.mp h.1).resolve_right two_ne_zero
    have hₘ : m 2 = 0 := (div_eq_zero_iff.mp h.2.2).resolve_right two_ne_zero
    have hcross : m 1 = 0 := hclosed.symm.trans h.2.1
    have hlin : Polynomial.C a * f + Polynomial.C b * g = 0 := by
      simpa only [h.1, h.2.1, h.2.2, map_zero, zero_mul, zero_add] using hrel
    obtain ⟨ha, hb⟩ := hindfg a b hlin
    rw [hU, hV', ha, hb] at hV
    simp only [affineTangentVerticalCoefficient, hℓ, h.2.1, hcross, hₘ,
      map_zero, zero_mul, add_zero, ← hF, ← hG] at hV
    have hz : H 1 = C (l 0) * H 0 + C (m 0) * H 2 := by
      apply rename_injective ternaryVerticalSwap ternaryVerticalSwap.injective
      simpa only [map_add, map_mul, rename_C] using hV
    apply hind
    refine ⟨![-l 0, 1, -m 0], fun hzero => one_ne_zero (congrFun hzero 1), ?_⟩
    rw [Fin.sum_univ_three]
    change (-l 0) • H 0 + (1 : K) • H 1 + (-m 0) • H 2 = 0
    simp only [smul_eq_C_mul, map_one, one_mul, map_neg]
    rw [hz]
    ring
  obtain ⟨k, u, v, hk, huv, hA, hB, hC⟩ := singular_nonzero_binary_quadratic_is_scalar_square _ _ _ hD hQ
  have hP := normalized_independent_polynomial_combination_pos_degree f g hf₀ hg₀ hindfg u v huv
  have hEq : Polynomial.C k * (Polynomial.C u * f + Polynomial.C v * g) ^ 2 +
      Polynomial.C a * f + Polynomial.C b * g = 0 := by
    rw [hA, hB, hC] at hrel
    simp only [map_mul, map_ofNat, map_pow] at hrel
    linear_combination hrel
  have hdet := normalized_scalar_square_relation_transverse_covectors_independent f g u v a b k hk hP hEq
  apply ternary_rank_one_graph_conjugates_to_normal_form H k u v (l 0) (m 0) a b hk hdet f g hf₀ hg₀ hP hEq
  let L : R₃ := C u * X 0 + C v * X 2
  let ρ : R₃ := X 1 - (C (l 0) * X 0 + C (m 0) * X 2) - C k * L ^ 2
  have hr : σ r = ρ := by
    change σ (X 2 - rename Fin.castSucc (affineTangentQuadraticPotential l m)) = _
    simp only [affineTangentQuadraticPotential, map_sub, map_add, map_mul, map_pow, rename_C, rename_X,
      ternaryVerticalSwap_two]
    change X 1 - (C (l 1 / 2) * X 0 ^ 2 + C (l 2) * X 0 * X 2 + C (m 2 / 2) * X 2 ^ 2 +
      C (l 0) * X 0 + C (m 0) * X 2) = ρ
    rw [hA, hB, hC]
    simp only [ρ, L, map_mul, map_ofNat, map_pow]
    ring
  rw [hr] at hf hg
  have h₁ : l 1 = 2 * k * u ^ 2 := by
    have he := (div_eq_iff two_ne_zero).mp hA
    linear_combination he
  have h₂ : m 2 = 2 * k * v ^ 2 := by
    have he := (div_eq_iff two_ne_zero).mp hC
    linear_combination he
  refine ⟨hf, hg, ?_⟩
  have he := congrArg σ hV
  simp only [ternaryVerticalSwap_rename_involutive, map_add, map_mul, rename_C, rename_X,
    ternaryVerticalSwap_zero, ternaryVerticalSwap_one, hU, hV', affineTangentVerticalCoefficient] at he
  change H 1 = (C (l 0) + C (l 1) * X 0 + C (l 2) * X 2) * σ F +
    (C (m 0) + C (m 1) * X 0 + C (m 2) * X 2) * σ G + (C a * X 0 + C b * X 2) at he
  rw [← hF, ← hG, ternaryVerticalSwap_rename_involutive, ternaryVerticalSwap_rename_involutive,
    ← hclosed, h₁, hB, h₂] at he
  change H 1 = C (l 0) * Polynomial.aeval ρ f + C (m 0) * Polynomial.aeval ρ g +
    2 * C k * L * (C u * Polynomial.aeval ρ f + C v * Polynomial.aeval ρ g) + (C a * X 0 + C b * X 2)
  rw [← hf, ← hg, he]
  simp only [L, map_mul, map_ofNat, map_pow]
  ring

/-- The full forward ternary classification over algebraically closed
characteristic-zero constants, from the original normalized map. -/
theorem closed_field_ternary_nilpotent_classification : TernaryNilpotentClassification K := by
  intro H h₀ hN hind
  obtain ⟨T, S, hTS, hST, hi, hAlg⟩ :=
    closed_field_normalized_independent_ternary_constructs_algebraic_pair_chart H h₀ hind hN
  let G := linearPolynomialConjugate T S H
  have hG₀ : ∀ i, O (G i) = 0 := by
    have he := linearPolynomialConjugate_aeval_extension_eq_zero T S hTS H
      (fun _ : Fin 3 => (0 : K)) h₀
    have hz : S.map (algebraMap K K) *ᵥ (fun _ : Fin 3 => (0 : K)) = 0 := mulVec_zero _
    rw [hz] at he
    exact he
  obtain ⟨A, B, P, hAB, hBA, hP, hP₀, he⟩ := closed_field_ternary_algebraic_pair_conjugates_to_normal_form
    G hG₀ (linearPolynomialConjugate_nilpotent T S hTS hST H hN)
    (linearPolynomialConjugate_componentsIndependent T S hTS hST H hind) (hi.transcendental 0) hAlg
  refine ⟨T * A, B * S, P, ?_, ?_, hP, hP₀, ?_⟩
  · rw [Matrix.mul_assoc T A, ← Matrix.mul_assoc A B, hAB, Matrix.one_mul, hTS]
  · rw [Matrix.mul_assoc B S, ← Matrix.mul_assoc S T, hST, Matrix.one_mul, hBA]
  · rw [← linearPolynomialConjugate_compose T S A B]
    exact he

end DimensionFourDependence
