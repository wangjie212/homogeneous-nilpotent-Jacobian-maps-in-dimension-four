import DimensionFourDependence.TernaryParameterPolynomialOutput
import DimensionFourDependence.TernaryQuadraticGraphOutput

/-! # Exact coordinate reordering and the resulting quadratic graph chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4400000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K

/-- The reindexing used to put the exceptional source coordinate last
while retaining the first horizontal coordinate. -/
def ternaryVerticalSwap : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

local notation "τ" => ternaryVerticalSwap
local notation "σ" => (rename (R := K) τ)
local notation "O" => (aeval (fun _ : Fin 3 => (0 : K)))

theorem ternaryVerticalSwap_zero : τ 0 = 0 := by decide
theorem ternaryVerticalSwap_one : τ 1 = 2 := by decide
theorem ternaryVerticalSwap_two : τ 2 = 1 := by decide

omit [Field K] [CharZero K] in
theorem ternaryVerticalSwap_rename_involutive {A : Type*} [CommSemiring A] (P : MvPolynomial (Fin 3) A) :
    rename τ (rename τ P) = P := by
  rw [rename_rename]
  have he : (τ : Fin 3 → Fin 3) ∘ τ = id := by funext i; exact Equiv.swap_apply_self 1 2 i
  rw [he, rename_id_apply]

omit [CharZero K] in
theorem ternaryVerticalSwap_origin (P : R₃) : O (σ P) = O P := aeval_rename _ _ _

omit [CharZero K] in
theorem ternaryVerticalSwap_pderiv (P : R₃) (i : Fin 3) :
    σ (pderiv i P) = pderiv (τ i) (σ P) := (pderiv_rename ternaryVerticalSwap.injective i P).symm

/-- The exact trace and minor equations with the two horizontal
coordinates first and the common parameter genuinely vertical. -/
theorem ternary_vertical_common_parameter_trace_and_minors
    (H : Fin 3 → R₃) (hN : IsNilpotent (jac H))
    (r : R₃) (f g : Polynomial K)
    (hf : H 0 = Polynomial.aeval r f) (hg : H 2 = Polynomial.aeval r g) :
    let q := σ r
    let v := σ (H 1)
    let U := Polynomial.aeval q f.derivative
    let V := Polynomial.aeval q g.derivative
    let W := U * pderiv 0 q + V * pderiv 1 q
    W + pderiv 2 v = 0 ∧
      W * pderiv 2 v - pderiv 2 q * (U * pderiv 0 v + V * pderiv 1 v) = 0 := by
  obtain ⟨ht, hm⟩ := ternary_common_parameter_trace_and_minors H hN r f g hf hg
  have htrace := congrArg σ ht
  have hminor := congrArg σ hm
  constructor
  · simpa only [map_add, map_mul, map_zero, ← Polynomial.aeval_algHom_apply,
      ternaryVerticalSwap_pderiv, ternaryVerticalSwap_zero, ternaryVerticalSwap_one, ternaryVerticalSwap_two] using htrace
  · simpa only [map_sub, map_add, map_mul, map_zero, ← Polynomial.aeval_algHom_apply,
      ternaryVerticalSwap_pderiv, ternaryVerticalSwap_zero, ternaryVerticalSwap_one, ternaryVerticalSwap_two] using hminor

variable [IsAlgClosed K]

/-- The exact common-parameter chart reduces to a quadratic graph in
the outer source coordinates. Its vertical output is the graph-gradient
combination of the other outputs, with an original linear remainder. -/
theorem ternary_algebraic_pair_constructs_quadratic_graph_chart
    (H : Fin 3 → R₃) (h₀ : ∀ i, O (H i) = 0) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H)
    (hTrans : Transcendental K (algebraMap R₃ (FractionRing R₃) (H 0)))
    (hAlg : IsAlgebraic (IntermediateField.adjoin K {algebraMap R₃ (FractionRing R₃) (H 0)})
      (algebraMap R₃ (FractionRing R₃) (H 2))) :
    ∃ (l m : Fin 3 → K) (a b : K) (f g : Polynomial K), l 2 = m 1 ∧ f.eval 0 = 0 ∧ g.eval 0 = 0 ∧
      let Q := affineTangentQuadraticPotential l m
      let r := X 2 - rename Fin.castSucc Q
      let U := rename Fin.castSucc (pderiv (0 : Fin 2) Q)
      let V := rename Fin.castSucc (pderiv (1 : Fin 2) Q)
      σ (H 0) = Polynomial.aeval r f ∧ σ (H 2) = Polynomial.aeval r g ∧
        σ (H 1) = U * Polynomial.aeval r f + V * Polynomial.aeval r g + (C a * X 0 + C b * X 1) := by
  obtain ⟨r, f, g, hr, _, hf₀, hg₀, hf, hg, hR⟩ :=
    ternary_algebraic_pair_has_normalized_closed_polynomial_parameter H h₀ hTrans hAlg
  have hu := ternary_parameter_derivatives_independent H hind r f g hf₀ hg₀ hf hg
  obtain ⟨ht, hm⟩ := ternary_common_parameter_trace_and_minors H hN r f g hf hg
  obtain ⟨hyr, a, b, c, hv⟩ := ternary_common_parameter_middle_output_is_polynomial_affine r (H 1) f g hr hR hu ht hm
  let q := σ r
  let v := σ (H 1)
  have hq : pderiv 2 q ≠ 0 := by
    rw [← ternaryVerticalSwap_one, ← ternaryVerticalSwap_pderiv]
    exact fun h => hyr ((rename_injective τ ternaryVerticalSwap.injective) (h.trans (map_zero σ).symm))
  have hv' : v = Polynomial.aeval q a * X 1 + Polynomial.aeval q b * X 0 + Polynomial.aeval q c := by
    simpa only [map_add, map_mul, ← Polynomial.aeval_algHom_apply, rename_X,
      ternaryVerticalSwap_zero, ternaryVerticalSwap_two] using congrArg σ hv
  obtain ⟨hTrace, _⟩ := ternary_vertical_common_parameter_trace_and_minors H hN r f g hf hg
  have hdiff : pderiv 2 v = (Polynomial.aeval q c.derivative + Polynomial.aeval q b.derivative * X 0 +
      Polynomial.aeval q a.derivative * X 1) * pderiv 2 q := by
    rw [hv']
    simp only [map_add, pderiv_mul, affine_partial_polynomial_parameter_chain_rule,
      pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2), pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2),
      mul_zero, add_zero]
    ring
  change Polynomial.aeval q f.derivative * pderiv 0 q + Polynomial.aeval q g.derivative * pderiv 1 q + pderiv 2 v = 0 at hTrace
  have hTrace' := hTrace
  rw [hdiff] at hTrace'
  obtain ⟨l, m, T, hclosed, hT⟩ := ternary_vertical_parameter_has_quadratic_potential q hq f g a b c hu hTrace'
  let Q := affineTangentQuadraticPotential l m
  let ρ := X 2 - rename Fin.castSucc Q
  have hρ₀ : O ρ = 0 := by
    change O (X 2 - rename Fin.castSucc (affineTangentQuadraticPotential l m)) = 0
    simp [map_sub, affineTangentQuadraticPotential]
  have he (P : Polynomial K) : Polynomial.aeval q P = Polynomial.aeval ρ (P.comp T) := by
    change q = Polynomial.aeval ρ T at hT
    rw [Polynomial.aeval_comp, ← hT]
  have hF : σ (H 0) = Polynomial.aeval ρ (f.comp T) := by
    rw [hf, ← Polynomial.aeval_algHom_apply]
    exact he f
  have hG : σ (H 2) = Polynomial.aeval ρ (g.comp T) := by
    rw [hg, ← Polynomial.aeval_algHom_apply]
    exact he g
  have hF₀ : (f.comp T).eval 0 = 0 := by
    have hz := congrArg O hF
    simpa only [ternaryVerticalSwap_origin, h₀, map_ordinary_parameter_value_at_zero _ ρ hρ₀,
      Algebra.algebraMap_self_apply] using hz.symm
  have hG₀ : (g.comp T).eval 0 = 0 := by
    have hz := congrArg O hG
    simpa only [ternaryVerticalSwap_origin, h₀, map_ordinary_parameter_value_at_zero _ ρ hρ₀,
      Algebra.algebraMap_self_apply] using hz.symm
  have hvρ : v = Polynomial.aeval ρ (a.comp T) * X 1 + Polynomial.aeval ρ (b.comp T) * X 0 +
      Polynomial.aeval ρ (c.comp T) := by rw [hv', he a, he b, he c]
  have hc₀ : (c.comp T).eval 0 = 0 := by
    have hz := congrArg O hvρ
    change O (σ (H 1)) = _ at hz
    simpa only [ternaryVerticalSwap_origin, h₀, map_add, map_mul, aeval_X, mul_zero, add_zero,
      zero_add, map_ordinary_parameter_value_at_zero _ ρ hρ₀, Algebra.algebraMap_self_apply] using hz.symm
  have hFinalTrace : pderiv 0 (Polynomial.aeval ρ (f.comp T)) + pderiv 1 (Polynomial.aeval ρ (g.comp T)) + pderiv 2 v = 0 := by
    rw [← he f, ← he g, affine_partial_polynomial_parameter_chain_rule,
      affine_partial_polynomial_parameter_chain_rule]
    exact hTrace
  have hV := ternary_quadratic_graph_trace_determines_middle_output Q (f.comp T) (g.comp T) (a.comp T) (b.comp T)
    (c.comp T) hF₀ hG₀ v hvρ hFinalTrace
  rw [hc₀, map_zero, add_zero, add_comm (C ((a.comp T).eval 0) * X 1) (C ((b.comp T).eval 0) * X 0)] at hV
  exact ⟨l, m, (b.comp T).eval 0, (a.comp T).eval 0, f.comp T, g.comp T, hclosed, hF₀, hG₀, hF, hG, hV⟩

end DimensionFourDependence
