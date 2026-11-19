import DimensionFourDependence.TernaryVerticalParameterChart

/-! # The nilpotent principal minors give the exact quadratic output relation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4350000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K

/-- Evaluating an ordinary polynomial at the graph parameter is
injective because its last partial is one. -/
theorem ternary_graph_parameter_polynomial_evaluation_injective
    (Q : MvPolynomial (Fin 2) K) :
    Function.Injective (Polynomial.aeval (R := K) (X (2 : Fin 3) - rename Fin.castSucc Q)) := by
  let r := X (2 : Fin 3) - rename Fin.castSucc Q
  let F := FractionRing R₃
  let j := IsScalarTower.toAlgHom K R₃ F
  let D := rationalPartial (K := K) (2 : Fin 3)
  have hr : pderiv 2 r = 1 := by
    change pderiv 2 (X 2 - rename Fin.castSucc Q) = 1
    rw [map_sub, pderiv_X_self, binary_rename_vertex_pderiv_zero, sub_zero]
  have hD : D (j r) = 1 := by
    change D (algebraMap R₃ F r) = 1
    rw [rationalPartial_polynomial, hr, map_one]
  have ht : Transcendental K (j r) := by
    intro h
    exact one_ne_zero (hD.symm.trans (derivation_zero_of_isAlgebraic D (j r) h))
  intro f g he
  apply (transcendental_iff_injective.mp ht)
  rw [Polynomial.aeval_algHom_apply j r, Polynomial.aeval_algHom_apply j r, he]

/-- On the quadratic graph the sum of principal minors is the negative
derivative of its quadratic-plus-linear output relation. -/
theorem ternary_quadratic_graph_minor_forces_output_identity
    (l m : Fin 3 → K) (hclosed : l 2 = m 1) (a b : K) (f g : Polynomial K)
    (hf : f.eval 0 = 0) (hg : g.eval 0 = 0) (v : R₃)
    (hData :
      let Q := affineTangentQuadraticPotential l m
      let r := X 2 - rename Fin.castSucc Q
      let U := Polynomial.aeval r f.derivative
      let V := Polynomial.aeval r g.derivative
      let W := U * pderiv 0 r + V * pderiv 1 r
      v = rename Fin.castSucc (pderiv (0 : Fin 2) Q) * Polynomial.aeval r f +
        rename Fin.castSucc (pderiv (1 : Fin 2) Q) * Polynomial.aeval r g + (C a * X 0 + C b * X 1) ∧
      W * pderiv 2 v - pderiv 2 r * (U * pderiv 0 v + V * pderiv 1 v) = 0) :
    Polynomial.C (l 1 / 2) * f ^ 2 + Polynomial.C (l 2) * f * g +
      Polynomial.C (m 2 / 2) * g ^ 2 + Polynomial.C a * f + Polynomial.C b * g = 0 := by
  let Q := affineTangentQuadraticPotential l m
  let r := X 2 - rename Fin.castSucc Q
  let F := Polynomial.aeval r f
  let G := Polynomial.aeval r g
  let P := Polynomial.aeval r f.derivative
  let R := Polynomial.aeval r g.derivative
  let U := rename Fin.castSucc (pderiv (0 : Fin 2) Q)
  let V := rename Fin.castSucc (pderiv (1 : Fin 2) Q)
  obtain ⟨hv, hm⟩ := hData
  change v = U * F + V * G + (C a * X 0 + C b * X 1) at hv
  change (P * pderiv 0 r + R * pderiv 1 r) * pderiv 2 v -
    pderiv 2 r * (P * pderiv 0 v + R * pderiv 1 v) = 0 at hm
  have hU : U = affineTangentVerticalCoefficient l := by
    change rename Fin.castSucc (pderiv (0 : Fin 2) (affineTangentQuadraticPotential l m)) = _
    rw [affineTangentQuadraticPotential_pderiv_x]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl
  have hV : V = affineTangentVerticalCoefficient m := by
    change rename Fin.castSucc (pderiv (1 : Fin 2) (affineTangentQuadraticPotential l m)) = _
    rw [affineTangentQuadraticPotential_pderiv_z l m hclosed]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl
  have hQ₀ : pderiv (0 : Fin 3) (rename Fin.castSucc Q) = U := pderiv_rename (Fin.castSucc_injective 2) 0 Q
  have hQ₁ : pderiv (1 : Fin 3) (rename Fin.castSucc Q) = V := pderiv_rename (Fin.castSucc_injective 2) 1 Q
  have hr₀ : pderiv 0 r = -U := by
    change pderiv 0 (X 2 - rename Fin.castSucc Q) = _
    rw [map_sub, hQ₀, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), zero_sub]
  have hr₁ : pderiv 1 r = -V := by
    change pderiv 1 (X 2 - rename Fin.castSucc Q) = _
    rw [map_sub, hQ₁, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1), zero_sub]
  have hr₂ : pderiv 2 r = 1 := by
    change pderiv 2 (X 2 - rename Fin.castSucc Q) = _
    rw [map_sub, pderiv_X_self, binary_rename_vertex_pderiv_zero, sub_zero]
  have hF (i : Fin 3) : pderiv i F = P * pderiv i r := affine_partial_polynomial_parameter_chain_rule i r f
  have hG (i : Fin 3) : pderiv i G = R * pderiv i r := affine_partial_polynomial_parameter_chain_rule i r g
  have hL₀ : pderiv (0 : Fin 3) (C a * X 0 + C b * X 1) = C a := by simp
  have hL₁ : pderiv (1 : Fin 3) (C a * X 0 + C b * X 1) = C b := by simp
  have hL₂ : pderiv (2 : Fin 3) (C a * X 0 + C b * X 1) = 0 := by simp
  have hw (i : Fin 3) : pderiv i v = pderiv i U * F + U * (P * pderiv i r) +
      (pderiv i V * G + V * (R * pderiv i r)) + pderiv i (C a * X 0 + C b * X 1) := by
    rw [hv]
    simp only [map_add, pderiv_mul, hF, hG]
  rw [hw 0, hw 1, hw 2, hr₀, hr₁, hr₂, hL₀, hL₁, hL₂] at hm
  have hUder (i : Fin 3) : pderiv i U = (![C (l 1), C (l 2), 0] : Fin 3 → R₃) i :=
    hU ▸ affineTangentVerticalCoefficient_pderiv l i
  have hVder (i : Fin 3) : pderiv i V = (![C (l 2), C (m 2), 0] : Fin 3 → R₃) i := by
    rw [hV, affineTangentVerticalCoefficient_pderiv, hclosed]
  rw [hUder 0, hUder 1, hUder 2, hVder 0, hVder 1, hVder 2] at hm
  have hm' : P * (C (l 1) * F + C (l 2) * G + C a) + R * (C (l 2) * F + C (m 2) * G + C b) = 0 := by
    change (P * -U + R * -V) * (0 * F + U * (P * 1) + (0 * G + V * (R * 1)) + 0) -
      1 * (P * (C (l 1) * F + U * (P * -U) + (C (l 2) * G + V * (R * -U)) + C a) +
        R * (C (l 2) * F + U * (P * -V) + (C (m 2) * G + V * (R * -V)) + C b)) = 0 at hm
    linear_combination -hm
  let W := Polynomial.C (l 1 / 2) * f ^ 2 + Polynomial.C (l 2) * f * g +
    Polynomial.C (m 2 / 2) * g ^ 2 + Polynomial.C a * f + Polynomial.C b * g
  have hcoef (k : K) : C (k / 2) * (2 : R₃) = C k := by
    change C (k / 2) * C (2 : K) = C k
    rw [← map_mul, div_mul_cancel₀ _ two_ne_zero]
  have hd : W.derivative = 0 := by
    apply ternary_graph_parameter_polynomial_evaluation_injective Q
    change Polynomial.aeval r W.derivative = Polynomial.aeval r 0
    simp only [W, map_add, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_pow,
      map_zero, map_mul, map_pow, map_natCast, Polynomial.aeval_C, algebraMap_eq, zero_mul, zero_add]
    change C (l 1 / 2) * (2 * F ^ (2 - 1) * P) +
      (C (l 2) * P * G + C (l 2) * F * R) + C (m 2 / 2) * (2 * G ^ (2 - 1) * R) + C a * P + C b * R = 0
    norm_num only [Nat.reduceSub, pow_one]
    linear_combination hm' + F * P * hcoef (l 1) + G * R * hcoef (m 2)
  have hW := Polynomial.eq_C_of_derivative_eq_zero hd
  have h₀ : W.eval 0 = 0 := by simp [W, hf, hg]
  have hconst : W.coeff 0 = 0 := by simpa only [Polynomial.eval_C, h₀] using congrArg (Polynomial.eval 0) hW.symm
  exact hW.trans (by rw [hconst, map_zero])

end DimensionFourDependence
