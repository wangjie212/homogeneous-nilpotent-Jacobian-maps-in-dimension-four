import DimensionFourDependence.TernaryParameterRationalOutput
import DimensionFourDependence.TernaryParameterPolynomialCoefficients

/-! # The dependent-pair chart has polynomial affine middle output -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 4200000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "D₀" => (rationalPartial (K := K) (n := 3))
local notation "x₀" => (rationalCoordinate (K := K) (n := 3))

/-- With the first and third outputs polynomial in a common closed
parameter, the actual middle output is affine in the two outer source
coordinates with ordinary polynomial coefficients in that parameter. -/
theorem ternary_common_parameter_middle_output_is_polynomial_affine
    (r v : R₃) (f g : Polynomial K) (hr : 0 < r.totalDegree)
    (hR : algebraicClosure (IntermediateField.adjoin K {ι r}) F = ⊥)
    (hind : ∀ a b : K, Polynomial.C a * f.derivative + Polynomial.C b * g.derivative = 0 →
      a = 0 ∧ b = 0)
    (ht : Polynomial.aeval r f.derivative * pderiv 0 r +
      Polynomial.aeval r g.derivative * pderiv 2 r + pderiv 1 v = 0)
    (hm : (Polynomial.aeval r f.derivative * pderiv 0 r +
      Polynomial.aeval r g.derivative * pderiv 2 r) * pderiv 1 v -
      pderiv 1 r * (Polynomial.aeval r f.derivative * pderiv 0 v +
        Polynomial.aeval r g.derivative * pderiv 2 v) = 0) :
    pderiv 1 r ≠ 0 ∧ ∃ a b c : Polynomial K,
      v = Polynomial.aeval r a * X 2 + Polynomial.aeval r b * X 0 + Polynomial.aeval r c := by
  classical
  have hyr := ternary_common_parameter_middle_partial_ne_zero r v f g hr hind ht hm
  have hy : D₀ 1 (ι r) ≠ 0 := by
    rw [rationalPartial_polynomial]
    exact fun h => hyr ((IsFractionRing.injective R₃ F) (h.trans (map_zero ι).symm))
  have hρ : Transcendental K (ι r) := fun h => hy (derivation_zero_of_isAlgebraic (D₀ 1) (ι r) h)
  let L := IntermediateField.adjoin K {ι r}
  let j := algebraMap (Polynomial K) (RatFunc K)
  let e := transcendentalParameterFieldHom (ι r) hρ
  have he : e RatFunc.X = ι r := transcendentalParameterFieldHom_X (ι r) hρ
  have hRange : e.fieldRange = L := (rational_parameter_hom_fieldRange e).symm.trans (congrArg
    (fun a : F => IntermediateField.adjoin K {a}) he)
  let a := j g.derivative / j f.derivative
  let U := e (j f.derivative)
  let V := e (j g.derivative)
  let α := e (rationalParameterDerivative K a)
  obtain ⟨h₁, h₂⟩ := rational_ratio_of_independent_polynomials_derivative_ne_zero f.derivative g.derivative hind
  have hU : U ≠ 0 := fun h => h₁ (e.injective (h.trans (map_zero e).symm))
  have hα : α ≠ 0 := fun h => h₂ (e.injective (h.trans (map_zero e).symm))
  have hea : e a = V / U := map_div₀ e _ _
  have hs (D : Derivation K F F) (h : D (ι r) = 0) : D U = 0 ∧ D α = 0 := by
    constructor
    · change D (e (j f.derivative)) = 0
      rw [rational_parameter_chain_rule, he, h, mul_zero]
    · change D (e (rationalParameterDerivative K a)) = 0
      rw [rational_parameter_chain_rule, he, h, mul_zero]
  have ha (D : Derivation K F F) : D (V / U) = α * D (ι r) := by
    rw [← hea, rational_parameter_chain_rule, he]
  have heval (q : Polynomial K) : e (j q) = ι (Polynomial.aeval r q) := by
    rw [rational_function_algHom_polynomial_value, he]
    exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K R₃ F) r q
  have htF : U * D₀ 0 (ι r) + V * D₀ 2 (ι r) + D₀ 1 (ι v) = 0 := by
    simp only [U, V, heval, rationalPartial_polynomial]
    simpa only [map_add, map_mul, map_zero] using congrArg ι ht
  have hmF : (U * D₀ 0 (ι r) + V * D₀ 2 (ι r)) * D₀ 1 (ι v) -
      D₀ 1 (ι r) * (U * D₀ 0 (ι v) + V * D₀ 2 (ι v)) = 0 := by
    simp only [U, V, heval, rationalPartial_polynomial]
    simpa only [map_sub, map_add, map_mul, map_zero] using congrArg ι hm
  obtain ⟨aL, bL, cL, hv⟩ := ternary_parameter_middle_output_affine_over_parameter_field r (ι v) U V α
    hU hα hy hR hs ha htF hmF
  have hPre (x : L) : ∃ y : RatFunc K, e y = (x : F) := by
    have hx : (x : F) ∈ e.fieldRange := hRange.symm ▸ x.property
    exact hx
  obtain ⟨a₀, ha₀⟩ := hPre aL
  obtain ⟨b₀, hb₀⟩ := hPre bL
  obtain ⟨c₀, hc₀⟩ := hPre cL
  let P : MvPolynomial (Fin 2) (RatFunc K) := C a₀ * X 1 + C b₀ * X 0 + C c₀
  have hP : eval₂ e.toRingHom (fun i => ι (X ((1 : Fin 3).succAbove i))) P = ι v := by
    simp only [P, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    change e a₀ * x₀ 2 + e b₀ * x₀ 0 + e c₀ = ι v
    rw [ha₀, hb₀, hc₀, ← hv]
  obtain ⟨Q, hQ⟩ := ternary_horizontal_form_rational_coefficients_are_polynomial r v hyr e he P hP
  let m₀ := Finsupp.single (0 : Fin 2) (1 : ℕ)
  let m₁ := Finsupp.single (1 : Fin 2) (1 : ℕ)
  have hn₀ : m₀ ≠ 0 := by simp [m₀]
  have hn₁ : m₁ ≠ 0 := by simp [m₁]
  have hne : m₀ ≠ m₁ := by
    intro h
    have hz := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp [m₀, m₁] at hz
  have hC (m : Fin 2 →₀ ℕ) : j (Q.coeff m) = P.coeff m := by
    have hp := congrArg (fun W : MvPolynomial (Fin 2) (RatFunc K) => W.coeff m) hQ
    rwa [coeff_map] at hp
  have hPC (m : Fin 2 →₀ ℕ) : P.coeff m =
      (if m₁ = m then a₀ else 0) + (if m₀ = m then b₀ else 0) + (if m = 0 then c₀ else 0) := by
    simp only [P, C_mul_X_eq_monomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_monomial, coeff_C, m₀, m₁, eq_comm]
  have haQ : j (Q.coeff m₁) = a₀ := by rw [hC, hPC]; simp [hne, hn₁]
  have hbQ : j (Q.coeff m₀) = b₀ := by rw [hC, hPC]; simp [hne.symm, hn₀]
  have hcQ : j (Q.coeff 0) = c₀ := by rw [hC, hPC]; simp [hn₀, hn₁]
  refine ⟨hyr, Q.coeff m₁, Q.coeff m₀, Q.coeff 0, ?_⟩
  apply IsFractionRing.injective R₃ F
  simp only [map_add, map_mul, ← heval, haQ, hbQ, hcQ, ha₀, hb₀, hc₀]
  exact hv

end DimensionFourDependence
