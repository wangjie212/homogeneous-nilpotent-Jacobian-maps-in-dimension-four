import DimensionFourDependence.DerivationSlicePolynomial
import DimensionFourDependence.ProjectiveSourceParameterField

/-! # The cubic coefficient of the transverse derivative must vanish -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1900000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x₀" => (rationalCoordinate (K := K) (n := 3))

/-- The highest slice coefficient of the transverse derivative of `y`
vanishes because that derivative and the original partial of the common
parameter multiply to one in the polynomial algebra of the slice. -/
theorem ternary_parameter_slice_cubic_coefficient_zero
    (D E G : Derivation K F F) (r : R₃) (a s α b c d : F)
    (hDx : D (x₀ 0) = 1) (hEx : E (x₀ 0) = 0) (hGx : G (x₀ 0) = 0)
    (hE : ∀ t, D (E t) = E (D t)) (hG : ∀ t, D (G t) = G (D t))
    (ha : D a = 0) (hs : D s = 0) (hα : D α = 0)
    (hb : D b = 0) (hc : D c = 0) (hd : D d = 0)
    (hy : x₀ 1 = b + c * x₀ 0 + d * x₀ 0 ^ 2) (hz : x₀ 2 = s + a * x₀ 0)
    (hOne : ι (pderiv 1 r) * (E (x₀ 1) - α * x₀ 0 * G (x₀ 1)) = 1) :
    α * G d = 0 := by
  let M := derivationConstants D
  let B : M := ⟨b, hb⟩
  let C₁ : M := ⟨c, hc⟩
  let C₂ : M := ⟨d, hd⟩
  let S : M := ⟨s, hs⟩
  let A : M := ⟨a, ha⟩
  let l : M := ⟨α, hα⟩
  let E₀ : M → M := fun t => ⟨E t, by
    change D (E t) = 0
    rw [hE, show D (t : F) = 0 from t.property, map_zero]⟩
  let G₀ : M → M := fun t => ⟨G t, by
    change D (G t) = 0
    rw [hG, show D (t : F) = 0 from t.property, map_zero]⟩
  let e := Polynomial.aeval (R := M) (x₀ 0)
  let Y : Polynomial M := Polynomial.C B + Polynomial.C C₁ * Polynomial.X +
    Polynomial.C C₂ * Polynomial.X ^ 2
  let Z : Polynomial M := Polynomial.C S + Polynomial.C A * Polynomial.X
  have hCoords (i : Fin 3) : ∃ P : Polynomial M, e P = x₀ i := by
    fin_cases i
    · exact ⟨Polynomial.X, Polynomial.aeval_X _⟩
    · refine ⟨Y, ?_⟩
      simp only [e, Y, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      exact hy.symm
    · refine ⟨Z, ?_⟩
      simp only [e, Z, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      exact hz.symm
  obtain ⟨P, hP⟩ := polynomial_values_are_polynomial_in_derivation_slice D (x₀ 0) x₀ hCoords (pderiv 1 r)
  rw [rationalCoordinate_aeval] at hP
  let Q : Polynomial M := Polynomial.C (E₀ B) + Polynomial.C (E₀ C₁) * Polynomial.X +
    Polynomial.C (E₀ C₂) * Polynomial.X ^ 2 - (Polynomial.C l * Polynomial.X) *
      (Polynomial.C (G₀ B) + Polynomial.C (G₀ C₁) * Polynomial.X +
        Polynomial.C (G₀ C₂) * Polynomial.X ^ 2)
  have hQ : e Q = E (x₀ 1) - α * x₀ 0 * G (x₀ 1) := by
    simp only [e, Q, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    change E b + E c * x₀ 0 + E d * x₀ 0 ^ 2 -
      α * x₀ 0 * (G b + G c * x₀ 0 + G d * x₀ 0 ^ 2) = _
    rw [hy]
    simp only [map_add, E.leibniz, G.leibniz, E.leibniz_pow, G.leibniz_pow,
      smul_eq_mul, hEx, hGx, mul_zero, zero_add]
    ring
  have hProd : e P * e Q = 1 := by rw [show e P = _ from hP, hQ, hOne]
  have hZero : Q.coeff 3 = 0 := derivation_slice_product_one_forces_constant D (x₀ 0) hDx P Q hProd 3 (by decide)
  have hCoeff : Q.coeff 3 = -(l * G₀ C₂) := by
    have hExpand : Q = Polynomial.C (E₀ B) +
        Polynomial.C (E₀ C₁ - l * G₀ B) * Polynomial.X +
        Polynomial.C (E₀ C₂ - l * G₀ C₁) * Polynomial.X ^ 2 -
        Polynomial.C (l * G₀ C₂) * Polynomial.X ^ 3 := by
      simp only [Q, map_sub, map_mul]
      ring
    rw [hExpand]
    have h1 (a : M) : (Polynomial.C a * Polynomial.X).coeff 3 = 0 := by
      rw [← pow_one (Polynomial.X : Polynomial M), Polynomial.coeff_C_mul_X_pow]
      rfl
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C,
      h1, Polynomial.coeff_C_mul_X_pow]
    norm_num
  have h := neg_eq_zero.mp (hCoeff.symm.trans hZero)
  exact congrArg (fun t : M => (t : F)) h

end DimensionFourDependence
