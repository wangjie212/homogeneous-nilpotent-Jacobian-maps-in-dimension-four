import DimensionFourDependence.ConeLinearFactorDescent
import DimensionFourDependence.LinearPowerQuotientRecovery

/-! # The fourth cone form descends with the common linear factor

The cone expression is a common (d-1)-st linear power times a linear
quotient. The first nonzero coordinate constructs a normalized common
covector over the original field. Coordinate-point recovery then descends
the entire fourth linear quotient over that same field.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {B E : Type*} [Field B] [Field E]

/-- The fourth actual cone form factors by any specified scalar
multiple representation of its common linear factor. -/
theorem cone_ternary_last_factor_of_scaled_linear_form
    {d : ℕ} (hd : 0 < d) (τ ν V : Fin 3 → E) (u a b : E)
    (ℓ : Fin 3 → E) (s : E)
    (hlin : C u * linearFormPolynomial τ = C s * linearFormPolynomial ℓ) :
    coneTernaryForms d τ ν V u a b (Fin.last 3) =
      linearFormPolynomial ℓ ^ (d - 1) *
        linearFormPolynomial (fun i => a * s ^ d * ℓ i + b * s ^ (d - 1) * ν i) := by
  have hquot : linearFormPolynomial (fun i => a * s ^ d * ℓ i + b * s ^ (d - 1) * ν i) =
      C (a * s ^ d) * linearFormPolynomial ℓ + C (b * s ^ (d - 1)) * linearFormPolynomial ν := by
    simp only [linearFormPolynomial, map_add, map_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hpow : linearFormPolynomial ℓ ^ d = linearFormPolynomial ℓ ^ (d - 1) * linearFormPolynomial ℓ := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [coneTernaryForms_last, hlin, hquot, mul_pow, mul_pow, ← map_pow, ← map_pow, hpow]
  simp only [map_mul]
  ring

variable [CharZero E]

/-- Whole cone coefficient descent constructs the common rational
linear factor, all first-three scalar factors and the fourth linear
quotient over the original coefficient field. -/
theorem cone_ternary_forms_construct_complete_rational_linear_factorization
    (f : B →+* E) (Q : Fin 4 → MvPolynomial (Fin 3) B)
    {d : ℕ} (hd : 0 < d) (τ ν V : Fin 3 → E) (u a b : E)
    (hQ : ∀ i, MvPolynomial.map f (Q i) = coneTernaryForms d τ ν V u a b i)
    (hQ0 : Q 0 ≠ 0) :
    ∃ ℓ : Fin 3 → B, ℓ ≠ 0 ∧ ∃ r : Fin 3 → B,
      (∀ i : Fin 3, Q i.castSucc = C (r i) * linearFormPolynomial ℓ ^ d) ∧
      ∃ m : Fin 3 → B, Q (Fin.last 3) = linearFormPolynomial ℓ ^ (d - 1) * linearFormPolynomial m := by
  classical
  let α : Fin 3 → E := fun i => u * τ i
  have hlin : C u * linearFormPolynomial τ = linearFormPolynomial α := by
    simp only [linearFormPolynomial, α, map_mul, Finset.mul_sum, mul_assoc]
  have hpower (i : Fin 3) : MvPolynomial.map f (Q i.castSucc) =
      C (V i) * linearFormPolynomial α ^ d := by
    rw [hQ, coneTernaryForms_castSucc, hlin]
  obtain ⟨j, ℓ, hℓj, hℓratio, r, hr⟩ := nonzero_linear_power_family_descends
    f (fun i : Fin 3 => Q i.castSucc) hd α V 0 hQ0 hpower
  have hαj : α j ≠ 0 := by
    intro hz
    have he := hℓratio j
    rw [hℓj, map_one, hz, div_zero] at he
    exact one_ne_zero he
  have hαform : linearFormPolynomial α = C (α j) * linearFormPolynomial (fun i => f (ℓ i)) := by
    simp only [linearFormPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← map_mul, hℓratio i, mul_div_cancel₀ _ hαj]
  let mE : Fin 3 → E := fun i => a * α j ^ d * f (ℓ i) + b * α j ^ (d - 1) * ν i
  have hlast : MvPolynomial.map f (Q (Fin.last 3)) =
      coefficientLinearForm (fun i => f (ℓ i)) ^ (d - 1) * coefficientLinearForm mE := by
    rw [hQ]
    exact cone_ternary_last_factor_of_scaled_linear_form hd τ ν V u a b _ (α j) (hlin.trans hαform)
  obtain ⟨m, _hm, hQlast⟩ := normalized_linear_power_quotient_descends f f.injective
    (Q (Fin.last 3)) ℓ j hℓj (d - 1) mE hlast
  refine ⟨ℓ, ?_, r, (fun i => (hr i).1), m, hQlast⟩
  intro hz
  have he := hℓj
  rw [hz] at he
  exact zero_ne_one he

end DimensionFourDependence
