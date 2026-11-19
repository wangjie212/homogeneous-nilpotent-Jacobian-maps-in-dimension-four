import DimensionFourDependence.LinearPowerCoefficientDescent
import DimensionFourDependence.ConeTernaryForms

/-! # The common cone linear factor descends with the entire ternary forms

The first three cone forms have the same linear power over the actual
coefficient branch. Any nonzero descended member recovers its normalized
covector over the original coefficient field. Every first-three member
then has that same factor, with scalar coefficient in the original field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {C E : Type*} [Field C] [Field E] [CharZero E]

/-- Exact descent of the whole cone coordinate forms constructs the
common linear factor and its first-three scalar coefficients over the
original field, from any nonzero first coordinate. -/
theorem cone_ternary_forms_construct_rational_linear_power_factor
    (f : C →+* E) (Q : Fin 4 → MvPolynomial (Fin 3) C)
    {d : ℕ} (hd : 0 < d) (τ ν V : Fin 3 → E) (u a b : E)
    (hQ : ∀ i, MvPolynomial.map f (Q i) = coneTernaryForms d τ ν V u a b i)
    (hQ0 : Q 0 ≠ 0) :
    ∃ ℓ : Fin 3 → C, ℓ ≠ 0 ∧ ∃ r : Fin 3 → C,
      ∀ i : Fin 3, Q i.castSucc = MvPolynomial.C (r i) * linearFormPolynomial ℓ ^ d := by
  classical
  let α : Fin 3 → E := fun i => u * τ i
  have hlin : MvPolynomial.C u * linearFormPolynomial τ = linearFormPolynomial α := by
    simp only [linearFormPolynomial, α, map_mul, Finset.mul_sum, mul_assoc]
  have hpower (i : Fin 3) : MvPolynomial.map f (Q i.castSucc) =
      MvPolynomial.C (V i) * linearFormPolynomial α ^ d := by
    rw [hQ, coneTernaryForms_castSucc, hlin]
  obtain ⟨j, ℓ, hℓj, _hℓ, r, hr⟩ := nonzero_linear_power_family_descends
    f (fun i : Fin 3 => Q i.castSucc) hd α V 0 hQ0 hpower
  refine ⟨ℓ, ?_, r, fun i => (hr i).1⟩
  intro hz
  have he := hℓj
  rw [hz] at he
  exact zero_ne_one he

end DimensionFourDependence
