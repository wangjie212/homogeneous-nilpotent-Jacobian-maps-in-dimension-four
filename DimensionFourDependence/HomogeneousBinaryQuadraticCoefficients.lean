import DimensionFourDependence.PlanarGroupedHomogeneousCoefficients

/-! # Coefficient presentation of a homogeneous binary quadratic -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K

theorem binary_exponent_degree_eq_two (m : Fin 2 →₀ ℕ) (hm : m.degree = 2) :
    m = Finsupp.single 0 2 ∨
      m = Finsupp.single 0 1 + Finsupp.single 1 1 ∨ m = Finsupp.single 1 2 := by
  have he : m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
    ext i
    fin_cases i <;> simp
  have hs : m 0 + m 1 = 2 := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hm
  generalize h₀ : m 0 = a at *
  generalize h₁ : m 1 = b at *
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> simp_all

/-- Only the three monomials of total degree two contribute to the form. -/
theorem homogeneous_binary_quadratic_expansion (p : R₂) (hp : p.IsHomogeneous 2) :
    ∃ a b c : K, p = C a * X 0 ^ 2 + C b * X 0 * X 1 + C c * X 1 ^ 2 := by
  classical
  let a : Fin 2 →₀ ℕ := Finsupp.single 0 2
  let b : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
  let c : Fin 2 →₀ ℕ := Finsupp.single 1 2
  refine ⟨p.coeff a, p.coeff b, p.coeff c, ?_⟩
  have he : p = monomial a (p.coeff a) + monomial b (p.coeff b) + monomial c (p.coeff c) := by
    ext m
    by_cases hm : m.degree = 2
    · rcases binary_exponent_degree_eq_two m hm with rfl | rfl | rfl <;>
        simp [a, b, c, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_two]
    · have hc : p.coeff m = 0 := by
        by_contra h
        apply hm
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp h
      have hd : a.degree = 2 ∧ b.degree = 2 ∧ c.degree = 2 := by
        simp [a, b, c, Finsupp.degree_eq_sum, Fin.sum_univ_two]
      have hne' (j : Fin 2 →₀ ℕ) (hj : j.degree = 2) : j ≠ m :=
        fun heq => hm (heq ▸ hj)
      have hne : a ≠ m ∧ b ≠ m ∧ c ≠ m := ⟨hne' _ hd.1, hne' _ hd.2.1, hne' _ hd.2.2⟩
      simp [hc, coeff_monomial, hne.1, hne.2.1, hne.2.2]
  calc
    p = _ := he
    _ = _ := by
      simp only [a, b, c, ← C_mul_X_pow_eq_monomial, monomial_add_single,
        pow_one, mul_assoc]

end DimensionFourDependence.Shear
