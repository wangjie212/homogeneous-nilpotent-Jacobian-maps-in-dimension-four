import DimensionFourDependence.PlanarShearCoefficientRing

/-! # Active monomial coefficients retain their prescribed homogeneous base degrees -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1400000

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "A₂" => MvPolynomial (Fin 2) R₂

noncomputable def activeExponents (m : Fin 4 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1)

noncomputable def baseExponents (m : Fin 4 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m 2) + Finsupp.single 1 (m 3)

theorem activeExponents_degree_add_baseExponents_degree (m : Fin 4 →₀ ℕ) :
    (activeExponents m).degree + (baseExponents m).degree = m.degree := by
  simp only [activeExponents, baseExponents, map_add, Finsupp.degree_single]
  rw [Finsupp.degree_eq_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  exact Nat.add_assoc (m 0) (m 1) (m 2 + m 3)

/-- Regrouping an original monomial keeps exactly its two active
exponents and puts the remaining exponents into its base coefficient. -/
theorem planarCoefficientEquiv_monomial (m : Fin 4 →₀ ℕ) (c : K) :
    planarCoefficientEquiv (monomial m c : R₄) =
      (monomial (activeExponents m) (monomial (baseExponents m) c) : A₂) := by
  have hx : planarCoefficientEquiv (X 0 : R₄) = (X 0 : A₂) := planarCoefficientEquiv_X_active (0 : Fin 2)
  have hy : planarCoefficientEquiv (X 1 : R₄) = (X 1 : A₂) := planarCoefficientEquiv_X_active (1 : Fin 2)
  have hz : planarCoefficientEquiv (X 2 : R₄) = (C (X 0) : A₂) := planarCoefficientEquiv_X_base (0 : Fin 2)
  have ht : planarCoefficientEquiv (X 3 : R₄) = (C (X 1) : A₂) := planarCoefficientEquiv_X_base (1 : Fin 2)
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
  simp only [map_mul, map_pow, planarCoefficientEquiv_C, hx, hy, hz, ht]
  simp only [activeExponents, baseExponents, monomial_add_single, ← C_mul_X_pow_eq_monomial,
    map_mul, map_pow]
  ring

/-- In a homogeneous form of total degree d, the coefficient of an
active monomial of degree k is homogeneous of degree d-k. -/
theorem homogeneous_planarCoefficientEquiv_coeff (p : R₄) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : Fin 2 →₀ ℕ) : ((planarCoefficientEquiv p).coeff m).IsHomogeneous (d - m.degree) := by
  classical
  have he : planarCoefficientEquiv p =
      ∑ e ∈ p.support, (monomial (activeExponents e) (monomial (baseExponents e) (p.coeff e)) : A₂) := by
    conv_lhs => rw [p.as_sum, map_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact planarCoefficientEquiv_monomial e (p.coeff e)
  rw [he, coeff_sum]
  apply IsHomogeneous.sum
  intro e he'
  rw [coeff_monomial]
  by_cases hm : activeExponents e = m
  · rw [if_pos hm]
    have hd := hp.degree_eq_sum_deg_support he'
    have hdeg : e.degree = d := by simpa only [Finsupp.degree_apply, Finsupp.sum] using hd.symm
    have hsplit := activeExponents_degree_add_baseExponents_degree e
    rw [hm, hdeg] at hsplit
    exact isHomogeneous_monomial _ (by omega)
  · rw [if_neg hm]
    exact isHomogeneous_zero _ _ _

end DimensionFourDependence.Shear
