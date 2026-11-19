import DimensionFourDependence.PlanarShearPolynomialRepresentation
import DimensionFourDependence.PlanarShearParameterDegrees

/-! # The nonzero pair in Proposition 6.3 -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 900000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "L" => FractionRing R₂
local notation "Aₗ" => MvPolynomial (Fin 2) L
local notation "ι" => (algebraMap R₂ L)

/-- The exact normalized form (6.8) and its weighted coefficients (6.9). -/
theorem normalized_planar_nonzero_pair_constructs_shear
    (A : Fin 2 → R₄) {d : ℕ} (hA : ∀ i, (A i).IsHomogeneous d)
    (hN : IsNilpotent (planarActiveJacobian A))
    (h0 : planarActiveNormalized (A 0) ≠ 0) (h1 : planarActiveNormalized (A 1) ≠ 0) :
    ∃ (r : ℕ) (a b : R₂) (f : Polynomial R₂),
      a ≠ 0 ∧ b ≠ 0 ∧ IsRelPrime a b ∧ a.IsHomogeneous r ∧ b.IsHomogeneous r ∧
      2 * r + 1 ≤ d ∧ f.coeff 0 = 0 ∧ f ≠ 0 ∧
      (∀ j, f.coeff j ≠ 0 →
        j * (r + 1) ≤ d - r ∧ (f.coeff j).IsHomogeneous (d - r - j * (r + 1))) ∧
      ![planarActiveNormalized (A 0), planarActiveNormalized (A 1), 0, 0] =
        perturbation4 a b (planarInvariantParameter3 f) := by
  obtain ⟨r, a, b, q, _, ha, hb, hq, hc, had, hbd, hqd, hx, hy⟩ :=
    normalized_planar_pair_constructs_primitive_shear_factor A hA hN h0 h1
  obtain ⟨g, hg⟩ :=
    normalized_planar_shear_multiplier_is_polynomial_over_fraction_field A hN a b ha q hx hy
  obtain ⟨f, hf⟩ := polynomial_in_coprime_linear_invariant_coefficients_descend
    a b hc (planarCoefficientEquiv q) g hg
  have he : activeFractionPolynomial q =
      Polynomial.aeval (C (ι a) * X 0 + C (ι b) * X 1 : Aₗ) (f.map ι) := by
    rwa [hf]
  have hparam := parameter4_eq_of_fraction_field_representation a b q f he
  have hzero := normalized_planar_shear_parameter_constant_zero (A 0) q a b hb hx f he
  have hn : f ≠ 0 := by
    intro h
    apply hq
    apply activeFractionPolynomial_injective
    change activeFractionPolynomial q = activeFractionPolynomialHom 0
    simpa only [h, Polynomial.map_zero, map_zero] using he
  have hweights (j : ℕ) (hj : f.coeff j ≠ 0) :
      j * (r + 1) ≤ d - r ∧ (f.coeff j).IsHomogeneous (d - r - j * (r + 1)) :=
    homogeneous_planar_shear_parameter_coeff_degree q hqd hq a b had ha f he j hj
  have hdegree : 2 * r + 1 ≤ d := by
    classical
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hn
    have hjne := Polynomial.mem_support_iff.mp hj
    have hjpos : 1 ≤ j := by
      by_contra! hjle
      exact hjne (by rwa [Nat.lt_one_iff.mp hjle])
    have hbound := (hweights j hjne).1
    have hmul := Nat.mul_le_mul_right (r + 1) hjpos
    rw [one_mul] at hmul
    omega
  refine ⟨r, a, b, f, ha, hb, hc, had, hbd, hdegree, hzero, hn, hweights, ?_⟩
  funext i
  fin_cases i
  · exact hx.trans (congrArg (base4 b * ·) hparam)
  · change planarActiveNormalized (A 1) = -(base4 a * parameter4 a b (planarInvariantParameter3 f))
    rw [hy, hparam]
    exact neg_mul _ _
  · rfl
  · rfl

end DimensionFourDependence.Shear
