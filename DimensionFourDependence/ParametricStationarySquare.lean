import DimensionFourDependence.WeightedStationaryPowerSquare

/-! # Actual stationary ruling coordinates construct the square form of Section 5.4 -/

namespace DimensionFourDependence

open Matrix

universe u
set_option maxHeartbeats 3000000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- A nonzero stationary function with nonzero Euler weight forces
an actual nonzero transverse coordinate to the given nonzero direction. -/
theorem stationary_nonzero_weight_exists_transverse_coordinate
    (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hv : v ≠ 0) (f : F) (hf : f ≠ 0) (w : F) (hw : w ≠ 0)
    (hDf : coordinateEuler v δ f = 0) (hweight : coordinateEuler y δ f = w * f) :
    ∃ a b : Fin n, v a ≠ 0 ∧ y b - v b * (y a / v a) ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  let r := y a / v a
  by_contra h
  have hline (b : Fin n) : y b = v b * r := by
    by_contra hb
    exact h ⟨a, b, ha, sub_ne_zero.mpr hb⟩
  have hED (x : F) : coordinateEuler y δ x = r * coordinateEuler v δ x := by
    simp only [coordinateEuler_apply, hline, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hED, hDf, mul_zero] at hweight
  exact (mul_ne_zero hw hf) hweight.symm

/-- The original parameter-algebraic stationary ruling direction and
Euler weight 2/d construct their own transverse square identity with
an actual nonzero scalar algebraic over the original ruling field. -/
theorem parametric_coordinate_stationary_weight_two_square
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hv : v ≠ 0) (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (htD : coordinateEuler v δ (p RatFunc.X) = 0)
    (htE : coordinateEuler y δ (p RatFunc.X) = 0)
    (htr : Algebra.trdeg K F ≤ 3) (d : ℕ) (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hDf : coordinateEuler v δ f = 0)
    (hweight : coordinateEuler y δ f = (2 * (d : F)⁻¹) * f) :
    ∃ (a b : Fin n) (α : F), v a ≠ 0 ∧ y b - v b * (y a / v a) ≠ 0 ∧
      IsAlgebraic p.fieldRange α ∧ α ≠ 0 ∧
      f ^ d = α * (y b - v b * (y a / v a)) ^ 2 := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let D := coordinateEuler v δ
  let E := coordinateEuler y δ
  have hvD (i : Fin n) : D (v i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p D htD (v i) (halg i)
  have hvE (i : Fin n) : E (v i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p E htE (v i) (halg i)
  have hw : (2 * (d : F)⁻¹) ≠ 0 :=
    mul_ne_zero (by norm_num) (inv_ne_zero (Nat.cast_ne_zero.mpr (by omega)))
  obtain ⟨a, b, ha, hs⟩ := stationary_nonzero_weight_exists_transverse_coordinate
    δ y v hcoord hv f hf _ hw hDf hweight
  let J := p.fieldRange
  letI : CharZero J := charZero_of_injective_algebraMap (algebraMap K J).injective
  have hJD : J ≤ derivationConstants D := by
    rintro _ ⟨r, rfl⟩
    change D (p r) = 0
    rw [rational_parameter_chain_rule p D r, htD, mul_zero]
  have hJE : J ≤ derivationConstants E := by
    rintro _ ⟨r, rfl⟩
    change E (p r) = 0
    rw [rational_parameter_chain_rule p E r, htE, mul_zero]
  let D₀ := derivationOverConstantSubfield D J hJD
  let E₀ := derivationOverConstantSubfield E J hJE
  let r := y a / v a
  let s := y b - v b * r
  have hrD : D₀ r = 1 := by
    change D (y a / v a) = 1
    rw [D.leibniz_div, coordinate_direction_coordinate δ y v hcoord a, hvD a]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp
  have hrE : E₀ r = r := by
    change E (y a / v a) = y a / v a
    have he := derivation_quotient_weight E (y a) (v a) 1 0
      (by simpa only [one_mul] using coordinate_direction_coordinate δ y y hcoord a) (by simpa using hvE a)
    simpa only [sub_zero, one_mul] using he
  have hsD : D₀ s = 0 := by
    change D (y b - v b * r) = 0
    rw [map_sub, D.leibniz, hvD b]
    rw [show D r = 1 from hrD, show D (y b) = v b from coordinate_direction_coordinate δ y v hcoord b]
    simp [smul_eq_mul]
  have hsE : E₀ s = s := by
    change E (y b - v b * r) = y b - v b * r
    rw [map_sub, E.leibniz, hvE b]
    rw [show E r = r from hrE, show E (y b) = y b from coordinate_direction_coordinate δ y y hcoord b]
    simp [smul_eq_mul]
  have hcommDE (x : F) : D₀ (E₀ x) = E₀ (D₀ x) + D₀ x :=
    coordinate_direction_euler_commutator δ y v hcoord hcomm hvE x
  obtain ⟨α, hαalg, hα, hpower⟩ := stationary_weight_two_power_constructs_algebraic_square_scalar
    D₀ E₀ r s hrD hsD hsE hs hcommDE (trdeg_over_rational_parameter_image_le_two p htr)
      d hd f hf hDf hweight
  exact ⟨a, b, α, ha, hs, hαalg, hα, hpower⟩

end DimensionFourDependence
