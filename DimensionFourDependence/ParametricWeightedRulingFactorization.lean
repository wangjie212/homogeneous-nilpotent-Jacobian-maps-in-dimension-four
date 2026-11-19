import DimensionFourDependence.GaussParameterSurfaceDimension
import DimensionFourDependence.WeightedRulingCoordinates

/-! # Weighted factorization in the actual parameter field

Directional and Euler derivations fixing the actual rational parameter
are derivations over its actual field image. Parameter-algebraic direction
coordinates are constants for both. The dimension tower, actual
longitudinal and transverse coordinates, and Euler commutator therefore
supply every input to the weighted affine-function calculation.
-/

namespace DimensionFourDependence

open Matrix

universe u

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- A parameter-algebraic actual ruling direction and its zero
acceleration construct the root factorization over the actual parameter
image, with algebraic coefficients and explicit original linear coordinates. -/
theorem parametric_coordinate_weighted_root_factorization
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hv : v ≠ 0) (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (htD : coordinateEuler v δ (p RatFunc.X) = 0)
    (htE : coordinateEuler y δ (p RatFunc.X) = 0)
    (htr : Algebra.trdeg K F ≤ 3) {d : ℕ} (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hsecond : coordinateEuler v δ (coordinateEuler v δ f) = 0)
    (hweight : coordinateEuler y δ f = (1 + (d : F)⁻¹) * f) :
    ∃ (a b : Fin n) (α β γ ρ : F), v a ≠ 0 ∧ y b - v b * (y a / v a) ≠ 0 ∧
      IsAlgebraic p.fieldRange α ∧ IsAlgebraic p.fieldRange β ∧ IsAlgebraic p.fieldRange γ ∧
      α ≠ 0 ∧ ρ ≠ 0 ∧
      f = (β * (y a / v a) + γ * (y b - v b * (y a / v a))) * ρ ∧
      ρ ^ d = α * (y b - v b * (y a / v a)) ∧
      coordinateEuler v δ ρ = 0 ∧ (β ≠ 0 ∨ γ ≠ 0) := by
  let D := coordinateEuler v δ
  let E := coordinateEuler y δ
  have hvD (i : Fin n) : D (v i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p D htD (v i) (halg i)
  have hvE (i : Fin n) : E (v i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p E htE (v i) (halg i)
  obtain ⟨a, b, ha, hs⟩ := weighted_zero_acceleration_exists_transverse_coordinate δ y v hcoord hv hvD
    hd f hf hsecond hweight
  let J := p.fieldRange
  let : CharZero J := charZero_of_injective_algebraMap (algebraMap K J).injective
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
  obtain ⟨α, β, γ, ρ, hα, hβ, hγ, hα0, hρ0, hfactor, hroot, hρD, hlinear⟩ :=
    weighted_affine_function_root_factorization D₀ E₀ r s hrD hrE hsD hsE hs hcommDE
      (trdeg_over_rational_parameter_image_le_two p htr) hd f hf hsecond hweight
  exact ⟨a, b, α, β, γ, ρ, ha, hs, hα, hβ, hγ, hα0, hρ0, hfactor, hroot, hρD, hlinear⟩

end DimensionFourDependence
