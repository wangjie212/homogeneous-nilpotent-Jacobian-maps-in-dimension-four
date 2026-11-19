import DimensionFourDependence.HomogeneousBinaryQuadraticCoefficients
import DimensionFourDependence.CoprimeLinearShearCoordinates

/-! # Coprime binary quadratics have a nonzero leading pencil minor -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K

/-- Homogeneity of positive degree rules out units, including when the
homogeneous form is zero. -/
theorem positive_degree_binary_form_not_isUnit (a : R₂) {d : ℕ}
    (ha : a.IsHomogeneous d) (hd : 0 < d) : ¬IsUnit a := by
  intro hu
  have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
  rw [ha.totalDegree hu.ne_zero] at h
  omega

/-- For two coprime quadratics, the square coefficient row is nonzero
and has a nonzero determinant with at least one other row. -/
theorem coprime_binary_quadratic_pencil_leading_minors
    (a b : R₂) (hc : IsRelPrime a b) (ah : a.IsHomogeneous 2) (bh : b.IsHomogeneous 2)
    (a₂ a₁ a₀ b₂ b₁ b₀ : K)
    (ha : a = C a₂ * X 0 ^ 2 + C a₁ * X 0 * X 1 + C a₀ * X 1 ^ 2)
    (hb : b = C b₂ * X 0 ^ 2 + C b₁ * X 0 * X 1 + C b₀ * X 1 ^ 2) :
    b₁ * a₂ - a₁ * b₂ ≠ 0 ∨ b₀ * a₂ - a₀ * b₂ ≠ 0 := by
  have hna := positive_degree_binary_form_not_isUnit a ah (by decide)
  have hnb := positive_degree_binary_form_not_isUnit b bh (by decide)
  have ha0 : a ≠ 0 := by
    intro hz
    exact hnb (hc (by simp [hz] : b ∣ a) (dvd_refl b))
  have hlead : a₂ ≠ 0 ∨ b₂ ≠ 0 := by
    by_contra! h
    have hdiv (u v : K) : (X 1 : R₂) ∣ C u * X 0 * X 1 + C v * X 1 ^ 2 := by
      refine ⟨C u * X 0 + C v * X 1, ?_⟩
      ring
    apply positive_degree_binary_form_not_isUnit (X 1 : R₂) (isHomogeneous_X _ _) (by decide)
    apply hc
    · rw [ha, h.1, map_zero, zero_mul, zero_add]
      exact hdiv _ _
    · rw [hb, h.2, map_zero, zero_mul, zero_add]
      exact hdiv _ _
  by_contra! h
  by_cases h₂ : a₂ ≠ 0
  · have h₁ : b₁ = a₁ * (b₂ / a₂) := by
      field_simp
      exact sub_eq_zero.mp h.1
    have h₀ : b₀ = a₀ * (b₂ / a₂) := by
      field_simp
      exact sub_eq_zero.mp h.2
    have he₂ : b₂ = a₂ * (b₂ / a₂) := by field_simp
    apply hna (hc (dvd_refl a) ?_)
    let s := b₂ / a₂
    have hm₂ : (C b₂ : R₂) = C a₂ * C s := by
      simpa only [map_mul] using congrArg (C : K →+* R₂) he₂
    have hm₁ : (C b₁ : R₂) = C a₁ * C s := by
      simpa only [map_mul] using congrArg (C : K →+* R₂) h₁
    have hm₀ : (C b₀ : R₂) = C a₀ * C s := by
      simpa only [map_mul] using congrArg (C : K →+* R₂) h₀
    refine ⟨C s, ?_⟩
    rw [ha, hb, hm₂, hm₁, hm₀]
    ring
  · have ha₂ : a₂ = 0 := not_ne_iff.mp h₂
    have hb₂ : b₂ ≠ 0 := hlead.resolve_left h₂
    have h₁ : a₁ = 0 := by
      have hm := sub_eq_zero.mp h.1
      rw [ha₂, mul_zero] at hm
      exact (mul_eq_zero.mp hm.symm).resolve_right hb₂
    have h₀ : a₀ = 0 := by
      have hm := sub_eq_zero.mp h.2
      rw [ha₂, mul_zero] at hm
      exact (mul_eq_zero.mp hm.symm).resolve_right hb₂
    exact ha0 (by simp [ha, ha₂, h₁, h₀])

end DimensionFourDependence.Shear
