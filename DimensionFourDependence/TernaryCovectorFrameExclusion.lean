import DimensionFourDependence.FixedCovectorCoordinateChoice
import DimensionFourDependence.TernaryFixedAxisProjectionPolynomial

/-! # A nonzero two-column determinant excludes fixed-plane linear forms -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]
local notation "R₀" => MvPolynomial (Fin 3) K

/-- A polynomial in the fixed source coordinates has zero partials
in both moving coordinates. -/
theorem ternary_fixed_axis_moving_partial_zero
    (P : MvPolynomial (Fin 1) K) (j : Fin 3) (hj0 : j ≠ 0) :
    pderiv j (ternaryFixedAxisCoefficientMap K P) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hj
  obtain ⟨i, _hi, he⟩ := mem_vars_rename (![0] : Fin 1 → Fin 3) P hj
  fin_cases i
  exact hj0 he.symm

/-- A nonzero determinant of a covector pair on the two moving
columns prevents every nonzero member of that covector plane from
pulling back to the fixed-coordinate polynomial ring. -/
theorem ternary_nonzero_covector_column_minor_excludes_fixed_plane_linear_form
    (T : Matrix (Fin 3) (Fin 3) K) (μ ν : Fin 3 → K)
    (hdet : (∑ i, μ i * T i 1) * (∑ i, ν i * T i 2) -
      (∑ i, ν i * T i 1) * (∑ i, μ i * T i 2) ≠ 0)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    linearPolynomialPullback T (linearFormPolynomial (a • μ + b • ν)) ∉
      Set.range (ternaryFixedAxisCoefficientMap K) := by
  rintro ⟨P, hP⟩
  have hc (j : Fin 3) (hj0 : j ≠ 0) :
      (∑ i, (a • μ + b • ν) i * T i j) = 0 := by
    have he := congrArg (pderiv j) hP
    rw [ternary_fixed_axis_moving_partial_zero P j hj0,
      linearPolynomialPullback_linear_form, linearFormPolynomial_pderiv] at he
    exact C_injective (Fin 3) K (he.symm.trans (map_zero C).symm)
  have hsum (j : Fin 3) :
      (∑ i, (a • μ + b • ν) i * T i j) =
        a * (∑ i, μ i * T i j) + b * (∑ i, ν i * T i j) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have hc1 := hc 1 (by decide)
  have hc2 := hc 2 (by decide)
  rw [hsum] at hc1 hc2
  have ha : a = 0 := (mul_eq_zero.mp (show
      a * ((∑ i, μ i * T i 1) * (∑ i, ν i * T i 2) -
        (∑ i, ν i * T i 1) * (∑ i, μ i * T i 2)) = 0 by
      linear_combination (∑ i, ν i * T i 2) * hc1 - (∑ i, ν i * T i 1) * hc2)).resolve_right hdet
  have hb : b = 0 := (mul_eq_zero.mp (show
      b * ((∑ i, μ i * T i 1) * (∑ i, ν i * T i 2) -
        (∑ i, ν i * T i 1) * (∑ i, μ i * T i 2)) = 0 by
      linear_combination (∑ i, μ i * T i 1) * hc2 - (∑ i, μ i * T i 2) * hc1)).resolve_right hdet
  exact hab.elim (fun h => h ha) (fun h => h hb)

/-- The same exclusion applies to every nonzero covector in the
entire original two-dimensional span, without supplied coefficients. -/
theorem ternary_nonzero_covector_column_minor_excludes_entire_plane
    (T : Matrix (Fin 3) (Fin 3) K) (μ ν : Fin 3 → K)
    (hdet : (∑ i, μ i * T i 1) * (∑ i, ν i * T i 2) -
      (∑ i, ν i * T i 1) * (∑ i, μ i * T i 2) ≠ 0)
    (w : Fin 3 → K) (hw : w ∈ Submodule.span K ({μ, ν} : Set (Fin 3 → K))) (hw0 : w ≠ 0) :
    linearPolynomialPullback T (linearFormPolynomial w) ∉ Set.range (ternaryFixedAxisCoefficientMap K) := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
  have hn : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    rw [← hab, h.1, h.2, zero_smul, zero_smul, add_zero]
  rw [← hab]
  exact ternary_nonzero_covector_column_minor_excludes_fixed_plane_linear_form T μ ν hdet a b hn

end DimensionFourDependence
