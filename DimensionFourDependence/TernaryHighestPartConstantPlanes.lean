import DimensionFourDependence.TriangularTernaryBasepointCover
import DimensionFourDependence.HomogeneousTernaryTriangularFrame
import DimensionFourDependence.LinearConjugacyEvaluationExtension
import DimensionFourDependence.TernaryHighestHomogeneousPart

/-! # The finite original constant-plane bound for the leading ternary map -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v

set_option maxHeartbeats 1900000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "M₃" => Matrix (Fin 3) (Fin 3) K

private theorem ternary_linearPolynomialConjugate_one (H : Fin 3 → R₃) :
    linearPolynomialConjugate (1 : M₃) 1 H = H := by
  have h : linearPolynomialMap (1 : M₃) = (X : Fin 3 → R₃) := by
    funext i
    simp [linearPolynomialMap, Matrix.one_apply, eq_comm]
  funext i
  simp [linearPolynomialConjugate, linearPolynomialPullback, h, Matrix.one_apply]

/-- The common zeros of a nonzero homogeneous nilpotent ternary map
lie in finitely many planes defined over the original closed field. -/
theorem homogeneous_ternary_common_zeros_constant_plane_cover
    (H : Fin 3 → R₃) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hne : H ≠ 0) :
    ∃ C₀ : Finset (Fin 3 → K), (∀ l ∈ C₀, l ≠ 0) ∧
      ∀ (F : Type v) [Field F] [Algebra K F] (e : Fin 3 → F),
        (∀ i, aeval e (H i) = 0) → ∃ l ∈ C₀, aeval e (linearFormPolynomial l) = 0 := by
  classical
  obtain ⟨T, S, P, c, hTS, hST, hP, htri⟩ :=
    homogeneous_ternary_nilpotent_constructs_triangular_frame H hd hH hN
  have hNonzero : P ≠ 0 ∨ c ≠ 0 := by
    by_contra! h
    have hZ : linearPolynomialConjugate T S H = 0 := by
      rw [htri, h.1, h.2, map_zero, map_zero, zero_mul]
      funext i
      fin_cases i <;> rfl
    have hBack := linearPolynomialConjugate_compose T S S T H
    rw [hZ, hTS, ternary_linearPolynomialConjugate_one] at hBack
    apply hne
    rw [← hBack]
    funext i
    simp [linearPolynomialConjugate, linearPolynomialPullback]
  obtain ⟨C₀, hC, hcover⟩ := triangular_ternary_common_zeros_constant_plane_cover P hP c hNonzero
  let L : (Fin 3 → K) → (Fin 3 → K) := fun l => l ᵥ* S
  refine ⟨C₀.image L, ?_, ?_⟩
  · intro l hl hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    apply hC a ha
    calc
      a = (L a) ᵥ* T := by
        change a = (a ᵥ* S) ᵥ* T
        rw [vecMul_vecMul, hST, vecMul_one]
      _ = 0 := by rw [hz, zero_vecMul]
  · intro F _ _ e he
    let e' := S.map (algebraMap K F) *ᵥ e
    have hh := linearPolynomialConjugate_aeval_extension_eq_zero T S hTS H e he
    rw [htri] at hh
    obtain ⟨l, hl, hZ⟩ := hcover F e' hh
    refine ⟨L l, Finset.mem_image_of_mem L hl, ?_⟩
    have hL : linearPolynomialPullback S (linearFormPolynomial l) = linearFormPolynomial (L l) := by
      rw [linearPolynomialPullback_linear_form]
      rfl
    rw [← hL, linearPolynomialPullback_aeval_extension]
    exact hZ

/-- A normalized independent ternary perturbation constructs its top
degree and a finite constant-plane bound on the top form's zeros. -/
theorem normalized_ternary_top_form_constructs_constant_planes
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H)) :
    ∃ (d : ℕ) (C₀ : Finset (Fin 3 → K)),
      0 < d ∧ (∀ i, (H i).totalDegree ≤ d) ∧ (∀ l ∈ C₀, l ≠ 0) ∧
      ∀ (F : Type v) [Field F] [Algebra K F] (e : Fin 3 → F),
        (∀ i, aeval e (homogeneousComponent d (H i)) = 0) →
        ∃ l ∈ C₀, aeval e (linearFormPolynomial l) = 0 := by
  obtain ⟨d, hd, hdeg, hne, hhom, hnil⟩ :=
    normalized_ternary_map_constructs_highest_homogeneous_nilpotent H h0 hind hN
  obtain ⟨C₀, hC, hcover⟩ :=
    homogeneous_ternary_common_zeros_constant_plane_cover
      (fun i => homogeneousComponent d (H i)) hd hhom hnil hne
  exact ⟨d, C₀, hd, hdeg, hC, hcover⟩

end DimensionFourDependence
