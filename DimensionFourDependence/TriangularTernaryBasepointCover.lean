import DimensionFourDependence.BinaryHomogeneousConstantRootCover
import DimensionFourDependence.FixedCovectorCoordinateChoice

/-! # The finite constant planes covering the base points in a triangular frame -/

namespace DimensionFourDependence

open MvPolynomial

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₃" => MvPolynomial (Fin 3) K

/-- A nonzero homogeneous triangular triple has constant linear
forms covering all of its common zeros over any extension. -/
theorem triangular_ternary_common_zeros_constant_plane_cover
    (P : R₂) {d : ℕ} (hP : P.IsHomogeneous d) (c : K) (hn : P ≠ 0 ∨ c ≠ 0) :
    ∃ C₀ : Finset (Fin 3 → K), (∀ l ∈ C₀, l ≠ 0) ∧
      ∀ (F : Type v) [Field F] [Algebra K F] (e : Fin 3 → F),
        (∀ i, aeval e ((![rename Fin.succ P, C c * X 2 ^ d, 0] : Fin 3 → R₃) i) = 0) →
        ∃ l ∈ C₀, aeval e (linearFormPolynomial l) = 0 := by
  classical
  by_cases hc : c ≠ 0
  · let l : Fin 3 → K := ![0, 0, 1]
    have hl : l ≠ 0 := by
      intro h
      have he := congrFun h (2 : Fin 3)
      simp [l] at he
    refine ⟨{l}, ?_, ?_⟩
    · intro a h
      simpa only [Finset.mem_singleton.mp h] using hl
    · intro F _ _ e he
      have hz : aeval e (C c * (X 2 : R₃) ^ d) = 0 := he 1
      rw [map_mul, map_pow, aeval_C, aeval_X] at hz
      have hpow := (mul_eq_zero.mp hz).resolve_left ((map_ne_zero (algebraMap K F)).mpr hc)
      have hz' : e 2 = 0 := by
        by_contra he₂
        exact pow_ne_zero d he₂ hpow
      refine ⟨l, Finset.mem_singleton_self _, ?_⟩
      simp [l, linearFormPolynomial, Fin.sum_univ_three, hz']
  · have hne : P ≠ 0 := hn.resolve_right hc
    obtain ⟨S, hS⟩ := homogeneous_binary_zero_has_constant_slope_cover P hP hne
    let l : Fin 3 → K := ![0, 1, 0]
    let m : K → Fin 3 → K := fun a => ![0, -a, 1]
    let C₀ := insert l (S.image m)
    refine ⟨C₀, ?_, ?_⟩
    · intro e he hz
      rcases Finset.mem_insert.mp he with rfl | he
      · have hz' := congrFun hz (1 : Fin 3)
        simp [l] at hz'
      · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
        have hz' := congrFun hz (2 : Fin 3)
        simp [m] at hz'
    · intro F _ _ e he
      have h : aeval e (rename Fin.succ P : R₃) = 0 := he 0
      rw [aeval_rename] at h
      have hcoords : (e ∘ Fin.succ : Fin 2 → F) = ![e 1, e 2] := by
        funext i
        fin_cases i <;> rfl
      rw [hcoords] at h
      rcases hS F (e 1) (e 2) h with hy | ⟨r, hr, hz⟩
      · refine ⟨l, Finset.mem_insert_self _ _, ?_⟩
        simp [l, linearFormPolynomial, Fin.sum_univ_three, hy]
      · refine ⟨m r, Finset.mem_insert_of_mem (Finset.mem_image_of_mem m hr), ?_⟩
        simp [m, linearFormPolynomial, Fin.sum_univ_three, hz]

end DimensionFourDependence
