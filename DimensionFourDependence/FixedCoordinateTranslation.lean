import DimensionFourDependence.NormalizedFixedCoordinateReduction
import DimensionFourDependence.Tame

/-! # The elementary translation removed in Section 6.2 -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- Each target correction depends only on the fixed final coordinate. -/
theorem fixed_coordinate_power_translation_notMem
    (c : K) (d : ℕ) (i : Fin 3) :
    i.castSucc ∉ (C c * (X (Fin.last 3) : MvPolynomial (Fin 4) K) ^ d).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
  · simpa using h
  · have hv := vars_pow (X (Fin.last 3) : MvPolynomial (Fin 4) K) d h
    simp only [vars_X, Finset.mem_singleton] at hv
    exact Fin.castSucc_ne_last i hv

/-- An actual elementary target translation in one active coordinate. -/
noncomputable def fixedCoordinateTranslationFactor4 (c : Fin 3 → K) (d : ℕ) (i : Fin 3) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  Tame.elementary i.castSucc (C (c i) * X (Fin.last 3) ^ d)
    (fixed_coordinate_power_translation_notMem (c i) d i)

theorem fixedCoordinateTranslationFactor4_X
    (c : Fin 3 → K) (d : ℕ) (i : Fin 3) (j : Fin 4) :
    fixedCoordinateTranslationFactor4 c d i (X j) =
      X j + if j = i.castSucc then C (c i) * X (Fin.last 3) ^ d else 0 :=
  Tame.elementary_X _ _ _ j

/-- The three elementary maps giving `τ_c` in equation (6.7). -/
noncomputable def fixedCoordinateTranslation4 (c : Fin 3 → K) (d : ℕ) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  fixedCoordinateTranslationFactor4 c d 0 *
    fixedCoordinateTranslationFactor4 c d 1 * fixedCoordinateTranslationFactor4 c d 2

/-- All four polynomial coordinates of the target correction. -/
theorem fixedCoordinateTranslation4_X (c : Fin 3 → K) (d : ℕ) (j : Fin 4) :
    fixedCoordinateTranslation4 c d (X j) =
      X j + Fin.lastCases 0 (fun i : Fin 3 => C (c i) * X (Fin.last 3) ^ d) j := by
  have hC (i : Fin 3) (a : K) : fixedCoordinateTranslationFactor4 c d i (C a) = C a :=
    (fixedCoordinateTranslationFactor4 c d i).commutes a
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.lastCases_last, add_zero]
    simp [fixedCoordinateTranslation4, AlgEquiv.mul_apply,
      fixedCoordinateTranslationFactor4_X]
  · rw [Fin.lastCases_castSucc]
    fin_cases i <;>
      simp [fixedCoordinateTranslation4, AlgEquiv.mul_apply,
        fixedCoordinateTranslationFactor4_X, map_add, map_mul, map_pow, hC]

/-- The removed translation is tame over the original coefficient field. -/
theorem fixedCoordinateTranslation4_tame (c : Fin 3 → K) (d : ℕ) :
    fixedCoordinateTranslation4 c d ∈ Tame.subgroup K 4 := by
  have hm (i : Fin 3) : fixedCoordinateTranslationFactor4 c d i ∈ Tame.subgroup K 4 :=
    Tame.elementary_mem _ _ _
  exact (Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem (hm 0) (hm 1)) (hm 2)

/-- Equation (6.7) as equality on the whole original polynomial algebra.
The reversed order is the pullback of ordinary point-map composition. -/
theorem fixed_coordinate_chart_target_translation_factorization
    (B : Fin 3 → MvPolynomial (Fin 4) K) {d : ℕ}
    (hB : ∀ i, (B i).IsHomogeneous d) :
    aeval (fun j : Fin 4 => X j + Fin.lastCases 0 B j) =
      (aeval (fun j : Fin 4 => X j + Fin.lastCases 0
        (fun i : Fin 3 => lastCoordinateHomogenize (normalizedFixedCoordinateChart B i) d) j)).comp
        (fixedCoordinateTranslation4 (fixedCoordinateChartConstants B) d).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, aeval_X, AlgEquiv.coe_toAlgHom, fixedCoordinateTranslation4_X]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.lastCases_last, map_add, aeval_X, map_zero, add_zero]
  · simp only [Fin.lastCases_castSucc, map_add, aeval_X, map_mul, aeval_C,
      algebraMap_eq, map_pow, Fin.lastCases_last, add_zero]
    rw [(normalizedFixedCoordinateChart_homogeneous_reconstruction B hB i).2]
    ring

end DimensionFourDependence
