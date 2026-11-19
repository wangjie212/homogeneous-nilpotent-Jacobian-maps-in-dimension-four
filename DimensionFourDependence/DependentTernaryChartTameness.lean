import DimensionFourDependence.PlanarBlockNilpotence
import DimensionFourDependence.PlanarTamenessReduction
import DimensionFourDependence.StableFixedCoordinateTameness
import DimensionFourDependence.FixedCoordinateChartNilpotence

/-! # The dependent normalized ternary branch in the original coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 900000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- The normalized dependent branch gives an actual one-stably tame
automorphism in all degrees and an ordinary tame automorphism through
degree four. The degree-five assertion reduces to the quadratic pencil family. -/
theorem original_tameness_of_dependent_ternary_chart
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (U V : Matrix (Fin 4) (Fin 4) K) (hUV : U * V = 1) (hVU : V * U = 1)
    (B : Fin 3 → R₄) (hB : linearPolynomialConjugate U V H = Fin.lastCases 0 B)
    (hdep : ComponentsDependent (normalizedFixedCoordinateChart B)) :
    ∃ E : Aut₄, (∀ i, E (X i) = X i + H i) ∧ Shear.IsOneStablyTame E ∧
      (d ≤ 4 → E ∈ Tame.subgroup K 4) ∧
      (d ≤ 5 → Shear.QuadraticPencilShearsTame K → E ∈ Tame.subgroup K 4) := by
  have hBh (i : Fin 3) : (B i).IsHomogeneous d := by
    have hh := linearPolynomialConjugate_homogeneous U V H hH i.castSucc
    simpa only [hB, Fin.lastCases_castSucc] using hh
  have hn := linearPolynomialConjugate_nilpotent U V hUV hVU H hN
  rw [hB] at hn
  have hb := normalizedFixedCoordinateChart_nilpotent_of_full (n := 3) B hn
  let G := normalizedFixedCoordinateHomogeneousCore B d
  have hGn : IsNilpotent (jac G) := normalizedFixedCoordinateHomogeneousCore_nilpotent B hBh hb
  have hGh : IsHomogMap G d := normalizedFixedCoordinateHomogeneousCore_isHomogMap B hBh
  obtain ⟨T, S, A, hTS, hST, hJ⟩ :=
    dependent_normalized_ternary_chart_constructs_planar_conjugacy B hBh hdep
  have hA (i : Fin 2) : (A i).IsHomogeneous d := by
    have hi := linearPolynomialConjugate_homogeneous T S G hGh (i.castAdd 2)
    rw [hJ] at hi
    fin_cases i <;> exact hi
  have hAn := linearPolynomialConjugate_nilpotent T S hTS hST G hGn
  rw [hJ] at hAn
  obtain ⟨e, he, hes, het4, het5⟩ :=
    Shear.homogeneous_planar_nilpotent_tameness A hA
      (planarActiveJacobian_nilpotent_of_full_nilpotent A hAn)
  have he' (i : Fin 4) : e (X i) = X i + linearPolynomialConjugate T S G i := by
    rw [hJ]
    exact he i
  obtain ⟨f, hf, hfs, hft⟩ :=
    one_stably_tame_automorphism_descends_from_constant_linear_conjugacy T S hTS hST G e he' hes
  obtain ⟨E, hE, hEs, hEt⟩ :=
    normalized_fixed_coordinate_core_stable_tameness_restores_original_map H U V hUV hVU B hB hBh f hf hfs
  exact ⟨E, hE, hEs, fun h => hEt (hft (het4 h)), fun h hq => hEt (hft (het5 h hq))⟩

end DimensionFourDependence
