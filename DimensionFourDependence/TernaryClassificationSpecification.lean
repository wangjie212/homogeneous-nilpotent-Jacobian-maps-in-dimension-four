import DimensionFourDependence.TamenessTheoremSpecification
import DimensionFourDependence.OriginalMapTamenessFromTernaryNormalForm
import DimensionFourDependence.FixedCoordinateChartNilpotence

/-! # The exact statement of Theorem 6.1 and its use on the independent chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 950000

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K

/-- The cited ternary classification, as a proposition over the original
field. Its proof is a separate requirement of the full formalization. -/
def TernaryNilpotentClassification (K : Type*) [Field K] : Prop :=
  ∀ h : Fin 3 → MvPolynomial (Fin 3) K,
    (∀ i, aeval (fun _ : Fin 3 => (0 : K)) (h i) = 0) →
    IsNilpotent (jac h) → ¬ComponentsDependent h →
    ∃ (T S : Matrix (Fin 3) (Fin 3) K) (P : Polynomial K),
      T * S = 1 ∧ S * T = 1 ∧ 0 < P.natDegree ∧ P.eval 0 = 0 ∧
      linearPolynomialConjugate T S h = TernaryNormalForm.perturbation3 P

/-- The exact independent-branch implication, assuming the classification
supplies the prescribed constant conjugacy over the original field. -/
theorem original_tameness_of_independent_chart_of_ternary_classification
    (hclass : TernaryNilpotentClassification K)
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : HasIndependentNormalizedTernaryChart H) :
    ∃ E : R₄ ≃ₐ[K] R₄, E ∈ Tame.subgroup K 4 ∧ ∀ i, E (X i) = X i + H i := by
  obtain ⟨U, V, B, hUV, hVU, hB, hb⟩ := hind
  have hn := linearPolynomialConjugate_nilpotent U V hUV hVU H hN
  rw [hB] at hn
  have hchart := normalizedFixedCoordinateChart_nilpotent_of_full (n := 3) B hn
  obtain ⟨T, S, P, hTS, hST, hP, _, hnormal⟩ :=
    hclass (normalizedFixedCoordinateChart B) (normalizedFixedCoordinateChart_origin B) hchart hb
  exact TernaryNormalForm.original_tameness_of_ternary_normal_form H hH
    U V hUV hVU B hB T S hTS hST P hP hnormal

end DimensionFourDependence
