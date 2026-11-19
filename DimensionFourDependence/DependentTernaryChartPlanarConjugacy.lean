import DimensionFourDependence.FixedCoordinateTamenessReduction
import DimensionFourDependence.FixedCoordinateChartLinearConjugacy

/-! # A dependent normalized ternary chart gives two fixed coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K

theorem normalizedFixedCoordinateHomogeneousCore_isHomogMap
    (B : Fin 3 → R₄) {d : ℕ} (hB : ∀ i, (B i).IsHomogeneous d) :
    IsHomogMap (normalizedFixedCoordinateHomogeneousCore B d) d := by
  intro j
  refine Fin.lastCases (motive := fun j =>
    (normalizedFixedCoordinateHomogeneousCore B d j).IsHomogeneous d) ?_ (fun i => ?_) j
  · simpa only [normalizedFixedCoordinateHomogeneousCore, Fin.lastCases_last] using
      (isHomogeneous_zero (Fin 4) K d)
  · simpa only [normalizedFixedCoordinateHomogeneousCore, Fin.lastCases_castSucc] using
      lastCoordinateHomogenize_isHomogeneous _ _
        (normalizedFixedCoordinateChart_homogeneous_reconstruction B hB i).1

/-- A constant relation on the normalized chart makes the penultimate
homogeneous component vanish under a constant conjugacy fixing the last
coordinate. The exact polynomial vanishing follows from homogeneity. -/
theorem dependent_normalized_ternary_chart_constructs_planar_conjugacy
    (B : Fin 3 → R₄) {d : ℕ} (hB : ∀ i, (B i).IsHomogeneous d)
    (hdep : ComponentsDependent (normalizedFixedCoordinateChart B)) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K) (A : Fin 2 → R₄),
      T * S = 1 ∧ S * T = 1 ∧
      linearPolynomialConjugate T S (normalizedFixedCoordinateHomogeneousCore B d) =
        ![A 0, A 1, 0, 0] := by
  obtain ⟨U, V, hUV, hVU, hz⟩ :=
    constant_relation_constructs_zero_component_conjugacy (normalizedFixedCoordinateChart B)
      hdep (Fin.last 2)
  let G := normalizedFixedCoordinateHomogeneousCore B d
  let T : Matrix (Fin 4) (Fin 4) K := vertexPreservingMatrix U
  let S : Matrix (Fin 4) (Fin 4) K := vertexPreservingMatrix V
  have hTS : T * S = 1 := by
    change vertexPreservingMatrix U * vertexPreservingMatrix V = 1
    rw [vertexPreservingMatrix_mul, hUV, vertexPreservingMatrix_one]
  have hST : S * T = 1 := by
    change vertexPreservingMatrix V * vertexPreservingMatrix U = 1
    rw [vertexPreservingMatrix_mul, hVU, vertexPreservingMatrix_one]
  have hG : IsHomogMap G d := normalizedFixedCoordinateHomogeneousCore_isHomogMap B hB
  have hlast : G (Fin.last 3) = 0 := by
    simp only [G, normalizedFixedCoordinateHomogeneousCore, Fin.lastCases_last]
  have hchart : (fun i : Fin 3 => lastCoordinateDehomogenize (G i.castSucc)) =
      normalizedFixedCoordinateChart B := by
    funext i
    simp only [G, normalizedFixedCoordinateHomogeneousCore, Fin.lastCases_castSucc,
      lastCoordinateDehomogenize_homogenize]
  let J := linearPolynomialConjugate T S G
  have hlast' : J 3 = 0 := vertexPreserving_conjugate_last_zero U V G hlast
  have hsecond : J 2 = 0 := by
    change J (Fin.last 2).castSucc = 0
    apply lastCoordinateDehomogenize_injective_on_homogeneous_degree _ _
      (linearPolynomialConjugate_homogeneous T S G hG (Fin.last 2).castSucc)
      (isHomogeneous_zero _ _ _)
    change lastCoordinateDehomogenize
      (linearPolynomialConjugate (vertexPreservingMatrix U) (vertexPreservingMatrix V)
        G (Fin.last 2).castSucc) = lastCoordinateDehomogenize (0 : R₄)
    rw [lastCoordinateDehomogenize_vertexPreserving_conjugate U V G, hchart, map_zero]
    exact hz
  refine ⟨T, S, ![J 0, J 1], hTS, hST, ?_⟩
  change J = _
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact hsecond
  · exact hlast'

end DimensionFourDependence
