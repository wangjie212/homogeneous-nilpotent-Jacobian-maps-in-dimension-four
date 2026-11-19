import DimensionFourDependence.Proposition66
import DimensionFourDependence.TernaryNormalFormDegreeBound
import DimensionFourDependence.FixedCoordinateChartLinearConjugacy
import DimensionFourDependence.FixedCoordinateTamenessReduction

/-! # Transport the checked canonical tame factorization back to the original map -/

namespace DimensionFourDependence.TernaryNormalForm

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K

/-- If an actual normalized chart has the canonical normal form,
the fixed-coordinate core inherits the explicit tame automorphism.
The matrices are over `K` and their four-variable extensions fix `t`. -/
theorem normalized_homogeneous_core_tame_of_ternary_normal_form
    (B : Fin 3 → R₄) {d : ℕ} (hB : ∀ i, (B i).IsHomogeneous d)
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (P : Polynomial K) (hm : 0 < P.natDegree)
    (hn : linearPolynomialConjugate T S (normalizedFixedCoordinateChart B) = perturbation3 P) :
    ∃ E : R₄ ≃ₐ[K] R₄, E ∈ Tame.subgroup K 4 ∧
      ∀ i, E (X i) = X i + normalizedFixedCoordinateHomogeneousCore B d i := by
  let G := normalizedFixedCoordinateHomogeneousCore B d
  let T' := vertexPreservingMatrix T
  let S' := vertexPreservingMatrix S
  have hh (i : Fin 3) : (normalizedFixedCoordinateChart B i).totalDegree ≤ d :=
    (normalizedFixedCoordinateChart_homogeneous_reconstruction B hB i).1
  have hd := canonical_ternary_degree_bound_of_linear_normal_form P
    (normalizedFixedCoordinateChart B) T S hh hn
  have hTS' : T' * S' = 1 := by
    change vertexPreservingMatrix T * vertexPreservingMatrix S = 1
    rw [vertexPreservingMatrix_mul, hTS, vertexPreservingMatrix_one]
  have hST' : S' * T' = 1 := by
    change vertexPreservingMatrix S * vertexPreservingMatrix T = 1
    rw [vertexPreservingMatrix_mul, hST, vertexPreservingMatrix_one]
  have hz : G (Fin.last 3) = 0 := by
    simp only [G, normalizedFixedCoordinateHomogeneousCore, Fin.lastCases_last]
  have hdegree : IsHomogMap G d := by
    intro i
    refine Fin.lastCases (motive := fun j => (G j).IsHomogeneous d) ?_ (fun i => ?_) i
    · rw [hz]
      exact isHomogeneous_zero _ _ _
    · simpa only [G, normalizedFixedCoordinateHomogeneousCore, Fin.lastCases_castSucc] using
        lastCoordinateHomogenize_isHomogeneous _ _ (hh i)
  have hchart : (fun i : Fin 3 => lastCoordinateDehomogenize (G i.castSucc)) = normalizedFixedCoordinateChart B := by
    funext i
    simp only [G, normalizedFixedCoordinateHomogeneousCore, Fin.lastCases_castSucc,
      lastCoordinateDehomogenize_homogenize]
  have heq : linearPolynomialConjugate T' S' G = perturbation4 P d := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact vertexPreserving_conjugate_last_zero T S G hz
    · apply lastCoordinateDehomogenize_injective_on_homogeneous_degree _ _
        (linearPolynomialConjugate_homogeneous T' S' G hdegree i.castSucc)
        (perturbation4_isHomogMap P hm hd i.castSucc)
      rw [lastCoordinateDehomogenize_vertexPreserving_conjugate T S G i, hchart,
        hn, dehomogenize_normal_perturbation4]
  apply tame_automorphism_descends_from_constant_linear_conjugacy T' S' hTS' hST' G
    (normalFormAutomorphism4 P d) _ (normalFormAutomorphism4_tame P d)
  intro j
  rw [heq, normalFormAutomorphism4_X P hm hd]

/-- The original map is tame once the specified chart conjugacy has
been constructed. Both constant linear changes and the removed target
translation are restored by the checked four-variable identities. -/
theorem original_tameness_of_ternary_normal_form
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d)
    (U V : Matrix (Fin 4) (Fin 4) K) (hUV : U * V = 1) (hVU : V * U = 1)
    (B : Fin 3 → R₄) (hB : linearPolynomialConjugate U V H = Fin.lastCases 0 B)
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (P : Polynomial K) (hm : 0 < P.natDegree)
    (hn : linearPolynomialConjugate T S (normalizedFixedCoordinateChart B) = perturbation3 P) :
    ∃ E : R₄ ≃ₐ[K] R₄, E ∈ Tame.subgroup K 4 ∧ ∀ i, E (X i) = X i + H i := by
  have hh (i : Fin 3) : (B i).IsHomogeneous d := by
    have h := linearPolynomialConjugate_homogeneous U V H hH i.castSucc
    simp only [hB, Fin.lastCases_castSucc] at h
    exact h
  obtain ⟨E, hE, hX⟩ := normalized_homogeneous_core_tame_of_ternary_normal_form B hh T S hTS hST P hm hn
  exact normalized_fixed_coordinate_core_tameness_restores_original_map H U V hUV hVU B hB hh E hE hX

end DimensionFourDependence.TernaryNormalForm
