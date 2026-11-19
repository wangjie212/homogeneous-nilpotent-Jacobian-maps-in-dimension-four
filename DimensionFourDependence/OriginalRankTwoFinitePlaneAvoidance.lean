import DimensionFourDependence.OriginalRankTwoOrbitMinors
import DimensionFourDependence.FiniteCovectorOrbitFrame
import DimensionFourDependence.CovectorPlaneFrameExclusion

/-! # The original rank-two hypotheses construct simultaneous finite-plane avoidance -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 4500000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A hypothetical original independent rank-two nilpotent map
constructs normalized coordinates in which every prescribed finite
family of constant covector planes can be avoided by one further
normalized source frame. Every nonzero linear form from each entire
plane stays outside the fixed-coordinate polynomial ring.

The source point, all inverse matrices, all nonzero minors and the
simultaneous exceptional-set avoidance are derived internally. No
orders, asymptotic expansions, Wronskians or nonzero determinant
conditions are supplied. -/
theorem original_independent_rank_two_nilpotent_map_constructs_finite_covector_plane_avoidance
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2)
    (hind : ¬ComponentsDependent H) :
    ∃ A B : Matrix (Fin 4) (Fin 4) K, A * B = 1 ∧ B * A = 1 ∧
      let G := linearPolynomialConjugate A B H
      IsHomogMap G d ∧ IsNilpotent (jac G) ∧ ¬ComponentsDependent G ∧ polyRank (jac G) = 2 ∧
      ∀ (F : Finset ((Fin 4 → K) × (Fin 4 → K))),
        (∀ c ∈ F, LinearIndependent K ![c.1, c.2]) →
        ∃ T S : Matrix (Fin 4) (Fin 4) K, T * S = 1 ∧ S * T = 1 ∧
          (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
            (pderiv 0 (linearPolynomialConjugate T S G i)) = if i = 1 then 1 else 0) ∧
          (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
            (pderiv 1 (linearPolynomialConjugate T S G i)) = if i = 2 then 1 else 0) ∧
          ∀ c ∈ F, ∀ w : Fin 4 → K,
            w ∈ Submodule.span K ({c.1, c.2} : Set (Fin 4 → K)) → w ≠ 0 →
              linearPolynomialPullback T (linearFormPolynomial w) ∉
                Set.range (fixedPlaneCoefficientMap K) := by
  obtain ⟨A, B, hAB, hBA, hGhom, hGnil, hGind, hrG, _hcol0, _hcol1, hminors, _hbase⟩ :=
    original_independent_rank_two_nilpotent_map_constructs_all_covector_orbit_minors H hd hH hN hrank hind
  let G := linearPolynomialConjugate A B H
  refine ⟨A, B, hAB, hBA, hGhom, hGnil, hGind, hrG, ?_⟩
  intro F hF
  have hW : jac G ^ 2 *ᵥ coordVec ≠ 0 :=
    original_independent_homogeneous_four_variable_squared_jacobian_euler_ne_zero G hd hGhom hGind
  obtain ⟨T, S, hTS, hST, hj0, hj1, hdet⟩ :=
    finite_nonzero_covector_orbit_minors_construct_normalized_avoiding_frame G hd hGhom hGnil hW F
      (fun c hc => hminors c.1 c.2 (hF c hc))
  refine ⟨T, S, hTS, hST, hj0, hj1, ?_⟩
  intro c hc w hw hw0
  exact nonzero_covector_column_minor_excludes_entire_plane T c.1 c.2 (hdet c hc) w hw hw0

end DimensionFourDependence
