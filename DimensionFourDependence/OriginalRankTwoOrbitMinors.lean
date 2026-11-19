import DimensionFourDependence.OriginalRankTwoLinearBaseComponent
import DimensionFourDependence.NormalizedPencilOrbitMinor

/-! # An original rank-two counterexample constructs all nonzero covector orbit minors -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 4000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- Starting with the original hypotheses alone, construct inverse
coordinates in which every independent constant covector pair has a
nonzero polynomial minor on the actual output and its actual Jacobian
acceleration. The same coordinates retain an actual height-two minimal
pencil base component with a nonzero fixed-plane linear form. -/
theorem original_independent_rank_two_nilpotent_map_constructs_all_covector_orbit_minors
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2)
    (hind : ¬ComponentsDependent H) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K, T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      IsHomogMap G d ∧ IsNilpotent (jac G) ∧ ¬ComponentsDependent G ∧ polyRank (jac G) = 2 ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 0 (G i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 (G i)) = if i = 2 then 1 else 0) ∧
      (∀ (μ ν : Fin 4 → K), LinearIndependent K ![μ, ν] →
        outputLinearCombination G μ * outputLinearCombination (jac G *ᵥ G) ν -
          outputLinearCombination G ν * outputLinearCombination (jac G *ᵥ G) μ ≠ 0) ∧
      ∃ (p q : R₀) (Q : Ideal R₀) (α β : K), IsRelPrime p q ∧
        Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes ∧ Q.height = 2 ∧
        (α ≠ 0 ∨ β ≠ 0) ∧ C α * X 0 + C β * X 3 ∈ Q ∧ ∀ i, G i ∈ Q := by
  obtain ⟨T, S, p, q, g, D, N, c, v, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1,
    _hD, _hNpos, hg, _hpH, _hqH, _hgH, _hdegree, hrel, hp0, hq1, _hgz, hpder, hVdeg, _hprim, hfactor,
    Q, α, β, hQ, hheight, hab, hlinear, hGI⟩ :=
    original_independent_rank_two_nilpotent_map_constructs_normalized_pencil_and_linear_height_two_base_component
      H hd hH hN hrank hind
  refine ⟨T, S, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1, ?_,
    p, q, Q, α, β, hrel, hQ, hheight, hab, hlinear, hGI⟩
  intro μ ν hμν
  exact normalized_independent_source_pencil_covector_orbit_minor_ne_zero
    (linearPolynomialConjugate T S H) hd hGhom hGind hcol0 p q g hg hp0 hq1 hpder v hVdeg hfactor μ ν hμν

end DimensionFourDependence
