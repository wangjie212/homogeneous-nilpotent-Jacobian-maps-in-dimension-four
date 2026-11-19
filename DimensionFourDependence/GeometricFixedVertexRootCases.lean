import DimensionFourDependence.FiniteAffineRootCaseRealization
import DimensionFourDependence.GeometricClosedGaussEmbedding
import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.RealizedConeMovingNormal
import DimensionFourDependence.RealizedConeNormalIncidence

/-! # The original fixed-vertex map constructs its root cases on each actual fiber

The original map constructs the finite affine root alternatives. Each
actual geometric generic component constructs a compatible source and
closed Gauss realization. Their common algebraic extension realizes the
same root alternatives and the actual moving normal on that component.
The nilpotent Jacobian supplies projected-direction incidence as well.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P
local notation "C₀" => closedGaussParameterField H I

include hd hH hN hrank hind hGauss hvertex hP

/-- The original map and its specified fixed vertex construct both
root alternatives on each actual geometric component, including the
complete second-case formula (4.7), its nonzero constant root and
algebraic coefficients, and the same actual moving-normal incidence.
No root cases, coefficient extension, cone formula or normal is supplied. -/
theorem geometric_fixed_vertex_map_constructs_realized_root_alternatives :
    ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
      ∃ g : C₀ →ₐ[K] E, (∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀)) ∧
        ∃ e : RatFunc K ≃ₐ[K] C₀,
          RealizedAffineFixedVertexRootAlternatives H I e g z₀ (genericOutputValue H E) d ∧
          ∃ (ν : Fin 3 → g.fieldRange) (k : Fin 3), ν k ≠ 0 ∧
            Algebra.trdeg K (projectiveRatioField (K := K) ν k) ≠ 0 ∧
            (∀ i : Fin 3, (ν i : E) = g (e (closedGaussParameterNormal H I e i.castSucc))) ∧
            ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E),
              (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
              (∑ i : Fin 3, (ν i : E) * A i) = 0 := by
  obtain ⟨p, hY, h, hh, e, hdata⟩ :=
    original_nonplanar_fixed_vertex_map_constructs_affine_root_alternatives H I hH hd hind hGauss hN hrank hvertex
  obtain ⟨f, hf, g, hg⟩ :=
    geometric_component_constructs_closed_gauss_field_embedding H I p hY h hh hrank E P hP
  have hout (i : Fin 4) : aeval z₀ (H i) = algebraMap E G₀ (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  have hcases := actual_finite_affine_root_cases_transfer_to_source_realization
    H I p hY h hh hH e hd hind hGauss hvertex hdata f g hg z₀ hf (genericOutputValue H E) hout
  obtain ⟨ν, k, hk, hdim, hνvalue, hν⟩ :=
    compatible_closed_gauss_realization_constructs_ternary_moving_normal H I hGauss hvertex e f g hg
  refine ⟨f, hf, g, hg, e, hcases, ν, k, hk, hdim, hνvalue, ?_⟩
  intro t ht x A hx
  exact realized_fixed_vertex_normal_incident_projected_fiber_direction
    H hN hrank I hvertex f z₀ hf (genericOutputValue H E) hout (fun i => (ν i : E)) hν t ht x A hx

end DimensionFourDependence
