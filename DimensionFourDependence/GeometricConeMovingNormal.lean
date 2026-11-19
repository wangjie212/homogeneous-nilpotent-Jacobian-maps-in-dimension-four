import DimensionFourDependence.GeometricConeScalarRoot
import DimensionFourDependence.RealizedConeMovingNormal
import DimensionFourDependence.RealizedConeNormalIncidence

/-! # The actual fixed-vertex component constructs scalar and normal data together

One compatible source and closed Gauss realization constructs the first
three scalar formulas, the normalized nonlinear directrix, its nonzero
degree-d root, and a moving normal over the exact same constant-field
range. The original nilpotent Jacobian proves incidence with every
affine-linear projected fiber direction.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s 3)))
    (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hN hind hGauss hvertex hY hh hrank hP

/-- The original map and specified fourth-axis vertex construct the
scalar cone data and moving-normal incidence on one actual geometric
component realization. No cone-coordinate formula, moving normal,
normal-image dimension, tangent equation or scalar root is supplied. -/
theorem geometric_fixed_vertex_cone_constructs_scalar_root_and_moving_normal
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
      ∃ g : closedGaussParameterField H I →ₐ[K] E,
        (∀ c : closedGaussParameterField H I, algebraMap E G₀ (g c) = f (c : S₀)) ∧
        ∃ (V : Fin 3 → RatFunc K) (j : Fin 3) (R : E),
          V j = 1 ∧ H j.castSucc ≠ 0 ∧ LinearIndependent K V ∧
          LinearIndependent K (fun i => g (e (V i))) ∧ R ≠ 0 ∧
          R ^ d = genericOutputValue H E j.castSucc ∧
          (∀ i : Fin 3, genericOutputValue H E i.castSucc = g (e (V i)) * R ^ d) ∧
          (∀ i : Fin 3, aeval z₀ (H i.castSucc) =
            algebraMap E G₀ (g (e (V i))) * (algebraMap E G₀ R) ^ d) ∧
          ∃ (ν : Fin 3 → g.fieldRange) (k : Fin 3), ν k ≠ 0 ∧
            Algebra.trdeg K (projectiveRatioField (K := K) ν k) ≠ 0 ∧
            (∀ i : Fin 3, (ν i : E) = g (e (closedGaussParameterNormal H I e i.castSucc))) ∧
            (fun i : Fin 3 => closedGaussParameterNormal H I e i.castSucc) ⬝ᵥ V = 0 ∧
            (fun i : Fin 3 => rationalParameterDerivative K
              (closedGaussParameterNormal H I e i.castSucc)) ⬝ᵥ V = 0 ∧
            (fun i : Fin 3 => closedGaussParameterNormal H I e i.castSucc) ⬝ᵥ
              (fun i => rationalParameterDerivative K (V i)) = 0 ∧
            ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E),
              (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
              (∑ i : Fin 3, (ν i : E) * A i) = 0 := by
  obtain ⟨f, hf, g, hg, V, j, R, hVj, hHj, hLI, hLIE, hR0, hR, hgeneric,
    hfirst, hnormal, hderivative, htangent⟩ :=
    geometric_fixed_vertex_cone_constructs_scalar_root_presentation
      H hd hH hind I hGauss hvertex s hY h hh hrank E P hP e
  obtain ⟨ν, k, hk, hdim, hνvalue, hν⟩ :=
    compatible_closed_gauss_realization_constructs_ternary_moving_normal
      H I hGauss hvertex e f g hg
  refine ⟨f, hf, g, hg, V, j, R, hVj, hHj, hLI, hLIE, hR0, hR, hgeneric,
    hfirst, ν, k, hk, hdim, hνvalue, hnormal, hderivative, htangent, ?_⟩
  intro t ht x A hx
  have hout (i : Fin 4) : aeval z₀ (H i) = algebraMap E G₀ (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  exact realized_fixed_vertex_normal_incident_projected_fiber_direction
    H hN hrank I hvertex f z₀ hf (genericOutputValue H E) hout (fun i => (ν i : E)) hν t ht x A hx

end DimensionFourDependence
