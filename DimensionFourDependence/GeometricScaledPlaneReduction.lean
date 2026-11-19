import DimensionFourDependence.GeometricConstructedConeExclusion
import DimensionFourDependence.FiniteAffineRootCaseRealization
import DimensionFourDependence.NonlinearProjectedDirection
import DimensionFourDependence.FixedVertexPencilBase

/-! # The original actual fixed-vertex root alternatives reduce to the scaled-plane branch -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P
local notation "C₀" => closedGaussParameterField H I

include hd hH hN hrank hind hGauss hvertex hP

/-- The original map constructs its own output chart, closed Gauss
parameter and finite root alternatives. On every supplied nonlinear
vertex parabola in the vertex-dependent pencil branch, the full cone
case is impossible and its actual original root must be the scaled
normal-plane root. Neither root alternatives nor cone data are assumed. -/
theorem original_fixed_vertex_map_reduces_to_actual_scaled_plane_root
    : ∃ (s : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
      (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
      (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
      (e : RatFunc K ≃ₐ[K] C₀),
      ∀ (hpara : LiesInAffineParabola (L := E) z₀), ¬ LiesInAffineLine (E := E) z₀ →
      ∀ (p q : MvPolynomial (Fin 4) K), p ≠ 0 → q ≠ 0 → IsRelPrime p q →
      ∀ (m : ℕ), p.IsHomogeneous m → q.IsHomogeneous m →
        closedGaussParameterSourceHom H I e RatFunc.X =
          algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q →
      ∀ (r : MvPolynomial (Fin 4) K), (r = p ∨ r = q) → 0 < r.degreeOf (Fin.last 3) →
      ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E) (w B C : E), C ≠ 0 →
        (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
        (z₀ (Fin.last 3) = algebraMap E G₀ w + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) →
        ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
          ∃ g : C₀ →ₐ[K] E, (∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀)) ∧
            ∃ (cS cN : Fin 4 → E) (R γ : E), (∀ i, IsAlgebraic g.fieldRange (cS i)) ∧ cS ≠ 0 ∧
              (∀ i, IsAlgebraic g.fieldRange (cN i)) ∧ cN ≠ 0 ∧ cN (Fin.last 3) = 0 ∧
              (∑ i : Fin 4, cN i * genericOutputValue H E i) ≠ 0 ∧
              (∑ i : Fin 4, MvPolynomial.C (cN i) * MvPolynomial.map (algebraMap K E) (H i)) ∈
                (Ideal.span ({MvPolynomial.map (algebraMap K E) p,
                  MvPolynomial.map (algebraMap K E) q} : Set (MvPolynomial (Fin 4) E))).radical ∧
              R ≠ 0 ∧ γ ≠ 0 ∧ IsAlgebraic g.fieldRange γ ∧
              R ^ d = ∑ i : Fin 4, cS i * genericOutputValue H E i ∧
              algebraMap E G₀ R = algebraMap E G₀ γ *
                (∑ i : Fin 3, algebraMap E G₀ (g (e (closedGaussParameterNormal H I e i.castSucc))) * z₀ i.castSucc) := by
  obtain ⟨s, hY, h, hh, e, hdata⟩ :=
    original_nonplanar_fixed_vertex_map_constructs_affine_root_alternatives H I hH hd hind hGauss hN hrank hvertex
  refine ⟨s, hY, h, hh, e, ?_⟩
  intro hpara hnotline p q hp hq hrel m hpH hqH hparameter r hr hrvertex t ht x A w B C hC hx hw
  obtain ⟨f, hf, g, hg, hexclude⟩ :=
    geometric_original_full_cone_data_impossible_with_constructed_quadratic_coefficient
      H I s hY h hh hd hH hN hrank hind hGauss hvertex E P hP e hpara hnotline
      p q hp hq hrel hpH hqH hparameter r hr hrvertex
  have hout (i : Fin 4) : aeval z₀ (H i) = algebraMap E G₀ (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  have hcases := actual_finite_affine_root_cases_transfer_to_source_realization
    H I s hY h hh hH e hd hind hGauss hvertex hdata f g hg z₀ hf (genericOutputValue H E) hout
  obtain ⟨cS, R, hcS, hcS0, hR, hpower, hnumerator, hbranch⟩ := hcases
  rcases hbranch with hscaled | hfull
  · obtain ⟨γ, hγ0, hγalg, hvalue⟩ := hscaled
    obtain ⟨cN, hcN, hcN0, hnlast, hnvalue⟩ := hnumerator
    have hnbase := vertex_output_covector_mem_pencil_base_radical
      H hd hH hind I hGauss hvertex e p q hq hrel hparameter (algebraMap K E) cN hnlast
    exact ⟨f, hf, g, hg, cS, cN, R, γ, hcS, hcS0, hcN, hcN0, hnlast, hnvalue, hnbase,
      hR, hγ0, hγalg, hpower, hvalue⟩
  · obtain ⟨V, a, b, hV0, hb0, hV, ha, hb, hfirst, hlast⟩ := hfull
    have hA0 := nonlinear_affine_fiber_projected_direction_ne_zero z₀ hnotline x A t hx
    obtain ⟨j, hj⟩ : ∃ j, A j ≠ 0 := by
      simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hA0
    exact (hexclude t ht x A w B C hC hx hw j hj R hR V hV0 a b hb0 hV ha hb hfirst hlast).elim

end DimensionFourDependence
