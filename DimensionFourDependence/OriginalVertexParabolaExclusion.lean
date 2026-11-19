import DimensionFourDependence.GeometricConstructedConeExclusion
import DimensionFourDependence.FiniteFullConeRealization
import DimensionFourDependence.VertexParabolaGeometry
import DimensionFourDependence.GenericFiberOutput

/-! # The original fixed-vertex map excludes a vertex-dependent nonlinear parabolic component -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
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

/-- An actual nonlinear vertex parabola in the vertex-dependent
closed Gauss pencil contradicts the original map hypotheses. The
original map constructs the finite coefficients and full cone formula;
the displayed actual coordinates construct parabola nondegeneracy and
nonlinearity. No cone data, quadratic numerator, independent directrix,
moving normal, direction algebraicity or chart is supplied. -/
theorem original_fixed_vertex_map_has_no_vertex_dependent_parabolic_component
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {m : ℕ} (hpH : p.IsHomogeneous m) (hqH : q.IsHomogeneous m)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r : MvPolynomial (Fin 4) K) (hr : r = p ∨ r = q) (hrvertex : 0 < r.degreeOf (Fin.last 3))
    (t : G₀) (ht : Transcendental E t) (x A : Fin 3 → E) (w B C : E)
    (hC : C ≠ 0) (hA : A ≠ 0)
    (hx : ∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (hw : z₀ (Fin.last 3) = algebraMap E G₀ w + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) :
    False := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, A j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hA
  have hpara := actual_vertex_coordinates_construct_affine_parabola t ht z₀ x A w B C hC j hj hx hw
  have hnotline := actual_vertex_coordinates_not_affine_line t ht z₀ x A w B C hC j hj hx hw
  obtain ⟨s, hY, h, hh, e₀, hdata⟩ :=
    original_nonplanar_fixed_vertex_map_constructs_full_affine_cone H I hH hind hGauss hN hrank hd hvertex
  obtain ⟨f, hf, g, hg, hexclude⟩ :=
    geometric_original_full_cone_data_impossible_with_constructed_quadratic_coefficient
      H I s hY h hh (lt_trans Nat.zero_lt_one hd) hH hN hrank hind hGauss hvertex E P hP
      e hpara hnotline p q hp hq hrel hpH hqH hparameter r hr hrvertex
  have hout (i : Fin 4) : aeval z₀ (H i) = algebraMap E G₀ (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  have hfull := actual_finite_full_cone_transfers_to_source_realization
    H I s hY h hh hH e₀ (lt_trans Nat.zero_lt_one hd) hind hGauss hvertex hdata
    e f g hg z₀ hf (genericOutputValue H E) hout
  obtain ⟨R, V, a, b, hR, hV, hb, hValg, ha, hbalg, hfirst, hlast, _hinc⟩ := hfull
  exact hexclude t ht x A w B C hC hx hw j hj R hR V hV a b hb hValg ha hbalg hfirst hlast

end DimensionFourDependence
