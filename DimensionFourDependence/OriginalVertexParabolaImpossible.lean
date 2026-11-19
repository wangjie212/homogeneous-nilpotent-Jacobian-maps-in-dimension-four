import DimensionFourDependence.OriginalVertexParabolaExclusion
import DimensionFourDependence.TransverseHomogeneousPencil
import DimensionFourDependence.GeometricParameterPencilConstants
import DimensionFourDependence.GeometricConstantProjectedDirection

/-! # The original fixed-vertex map has no nonlinear vertex-parabolic generic component -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000

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

include hd hH hN hrank hind hP

/-- If the reduced pencil is transverse, its two actual constant
values on the parabola put the projected direction on a fixed coprime
ternary base. Its algebraic direction ratios give the original fixed
plane obstruction, contradicting independence. -/
theorem original_map_transverse_pencil_vertex_parabolic_component_impossible
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {m : ℕ} (hm : 0 < m) (hpH : p.IsHomogeneous m) (hqH : q.IsHomogeneous m)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hpw : p.degreeOf (Fin.last 3) = 0) (hqw : q.degreeOf (Fin.last 3) = 0)
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
  obtain ⟨cp, cq, _hcp0, _hcq0, hcp, hcq⟩ :=
    geometric_parabola_reduced_parameter_pencil_nonzero_constants
      H I s hY h hh e hrank E P hP hpara p q hp hq hrel hparameter
  have hcp' : aeval z₀ p = algebraMap E G₀ cp := by simpa only [aeval_map_coefficients] using hcp
  have hcq' : aeval z₀ q = algebraMap E G₀ cq := by simpa only [aeval_map_coefficients] using hcq
  have halg := transverse_coprime_pencil_constant_on_fiber_direction_ratios_algebraic
    p q hp hq hrel hm hpH hqH hpw hqw t ht z₀ x A hx cp cq hcp' hcq' j hj
  exact hind (dependence_of_geometric_algebraic_projected_direction H (lt_trans Nat.zero_lt_one hd)
    hH hN hrank E P hP x A t hx j hj halg hnotline)

include hGauss hvertex

/-- The original fixed-vertex map cannot have an actual nonlinear
vertex-parabolic geometric generic component. Its own closed parameter
and positive reduced homogeneous pencil are constructed, and both the
vertex-dependent and transverse cases are excluded. No pencil, cone
formula, scalar root, moving normal or derivative data are supplied. -/
theorem original_fixed_vertex_map_has_no_nonlinear_vertex_parabolic_component
    (t : G₀) (ht : Transcendental E t) (x A : Fin 3 → E) (w B C : E)
    (hC : C ≠ 0) (hA : A ≠ 0)
    (hx : ∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (hw : z₀ (Fin.last 3) = algebraMap E G₀ w + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) :
    False := by
  obtain ⟨s, hY, h, hh, e, _hdata⟩ :=
    original_nonplanar_fixed_vertex_map_constructs_full_affine_cone H I hH hind hGauss hN hrank hd hvertex
  obtain ⟨p, q, m, hm, hp, hq, hpH, hqH, hrel, hparameter⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  by_cases hdep : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3)
  · rcases hdep with hdep | hdep
    · exact original_fixed_vertex_map_has_no_vertex_dependent_parabolic_component
        H hd hH hN hrank hind I hGauss hvertex E P hP e p q hp hq hrel hpH hqH hparameter
        p (Or.inl rfl) hdep t ht x A w B C hC hA hx hw
    · exact original_fixed_vertex_map_has_no_vertex_dependent_parabolic_component
        H hd hH hN hrank hind I hGauss hvertex E P hP e p q hp hq hrel hpH hqH hparameter
        q (Or.inr rfl) hdep t ht x A w B C hC hA hx hw
  · have hpw : p.degreeOf (Fin.last 3) = 0 := by omega
    have hqw : q.degreeOf (Fin.last 3) = 0 := by omega
    exact original_map_transverse_pencil_vertex_parabolic_component_impossible
      H hd hH hN hrank hind I E P hP s hY h hh e p q hp hq hrel hm hpH hqH hparameter hpw hqw
      t ht x A w B C hC hA hx hw

end DimensionFourDependence
