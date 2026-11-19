import DimensionFourDependence.OriginalVertexParabolaImpossible
import DimensionFourDependence.VertexParabolaFromInfinity

/-! # Exclude actual parabola components containing the fixed vertex at infinity -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

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

include hd hH hN hrank hind hGauss hvertex hP

/-- The original nonplanar fixed-vertex map cannot have an actual
parabola component whose projective closure contains the fixed fourth
axis. The vertex-parabola coordinates, both nonzero directions, the
parameter pencil, scalar root and full cone form are all constructed. -/
theorem original_fixed_vertex_map_actual_parabola_cannot_contain_vertex_at_infinity
    (hpara : LiesInAffineParabola (L := E) (primeQuotientCoordinate P)) :
    fourthAxisAffineInfinityPoint E ∉
      projectiveClosureSet (L := E) (primeQuotientCoordinate P) := by
  intro hpoint
  obtain ⟨t, x, A, w, B, C, ht, hC, hA, hx, hw⟩ :=
    actual_parabola_fourth_axis_infinity_constructs_vertex_coordinates
      (primeQuotientCoordinate P) hpara hpoint
  exact original_fixed_vertex_map_has_no_nonlinear_vertex_parabolic_component
    H hd hH hN hrank hind I hGauss hvertex E P hP t ht x A w B C hC hA hx hw

end DimensionFourDependence
