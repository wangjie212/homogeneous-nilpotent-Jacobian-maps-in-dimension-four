import DimensionFourDependence.OriginalMapFixedVertexDegree
import DimensionFourDependence.SelectedGeometricParabola

/-! # Actual nonlinear geometric components in the fixed-vertex case are parabolas -/

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

/-- Every actual nonlinear geometric component of the original fixed-vertex
map is a parabola. The root independence and actual full-fiber degree bound
are constructed from the original map rather than supplied. -/
theorem original_fixed_vertex_map_nonlinear_geometric_component_is_parabola
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    LiesInAffineParabola (L := E) (primeQuotientCoordinate P) := by
  obtain ⟨p, hY, h, c, hh, e, _hc0, _hc, eCurve, _heCurve, _hupper, hparabola⟩ :=
    original_fixed_vertex_map_constructs_full_fiber_degree_bound
      H I hH hind hGauss hN hrank hd hvertex
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)
  have hrankQ : (rationalJacobian Q).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  have hnonlinear := selected_geometric_component_nonlinear_implies_actual_nonlinear
    Q hrankQ p hY E P hP hline
  have hactual := (hparabola hnonlinear).2
  exact selected_geometric_component_parabola_of_actual_parabola Q hrankQ p hY hactual E P hP hline

end DimensionFourDependence
