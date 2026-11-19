import DimensionFourDependence.OriginalFixedVertexDegreeAndBoundary
import DimensionFourDependence.CompatibleVertexParabola
import DimensionFourDependence.OriginalVertexParabolaImpossible
import DimensionFourDependence.SelectedGeometricParabola

/-! # The original fixed-vertex case has no nonlinear geometric generic component -/

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

/-- Every actual nonlinear geometric component would be a parabola
through the original fixed vertex. The checked vertex-parabola
exclusion therefore rules it out without supplied root or boundary data. -/
theorem original_fixed_vertex_map_has_no_nonlinear_geometric_component
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : False := by
  obtain ⟨p, hY, h, c, hh, e, _hc0, _hc, haxis, eCurve, _heCurve, _hupper, hparabola⟩ :=
    original_fixed_vertex_map_constructs_degree_bound_and_vertex_boundary
      H I hH hind hGauss hN hrank hd hvertex
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)
  have hrankQ : (rationalJacobian Q).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  have hnonlinear := selected_geometric_component_nonlinear_implies_actual_nonlinear
    Q hrankQ p hY E P hP hline
  have hactual := (hparabola hnonlinear).2
  let := fullOutputCoefficientAlgebra Q hrankQ p hY
  obtain ⟨f, hf, g, hg⟩ := selected_full_output_geometric_coefficient_embedding Q hrankQ p hY E P hP
  have hcoords : f.toRingHom ∘ rationalCoordinate (K := K) (n := 4) = primeQuotientCoordinate P := by
    funext i
    exact hf i
  have hline' : ¬ LiesInAffineLine (E := E)
      (f.toRingHom ∘ rationalCoordinate (K := K) (n := 4)) := by rwa [hcoords]
  obtain ⟨t, x₀, A, w, B, C, ht, hC, hA, hx, hw⟩ :=
    compatible_parabola_vertex_coordinates_of_nonlinear_image f.toRingHom g.toRingHom hg
      (rationalCoordinate (K := K) (n := 4)) hactual haxis hline'
  have hx' : ∀ i : Fin 3, primeQuotientCoordinate P i.castSucc =
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (x₀ i) +
        algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (A i) * t := by
    simpa only [hcoords] using hx
  have hw' : primeQuotientCoordinate P (Fin.last 3) =
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) w +
        algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) B * t +
          algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) C * t ^ 2 := by
    simpa only [hcoords] using hw
  exact original_fixed_vertex_map_has_no_nonlinear_vertex_parabolic_component
    H hd hH hN hrank hind I hGauss hvertex E P hP t ht x₀ A w B C hC hA hx' hw'

/-- In the fixed-vertex Gauss-dimension-one case every actual
geometric generic-fiber component is contained in an affine line. -/
theorem original_fixed_vertex_map_geometric_component_lies_in_affine_line :
    LiesInAffineLine (E := E) (primeQuotientCoordinate P) := by
  classical
  by_contra hline
  exact original_fixed_vertex_map_has_no_nonlinear_geometric_component
    H hd hH hN hrank hind I hGauss hvertex E P hP hline

end DimensionFourDependence
