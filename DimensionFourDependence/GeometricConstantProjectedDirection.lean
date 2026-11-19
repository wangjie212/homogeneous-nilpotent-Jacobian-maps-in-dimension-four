import DimensionFourDependence.ConstantProjectedDirectionPlane
import DimensionFourDependence.ProjectiveRatioEmbedding
import DimensionFourDependence.ActualParabolicVertexConstraint

/-! # The original independent map excludes a constant projected direction

Under the paper's algebraically closed base-field reduction, a
zero-dimensional projected-direction field supplies a fixed original
direction plane. The actual full-output nonlinear geometric component
then gives component dependence by the verified Proposition 2.3. Thus
an independent original map has a nonconstant projected direction.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hN hrank hP

/-- Algebraic projected-direction ratios on an actual nonlinear
geometric generic component force dependence of the original map. -/
theorem dependence_of_geometric_algebraic_projected_direction
    (x A : Fin 3 → E) (t : G₀)
    (hx : ∀ i : Fin 3, (z₀) i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (j : Fin 3) (hj : A j ≠ 0) (halg : ∀ i : Fin 3, IsAlgebraic K (A i / A j))
    (hline : ¬ LiesInAffineLine (E := E) (z₀)) : ComponentsDependent H := by
  obtain ⟨a, _haj, hLI, hplane⟩ :=
    algebraic_projected_direction_constructs_original_constant_plane (z₀) x A t hx j hj halg
  exact dependence_of_geometric_nonlinear_fixed_plane_fiber H hd hH hN hrank E P hP
    (Fin.snoc a 0) (Fin.snoc (0 : Fin 3 → K) 1) hLI hplane hline

/-- Independence of the original map forces positive dimension of
every actual normalized projected-direction field. -/
theorem independent_map_geometric_projected_direction_positive_dimension
    (hind : ¬ ComponentsDependent H)
    (x A : Fin 3 → E) (t : G₀)
    (hx : ∀ i : Fin 3, (z₀) i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (j : Fin 3) (hj : A j ≠ 0)
    (hline : ¬ LiesInAffineLine (E := E) (z₀)) :
    Algebra.trdeg K (projectiveRatioField (K := K) A j) ≠ 0 := by
  intro hz
  have halg := (projective_ratio_dimension_zero_iff_coordinate_algebraic A j).mp hz
  exact hind (dependence_of_geometric_algebraic_projected_direction
    H hd hH hN hrank E P hP x A t hx j hj halg hline)

/-- The actual nonlinear component constructs a nonzero projected
chart whose entire original ratio field is nonconstant. -/
theorem independent_map_geometric_projected_direction_constructs_nonconstant_chart
    (hind : ¬ ComponentsDependent H)
    (x A : Fin 3 → E) (t : G₀)
    (hx : ∀ i : Fin 3, (z₀) i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (hline : ¬ LiesInAffineLine (E := E) (z₀)) :
    ∃ j : Fin 3, A j ≠ 0 ∧ Algebra.trdeg K (projectiveRatioField (K := K) A j) ≠ 0 := by
  have hA : A ≠ 0 := nonlinear_vertex_fiber_projected_direction_ne_zero (z₀) x A t hx hline
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, A j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hA
  exact ⟨j, hj, independent_map_geometric_projected_direction_positive_dimension
    H hd hH hN hrank E P hP hind x A t hx j hj hline⟩

end DimensionFourDependence
