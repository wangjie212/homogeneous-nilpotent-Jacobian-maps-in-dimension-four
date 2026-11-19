import DimensionFourDependence.GeometricConstantProjectedDirection
import DimensionFourDependence.ProjectedDirectionCurveDimension
import DimensionFourDependence.GeometricParameterDirectionAlgebraicity

/-! # The actual projected-direction image is a curve

For an independent original map over the paper's algebraically closed
base, Proposition 2.3 excludes a constant projected direction. Finiteness
over the one-dimensional ruling field supplies the matching upper bound.
The actual original projective direction-ratio field therefore has
dimension exactly one, retaining the constructed finite representative.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hN hrank hP

/-- The entire actual original projected-direction field is
one-dimensional whenever its ruling-field coordinate extension is finite. -/
theorem geometric_independent_projected_direction_curve_dimension_one
    (hind : ¬ ComponentsDependent H) (x A : Fin 3 → E) (t : G₀)
    (hx : ∀ i : Fin 3, (z₀) i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (hline : ¬ LiesInAffineLine (E := E) (z₀)) (j : Fin 3) (hj : A j ≠ 0)
    (L : Type u) [Field L] [Algebra K L] [Algebra L E] [IsScalarTower K L E]
    (hL : Algebra.trdeg K L = 1)
    (hfinite : Module.Finite L (IntermediateField.adjoin L (Set.range (fun i => A i / A j)))) :
    Algebra.trdeg K (projectiveRatioField (K := K) A j) = 1 := by
  have hpositive := independent_map_geometric_projected_direction_positive_dimension
    H hd hH hN hrank E P hP hind x A t hx j hj hline
  exact original_projective_direction_trdeg_one_of_finite_ruling_extension A j hL hfinite hpositive

/-- The actual reduced Gauss pencil constructs a nonconstant
one-dimensional original direction image and its normalized finite
ruling-field representative, given the specified vertex and tangent data. -/
theorem geometric_parameter_vertex_constructs_projected_direction_curve
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hpara : LiesInAffineParabola (L := E) (z₀))
    (hline : ¬ LiesInAffineLine (E := E) (z₀))
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r : MvPolynomial (Fin 4) K) (hr : r = p ∨ r = q)
    {D : ℕ} (hrhom : r.IsHomogeneous D) (hrvertex : 0 < r.degreeOf (Fin.last 3))
    (t : G₀) (ht : Transcendental E t) (x A : Fin 3 → E) (w0 B C : E) (hC : C ≠ 0)
    (hx : ∀ i : Fin 3, (z₀) i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (hw : (z₀) (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2)
    (L : Type u) [Field L] [Algebra K L] [Algebra L E] [IsScalarTower K L E]
    (hL : Algebra.trdeg K L = 1)
    (nu : Fin 3 → L) (k : Fin 3) (hk : nu k ≠ 0)
    (hdim : Algebra.trdeg K (projectiveRatioField (K := K) nu k) ≠ 0)
    (hincidence : ∑ i : Fin 3, algebraMap L E (nu i) * A i = 0)
    (j : Fin 3) (hj : A j ≠ 0) :
    Algebra.trdeg K (projectiveRatioField (K := K) A j) = 1 ∧
      Module.Finite L (IntermediateField.adjoin L (Set.range (fun i => A i / A j))) ∧
      ∃ v : Fin 3 → IntermediateField.adjoin L (Set.range (fun i => A i / A j)),
        v j = 1 ∧ ∀ i, A i = A j * (v i : E) := by
  obtain ⟨_halg, hfinite, v, hvj, hv⟩ :=
    geometric_parameter_vertex_direction_constructs_finite_ruling_representative
      H I s hY h hh e hrank E P hP hpara hline p q hp hq hrel hparameter r hr
      hrhom hrvertex t ht x A w0 B C hC hx hw L nu k hk hdim hincidence j hj
  exact ⟨geometric_independent_projected_direction_curve_dimension_one
      H hd hH hN hrank E P hP hind x A t hx hline j hj L hL hfinite,
    hfinite, v, hvj, hv⟩

end DimensionFourDependence
