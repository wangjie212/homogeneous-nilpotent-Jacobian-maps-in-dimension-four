import DimensionFourDependence.GeometricParameterPencilConstants
import DimensionFourDependence.ActualParabolicVertexConstraint

/-! # The original parameter pencil gives a proper projected-direction locus

Use the verified nonzero-constant conclusion for the actual original
reduced Gauss pencil on a full-output geometric component. Once its
parabola is written with the specified fourth-coordinate vertex, either
vertex-dependent pencil member supplies its own fixed proper original
ternary homogeneous equation for the nonzero projected direction.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hY hh hrank hP

/-- Either original vertex-dependent reduced parameter-pencil member
constructs its fixed proper homogeneous plane locus for the projected
direction of the actual nonlinear geometric parabolic component.
The supplied vertex form is retained as an explicit geometric premise. -/
theorem geometric_parameter_pencil_constructs_vertex_direction_equation
    (hpara : LiesInAffineParabola (L := E) (z₀))
    (hline : ¬ LiesInAffineLine (E := E) (z₀))
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r : MvPolynomial (Fin 4) K) (hr : r = p ∨ r = q)
    {D : ℕ} (hrhom : r.IsHomogeneous D) (hrvertex : 0 < r.degreeOf (Fin.last 3))
    (t : G₀) (ht : Transcendental E t) (x A : Fin 3 → E) (w0 B C : E) (hC : C ≠ 0)
    (hx : ∀ i : Fin 3, (z₀) i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t)
    (hw : (z₀) (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t +
      algebraMap E G₀ C * t ^ 2) :
    let R := (optionEquivLeft K (Fin 3) (lastVertexPolynomial r)).coeff (r.degreeOf (Fin.last 3))
    A ≠ 0 ∧ R ≠ 0 ∧ R.IsHomogeneous (D - r.degreeOf (Fin.last 3)) ∧
      0 < R.totalDegree ∧ aeval A R = 0 := by
  obtain ⟨a, b, _ha, _hb, hpvalue, hqvalue⟩ :=
    geometric_parabola_reduced_parameter_pencil_nonzero_constants
      H I s hY h hh e hrank E P hP hpara p q hp hq hrel hparameter
  have hr0 : r ≠ 0 := by rcases hr with rfl | rfl <;> assumption
  have hrvalue : ∃ c : E, aeval (z₀) r = algebraMap E G₀ c := by
    rcases hr with rfl | rfl
    · refine ⟨a, ?_⟩
      simpa only [aeval_map_coefficients] using hpvalue
    · refine ⟨b, ?_⟩
      simpa only [aeval_map_coefficients] using hqvalue
  obtain ⟨c, hc⟩ := hrvalue
  exact actual_four_coordinate_parabola_original_vertex_direction_equation
    r hr0 hrhom hrvertex t ht (z₀) x A w0 B C hC hx hw hline c hc

end DimensionFourDependence
