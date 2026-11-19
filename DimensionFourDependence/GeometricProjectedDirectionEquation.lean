import DimensionFourDependence.GeometricConstantProjectedDirection
import DimensionFourDependence.GeometricParameterVertexConstraint
import DimensionFourDependence.ProjectivePointEquationRegularity

/-! # The original geometric parameter pencil constructs its direction equation

The original highest vertex coefficient supplies a proper direction
relation. Proposition 2.3 excludes a constant direction for an independent
map. Together these construct the entire irreducible projective direction
equation and its nonzero generic normal in the original coefficient ring.
The actual specified vertex-normal parametrization remains explicit.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

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

/-- The actual reduced pencil constructs the whole direction-curve
equation and its nonzero tangent form. Neither the equation nor the
algebraicity or dimension of the direction field is supplied. -/
theorem geometric_parameter_vertex_constructs_regular_direction_equation
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
    (hw : (z₀) (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) :
    ∃ (Φ : MvPolynomial (Fin 3) K) (m : ℕ),
      Φ ≠ 0 ∧ Φ.IsHomogeneous m ∧ 0 < m ∧ Irreducible Φ ∧ aeval A Φ = 0 ∧
      (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} ∧
      (fun i => aeval A (pderiv i Φ)) ≠ 0 ∧
      (∑ i : Fin 3, A i * aeval A (pderiv i Φ)) = 0 ∧
      ∀ (Q : MvPolynomial (Fin 3) K) (f : ℕ),
        Q.IsHomogeneous f → (aeval A Q = 0 ↔ Φ ∣ Q) := by
  obtain ⟨_hA, hR0, hRhom, _hRdegree, hRzero⟩ :=
    geometric_parameter_pencil_constructs_vertex_direction_equation
      H I s hY h hh e hrank E P hP hpara hline p q hp hq hrel hparameter r hr
      hrhom hrvertex t ht x A w0 B C hC hx hw
  let R := (optionEquivLeft K (Fin 3) (lastVertexPolynomial r)).coeff (r.degreeOf (Fin.last 3))
  obtain ⟨j, hj, hpositive⟩ :=
    independent_map_geometric_projected_direction_constructs_nonconstant_chart
      H hd hH hN hrank E P hP hind x A t hx hline
  obtain ⟨Φ, m, hΦ0, hΦ, hm, hirr, hvalue, hI, hgrad, htest⟩ :=
    nonconstant_ternary_direction_constructs_regular_equation A j hj hpositive R hR0 hRhom hRzero
  exact ⟨Φ, m, hΦ0, hΦ, hm, hirr, hvalue, hI, hgrad,
    homogeneous_equation_gradient_annihilates_point A Φ hΦ hvalue, htest⟩

end DimensionFourDependence
