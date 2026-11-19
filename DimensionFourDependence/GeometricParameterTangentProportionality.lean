import DimensionFourDependence.ActualParabolaTangentConstraint
import DimensionFourDependence.GeometricProjectedDirectionEquation

/-! # The actual reduced geometric pencil constructs tangent proportionality

The original pencil supplies both its proper direction equation and
its actual invariant value. The affine calculation then constructs the
finite tangent-proportionality field. The specified vertex form,
direction-field realization, projected-source independence and quadratic
coefficient formula remain explicit geometric premises.
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
local notation "z₀" => primeQuotientCoordinate P

variable (F : Type u) [Field F] [Algebra K F] [Algebra F E] [IsScalarTower K F E]

include hd hH hN hrank hP

/-- The actual original geometric pencil constructs its entire
irreducible direction equation and a finite extension containing the
nonzero scalar that makes the specified denominator a tangent multiple. -/
theorem geometric_parameter_vertex_constructs_finite_tangent_proportionality
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hpara : LiesInAffineParabola (L := E) z₀) (hline : ¬ LiesInAffineLine (E := E) z₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r : MvPolynomial (Fin 4) K) (hr : r = p ∨ r = q)
    {D : ℕ} (hrhom : r.IsHomogeneous D) (hrvertex : 0 < r.degreeOf (Fin.last 3))
    (t : (FractionRing (MvPolynomial (Fin 4) E ⧸ P))) (ht : Transcendental E t) (x : Fin 3 → E) (A : Fin 3 → F) (w0 B C : E)
    (hx : ∀ i : Fin 3, z₀ i.castSucc = algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (x i) + algebraMap F (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (A i) * t)
    (hw : z₀ (Fin.last 3) = algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) w0 + algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) B * t + algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) C * t ^ 2)
    (hindsource : AlgebraicIndependent F (fun i : Fin 3 => z₀ i.castSucc))
    (R : E) (hR : R ≠ 0) (κ : F) (hκ : κ ≠ 0) (hC : C = algebraMap F E κ / R) :
    ∃ (Φ : MvPolynomial (Fin 3) K) (m : ℕ),
      Φ ≠ 0 ∧ Φ.IsHomogeneous m ∧ 0 < m ∧ Irreducible Φ ∧
      (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} ∧
      let T := ∑ i : Fin 3, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i
      IsAlgebraic F (R / T) ∧ Module.Finite F (IntermediateField.adjoin F {R / T}) ∧
        ∃ u : IntermediateField.adjoin F {R / T}, u ≠ 0 ∧ R = (u : E) * T := by
  let : IsScalarTower F E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) :=
    IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  let : IsScalarTower K F (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      change algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P))
        (algebraMap K E a) =
          algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (algebraMap F E (algebraMap K F a))
      rw [IsScalarTower.algebraMap_apply K F E])
  have hC0 : C ≠ 0 := by
    rw [hC]
    exact div_ne_zero (by simpa only [map_zero] using (algebraMap F E).injective.ne hκ) hR
  have hxE (i : Fin 3) : z₀ i.castSucc = algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (x i) +
      algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (algebraMap F E (A i)) * t := by
    simpa only [IsScalarTower.algebraMap_apply F E (FractionRing (MvPolynomial (Fin 4) E ⧸ P))] using hx i
  obtain ⟨Φ, m, hΦ0, hΦ, hm, hirr, _hvalue, hIE, _hgrad, _hEuler, _htest⟩ :=
    geometric_parameter_vertex_constructs_regular_direction_equation H hd hH hN hrank E P hP
      hind I s hY h hh e hpara hline p q hp hq hrel hparameter r hr hrhom hrvertex
      t ht x (fun i => algebraMap F E (A i)) w0 B C hC0 hxE hw
  have hIF : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} := by
    have he := projectiveFieldPointIdeal_algHom A (IsScalarTower.toAlgHom K F E)
    change (projectiveFieldPointIdeal (E := K) (fun i => algebraMap F E (A i))).toIdeal =
      (projectiveFieldPointIdeal (E := K) A).toIdeal at he
    exact he.symm.trans hIE
  obtain ⟨a, b, _ha, _hb, hpvalue, hqvalue⟩ :=
    geometric_parabola_reduced_parameter_pencil_nonzero_constants
      H I s hY h hh e hrank E P hP hpara p q hp hq hrel hparameter
  have hr0 : r ≠ 0 := by rcases hr with rfl | rfl <;> assumption
  have hrvalue : ∃ c : E, aeval z₀ r = algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) c := by
    rcases hr with rfl | rfl
    · exact ⟨a, by simpa only [aeval_map_coefficients] using hpvalue⟩
    · exact ⟨b, by simpa only [aeval_map_coefficients] using hqvalue⟩
  obtain ⟨c, hc⟩ := hrvalue
  exact ⟨Φ, m, hΦ0, hΦ, hm, hirr, hIF,
    actual_parabola_invariant_constructs_finite_tangent_proportionality A Φ hΦ hirr hIF
      r hr0 hrhom hrvertex t ht z₀ x w0 B C hx hw hindsource c hc R hR κ hκ hC⟩

end DimensionFourDependence
