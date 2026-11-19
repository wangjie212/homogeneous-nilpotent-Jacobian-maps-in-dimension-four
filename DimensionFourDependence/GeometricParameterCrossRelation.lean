import DimensionFourDependence.FullOutputGeometricFiber
import DimensionFourDependence.ClosedGaussCoefficientRealization
import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.CompatibleParameterPolynomialRelation
import DimensionFourDependence.ProjectiveSourceParameterField

/-! # The original closed Gauss parameter on each geometric component

The actual closed-cover parameter lies in the selected graph coefficient
field, hence is algebraic over the full output field. Its source-field
embedding lands in the algebraically closed geometric constants. This
supplies a nonzero parameter value and the exact original cross equation
in the entire component ideal, including possible denominator zeros.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

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
local notation "Q₀" => fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)

include hY hh hrank hP

/-- The actual original homogeneous parameter presentation gives
a nonzero constant cross equation in every full-output component ideal. -/
theorem geometric_component_closed_parameter_cross_relation
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p /
        algebraMap (MvPolynomial (Fin 4) K) S₀ q) :
    ∃ tval : E, tval ≠ 0 ∧
      MvPolynomial.map (algebraMap K E) p - C tval * MvPolynomial.map (algebraMap K E) q ∈ P := by
  let M := polynomialOutputField H
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let mGAlgebra : Algebra M G := inferInstance
  let : SMul M G := mGAlgebra.toSMul
  let : IsScalarTower M E G := inferInstance
  let : IsScalarTower K M G := IsScalarTower.of_algebraMap_eq
    (R := K) (S := M) (A := G) (by
      intro r
      rw [IsScalarTower.algebraMap_apply K E G, IsScalarTower.algebraMap_apply K M E,
        ← IsScalarTower.algebraMap_apply M E G])
  have hr : (rationalJacobian (Q₀)).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq
    (rationalCoordinate (K := K) (n := 4)) (primeQuotientCoordinate P)
    (rationalSource_adjoin_coordinates_eq_top M)
    (componentGenericPoint_original_relations (rationalCoordinate (K := K) (n := 4)) P hP)
  let t : S₀ := closedGaussParameterSourceHom H I e RatFunc.X
  have htmem : t ∈ coefficientField (K := K) (fun i : Fin 3 => (Q₀) (s i.castSucc)) :=
    actual_closed_gauss_field_le_graph_coefficient_field H I s hY h hh (e RatFunc.X).property
  have htalg : IsAlgebraic M t :=
    (fullOutput_algebraic_iff_coefficientField (Q₀) hr s hY t).mpr htmem
  have htalgE : IsAlgebraic E (f t) := (IsAlgebraic.algHom f htalg).tower_top E
  obtain ⟨tval, htvalmap⟩ := algebraic_value_preimage_of_isAlgClosed (f t) htalgE
  have hev (R : MvPolynomial (Fin 4) K) :
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ R) =
        aeval (primeQuotientCoordinate P) (MvPolynomial.map (algebraMap K E) R) := by
    rw [aeval_map_coefficients]
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) (f.restrictScalars K) R
    have he' : f (aeval (rationalCoordinate (K := K) (n := 4)) R) =
        aeval (primeQuotientCoordinate P) R := by
      simpa only [AlgHom.restrictScalars_apply, hf] using he
    rw [rationalCoordinate_aeval] at he'
    exact he'
  have hqF : algebraMap (MvPolynomial (Fin 4) K) S₀ q ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀).ne hq
  have hpF : algebraMap (MvPolynomial (Fin 4) K) S₀ p ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀).ne hp
  have htF : t ≠ 0 := by
    change closedGaussParameterSourceHom H I e RatFunc.X ≠ 0
    rw [ht]
    exact div_ne_zero hpF hqF
  have htval : tval ≠ 0 := by
    intro hz
    have htG : f t ≠ 0 := by
      intro hzero
      apply htF
      apply f.injective
      exact hzero.trans (map_zero f).symm
    apply htG
    calc
      f t = algebraMap E G tval := htvalmap.symm
      _ = 0 := (congrArg (algebraMap E G) hz).trans (map_zero _)
  refine ⟨tval, htval, ?_⟩
  have hzero := compatible_parameter_fraction_polynomial_relation f.toRingHom
    (algebraMap (MvPolynomial (Fin 4) K) S₀)
    (aeval (primeQuotientCoordinate P) : MvPolynomial (Fin 4) E →ₐ[E] G) hev t tval htvalmap p q hqF ht
  have hmem : MvPolynomial.map (algebraMap K E) p - C tval *
      MvPolynomial.map (algebraMap K E) q ∈
        fiberVanishingIdeal (L := E) (primeQuotientCoordinate P) := by
    exact hzero
  exact (primeQuotientCoordinate_relations P) ▸ hmem

end DimensionFourDependence
