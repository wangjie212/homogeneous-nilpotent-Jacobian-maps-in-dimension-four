import DimensionFourDependence.ClosedGaussCoefficientRealization

/-! # The actual second-graph-derivative numerator retained by the root construction

The weighted root argument constructs n from the original second
parameter derivatives of the graph gradient. These definitions keep
those coefficients, their original source labels and the precise normal
pivot rescaling used in the chosen native tangent-plane formula.
-/

namespace DimensionFourDependence

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

section Chart

variable (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The actual second graph-gradient parameter derivative as an
element of the original closed Gauss field. -/
noncomputable def closedGaussRootNumeratorCoefficient (i : Fin 3) : closedGaussParameterField H I :=
  e (rationalParameterDerivative K (rationalParameterDerivative K
    (closedGaussCoefficientGraphSlope H I p hY h hh e i)))

/-- The actual four-coordinate numerator covector after precisely
the same nonzero normal-pivot rescaling as the chosen-plane root formula. -/
noncomputable def closedGaussCanonicalRootNumerator
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E] : Fin 4 → E :=
  (algebraMap (closedGaussParameterField H I) E
    (e (closedGaussParameterNormal H I e (p 3))))⁻¹ •
      (Fin.snoc (fun i => algebraMap (closedGaussParameterField H I) E
        (closedGaussRootNumeratorCoefficient H I p hY h hh e i)) 0 ∘ p.symm)

end Chart

/-- A numerator whose original graph chart and exact second-normal
derivative provenance are retained, rather than assumed geometrically. -/
noncomputable def HasActualGaussRootNumerator
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (cN : Fin 4 → E) : Prop :=
  ∃ (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3))),
    cN = closedGaussCanonicalRootNumerator H I p hY h hh e E

end DimensionFourDependence
