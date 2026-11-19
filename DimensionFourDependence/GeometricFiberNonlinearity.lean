import DimensionFourDependence.PlanarFiberDependence

/-! # Comparing affine-line containment with actual geometric components

A compatible source-field/coefficient-field embedding carries an actual
line to a geometric line. Thus a nonlinear geometric generic component
forces nonlinearity over the actual coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F E G : Type*} [Field L] [Field F] [Field E] [Field G]
    [Algebra L F] [Algebra E G] {n : ℕ}

/-- An affine line remains an affine line under compatible embeddings. -/
theorem LiesInAffineLine.map_of_compatible (f : F →+* G) (g : L →+* E)
    (hcomp : ∀ l : L, algebraMap E G (g l) = f (algebraMap L F l))
    (x : Fin n → F) (hx : LiesInAffineLine (E := L) x) :
    LiesInAffineLine (E := E) (f ∘ x) := by
  obtain ⟨a, v, hv, t, hpos⟩ := hx
  refine ⟨g ∘ a, g ∘ v, ?_, f t, ?_⟩
  · intro hz
    apply hv
    funext i
    apply g.injective
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i
  · intro i
    change f (x i) = algebraMap E G (g (a i)) + algebraMap E G (g (v i)) * f t
    rw [hcomp, hcomp]
    simpa only [map_add, map_mul] using congrArg f (hpos i)

variable {K : Type*} [Field K] [CharZero K]

/-- Nonlinearity of any actual full-output geometric generic component
implies nonlinearity over the verified relative algebraic coefficient field. -/
theorem geometric_component_nonlinear_implies_actual_fiber_nonlinear
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (W : FiberEquationWitness H)
    (E : Type*) [Field E] [Algebra (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ¬ LiesInAffineLine
      (E := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (rationalCoordinate (K := K) (n := 4)) := by
  let := fullOutputCoefficientAlgebra H hrank W.chart W.independent
  obtain ⟨f, hf, g, hg⟩ := full_output_geometric_coefficient_embedding H hrank W E P hP
  intro hx
  apply hline
  have hm := LiesInAffineLine.map_of_compatible f.toRingHom g.toRingHom hg
    (rationalCoordinate (K := K) (n := 4)) hx
  have he : f.toRingHom ∘ rationalCoordinate (K := K) (n := 4) = primeQuotientCoordinate P := by
    funext i
    exact hf i
  rwa [he] at hm

/-- A nonlinear actual geometric component gives dependence when the
actual source fiber lies in a translate of one fixed original-field plane.
Descent of the plane-translation hypothesis itself is a separate step. -/
theorem dependent_of_geometric_nonlinearity_and_fixed_actual_plane
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (W : FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hplane : LiesInConstantPlaneTranslate
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc)))) v w
      (rationalCoordinate (K := K) (n := 4)))
    (E : Type*) [Field E]
    [Algebra (fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
      (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : ComponentsDependent H := by
  apply dependent_of_nonlinear_fiber_in_fixed_plane H hd hH hN hrank W v w hvw hplane
  apply geometric_component_nonlinear_implies_actual_fiber_nonlinear _ _ W E P hP hline
  rw [rationalJacobian_polynomial H]
  exact hrank

end DimensionFourDependence
