import DimensionFourDependence.PlaneTranslateDescent

/-! # The geometric fixed-plane assertion of Proposition 2.3

Containment in a translate of one fixed original-field two-space
descends from a geometric component to the actual coefficient field.
Nonlinearity descends as well. The verified function-field criterion
therefore gives component dependence for the original polynomial map.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A geometric generic component's containment in a fixed direction
plane descends to the actual coefficient field of the source. -/
theorem geometric_component_plane_implies_actual_fiber_plane
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (W : FiberEquationWitness H)
    (E : Type*) [Field E] [Algebra (fullOutputField (K := K) H) E]
    [Algebra K E] [IsScalarTower K (fullOutputField (K := K) H) E]
    [Algebra.IsAlgebraic (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hplane : LiesInConstantPlaneTranslate (E := E) v w (primeQuotientCoordinate P)) :
    LiesInConstantPlaneTranslate
      (E := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))) v w
      (rationalCoordinate (K := K) (n := 4)) := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let mGAlgebra : Algebra M G := inferInstance
  let : SMul M G := mGAlgebra.toSMul
  let : IsScalarTower M E G := inferInstance
  let : Algebra M L := fullOutputCoefficientAlgebra H hrank W.chart W.independent
  let : IsScalarTower K M G := IsScalarTower.of_algebraMap_eq
    (R := K) (S := M) (A := G) (by
      intro c
      rw [IsScalarTower.algebraMap_apply K E G, IsScalarTower.algebraMap_apply K M E,
        ← IsScalarTower.algebraMap_apply M E G])
  obtain ⟨f, hf, _, _⟩ := full_output_geometric_coefficient_embedding H hrank W E P hP
  obtain ⟨a, r, s, hpos⟩ := hplane
  have hpos' (i : Fin 4) : f (rationalCoordinate (K := K) i) = algebraMap E G (a i) +
      algebraMap M G (algebraMap K M (v i)) * r +
      algebraMap M G (algebraMap K M (w i)) * s := by
    rw [hf i]
    simpa only [← IsScalarTower.algebraMap_apply K M G] using hpos i
  obtain ⟨b, hb, p, q, hsource⟩ := plane_translate_algebraic_descent
    (algebraMap K M) f v w hvw (rationalCoordinate (K := K) (n := 4)) a r s hpos'
  let a' : Fin 4 → L := fun i => ⟨b i,
    (fullOutput_algebraic_iff_coefficientField H hrank W.chart W.independent (b i)).mp (hb i)⟩
  refine ⟨a', p, q, ?_⟩
  intro i
  change rationalCoordinate (K := K) i = b i +
    algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i) * p +
    algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (w i) * q
  simpa only [← IsScalarTower.algebraMap_apply K M (FractionRing (MvPolynomial (Fin 4) K))] using hsource i

/-- The fixed-plane assertion of Proposition 2.3 for an actual nonlinear
geometric generic component over the full output field. All fiber,
coefficient, tangent and normal choices are constructed in the proof. -/
theorem dependence_of_geometric_nonlinear_fixed_plane_fiber
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E]
    [Algebra (fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) E]
    [Algebra K E] [IsScalarTower K (fullOutputField (K := K) (fun i =>
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i))) E]
    [Algebra.IsAlgebraic (fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
      (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hplane : LiesInConstantPlaneTranslate (E := E) v w (primeQuotientCoordinate P))
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : ComponentsDependent H := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hrQ : (rationalJacobian Q).rank = 3 := by rw [rationalJacobian_polynomial H]; exact hrank
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  have hactualPlane := geometric_component_plane_implies_actual_fiber_plane Q hrQ W E P hP v w hvw hplane
  have hactualNonlinear := geometric_component_nonlinear_implies_actual_fiber_nonlinear Q hrQ W E P hP hline
  exact dependent_of_nonlinear_fiber_in_fixed_plane H hd hH hN hrank W v w hvw hactualPlane hactualNonlinear

end DimensionFourDependence
