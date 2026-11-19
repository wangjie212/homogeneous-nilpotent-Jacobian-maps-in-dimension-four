import DimensionFourDependence.GeometricGenericDegree

/-! # The degree bound for the full-output geometric generic fiber

The generic affine fiber is represented by the prime of relations among
the source coordinates over `K(H)`. Every prime component after extending
to algebraically closed algebraic constants has projective Hilbert degree
between one and six in the original four source coordinates.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- All rational source coordinates generate the source field over any
intermediate coefficient field containing the original field. -/
theorem rationalSource_adjoin_coordinates_eq_top (E : Type*) [Field E] [Algebra K E]
    [Algebra E (FractionRing (MvPolynomial (Fin n) K))]
    [IsScalarTower K E (FractionRing (MvPolynomial (Fin n) K))] :
    IntermediateField.adjoin E (Set.range (rationalCoordinate (K := K) (n := n))) = ⊤ := by
  let A := IntermediateField.adjoin E (Set.range (rationalCoordinate (K := K) (n := n)))
  have hA : A.restrictScalars K = ⊤ := by
    apply rationalSource_field_eq_top_of_coordinates
    intro i
    exact IntermediateField.subset_adjoin E _ ⟨i, rfl⟩
  apply top_unique
  intro z _
  change z ∈ A
  have hz : z ∈ A.restrictScalars K := by rw [hA]; trivial
  exact hz

variable [CharZero K]

/-- On every geometric component the actual algebraic coefficient field
embeds in the constants, compatibly with the embedded source coordinates. -/
theorem full_output_geometric_coefficient_embedding
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (W : FiberEquationWitness H)
    (E : Type*) [Field E] [Algebra (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    let M := fullOutputField (K := K) H
    let L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))
    letI := fullOutputCoefficientAlgebra H hrank W.chart W.independent
    ∃ f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[M]
        FractionRing (MvPolynomial (Fin 4) E ⧸ P),
      (∀ i, f (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i) ∧
      ∃ g : L →ₐ[M] E, ∀ l : L,
        algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (g l) =
          f (algebraMap L (FractionRing (MvPolynomial (Fin 4) K)) l) := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))
  let : Algebra M L := fullOutputCoefficientAlgebra H hrank W.chart W.independent
  let : IsScalarTower M L (FractionRing (MvPolynomial (Fin 4) K)) :=
    IsScalarTower.of_algebraMap_eq (R := M) (S := L)
      (A := FractionRing (MvPolynomial (Fin 4) K)) (by intro a; rfl)
  let : Algebra.IsAlgebraic M L := fullOutputCoefficient_isAlgebraic H hrank W.chart W.independent
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq
    (rationalCoordinate (K := K) (n := 4)) (primeQuotientCoordinate P)
    (rationalSource_adjoin_coordinates_eq_top M)
    (componentGenericPoint_original_relations (rationalCoordinate (K := K) (n := 4)) P hP)
  obtain ⟨g, hg⟩ := exists_algebraic_coefficient_embedding (L := L) (E := E) f
  exact ⟨f, hf, g, hg⟩

/-- The full-output geometric generic-fiber degree bound, with its
verified hyperplane/quadric/cubic witness supplied explicitly. -/
theorem full_output_geometric_fiber_degree
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) (E : Type*) [Field E]
    [Algebra (fullOutputField (K := K) H) E]
    [Algebra.IsAlgebraic (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveConeIdeal (L := E) (primeQuotientCoordinate P)) d := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))
  let : Algebra M L := fullOutputCoefficientAlgebra H hrank W.affine.chart W.affine.independent
  let : IsScalarTower M L (FractionRing (MvPolynomial (Fin 4) K)) :=
    IsScalarTower.of_algebraMap_eq (R := M) (S := L)
      (A := FractionRing (MvPolynomial (Fin 4) K)) (by intro a; rfl)
  let : Algebra.IsAlgebraic M L :=
    fullOutputCoefficient_isAlgebraic H hrank W.affine.chart W.affine.independent
  obtain ⟨i, hi⟩ := exists_transcendental_coordinate
    (L := L) (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))
    (fiber_witness_coordinate_field_eq_top H W.affine.toFiberEquationWitness)
    (by rw [fiber_witness_trdeg_eq_one H hN hrank W.affine.toFiberEquationWitness]; exact one_ne_zero)
  have hiM : Transcendental M (rationalCoordinate (K := K) (W.affine.chart i.castSucc)) :=
    fun ha => hi (ha.tower_top L)
  apply geometric_component_degree_of_algebraic_coefficients (L := L)
    (rationalCoordinate (K := K) (n := 4)) (rationalSource_adjoin_coordinates_eq_top M)
    (W.affine.chart i.castSucc) hiM _ P hP
  intro d hd
  rw [fiber_witness_full_source_hilbert H W.affine.toFiberEquationWitness]
  exact projective_fiber_witness_hilbert_le_six H W d hd

/-- Every component of the actual full-output geometric generic fiber
has positive projective Hilbert degree at most six. All auxiliary fiber
equations are constructed from the nilpotent rank-three hypothesis. -/
theorem nilpotent_rank_three_geometric_fiber_degree
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (E : Type*) [Field E] [Algebra (fullOutputField (K := K) H) E]
    [Algebra.IsAlgebraic (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveConeIdeal (L := E) (primeQuotientCoordinate P)) d := by
  obtain ⟨W⟩ := exists_projective_fiber_equation_witness H hN hrank
  exact full_output_geometric_fiber_degree H hN hrank W E P hP

/-- The degree conclusion of Lemma 2.2 for the original polynomial map,
over an algebraic closure of the full output field. -/
theorem polynomial_geometric_generic_fiber_degree
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E]
    [Algebra (fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) E]
    [Algebra.IsAlgebraic (fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
      (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveConeIdeal (L := E) (primeQuotientCoordinate P)) d := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hJ : rationalJacobian Q = (jac H).map
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))) :=
    rationalJacobian_polynomial H
  apply nilpotent_rank_three_geometric_fiber_degree Q _ _ E P hP
  · rw [hJ]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  · rw [hJ]
    exact hrank

end DimensionFourDependence
