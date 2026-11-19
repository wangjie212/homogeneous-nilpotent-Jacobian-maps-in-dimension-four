import DimensionFourDependence.ZeroDimensionalGaussImage
import DimensionFourDependence.Proposition31

/-! # Reduction of a nonplanar nonlinear-fiber image to the two surface exclusions

The actual Gauss image has dimension at most two, and dimension zero
forces a constant component relation over the original field. The only
remaining dimensions are one and two. Proposition 3.1 identifies the
second case with a geometrically smooth quadric, leaving precisely the
developable and smooth-quadric exclusions of Sections 4 and 5.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- A homogeneous nilpotent map with independent components has degree
strictly greater than one. -/
theorem independent_homogeneous_nilpotent_degree_gt_one
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H) : 1 < d := by
  have hd1 : d ≠ 1 := by
    intro he
    subst d
    exact hind (dependence_degree_one H hH hN)
  omega

/-- For the original rank-three map with independent components, the
actual Gauss-image function field has dimension exactly one or two. -/
theorem independent_gauss_image_dimension_one_or_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H) :
    gaussImageDimension H I = 1 ∨ gaussImageDimension H I = 2 := by
  have hz : gaussImageDimension H I ≠ 0 :=
    fun h => hind (componentsDependent_of_gauss_image_dimension_zero H hd hH I h)
  by_cases hle : gaussImageDimension H I ≤ 1
  · exact Or.inl ((Cardinal.le_one_iff.mp hle).resolve_left hz)
  · exact Or.inr (le_antisymm (gauss_image_dimension_le_two H hd hH hN hrank I)
      (Cardinal.two_le_iff_one_lt.mpr (lt_of_not_ge hle)))

universe u

/-- The actual nonlinear full-output geometric generic component of a
nonplanar original rank-three map leaves exactly the two cases needed
by Sections 4 and 5. No Gauss-dimension exhaustiveness or geometric
coefficient comparison is assumed. -/
theorem nonlinear_geometric_image_developable_or_smooth_quadric
    {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [IsScalarTower K (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    1 < d ∧ (gaussImageDimension H I = 1 ∨
      I.degree = 2 ∧
      (∀ x : Fin 4 → K, x ≠ 0 → (fun i => aeval x (pderiv i I.equation)) ≠ 0) ∧
      (∀ x : Fin 4 → AlgebraicClosure K, x ≠ 0 →
        (fun i => aeval x (pderiv i (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) I.equation))) ≠ 0) ∧
      ∃ (e : (Fin 4 → AlgebraicClosure K) ≃ₗ[AlgebraicClosure K]
          ((Fin 2 → AlgebraicClosure K) × (Fin 2 → AlgebraicClosure K))) (c : AlgebraicClosure K),
        c ≠ 0 ∧ rulingPolynomialInCoordinates e = MvPolynomial.C c *
          MvPolynomial.map (algebraMap K (AlgebraicClosure K)) I.equation ∧
        ∀ x : Fin 4 → AlgebraicClosure K,
          aeval x (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) I.equation) = 0 ↔
          standardRulingQuadric (e x) = 0) := by
  refine ⟨independent_homogeneous_nilpotent_degree_gt_one H hd hH hN hind, ?_⟩
  rcases independent_gauss_image_dimension_one_or_two H hd hH hN hrank hind I with h | h
  · exact Or.inl h
  · exact Or.inr (proposition_3_1 H hd hH hN hrank hind I h P hP hline (AlgebraicClosure K))

end DimensionFourDependence
