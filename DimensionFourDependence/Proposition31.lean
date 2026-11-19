import DimensionFourDependence.AlgebraicCoefficientQuadric
import DimensionFourDependence.GradientFieldExtension

/-! # Proposition 3.1 over the original characteristic-zero field

An algebraic closure of the original coefficient field embeds in the
algebraically closed constants of the actual generic fiber. The two
actual lines are constructed there from the original map and component.
The algebraic-coefficient quadric theorem then identifies the original
image equation over that algebraic closure, with a nonsingular gradient.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- Proposition 3.1: over every characteristic-zero original field, an
actual nonlinear geometric generic component and actual Gauss-image
dimension two force the image to be a geometrically smooth quadric.
The original defining equation is quadratic and is exactly a nonzero
scalar multiple of the determinant in invertible coordinates over any
algebraically closed algebraic extension of the original field. -/
theorem proposition_3_1
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2)
    [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [IsScalarTower K (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P))
    (F : Type u) [Field F] [Algebra K F] [IsAlgClosed F] [Algebra.IsAlgebraic K F] :
    I.degree = 2 ∧
      (∀ x : Fin 4 → K, x ≠ 0 → (fun i => aeval x (pderiv i I.equation)) ≠ 0) ∧
      (∀ x : Fin 4 → F, x ≠ 0 →
        (fun i => aeval x (pderiv i (MvPolynomial.map (algebraMap K F) I.equation))) ≠ 0) ∧
      ∃ (e : (Fin 4 → F) ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F))) (c : F), c ≠ 0 ∧
        rulingPolynomialInCoordinates e = MvPolynomial.C c * MvPolynomial.map (algebraMap K F) I.equation ∧
        ∀ x : Fin 4 → F, aeval x (MvPolynomial.map (algebraMap K F) I.equation) = 0 ↔
          standardRulingQuadric (e x) = 0 := by
  let f : F →ₐ[K] E := IsAlgClosed.lift
  let : Algebra F E := f.toRingHom.toAlgebra
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun k => (f.commutes k).symm)
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, k, hh, hc, hq, hk⟩ :=
    fiberEquationWitness_exists_invariant_coefficients H hN hrank W
  obtain ⟨s, t, _, hne, hs, ht⟩ := geometric_fiber_two_actual_line_atlas_points
    H hd hH hN hrank hind W h c q k hh hc hq hk E P hP hline I hGauss
  obtain ⟨hdeg, hsmooth, hcoordinates⟩ := algebraic_coefficient_extension_two_lines_quadric (F := F)
    H hd hH hN hrank hind I hGauss (genericOutputValue H E)
    (genericOutputValue_relations H E) s t hs ht hne
  exact ⟨hdeg, projective_gradient_nonvanishing_descends I.equation hsmooth, hsmooth, hcoordinates⟩

end DimensionFourDependence
