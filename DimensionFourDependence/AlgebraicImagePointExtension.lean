import DimensionFourDependence.ScalarExtendedImageEquation
import DimensionFourDependence.GenericOutputPoint
import DimensionFourDependence.FiberAlgebraicBaseChange

/-! # Exact image-point relations after an algebraic coefficient extension

The evaluation prime contracts to the actual original image ideal.
An algebraic coefficient extension is integral, so this evaluation prime
is minimal over the extended original image ideal. That extended ideal
is already prime by the checked polynomial image base-change theorem.
The two primes therefore coincide, giving exact extended relations.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Algebra.IsAlgebraic K F]

/-- An actual point with exactly the original polynomial image
relations retains exactly the scalar-extended image relations after
adjoining algebraic coefficients inside its ambient field. -/
theorem algebraic_coefficient_extension_image_point_relations
    (H : Fin 4 → MvPolynomial (Fin 4) K) (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0) :
    ∀ P : MvPolynomial (Fin 4) F, aeval O P = 0 ↔
      aeval (fun i => MvPolynomial.map (algebraMap K F) (H i)) P = 0 := by
  let J : Ideal (MvPolynomial (Fin 4) F) :=
    RingHom.ker (aeval O : MvPolynomial (Fin 4) F →ₐ[F] E)
  let : J.IsPrime := RingHom.ker_isPrime _
  have hcomp : J.comap (MvPolynomial.map (algebraMap K F)) = imageRelationIdeal H := by
    ext P
    change aeval (R := F) O (MvPolynomial.map (algebraMap K F) P) = 0 ↔ aeval H P = 0
    rw [aeval_map_algebra_extension]
    exact hrel P
  have hint : (MvPolynomial.map (algebraMap K F) (σ := Fin 4)).IsIntegral := by
    rw [← MvPolynomial.algebraMap_def]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hmin := prime_minimal_over_integral_extension
    (MvPolynomial.map (algebraMap K F)) hint (imageRelationIdeal H) J hcomp
  have hprime : (extendCoefficientIdeal F (imageRelationIdeal H)).IsPrime :=
    imageRelationIdeal_scalar_extension_isPrime F H
  have heq : J = extendCoefficientIdeal F (imageRelationIdeal H) := by
    exact le_antisymm (hmin.2 ⟨hprime, le_rfl⟩ hmin.le) hmin.le
  have hj : J = imageRelationIdeal (fun i => MvPolynomial.map (algebraMap K F) (H i)) :=
    heq.trans (imageRelationIdeal_scalar_extension F H)
  intro P
  change P ∈ J ↔ P ∈ imageRelationIdeal (fun i => MvPolynomial.map (algebraMap K F) (H i))
  rw [hj]

/-- The actual generic output keeps its exact image relations after
the algebraic coefficient extension used for the geometric argument. -/
theorem genericOutputValue_algebraic_coefficient_extension_relations
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E] :
    ∀ P : MvPolynomial (Fin 4) F, aeval (genericOutputValue H E) P = 0 ↔
      aeval (fun i => MvPolynomial.map (algebraMap K F) (H i)) P = 0 :=
  algebraic_coefficient_extension_image_point_relations H (genericOutputValue H E)
    (genericOutputValue_relations H E)

end DimensionFourDependence
