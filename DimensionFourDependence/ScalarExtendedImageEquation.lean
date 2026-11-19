import DimensionFourDependence.ImageIdealFieldExtension
import DimensionFourDependence.ProjectiveLineAtlasPoints

/-! # The actual image equation remains irreducible after field extension

Its principal ideal is the prime scalar extension of the polynomial image
ideal. The actual evaluated normal also commutes with coefficient extension.
Together these facts construct a full image-equation witness over every
extension field, with the original homogeneous degree.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Polynomial-map evaluation commutes with extension of every coefficient. -/
theorem aeval_polynomial_map_scalar_extension
    (H : Fin 4 → MvPolynomial (Fin 4) K) (R : MvPolynomial (Fin 4) K) :
    aeval (fun i => MvPolynomial.map (algebraMap K E) (H i))
      (MvPolynomial.map (algebraMap K E) R) = MvPolynomial.map (algebraMap K E) (aeval H R) := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) E :=
    MvPolynomial.mapAlgHom (Algebra.ofId K E)
  calc
    _ = aeval (R := K) (fun i => MvPolynomial.map (algebraMap K E) (H i)) R :=
      aeval_map_algebra_extension R _
    _ = f (aeval H R) := (comp_aeval_apply H f R).symm
    _ = _ := rfl

/-- The evaluated gradient of the actual equation commutes with coefficient extension. -/
theorem imageRelationNormal_scalar_extension
    (H : Fin 4 → MvPolynomial (Fin 4) K) (R : MvPolynomial (Fin 4) K) :
    imageRelationNormal (fun i => MvPolynomial.map (algebraMap K E) (H i))
      (MvPolynomial.map (algebraMap K E) R) =
      fun i => MvPolynomial.map (algebraMap K E) (imageRelationNormal H R i) := by
  funext i
  unfold imageRelationNormal
  rw [MvPolynomial.pderiv_map, aeval_polynomial_map_scalar_extension]

variable [CharZero K]

/-- The scalar-extended defining equation of the actual rank-three image is prime. -/
theorem ImageRelationWitness.scalar_extended_equation_prime
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) : Prime (MvPolynomial.map (algebraMap K E) I.equation) := by
  have hzero : MvPolynomial.map (algebraMap K E) I.equation ≠ 0 := by
    simpa only [map_zero] using
      (MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective).ne
        I.irreducible.ne_zero
  have heq : extendCoefficientIdeal E (imageRelationIdeal H) =
      Ideal.span {MvPolynomial.map (algebraMap K E) I.equation} := by
    unfold extendCoefficientIdeal
    rw [I.ideal_eq_span H hrank, Ideal.map_span, Set.image_singleton]
  apply (Ideal.span_singleton_prime hzero).mp
  rw [← heq]
  exact imageRelationIdeal_scalar_extension_isPrime E H

/-- The actual image equation is geometrically irreducible under every field extension. -/
theorem ImageRelationWitness.scalar_extended_equation_irreducible
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) : Irreducible (MvPolynomial.map (algebraMap K E) I.equation) :=
  (I.scalar_extended_equation_prime (E := E) H hrank).irreducible

/-- A full defining-equation witness for the scalar-extended polynomial image. -/
noncomputable def ImageRelationWitness.scalarExtension
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) :
    ImageRelationWitness (fun i => MvPolynomial.map (algebraMap K E) (H i)) where
  equation := MvPolynomial.map (algebraMap K E) I.equation
  degree := I.degree
  degree_pos := I.degree_pos
  homogeneous := I.homogeneous.map (algebraMap K E)
  irreducible := I.scalar_extended_equation_irreducible H hrank
  vanishing := by rw [aeval_polynomial_map_scalar_extension, I.vanishing, map_zero]
  normal_ne_zero := by
    intro hz
    rw [imageRelationNormal_scalar_extension] at hz
    apply I.normal_ne_zero
    funext i
    apply MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun hz i

end DimensionFourDependence
