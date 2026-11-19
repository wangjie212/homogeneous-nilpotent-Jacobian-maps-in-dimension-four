import DimensionFourDependence.PolynomialMapScalarExtension
import DimensionFourDependence.ConstantVertexGaussDimension

/-! # The map and normal obstructions survive coefficient extension

Homogeneity, nilpotence and rational Jacobian rank commute with the
actual coefficient map. Constant component independence descends by the
checked coefficient functional argument. Gauss dimension two makes the
original normal polynomials independent, so the same vertex obstruction
holds over every extended coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Actual positive-degree homogeneity is preserved by coefficient extension. -/
theorem isHomogMap_map_coefficients
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d) :
    IsHomogMap (fun i => MvPolynomial.map (algebraMap K F) (H i)) d :=
  fun i => (hH i).map (algebraMap K F)

/-- Actual nilpotence is preserved by the coefficient-extended Jacobian. -/
theorem nilpotent_jac_map_coefficients
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H)) :
    IsNilpotent (jac (fun i => MvPolynomial.map (algebraMap K F) (H i))) := by
  rw [jac_map_coefficients]
  exact hN.map (MvPolynomial.map (algebraMap K F)).mapMatrix

/-- Component independence is preserved over every extended coefficient field. -/
theorem componentsIndependent_map_coefficients
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H) :
    ¬ ComponentsDependent (fun i => MvPolynomial.map (algebraMap K F) (H i)) :=
  fun h => hind (componentsDependent_of_map F H h)

variable [CharZero K]

omit [Field F] [Algebra K F] in
/-- Gauss dimension two forces the four actual image-normal polynomials
to be linearly independent over the original coefficient field. -/
theorem ImageRelationWitness.normal_components_independent_of_gauss_dimension_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2) :
    ¬ ComponentsDependent (imageRelationNormal H I.equation) := by
  rintro ⟨v, hv, hrel⟩
  apply hv
  apply gauss_dimension_two_no_constant_image_normal_vertex H hd hH hN hrank I hGauss v
  simpa only [MvPolynomial.smul_eq_C_mul] using hrel

/-- Independence of the original actual normal survives in the full
extended image-equation witness. -/
theorem ImageRelationWitness.scalar_extended_normal_components_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hNormal : ¬ ComponentsDependent (imageRelationNormal H I.equation)) :
    ¬ ComponentsDependent (imageRelationNormal (fun i => MvPolynomial.map (algebraMap K F) (H i))
      (I.scalarExtension (E := F) H hrank).equation) := by
  change ¬ ComponentsDependent (imageRelationNormal (fun i => MvPolynomial.map (algebraMap K F) (H i))
    (MvPolynomial.map (algebraMap K F) I.equation))
  rw [imageRelationNormal_scalar_extension]
  exact fun h => hNormal (componentsDependent_of_map F (imageRelationNormal H I.equation) h)

/-- The original Gauss-dimension-two hypotheses supply the actual
normal rigidity over every extended coefficient field directly. -/
theorem ImageRelationWitness.gauss_two_scalar_extended_normal_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2) :
    ¬ ComponentsDependent (imageRelationNormal (fun i => MvPolynomial.map (algebraMap K F) (H i))
      (I.scalarExtension (E := F) H hrank).equation) :=
  I.scalar_extended_normal_components_independent H hrank
    (I.normal_components_independent_of_gauss_dimension_two H hd hH hN hrank hGauss)

end DimensionFourDependence
