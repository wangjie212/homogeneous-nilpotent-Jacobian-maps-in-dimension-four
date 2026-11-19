import DimensionFourDependence.RationalCoverParameterScheme
import DimensionFourDependence.ExtendedGaussSourceMorphism

/-! # The actual normalized affine parameter curve for a closed Gauss cover -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The specified rational Gauss parameter acts on the actual
coefficient extension through its original closed Gauss field. -/
noncomputable def closedGaussCoverRatFuncAlgebra : Algebra (RatFunc K) E :=
  ((algebraMap (closedGaussParameterField H I) E).comp e.toRingHom).toAlgebra

/-- An actual normalized affine parameter curve with the specified
extension field, formed over the original rational Gauss parameter. -/
noncomputable def closedGaussCoverParameterScheme : Scheme.{u} :=
  letI := closedGaussCoverRatFuncAlgebra H I E e
  rationalCoverParameterScheme K E

/-- Its actual original-field structure morphism. -/
noncomputable def closedGaussCoverParameterSchemeToBase :
    closedGaussCoverParameterScheme H I E e ⟶ Spec (CommRingCat.of K) := by
  letI := closedGaussCoverRatFuncAlgebra H I E e
  exact rationalCoverParameterSchemeToBase K E

/-- The actual extension-field point of the normalized parameter curve. -/
noncomputable def closedGaussCoverParameterGenericMorphism :
    Spec (CommRingCat.of E) ⟶ closedGaussCoverParameterScheme H I E e := by
  letI := closedGaussCoverRatFuncAlgebra H I E e
  exact rationalCoverParameterGenericMorphism K E

/-- The parameter curve's field morphism uses the same original
constant-field embedding as the actual extended projective source. -/
theorem closedGaussCoverParameterGenericMorphism_over :
    closedGaussCoverParameterGenericMorphism H I E e ≫
        closedGaussCoverParameterSchemeToBase H I E e =
      Spec.map (CommRingCat.ofHom (extendedClosedGaussSourceCoefficientHom H I E)) := by
  letI := closedGaussCoverRatFuncAlgebra H I E e
  have hc : CommRingCat.ofHom
      ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))) =
        CommRingCat.ofHom (extendedClosedGaussSourceCoefficientHom H I E) := by
    ext k
    change algebraMap (closedGaussParameterField H I) E (e (algebraMap K (RatFunc K) k)) =
      algebraMap (closedGaussParameterField H I) E (algebraMap K (closedGaussParameterField H I) k)
    rw [e.commutes]
  exact (rationalCoverParameterGenericMorphism_over K E).trans (congrArg Spec.map hc)

/-- The actual normalized parameter curve is integral. -/
theorem closedGaussCoverParameterScheme_isIntegral :
    IsIntegral (closedGaussCoverParameterScheme H I E e) := by
  letI := closedGaussCoverRatFuncAlgebra H I E e
  exact rationalCoverParameterScheme_isIntegral K E

/-- A finite closed-Gauss-field extension is finite over the actual
original rational parameter as well. -/
theorem closedGaussCoverRatFunc_finite [Module.Finite (closedGaussParameterField H I) E] :
    letI := closedGaussCoverRatFuncAlgebra H I E e
    Module.Finite (RatFunc K) E := by
  letI := closedGaussCoverRatFuncAlgebra H I E e
  let : Algebra (RatFunc K) (closedGaussParameterField H I) := e.toRingHom.toAlgebra
  let : Module.Finite (RatFunc K) (closedGaussParameterField H I) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) (closedGaussParameterField H I)) e.surjective
  let : IsScalarTower (RatFunc K) (closedGaussParameterField H I) E :=
    IsScalarTower.of_algebraMap_eq (by intro r; rfl)
  exact Module.Finite.trans (R := RatFunc K) (closedGaussParameterField H I) E

/-- The actual normalized parameter scheme is Noetherian for every
finite coefficient-field extension used in Lemma 4.2. -/
theorem closedGaussCoverParameterScheme_isNoetherian
    [Module.Finite (closedGaussParameterField H I) E] :
    IsNoetherian (closedGaussCoverParameterScheme H I E e) := by
  letI := closedGaussCoverRatFuncAlgebra H I E e
  let : Module.Finite (RatFunc K) E := closedGaussCoverRatFunc_finite H I E e
  exact rationalCoverParameterScheme_isNoetherian K E

end DimensionFourDependence
