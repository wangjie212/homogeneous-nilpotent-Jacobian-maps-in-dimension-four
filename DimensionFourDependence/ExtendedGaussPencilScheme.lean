import DimensionFourDependence.ExtendedGaussPencilPrime
import DimensionFourDependence.FiniteIntegralSchemeNormalization
import DimensionFourDependence.IntegralSchemeNormalizationNormal
import DimensionFourDependence.PolynomialProjectiveBase

/-! # The actual projective pencil normalized after coefficient extension

The extended original homogeneous prime defines the actual projective
pencil over the algebraic coefficient field. Its reduced closed scheme
is integral and proper. Normalizing that extended scheme, in that order,
constructs a finite normal proper global scheme over the extended field.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The actual reduced closed projective pencil after coefficient extension. -/
noncomputable def extendedClosedGaussPencilScheme : Scheme.{u} :=
  reducedPointClosureScheme (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E))
    (extendedClosedGaussPencilGenericPoint H I E hH e)

/-- The extended pencil in the original four-coordinate projective space. -/
noncomputable def extendedClosedGaussPencilSchemeInclusion :
    extendedClosedGaussPencilScheme H I E hH e ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E) :=
  reducedPointClosureInclusion _ _

/-- The actual extended pencil is integral. -/
theorem extendedClosedGaussPencilScheme_isIntegral :
    IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
  reducedPointClosureScheme_isIntegral _ _

/-- Its original-coordinate projective inclusion is a closed immersion. -/
theorem extendedClosedGaussPencilSchemeInclusion_isClosedImmersion :
    IsClosedImmersion (extendedClosedGaussPencilSchemeInclusion H I E hH e) :=
  reducedPointClosureInclusion_isClosedImmersion _ _

/-- The actual extended projective scheme has exactly the extended
original homogeneous source ideal as its projective image. -/
theorem extendedClosedGaussPencilSchemeInclusion_range :
    Set.range (extendedClosedGaussPencilSchemeInclusion H I E hH e) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E)
        (extendedClosedGaussPencilIdeal H I E : Set (MvPolynomial (Fin 4) E)) := by
  change Set.range (reducedPointClosureInclusion _ _) = _
  rw [reducedPointClosureInclusion_range, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  rfl

/-- The actual extended pencil's structure morphism to the new coefficient field. -/
noncomputable def extendedClosedGaussPencilSchemeToBase :
    extendedClosedGaussPencilScheme H I E hH e ⟶ Spec (CommRingCat.of E) :=
  extendedClosedGaussPencilSchemeInclusion H I E hH e ≫ polynomialProjectiveToBase E

/-- The extended projective pencil is proper over the actual new field. -/
theorem extendedClosedGaussPencilSchemeToBase_isProper :
    IsProper (extendedClosedGaussPencilSchemeToBase H I E hH e) := by
  let : IsClosedImmersion (extendedClosedGaussPencilSchemeInclusion H I E hH e) :=
    extendedClosedGaussPencilSchemeInclusion_isClosedImmersion H I E hH e
  let : IsProper (polynomialProjectiveToBase E) := polynomialProjectiveToBase_isProper E
  unfold extendedClosedGaussPencilSchemeToBase
  infer_instance

/-- The global normalization is formed after the actual coefficient extension. -/
noncomputable def extendedClosedGaussNormalizationScheme : Scheme.{u} :=
  letI : IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
    extendedClosedGaussPencilScheme_isIntegral H I E hH e
  integralSchemeNormalization (extendedClosedGaussPencilScheme H I E hH e)

/-- Its actual map to the original extended projective pencil. -/
noncomputable def extendedClosedGaussNormalizationSchemeMap :
    extendedClosedGaussNormalizationScheme H I E hH e ⟶ extendedClosedGaussPencilScheme H I E hH e := by
  let : IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
    extendedClosedGaussPencilScheme_isIntegral H I E hH e
  exact integralSchemeNormalizationMap _

/-- The actual normalization of the extended pencil is finite over that pencil. -/
theorem extendedClosedGaussNormalizationSchemeMap_isFinite :
    IsFinite (extendedClosedGaussNormalizationSchemeMap H I E hH e) := by
  let : CharZero (closedGaussParameterField H I) :=
    charZero_of_injective_algebraMap (algebraMap K (closedGaussParameterField H I)).injective
  let : CharZero E := charZero_of_injective_algebraMap
    (algebraMap (closedGaussParameterField H I) E).injective
  let : IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
    extendedClosedGaussPencilScheme_isIntegral H I E hH e
  let : IsProper (extendedClosedGaussPencilSchemeToBase H I E hH e) :=
    extendedClosedGaussPencilSchemeToBase_isProper H I E hH e
  exact integralSchemeNormalizationMap_finite_of_finiteType _
    (extendedClosedGaussPencilSchemeToBase H I E hH e)

/-- Every local ring on the actual extended global normalization is normal. -/
theorem extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed
    (y : extendedClosedGaussNormalizationScheme H I E hH e) :
    IsIntegrallyClosed ((extendedClosedGaussNormalizationScheme H I E hH e).presheaf.stalk y) := by
  let : IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
    extendedClosedGaussPencilScheme_isIntegral H I E hH e
  exact integralSchemeNormalization_stalk_isIntegrallyClosed _ y

/-- The actual extended normalization scheme is integral. -/
theorem extendedClosedGaussNormalizationScheme_isIntegral :
    IsIntegral (extendedClosedGaussNormalizationScheme H I E hH e) := by
  let : IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
    extendedClosedGaussPencilScheme_isIntegral H I E hH e
  exact integralSchemeNormalization_isIntegral _

/-- The actual normalized extended pencil over its new coefficient field. -/
noncomputable def extendedClosedGaussNormalizationSchemeToBase :
    extendedClosedGaussNormalizationScheme H I E hH e ⟶ Spec (CommRingCat.of E) :=
  extendedClosedGaussNormalizationSchemeMap H I E hH e ≫ extendedClosedGaussPencilSchemeToBase H I E hH e

/-- The normalization formed after coefficient extension is proper over that field. -/
theorem extendedClosedGaussNormalizationSchemeToBase_isProper :
    IsProper (extendedClosedGaussNormalizationSchemeToBase H I E hH e) := by
  let : IsFinite (extendedClosedGaussNormalizationSchemeMap H I E hH e) :=
    extendedClosedGaussNormalizationSchemeMap_isFinite H I E hH e
  let : IsProper (extendedClosedGaussPencilSchemeToBase H I E hH e) :=
    extendedClosedGaussPencilSchemeToBase_isProper H I E hH e
  unfold extendedClosedGaussNormalizationSchemeToBase
  infer_instance

/-- Its actual global normalized source is Noetherian. -/
theorem extendedClosedGaussNormalizationScheme_isNoetherian :
    IsNoetherian (extendedClosedGaussNormalizationScheme H I E hH e) := by
  let : IsProper (extendedClosedGaussNormalizationSchemeToBase H I E hH e) :=
    extendedClosedGaussNormalizationSchemeToBase_isProper H I E hH e
  let : IsLocallyNoetherian (extendedClosedGaussNormalizationScheme H I E hH e) :=
    LocallyOfFiniteType.isLocallyNoetherian (extendedClosedGaussNormalizationSchemeToBase H I E hH e)
  let : CompactSpace (extendedClosedGaussNormalizationScheme H I E hH e) :=
    QuasiCompact.compactSpace_of_compactSpace (extendedClosedGaussNormalizationSchemeToBase H I E hH e)
  exact ⟨⟩

include hH in
/-- The actual extended scheme is precisely the hypersurface obtained
by extending the original homogeneous pencil equation's coefficients. -/
theorem extendedClosedGaussPencilSchemeInclusion_range_equation
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q) :
    Set.range (extendedClosedGaussPencilSchemeInclusion H I E hH e) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E)
        {MvPolynomial.map (algebraMap (closedGaussParameterField H I) E)
          (closedGaussPencilEquation H I e p q)} := by
  rw [extendedClosedGaussPencilSchemeInclusion_range]
  change ProjectiveSpectrum.zeroLocus _
    (extendCoefficientIdeal E (fiberVanishingIdeal (L := closedGaussParameterField H I)
      (rationalCoordinate (K := K) (n := 4))) : Set (MvPolynomial (Fin 4) E)) = _
  rw [actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht]
  simp only [extendCoefficientIdeal, Ideal.map_span, Set.image_singleton, ProjectiveSpectrum.zeroLocus_span]

end DimensionFourDependence
