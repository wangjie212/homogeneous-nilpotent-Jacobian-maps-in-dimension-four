import DimensionFourDependence.ExtendedNormalizationFunctionField
import DimensionFourDependence.ExtendedGaussSchemeTensorAtlas
import DimensionFourDependence.ProjectivePullbackHyperplaneSheaf

/-! # Original hyperplane frames on the actual normalized extended pencil -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)

local instance : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- The original projective coordinate morphism on the normalization
formed after the paper's algebraic coefficient extension. -/
noncomputable def extendedClosedGaussNormalizationProjectiveMap :
    N ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E) :=
  extendedClosedGaussNormalizationSchemeMap H I E hH e ≫
    extendedClosedGaussPencilSchemeInclusion H I E hH e

/-- The inverse original projective coordinate opens are exactly the
already constructed original tensor-normalization affine charts. -/
theorem extendedClosedGaussNormalizationProjectiveMap_preimage (a : Fin 4) :
    extendedClosedGaussNormalizationProjectiveMap H I E hH e ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a) = U a := by
  simp only [extendedClosedGaussNormalizationProjectiveMap, Scheme.Hom.comp_preimage,
    extendedClosedGaussNormalizationChartOpen, extendedClosedGaussPencilChartOpen,
    finSuccEquiv'_symm_none]

/-- All original inverse coordinate charts are nonempty on the
actual normalized extended pencil. -/
theorem extendedClosedGaussNormalizationProjectiveMap_chart_nonempty (a : Fin 4) :
    Nonempty (extendedClosedGaussNormalizationProjectiveMap H I E hH e ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a)) := by
  rw [extendedClosedGaussNormalizationProjectiveMap_preimage]
  exact extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)

/-- The paper's original frame Xa has its rational weight Xa/X0 in
the actual normalized pencil's own generic-point function field. -/
noncomputable def extendedClosedGaussNormalizationHyperplaneWeight (a : Fin 4) :
    (N).functionField :=
  projectivePullbackHyperplaneWeight N
    (extendedClosedGaussNormalizationProjectiveMap H I E hH e)
    (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) a

/-- Every original hyperplane frame on the actual normalized pencil
is nonzero in that scheme's own function field. -/
theorem extendedClosedGaussNormalizationHyperplaneWeight_ne_zero (a : Fin 4) :
    extendedClosedGaussNormalizationHyperplaneWeight H I E hH e a ≠ 0 :=
  projectivePullbackHyperplaneWeight_ne_zero N
    (extendedClosedGaussNormalizationProjectiveMap H I E hH e)
    (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) a

/-- The actual regular transition Xi/Xj on an original pair of tensor
normalization charts, obtained directly by geometric section pullback. -/
noncomputable def extendedClosedGaussNormalizationHyperplaneTransition (i j : Fin 4) :
    Γ(N, U i ⊓ U j) :=
  (extendedClosedGaussNormalizationProjectiveMap H I E hH e).appLE
    (Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X j)) (U i ⊓ U j)
    (inf_le_right.trans (le_of_eq
      (extendedClosedGaussNormalizationProjectiveMap_preimage H I E hH e j).symm))
    (projectiveCoordinateRatioSection E j i)

/-- The constructed regular transitions retain their original
coordinate-ratio values in the normalized scheme's own function field. -/
theorem extendedClosedGaussNormalizationHyperplaneTransition_value (i j : Fin 4)
    (p : (U i ⊓ U j : (N).Opens)) :
    schemeRationalSectionFunction N (U i ⊓ U j)
        (extendedClosedGaussNormalizationHyperplaneTransition H I E hH e i j) p =
      extendedClosedGaussNormalizationHyperplaneWeight H I E hH e i /
        extendedClosedGaussNormalizationHyperplaneWeight H I E hH e j := by
  unfold extendedClosedGaussNormalizationHyperplaneTransition Scheme.Hom.appLE
  simp only [ConcreteCategory.comp_apply]
  rw [schemeRationalSectionFunction_res]
  exact (projectivePullbackRationalCoordinate_section_at_point N
    (extendedClosedGaussNormalizationProjectiveMap H I E hH e)
    (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) j i _).trans
      (projectivePullbackRationalCoordinate_div N
        (extendedClosedGaussNormalizationProjectiveMap H I E hH e)
        (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) j 0 i)

/-- The original tensor-normalization opens admit actual regular
frame changes with exactly the original rational coordinate ratios. -/
theorem extendedClosedGaussNormalizationHyperplaneFrameData :
    ∃ t : ∀ i j : Fin 4, Γ(N, U i ⊓ U j),
      ∀ (i j : Fin 4) (p : (U i ⊓ U j : (N).Opens)),
        schemeRationalSectionFunction N (U i ⊓ U j) (t i j) p =
          extendedClosedGaussNormalizationHyperplaneWeight H I E hH e i /
            extendedClosedGaussNormalizationHyperplaneWeight H I E hH e j :=
  ⟨extendedClosedGaussNormalizationHyperplaneTransition H I E hH e,
    extendedClosedGaussNormalizationHyperplaneTransition_value H I E hH e⟩

/-- The actual hyperplane-frame module sheaf on the actual normalized
extended pencil, using its original projective coordinate morphism. -/
noncomputable def extendedClosedGaussNormalizationHyperplaneModuleSheaf : (N).Modules :=
  rationalFrameModuleSheaf N (fun a : Fin 4 => U a)
    (extendedClosedGaussNormalizationHyperplaneWeight H I E hH e)

/-- The original hyperplane-frame sheaf is locally free of rank one
on the actual normalization, proved from its original four-chart cover. -/
theorem extendedClosedGaussNormalizationHyperplaneModuleSheaf_locallyFreeRankOne :
    SchemeModuleIsLocallyFreeRankOne
      (extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e) := by
  exact rationalFrameModuleSheaf_locallyFreeRankOne N (fun a : Fin 4 => U a)
    (extendedClosedGaussNormalizationHyperplaneWeight H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneTransition H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneTransition_value H I E hH e)
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)

end DimensionFourDependence
