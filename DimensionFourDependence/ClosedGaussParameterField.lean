import DimensionFourDependence.FiniteAlgebraicSubextension
import DimensionFourDependence.ProjectiveEulerWeight

/-! # The actual relatively closed Gauss parameter field

Take the relative algebraic closure of the actual Gauss field inside
the original rational source field. Its extension over the Gauss field
is finite, it has transcendence degree one, and it is relatively closed
inside the source. The source Euler derivation annihilates the whole
closure, not merely the original projective-normal ratios.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K : Type u} [Field K]

/-- The rational source is finitely generated as a field over its
original coefficient field. -/
theorem rationalSource_essFiniteType {n : ℕ} :
    Algebra.EssFiniteType K (FractionRing (MvPolynomial (Fin n) K)) := by
  let : Algebra.EssFiniteType (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (MvPolynomial (Fin n) K))
  exact Algebra.EssFiniteType.comp K (MvPolynomial (Fin n) K) _

/-- The actual relative algebraic closure of the Gauss field,
viewed as an original-coefficient intermediate source field. -/
noncomputable def closedGaussParameterField
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    IntermediateField K (FractionRing (MvPolynomial (Fin 4) K)) :=
  (algebraicClosure
    (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (FractionRing (MvPolynomial (Fin 4) K))).restrictScalars K

/-- The actual Gauss field embeds in its actual relatively closed
parameter field inside the original source field. -/
theorem actual_gauss_field_le_closed_parameter_field
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) ≤
      closedGaussParameterField H I := by
  intro x hx
  apply mem_algebraicClosure_iff.mpr
  have he : IsAlgebraic
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (algebraMap _ (FractionRing (MvPolynomial (Fin 4) K))
        (⟨x, hx⟩ : projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))) := isAlgebraic_algebraMap
    (⟨x, hx⟩ : projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
  exact he

/-- The actual finite-cover field carries the actual Gauss-field
algebra structure supplied by their inclusion in the same source. -/
@[instance_reducible]
noncomputable def closedGaussParameterFieldGaussAlgebra
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    Algebra (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (closedGaussParameterField H I) :=
  (IntermediateField.inclusion (actual_gauss_field_le_closed_parameter_field H I)).toRingHom.toAlgebra

attribute [instance] closedGaussParameterFieldGaussAlgebra

/-- The Gauss-field inclusion respects the original coefficient action. -/
theorem closedGaussParameterField_base_scalar_tower
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    IsScalarTower K
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (closedGaussParameterField H I) :=
  IsScalarTower.of_algebraMap_eq (by intro k; rfl)

/-- The Gauss-field inclusion and cover-field inclusion have the same
actual realization in the original source field. -/
theorem closedGaussParameterField_source_scalar_tower
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    IsScalarTower
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (closedGaussParameterField H I) (FractionRing (MvPolynomial (Fin 4) K)) :=
  IsScalarTower.of_algebraMap_eq (by intro k; rfl)

attribute [instance] closedGaussParameterField_base_scalar_tower closedGaussParameterField_source_scalar_tower

/-- The actual cover field is algebraic over the actual Gauss field. -/
theorem closedGaussParameterField_isAlgebraic
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    Algebra.IsAlgebraic
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (closedGaussParameterField H I) := by
  constructor
  intro x
  apply (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom _ (closedGaussParameterField H I)
    (FractionRing (MvPolynomial (Fin 4) K))) Subtype.val_injective).mp
  exact mem_algebraicClosure_iff.mp x.property

attribute [instance] closedGaussParameterField_isAlgebraic

/-- Passing to the actual closed parameter field leaves no further
algebraic constants inside the original rational source field. -/
theorem closedGaussParameterField_relatively_closed
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    algebraicClosure (closedGaussParameterField H I) (FractionRing (MvPolynomial (Fin 4) K)) = ⊥ := by
  exact algebraicClosure.algebraicClosure_eq_bot _ _

/-- The actual relatively closed parameter field is a finite
extension of the actual Gauss field, with finiteness derived from the
finitely generated original source field. -/
theorem closedGaussParameterField_finite_over_gauss
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    Module.Finite
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (closedGaussParameterField H I) := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let F := FractionRing (MvPolynomial (Fin 4) K)
  let : Algebra.EssFiniteType K F := rationalSource_essFiniteType
  let : Algebra.EssFiniteType M F := Algebra.EssFiniteType.of_comp K M F
  exact algebraic_subextension_finite_of_essFiniteType (E := F)

/-- The actual finite cover of a one-dimensional Gauss field has
transcendence degree exactly one over the original coefficient field. -/
theorem closedGaussParameterField_trdeg_one
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    Algebra.trdeg K (closedGaussParameterField H I) = 1 := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let C := closedGaussParameterField H I
  let : FaithfulSMul K M :=
    (faithfulSMul_iff_algebraMap_injective K M).mpr (algebraMap K M).injective
  let : FaithfulSMul M C :=
    (faithfulSMul_iff_algebraMap_injective M C).mpr (algebraMap M C).injective
  have ht := trdeg_add_eq (A := C) K M
  have hz : Algebra.trdeg M C = 0 := trdeg_eq_zero
  rw [hz, add_zero] at ht
  exact ht.symm.trans hGauss

variable [CharZero K]

/-- Every element of the actual relatively closed Gauss parameter
field has source Euler weight zero. -/
theorem closedGaussParameterField_le_sourceEuler_constants
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) :
    closedGaussParameterField H I ≤ derivationConstants (sourceEuler (K := K) (n := 4)) := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let F := FractionRing (MvPolynomial (Fin 4) K)
  have hweight (i : Fin 4) : sourceEuler (K := K) (rationalImageNormal H I.equation i) =
      ((d * (I.degree - 1) : ℕ) : F) * rationalImageNormal H I.equation i :=
    sourceEuler_homogeneous _ (I.normal_homogeneous H hH i)
  have hM : M ≤ derivationConstants (sourceEuler (K := K) (n := 4)) :=
    projectiveRatioField_le_derivationConstants_of_weight _ _ _ _ hweight
  let D := derivationOverConstantSubfield (sourceEuler (K := K) (n := 4)) M hM
  let : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  intro x hx
  have ha : IsAlgebraic M x := mem_algebraicClosure_iff.mp hx
  exact derivation_zero_of_isAlgebraic D x ha

end DimensionFourDependence
