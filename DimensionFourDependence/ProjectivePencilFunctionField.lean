import DimensionFourDependence.ProjectiveSourceParameterField
import DimensionFourDependence.AdjoinCoordinateLocalRing
import DimensionFourDependence.IntermediateFunctionField

/-! # The actual projective pencil coordinate algebra in the source field

The source chart polynomial functions include in the pencil coordinate
algebra through their original ratios. The entire pencil algebra embeds
in the original projective source field, independently of a chosen
divisor or horizontal parameter residue. That field is its actual
fraction field. These maps allow curve-prime contraction to determine
the source local extension directly.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "G₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "L₀" => projectiveCoordinateChartField (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

/-- The actual original-source projective chart includes into the
closed Gauss pencil chart by the same original coordinate functions. -/
noncomputable def projectivePencilBaseInclusion : R₀ →ₐ[K] G₀ :=
  adjoinCoefficientInclusion (C := C₀)
    (fun i : Fin 4 => rationalCoordinate (K := K) i / rationalCoordinate (K := K) (s.symm none))

/-- The projective source inclusion preserves the actual source value. -/
theorem projectivePencilBaseInclusion_source (r : R₀) :
    (projectivePencilBaseInclusion H I s r : F₀) = r.val := rfl

variable [CharZero K] {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The actual projective pencil coordinate algebra in the original
projective source field, without a divisor-local regularity assumption. -/
noncomputable def projectivePencilSourceFieldHom :
    letI : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
    G₀ →ₐ[C₀] L₀ := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let hC := actual_closed_gauss_parameter_field_le_projective_source_chart H hH I e (s.symm none)
  let L' := IntermediateField.extendScalars hC
  have hG : G₀ ≤ L'.toSubalgebra := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  exact
    { toFun := fun r => ⟨r.val, hG r.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }

/-- The pencil field map is the original identity on rational functions. -/
theorem projectivePencilSourceFieldHom_source (r : G₀) :
    letI : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
    (projectivePencilSourceFieldHom H I s hH e r : F₀) = r.val := rfl

/-- The actual pencil field map is injective. -/
theorem projectivePencilSourceFieldHom_injective :
    letI : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
    Function.Injective (projectivePencilSourceFieldHom H I s hH e) := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  intro r r' hrr'
  apply Subtype.ext
  rw [← projectivePencilSourceFieldHom_source H I s hH e r,
    ← projectivePencilSourceFieldHom_source H I s hH e r']
  exact congrArg Subtype.val hrr'

/-- The explicit pencil coordinate action on the actual source field. -/
@[instance_reducible]
noncomputable def projectivePencilSourceFieldAlgebra : Algebra G₀ L₀ := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  exact (projectivePencilSourceFieldHom H I s hH e).toRingHom.toAlgebra

/-- The source-chart inclusion and pencil-field inclusion give the same
original-source scalar tower. -/
theorem projectivePencilSourceField_scalarTower :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
    IsScalarTower R₀ G₀ L₀ := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
  apply IsScalarTower.of_algebraMap_eq
  intro r
  apply Subtype.val_injective
  exact (projectivePencilSourceFieldHom_source H I s hH e (projectivePencilBaseInclusion H I s r)).symm

/-- The actual pencil coordinate algebra has the original projective
source field as its actual fraction field, before choosing any divisor. -/
theorem actual_projective_pencil_source_isFractionRing :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
    IsFractionRing G₀ L₀ := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
  let : IsScalarTower R₀ G₀ L₀ := projectivePencilSourceField_scalarTower H I s hH e
  let : FaithfulSMul G₀ L₀ := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (projectivePencilSourceFieldHom_injective H I s hH e)
  exact intermediate_algebra_same_fraction_field (R := R₀)

end DimensionFourDependence
