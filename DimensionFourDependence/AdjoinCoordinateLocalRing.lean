import DimensionFourDependence.IntermediateLocalRing
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Coordinate algebras in compatible source local rings

If a coefficient field and a collection of source coordinates lie in a
source local ring, their actual adjoin algebra does too. The maps preserve
their ambient function-field values. When the source local ring is a
prime localization of the original-coefficient coordinate algebra, the
coefficient adjoin algebra has exactly that same contracted local ring.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K C F : Type*} [Field K] [Field C] [Field F]
  [Algebra K C] [Algebra K F] [Algebra C F] [IsScalarTower K C F]
  {n : ℕ}

/-- Enlarging coefficients includes the actual source coordinate algebra
into the larger-coefficient coordinate algebra by the same functions. -/
noncomputable def adjoinCoefficientInclusion (x : Fin n → F) :
    Algebra.adjoin K (Set.range x) →ₐ[K] Algebra.adjoin C (Set.range x) :=
  Subalgebra.inclusion (show Algebra.adjoin K (Set.range x) ≤
      (Algebra.adjoin C (Set.range x)).restrictScalars K from
    Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx)

/-- Coefficient inclusion preserves the original rational function. -/
theorem adjoinCoefficientInclusion_source (x : Fin n → F)
    (r : Algebra.adjoin K (Set.range x)) :
    (adjoinCoefficientInclusion (C := C) x r : F) = r.val := rfl

variable (x : Fin n → F) {A : Type*} [CommRing A]
  [Algebra (Algebra.adjoin K (Set.range x)) A] [Algebra C A] [Algebra A F]
  [IsScalarTower (Algebra.adjoin K (Set.range x)) A F] [IsScalarTower C A F]
  [FaithfulSMul A F]

include K in
omit [Algebra K C] [IsScalarTower K C F] [FaithfulSMul A F] in
/-- The actual coefficient adjoin algebra lies in the image of the
source local ring when its coefficients and original coordinates do. -/
theorem adjoinCoordinateAlgebra_le_local_range :
    Algebra.adjoin C (Set.range x) ≤ (IsScalarTower.toAlgHom C A F).range := by
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  refine ⟨algebraMap (Algebra.adjoin K (Set.range x)) A
    ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩, ?_⟩
  exact (IsScalarTower.algebraMap_apply (Algebra.adjoin K (Set.range x)) A F
    ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩).symm

/-- The constructed coefficient-coordinate map into the source local
ring, using its given actual ambient field inclusion. -/
noncomputable def adjoinCoordinateLocalHom : Algebra.adjoin C (Set.range x) →ₐ[C] A :=
  (AlgEquiv.ofInjective (IsScalarTower.toAlgHom C A F)
    (FaithfulSMul.algebraMap_injective A F)).symm.toAlgHom.comp
      (Subalgebra.inclusion (adjoinCoordinateAlgebra_le_local_range (K := K) (A := A) x))

omit [Algebra K C] [IsScalarTower K C F] in
/-- The constructed coordinate map preserves every ambient rational
function, including all original coefficient and coordinate values. -/
theorem adjoinCoordinateLocalHom_source (r : Algebra.adjoin C (Set.range x)) :
    algebraMap A F (adjoinCoordinateLocalHom (K := K) (A := A) x r) = r.val := by
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective (IsScalarTower.toAlgHom C A F)
      (FaithfulSMul.algebraMap_injective A F)).apply_symm_apply
        (Subalgebra.inclusion (adjoinCoordinateAlgebra_le_local_range (K := K) (A := A) x) r))

omit [Algebra K C] [IsScalarTower K C F] in
/-- The coordinate local map is injective. -/
theorem adjoinCoordinateLocalHom_injective :
    Function.Injective (adjoinCoordinateLocalHom (K := K) (C := C) (A := A) x) := by
  intro r s hrs
  apply Subtype.ext
  rw [← adjoinCoordinateLocalHom_source (K := K) (A := A) x r,
    ← adjoinCoordinateLocalHom_source (K := K) (A := A) x s, hrs]

/-- Coefficient inclusion followed by the coordinate local map agrees
with the original source coordinate localization map. -/
theorem adjoinCoefficientInclusion_local (r : Algebra.adjoin K (Set.range x)) :
    adjoinCoordinateLocalHom (K := K) (A := A) x (adjoinCoefficientInclusion (C := C) x r) =
      algebraMap (Algebra.adjoin K (Set.range x)) A r := by
  apply FaithfulSMul.algebraMap_injective A F
  rw [adjoinCoordinateLocalHom_source, adjoinCoefficientInclusion_source]
  exact IsScalarTower.algebraMap_apply (Algebra.adjoin K (Set.range x)) A F r

/-- The actual coefficient-coordinate local ring is precisely the
original source local ring at the contracted source divisor prime. -/
theorem adjoin_coordinate_source_localization [IsLocalRing A]
    (P : Ideal (Algebra.adjoin K (Set.range x))) [P.IsPrime] [IsLocalization.AtPrime A P] :
    letI : Algebra (Algebra.adjoin C (Set.range x)) A :=
      (adjoinCoordinateLocalHom (K := K) (A := A) x).toRingHom.toAlgebra
    IsLocalization.AtPrime A ((IsLocalRing.maximalIdeal A).under (Algebra.adjoin C (Set.range x))) := by
  let : Algebra (Algebra.adjoin K (Set.range x)) (Algebra.adjoin C (Set.range x)) :=
    (adjoinCoefficientInclusion (C := C) x).toRingHom.toAlgebra
  let : Algebra (Algebra.adjoin C (Set.range x)) A :=
    (adjoinCoordinateLocalHom (K := K) (A := A) x).toRingHom.toAlgebra
  let : IsScalarTower (Algebra.adjoin K (Set.range x)) (Algebra.adjoin C (Set.range x)) A :=
    IsScalarTower.of_algebraMap_eq (fun r => (adjoinCoefficientInclusion_local (K := K) (A := A) x r).symm)
  let : FaithfulSMul (Algebra.adjoin C (Set.range x)) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (adjoinCoordinateLocalHom_injective (K := K) (A := A) x)
  exact intermediate_algebra_source_localization P

end DimensionFourDependence
