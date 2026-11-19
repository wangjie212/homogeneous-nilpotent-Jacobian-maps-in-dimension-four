import DimensionFourDependence.IntermediateLocalRing
import DimensionFourDependence.NormalizationRing

/-! # Identifying normalized coordinate local rings at a normal source point

If a source local ring is normal, integral elements of any intermediate
coordinate algebra already belong to that source local ring. The induced
map from the coordinate normalization therefore localizes back to exactly
the same source local ring at the contracted maximal ideal.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {S A F : Type*} [CommRing S] [CommRing A] [Field F]
  [Algebra S A] [Algebra S F] [Algebra A F] [IsScalarTower S A F]
  [IsFractionRing A F] [IsIntegrallyClosed A]

/-- Every integral coordinate function lies in the normal source local
ring; its realization in the function field determines the lift. -/
noncomputable def integralClosureToNormalLocalHom : integralClosure S F →ₐ[S] A := by
  let : IsIntegralClosure A A F :=
    (isIntegrallyClosed_iff_isIntegralClosure F).mp inferInstance
  exact
    { toFun := fun x => IsIntegralClosure.mk' (R := A) A x.val x.property.tower_top
      map_zero' := by apply IsFractionRing.injective A F; simp
      map_one' := by apply IsFractionRing.injective A F; simp
      map_add' := by intro x y; apply IsFractionRing.injective A F; simp
      map_mul' := by intro x y; apply IsFractionRing.injective A F; simp
      commutes' := by
        intro s
        apply IsFractionRing.injective A F
        simp only [IsIntegralClosure.algebraMap_mk']
        exact IsScalarTower.algebraMap_apply S A F s }

/-- The normal local lift preserves the actual rational function. -/
theorem integralClosureToNormalLocalHom_source (x : integralClosure S F) :
    algebraMap A F (integralClosureToNormalLocalHom (A := A) x) = x.val := by
  let : IsIntegralClosure A A F :=
    (isIntegrallyClosed_iff_isIntegralClosure F).mp inferInstance
  exact IsIntegralClosure.algebraMap_mk' (R := A) A x.val x.property.tower_top

/-- The induced map of the coordinate normalization is injective because
it realizes the same functions in the source function field. -/
theorem integralClosureToNormalLocalHom_injective :
    Function.Injective (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)) := by
  intro x y hxy
  apply Subtype.ext
  rw [← integralClosureToNormalLocalHom_source (A := A) x,
    ← integralClosureToNormalLocalHom_source (A := A) y, hxy]

variable {R : Type*} [CommRing R] [Algebra R S] [Algebra R A]
  [IsScalarTower R S A] [IsLocalRing A] [FaithfulSMul S A]

/-- Normalizing an intermediate coordinate algebra does not change its
local ring at the given normal source point. The normalization prime is
constructed as the contraction of the actual source maximal ideal. -/
theorem normalized_intermediate_algebra_source_localization
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime A P] :
    letI : Algebra (integralClosure S F) A :=
      (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
    IsLocalization.AtPrime A ((IsLocalRing.maximalIdeal A).under (integralClosure S F)) := by
  let : Algebra (integralClosure S F) A :=
    (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
  let : FaithfulSMul (integralClosure S F) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr integralClosureToNormalLocalHom_injective
  let : IsScalarTower S (integralClosure S F) A :=
    IsScalarTower.of_algebraMap_eq (fun s =>
      ((integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).commutes s).symm)
  let : IsLocalization.AtPrime A ((IsLocalRing.maximalIdeal A).under S) :=
    intermediate_algebra_source_localization P
  exact intermediate_algebra_source_localization ((IsLocalRing.maximalIdeal A).under S)

/-- The normalized coordinate prime localization is the original normal
source local ring, with its explicit coordinate-normalization algebra map. -/
noncomputable def normalizedIntermediateSourceLocalEquiv
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime A P] :
    letI : Algebra (integralClosure S F) A :=
      (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
    Localization.AtPrime ((IsLocalRing.maximalIdeal A).under (integralClosure S F))
      ≃ₐ[integralClosure S F] A := by
  let : Algebra (integralClosure S F) A :=
    (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
  let : IsLocalization.AtPrime A ((IsLocalRing.maximalIdeal A).under (integralClosure S F)) :=
    normalized_intermediate_algebra_source_localization P
  exact IsLocalization.algEquiv ((IsLocalRing.maximalIdeal A).under (integralClosure S F)).primeCompl _ _

end DimensionFourDependence
