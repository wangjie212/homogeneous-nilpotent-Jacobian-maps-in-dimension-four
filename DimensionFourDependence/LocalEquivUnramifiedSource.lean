import DimensionFourDependence.LocalEquivSourceMap
import DimensionFourDependence.UnramifiedDivisorOrder
import Mathlib.RingTheory.EssentialFiniteness

/-! # The normalization local ring as an actual unramified source extension

The inverse local isomorphism constructs the source-local action. The
normalization local ring then inherits the DVR, torsion-free, essentially
finite type, unramified, and local-map properties from the checked model.
-/

namespace DimensionFourDependence

variable {R O A B : Type*} [CommRing R]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing A] [IsDomain A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra R O] [Algebra R A] [Algebra R B] [Algebra O B] [IsScalarTower R O B]
  [Module.IsTorsionFree O B] [Algebra.EssFiniteType O B]
  [Algebra.FormallyUnramified O B] [IsLocalHom (algebraMap O B)]

omit [IsDiscreteValuationRing O] [IsDomain A] [IsLocalRing A]
  [Algebra.EssFiniteType O B] [Algebra.FormallyUnramified O B] [IsLocalHom (algebraMap O B)] in
/-- The constructed source-local map is injective, with the given
source functions preserved by its original-source algebra structure. -/
theorem localEquivSource_algebraMap_injective (e : A ≃ₐ[R] B) :
    letI : Algebra O A := localEquivSourceAlgebra (O := O) e
    Function.Injective (algebraMap O A) := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  let u : A ≃ₐ[O] B := localEquivOverSource e
  intro x y hxy
  apply FaithfulSMul.algebraMap_injective O B
  simpa only [u.commutes] using congrArg u hxy

omit [IsDiscreteValuationRing O] in
/-- The actual normalization local ring is an unramified DVR extension
of the source DVR, using its constructed original-source local map. -/
theorem localEquivSource_unramified_structure (e : A ≃ₐ[R] B) :
    letI : Algebra O A := localEquivSourceAlgebra (O := O) e
    IsDiscreteValuationRing A ∧ Module.IsTorsionFree O A ∧ Algebra.EssFiniteType O A ∧
      Algebra.FormallyUnramified O A ∧ IsLocalHom (algebraMap O A) := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  let u : A ≃ₐ[O] B := localEquivOverSource e
  have htf : Module.IsTorsionFree O A :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := O) (A := A)).mpr
      (localEquivSource_algebraMap_injective e)
  refine ⟨local_equiv_isDiscreteValuationRing u.toRingEquiv, htf,
    (Algebra.EssFiniteType.iff_of_algEquiv u).mpr inferInstance,
    Algebra.FormallyUnramified.of_equiv u.symm, ?_⟩
  constructor
  intro x hx
  apply isUnit_of_map_unit (algebraMap O B) x
  rw [← u.commutes x]
  exact hx.map u.toRingHom

variable {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F]

omit [IsDiscreteValuationRing O] [IsLocalRing A]
  [Algebra.EssFiniteType O B] [Algebra.FormallyUnramified O B] [IsLocalHom (algebraMap O B)] in
/-- The original source function field in the normalization local
fraction field, extending the constructed original source-local map. -/
noncomputable def localEquivSourceFractionHom (e : A ≃ₐ[R] B) :
    letI : Algebra O A := localEquivSourceAlgebra (O := O) e
    F →ₐ[O] FractionRing A := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  let : FaithfulSMul O A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (localEquivSource_algebraMap_injective e)
  exact IsFractionRing.liftAlgHom (g := Algebra.ofId O (FractionRing A))
    (FaithfulSMul.algebraMap_injective O (FractionRing A))

omit [IsDiscreteValuationRing O] [IsLocalRing A]
  [Algebra.EssFiniteType O B] [Algebra.FormallyUnramified O B] [IsLocalHom (algebraMap O B)] in
/-- Every regular source-local function retains its source field value
under the constructed rational pullback. -/
theorem localEquivSourceFractionHom_algebraMap (e : A ≃ₐ[R] B) (x : O) :
    letI : Algebra O A := localEquivSourceAlgebra (O := O) e
    localEquivSourceFractionHom (O := O) (F := F) e (algebraMap O F x) =
      algebraMap A (FractionRing A) (localEquivSourceAlgHom (O := O) e x) := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  exact (localEquivSourceFractionHom (O := O) (F := F) e).commutes x

end DimensionFourDependence
