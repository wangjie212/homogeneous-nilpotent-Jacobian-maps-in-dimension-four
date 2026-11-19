import DimensionFourDependence.ValuationLocalDescent
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Constructing coefficient-field embeddings from domination

A coefficient field common to the source function field and a dominating
local extension lies in the source valuation ring. The regular-fraction
descent theorem constructs its ring homomorphism into that source ring,
and proves compatibility with both given field and local-ring maps.
-/

namespace DimensionFourDependence

variable {A B C F L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [CommRing B] [Field C] [Field F] [Field L]
  [Algebra A F] [IsFractionRing A F] [Algebra A B] [Algebra F L]
  [Algebra A L] [IsScalarTower A F L] [Algebra B L] [IsScalarTower A B L]
  [FaithfulSMul B L] [IsLocalHom (algebraMap A B)]
  [Algebra C F] [Algebra C B] [Algebra C L] [IsScalarTower C F L] [IsScalarTower C B L]

/-- The coefficient field embeds into the source valuation ring, with
its values constructed from their regular source fractions. -/
noncomputable def valuationCoefficientLocalHom : C →+* A := by
  let f : C → A := fun c => Classical.choose
    (valuation_source_contains_coefficient_field (A := A) (B := B) (F := F) (L := L) c)
  have hf (c : C) : algebraMap A F (f c) = algebraMap C F c :=
    Classical.choose_spec (valuation_source_contains_coefficient_field (A := A) (B := B) (F := F) (L := L) c)
  exact
    { toFun := f
      map_zero' := by apply IsFractionRing.injective A F; simp only [hf, map_zero]
      map_one' := by apply IsFractionRing.injective A F; simp only [hf, map_one]
      map_add' := by intro c c'; apply IsFractionRing.injective A F; simp only [hf, map_add]
      map_mul' := by intro c c'; apply IsFractionRing.injective A F; simp only [hf, map_mul] }

/-- The constructed coefficient map is its original source-field
realization, not an unrelated coefficient embedding. -/
theorem valuationCoefficientLocalHom_source (c : C) :
    algebraMap A F (valuationCoefficientLocalHom (B := B) (F := F) (L := L) c) = algebraMap C F c :=
  Classical.choose_spec (valuation_source_contains_coefficient_field (A := A) (B := B) (F := F) (L := L) c)

/-- The constructed coefficient map agrees with the given coefficient
map in the dominating local extension. -/
theorem valuationCoefficientLocalHom_target (c : C) :
    algebraMap A B (valuationCoefficientLocalHom (B := B) (F := F) (L := L) c) = algebraMap C B c := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A F L,
    valuationCoefficientLocalHom_source, ← IsScalarTower.algebraMap_apply C F L,
    ← IsScalarTower.algebraMap_apply C B L]

/-- The source valuation ring carries the coefficient-field action
compatible with its actual source function field. -/
theorem valuationCoefficientLocalHom_source_scalarTower :
    letI : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
    IsScalarTower C A F := by
  let : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
  exact IsScalarTower.of_algebraMap_eq
    (fun c => (valuationCoefficientLocalHom_source (B := B) (F := F) (L := L) c).symm)

/-- The same coefficient-field action is compatible with the actual
dominating local extension. -/
theorem valuationCoefficientLocalHom_target_scalarTower :
    letI : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
    IsScalarTower C A B := by
  let : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
  exact IsScalarTower.of_algebraMap_eq
    (fun c => (valuationCoefficientLocalHom_target (B := B) (F := F) (L := L) c).symm)

/-- Every nonzero coefficient is a unit in the constructed source
valuation ring, as required by a horizontal coefficient-field action. -/
theorem valuationCoefficientLocalHom_isUnit (c : C) (hc : c ≠ 0) :
    IsUnit (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L) c) :=
  (isUnit_iff_ne_zero.mpr hc).map _

variable {K : Type*} [Field K] [Algebra K C] [Algebra K A] [Algebra K F]
  [IsScalarTower K C F] [IsScalarTower K A F]

/-- The descended coefficient action preserves the original coefficient
field action on the source valuation ring. -/
theorem valuationCoefficientLocalHom_base_scalarTower :
    letI : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
    IsScalarTower K C A := by
  let : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro k
  apply IsFractionRing.injective A F
  change algebraMap A F (algebraMap K A k) = algebraMap A F
    (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L) (algebraMap K C k))
  rw [← IsScalarTower.algebraMap_apply K A F, valuationCoefficientLocalHom_source,
    ← IsScalarTower.algebraMap_apply K C F]

/-- The horizontal residue condition follows from the descended curve
field: its actual rational parameter has transcendental residue in the
source divisor, so horizontality need not be separately assumed here. -/
theorem valuationCoefficientLocalHom_parameter_residue_transcendental
    (e : RatFunc K ≃ₐ[K] C) :
    letI : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
    Transcendental K (IsLocalRing.residue A
      (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L) (e RatFunc.X))) := by
  let : Algebra C A := (valuationCoefficientLocalHom (A := A) (B := B) (F := F) (L := L)).toAlgebra
  let : IsScalarTower K C A := valuationCoefficientLocalHom_base_scalarTower
    (K := K) (A := A) (B := B) (F := F) (L := L)
  let j : C →ₐ[K] IsLocalRing.ResidueField A :=
    (IsScalarTower.toAlgHom K A (IsLocalRing.ResidueField A)).comp (IsScalarTower.toAlgHom K C A)
  intro ha
  change IsAlgebraic K (j (e RatFunc.X)) at ha
  have hc : IsAlgebraic K (e RatFunc.X) := (isAlgebraic_algHom_iff j j.injective).mp ha
  exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff e.toAlgHom e.injective).mp hc)

end DimensionFourDependence
