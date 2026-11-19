import DimensionFourDependence.ResidueTranscendentalParameter

/-! # Horizontal local embeddings of rationally parametrized curve fields

The local rational-parameter map extends to any given rational curve
field. Agreement on the parameter proves compatibility with its actual
source-field inclusion. This version also applies to projective source
fields, without adjoining a radial coordinate.
-/

namespace DimensionFourDependence

variable {K C A F : Type*} [Field K] [Field C] [CommRing A] [CommRing F]
  [Algebra K C] [Algebra K A] [Algebra K F] [IsLocalRing A]

/-- The rationally parametrized curve field in a horizontal source local
ring, constructed from the actual residue-transcendental parameter. -/
noncomputable def rationalCoverHorizontalLocalHom
    (e : RatFunc K ≃ₐ[K] C) (t : A) (ht : Transcendental K (IsLocalRing.residue A t)) :
    C →ₐ[K] A := (horizontalParameterHom t ht).comp e.symm.toAlgHom

variable [Algebra A F] [IsScalarTower K A F] [Algebra C F] [IsScalarTower K C F]

/-- Agreement on the original parameter identifies every curve-field
function with its given actual realization in the source. -/
theorem rationalCoverHorizontalLocalHom_source
    (e : RatFunc K ≃ₐ[K] C) (t : A) (ht : Transcendental K (IsLocalRing.residue A t))
    (hX : algebraMap A F t = algebraMap C F (e RatFunc.X)) :
    (IsScalarTower.toAlgHom K A F).comp (rationalCoverHorizontalLocalHom e t ht) =
      IsScalarTower.toAlgHom K C F := by
  have hc := horizontalParameterHom_comp_source t ht
    ((IsScalarTower.toAlgHom K C F).comp e.toAlgHom) hX
  ext c
  have h := AlgHom.congr_fun hc (e.symm c)
  change algebraMap A F (horizontalParameterHom t ht (e.symm c)) = _ at h ⊢
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e.apply_symm_apply] using h

/-- The constructed curve-field action on the horizontal local ring is
compatible with its given action on the actual source function field. -/
theorem rationalCoverHorizontalLocalHom_scalarTower
    (e : RatFunc K ≃ₐ[K] C) (t : A) (ht : Transcendental K (IsLocalRing.residue A t))
    (hX : algebraMap A F t = algebraMap C F (e RatFunc.X)) :
    letI : Algebra C A := (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
    IsScalarTower C A F := by
  let : Algebra C A := (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq
    (fun c => (AlgHom.congr_fun (rationalCoverHorizontalLocalHom_source e t ht hX) c).symm)

end DimensionFourDependence
