import DimensionFourDependence.ReducedClosureAffineChart

/-! # The actual reduced-closure affine charts commute with their inclusion

The original ambient affine ring maps to its point-prime quotient.
The affine chart isomorphism on the global reduced closure realizes
exactly that same quotient morphism.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The reduced-closure chart isomorphism commutes with the actual
global inclusion through the original point-prime quotient map. -/
theorem reducedPointClosureAffineChart_inv_to_ambient
    (X : Scheme.{u}) (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    (reducedPointClosureAffineChart X x U hx).inv ≫
        (reducedPointClosureInclusion X x ⁻¹ᵁ U.1).ι ≫
        reducedPointClosureInclusion X x =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)) ≫ U.2.fromSpec := by
  let I := reducedPointClosureIdeal X x
  let raw : (I.subschemeι ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)) :=
    IsOpenImmersion.isoOfRangeEq (I.subschemeι ⁻¹ᵁ U.1).ι (I.subschemeCover.f U) (by
      ext z
      constructor
      · rintro ⟨z, rfl⟩
        exact (I.opensRange_subschemeCover_map U).ge z.property
      · intro hz
        exact ⟨⟨z, (I.opensRange_subschemeCover_map U).le hz⟩, rfl⟩)
  let b := Ideal.quotEquivOfEq (reducedPointClosureIdeal_affine_eq X x U hx)
  have hraw : raw.inv ≫ (I.subschemeι ⁻¹ᵁ U.1).ι = I.subschemeCover.f U :=
    IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have hb : CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫
        CommRingCat.ofHom b.toRingHom =
      CommRingCat.ofHom (Ideal.Quotient.mk (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Ideal.quotEquivOfEq_mk (reducedPointClosureIdeal_affine_eq X x U hx) r
  change Spec.map (CommRingCat.ofHom b.toRingHom) ≫ raw.inv ≫
    (I.subschemeι ⁻¹ᵁ U.1).ι ≫ I.subschemeι = _
  rw [← Category.assoc _ (I.subschemeι ⁻¹ᵁ U.1).ι, hraw,
    Scheme.IdealSheafData.subschemeCover_map_subschemeι,
    Scheme.IdealSheafData.glueDataObjι_ι, ← Spec.map_comp_assoc, hb]

end DimensionFourDependence
