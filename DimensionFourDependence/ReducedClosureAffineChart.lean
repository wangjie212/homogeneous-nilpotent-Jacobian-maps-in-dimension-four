import DimensionFourDependence.ReducedPointClosureScheme

/-! # Exact affine charts on a point's reduced closure scheme

On any ambient affine open containing the given point, the reduced
closure ideal is exactly the prime corresponding to that same point.
The actual inverse open is the spectrum of its quotient ring.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable (X : Scheme.{u}) (x : X)

/-- The ideal on an ambient affine neighborhood is the prime of the
original point, rather than an independent defining ideal. -/
theorem reducedPointClosureIdeal_affine_eq
    (U : X.affineOpens) (hx : x ∈ U.1) :
    (reducedPointClosureIdeal X x).ideal U = (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure {x}) = _
  have hpre : U.2.fromSpec ⁻¹' ({x} : Set X) = {U.2.primeIdealOf ⟨x, hx⟩} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hp
      apply U.2.fromSpec.isOpenEmbedding.injective
      exact hp.trans (U.2.fromSpec_primeIdealOf ⟨x, hx⟩).symm
    · rintro rfl
      exact U.2.fromSpec_primeIdealOf ⟨x, hx⟩
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous, hpre, PrimeSpectrum.vanishingIdeal_closure,
    PrimeSpectrum.vanishingIdeal_singleton]

/-- The actual inverse affine open in the reduced closure is the
spectrum of the quotient by that original point prime. -/
noncomputable def reducedPointClosureAffineChart
    (U : X.affineOpens) (hx : x ∈ U.1) :
    (reducedPointClosureInclusion X x ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of (Γ(X, U.1) ⧸ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)) := by
  let I := reducedPointClosureIdeal X x
  let e : (I.subschemeι ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)) :=
    IsOpenImmersion.isoOfRangeEq (I.subschemeι ⁻¹ᵁ U.1).ι (I.subschemeCover.f U) (by
      ext z
      constructor
      · rintro ⟨z, rfl⟩
        exact (I.opensRange_subschemeCover_map U).ge z.property
      · intro hz
        exact ⟨⟨z, (I.opensRange_subschemeCover_map U).le hz⟩, rfl⟩)
  exact e ≪≫ Scheme.Spec.mapIso
    (Ideal.quotEquivOfEq (reducedPointClosureIdeal_affine_eq X x U hx)).symm.toCommRingCatIso.op

end DimensionFourDependence
