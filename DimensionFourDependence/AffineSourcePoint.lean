import DimensionFourDependence.AffineChartStalkNaturality

/-! # Actual affine target points retain their specified source-ring primes -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The prime of the actual affine target point in a specified scheme
diagram is exactly contraction through the specified section-ring map. -/
theorem affineSourceDiagram_primeIdealOf
    {X : Scheme.{u}} (B : CommRingCat.{u}) (U : X.affineOpens)
    (φ : Γ(X, U.1) ⟶ B) (f : Spec B ⟶ X)
    (hf : f = Spec.map φ ≫ U.2.fromSpec) (q : PrimeSpectrum B) :
    U.2.primeIdealOf ⟨f q, affineSourceDiagram_mem B U φ f hf q⟩ =
      q.comap φ.hom := by
  apply U.2.fromSpec.isOpenEmbedding.injective
  rw [IsAffineOpen.fromSpec_primeIdealOf]
  exact congrArg (fun g : Spec B ⟶ X => g q) hf

end DimensionFourDependence
