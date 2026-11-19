import DimensionFourDependence.IntrinsicDivisorPullbackEquiv
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Divisor pullbacks through actual scheme isomorphisms -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

/-- An open immersion identifies the upstairs stalks, so an intrinsic
comparison for the composite is the comparison on its image. -/
theorem intrinsic_divisor_pullback_openImmersion
    {X Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsOpenImmersion i] (g : Z ⟶ X)
    (y : Y) (h : IntrinsicDivisorPullbackComparison ((i ≫ g).stalkMap y).hom) :
    IntrinsicDivisorPullbackComparison (g.stalkMap (i y)).hom := by
  let b := (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
  apply intrinsic_divisor_pullback_equiv
    (RingEquiv.refl (X.presheaf.stalk (g (i y)))) b.symm
    ((i ≫ g).stalkMap y).hom (g.stalkMap (i y)).hom ?_ h
  intro z
  rw [Scheme.Hom.stalkMap_comp]
  change b.symm (b (g.stalkMap (i y) z)) = g.stalkMap (i y) z
  exact b.symm_apply_apply _

/-- A compatible isomorphism of the upstairs schemes transports the
intrinsic comparison at every point over a source divisor. -/
theorem intrinsic_divisor_pullback_iso
    {X Y Z : Scheme.{u}} (e : Y ≅ Z) (f : Y ⟶ X) (g : Z ⟶ X)
    (hcomm : e.hom ≫ g = f)
    (hf : ∀ y : Y, Order.coheight (f y) = 1 →
      IntrinsicDivisorPullbackComparison (f.stalkMap y).hom)
    (z : Z) (hz : Order.coheight (g z) = 1) :
    IntrinsicDivisorPullbackComparison (g.stalkMap z).hom := by
  have hpoint : e.hom (e.inv z) = z := by simp
  have hcomp : IntrinsicDivisorPullbackComparison
      ((e.hom ≫ g).stalkMap (e.inv z)).hom := by
    rw [hcomm]
    apply hf
    have heval : f (e.inv z) = g z := by
      rw [← hcomm]
      change g (e.hom (e.inv z)) = g z
      rw [hpoint]
    rw [heval]
    exact hz
  have h := intrinsic_divisor_pullback_openImmersion e.hom g (e.inv z) hcomp
  rw [hpoint] at h
  exact h

end DimensionFourDependence
