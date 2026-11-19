import DimensionFourDependence.ZeroPoleGeneralLevelClosure
import Mathlib.AlgebraicGeometry.Stalk

/-! # Actual local quotient levels map into the same affine-chart levels -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Contraction of a prime preserves the prescribed quotient equation
and its denominator open, with exactly the given ring map. -/
theorem quotient_level_comap_mem
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (n b c : A) (p : PrimeSpectrum B)
    (hp : p ∈ quotientLevelLocus B (φ n) (φ b) (φ c)) :
    p.comap φ ∈ quotientLevelLocus A n b c := by
  obtain ⟨hb, hlevel⟩ := hp
  refine ⟨hb, ?_⟩
  change φ (n - c * b) ∈ p.asIdeal
  simpa only [map_sub, map_mul] using hlevel

/-- If a quotient level accumulates at the actual local closed point,
its original affine-chart level accumulates at the same scheme point.
The map used is the genuine canonical map from the spectrum of the stalk. -/
theorem affine_stalk_level_closure_maps_to_chart_level_closure
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (z : X) (hz : z ∈ U) (n b c : Γ(X, U))
    (hlevel : IsLocalRing.closedPoint (X.presheaf.stalk z) ∈
      closure (quotientLevelLocus (X.presheaf.stalk z)
        (X.presheaf.germ U z hz n) (X.presheaf.germ U z hz b) (X.presheaf.germ U z hz c))) :
    z ∈ closure (hU.fromSpec '' quotientLevelLocus Γ(X, U) n b c) := by
  have hmap := mem_closure_image (hU.fromSpecStalk hz).continuous.continuousAt hlevel
  rw [hU.fromSpecStalk_closedPoint hz] at hmap
  apply closure_mono _ hmap
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p.comap (X.presheaf.germ U z hz).hom,
    quotient_level_comap_mem (X.presheaf.germ U z hz).hom n b c p hp, ?_⟩
  rfl

end DimensionFourDependence
