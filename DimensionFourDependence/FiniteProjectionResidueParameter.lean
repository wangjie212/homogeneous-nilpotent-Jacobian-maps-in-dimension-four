import DimensionFourDependence.FiniteProjectionIndependence
import DimensionFourDependence.HeightOneResidueCoordinate

/-! # A finite projection supplies a base residue parameter at each divisor

At a height-one center on an integral normalization, the actual finite
projection algebra has the original surface dimension. Its two original
projection coordinates generate that algebra. Nonclosedness therefore
forces a transcendental residue among those two base coordinates, rather
than among arbitrary coordinates of the original surface.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k A S B : Type u} [Field k]
  [CommRing A] [IsDomain A] [Algebra k A]
  [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
  [Algebra A S] [FaithfulSMul A S] [Algebra.IsIntegral A S] [IsScalarTower k A S]
  [CommRing B] [IsLocalRing B] [Algebra k B] [Algebra A B] [Algebra S B]
  [IsScalarTower k A B] [IsScalarTower A S B]

/-- At every height-one normalization center, a finite actual surface
projection supplies one of its two original base coordinates with
transcendental residue. No residue parameter or nonclosedness hypothesis
is supplied separately. -/
theorem height_one_finite_projection_has_transcendental_base_coordinate
    (y : Option (Fin 2) → A)
    (hfinite : Module.Finite (affineProjectionAlgebra (k := k) y) A)
    (htr : 2 ≤ Algebra.trdeg k A)
    (hcenter : ((IsLocalRing.maximalIdeal B).under S).height = 1) :
    ∃ j : Fin 2, Transcendental k (IsLocalRing.residue B (algebraMap A B (y (some j)))) := by
  let R := affineProjectionAlgebra (k := k) y
  let : Module.Finite R A := hfinite
  have hdim : Algebra.trdeg k R = Algebra.trdeg k A :=
    @affine_finite_projection_trdeg_eq k A
      (inferInstance : Field k) (inferInstance : CommRing A) (inferInstance : IsDomain A)
      (inferInstance : Algebra k A) (Fin 2) y hfinite
  have htrR : 2 ≤ Algebra.trdeg k R := htr.trans_eq hdim.symm
  let : Algebra R S := inferInstance
  let : Algebra R B := inferInstance
  let : IsScalarTower R A S := inferInstance
  let : IsScalarTower R A B := inferInstance
  let : IsScalarTower R S B := inferInstance
  let : IsScalarTower k R S := inferInstance
  let : IsScalarTower k R B := inferInstance
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.trans A
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro r t h
    apply Subtype.ext
    exact (FaithfulSMul.algebraMap_injective A S) h)
  obtain ⟨j, hj⟩ := height_one_integral_extension_has_transcendental_coordinate
    (k := k) (A := R) (S := S) (B := B) (affineProjectionCoordinate (k := k) y)
    (affineProjectionCoordinate_adjoin (k := k) y) htrR hcenter
  exact ⟨j, hj⟩

end DimensionFourDependence
