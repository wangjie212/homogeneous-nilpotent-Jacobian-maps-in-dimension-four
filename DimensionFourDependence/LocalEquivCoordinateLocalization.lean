import DimensionFourDependence.LocalEquivCoefficientField
import Mathlib.RingTheory.Localization.Basic

/-! # A local source isomorphism recovers coordinate denominator localization

The inverse source local isomorphism gives the coordinate map into the
original source ring. The original source ring is then a localization of
the coordinate ring at exactly its original prime-complement denominators.
This is the form needed before coefficient base change and normalization.
-/

namespace DimensionFourDependence

variable {K S A B : Type*} [CommRing K] [CommRing S] [CommRing A] [CommRing B]
  [Algebra A B] [Algebra K A] [Algebra K B] [Algebra K S] [Algebra S B]
  [IsScalarTower K A B] [IsScalarTower K S B]

/-- The coordinate homomorphism into the source ring obtained by the
inverse of its actual local algebra isomorphism. -/
noncomputable def localEquivCoordinateAlgHom (u : A ≃ₐ[A] B) : S →ₐ[K] A :=
  (u.symm.restrictScalars K).toAlgHom.comp (IsScalarTower.toAlgHom K S B)

/-- The coordinate descent retains each coordinate's original upstairs value. -/
theorem localEquivCoordinateAlgHom_target (u : A ≃ₐ[A] B) (s : S) :
    algebraMap A B (localEquivCoordinateAlgHom (K := K) u s) = algebraMap S B s := by
  have hu (a : A) : u a = algebraMap A B a := by simpa using u.commutes a
  rw [← hu]
  exact u.apply_symm_apply (algebraMap S B s)

/-- The coordinate action supplied by the inverse local source isomorphism. -/
@[instance_reducible]
noncomputable def localEquivCoordinateAlgebra (u : A ≃ₐ[A] B) : Algebra S A :=
  (localEquivCoordinateAlgHom (K := K) (S := S) u).toRingHom.toAlgebra

/-- The local equivalence is also an equivalence over the original
coordinate ring, with the constructed source-coordinate action. -/
noncomputable def localEquivCoordinateEquiv (u : A ≃ₐ[A] B) :
    letI : Algebra S A := localEquivCoordinateAlgebra (K := K) (S := S) u
    B ≃ₐ[S] A := by
  let : Algebra S A := localEquivCoordinateAlgebra (K := K) (S := S) u
  exact { u.symm.toRingEquiv with commutes' := fun _ => rfl }

/-- The source ring is localized at the very same coordinate denominators;
this conclusion does not assume a local coordinate-ring identification. -/
theorem local_equiv_coordinate_isLocalization (u : A ≃ₐ[A] B)
    (M : Submonoid S) [IsLocalization M B] :
    letI : Algebra S A := localEquivCoordinateAlgebra (K := K) (S := S) u
    IsLocalization M A := by
  let : Algebra S A := localEquivCoordinateAlgebra (K := K) (S := S) u
  exact IsLocalization.isLocalization_of_algEquiv M (localEquivCoordinateEquiv (K := K) u)

end DimensionFourDependence
