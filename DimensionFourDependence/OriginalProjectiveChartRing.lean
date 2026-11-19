import DimensionFourDependence.ExtendedGaussSourceFractions
import DimensionFourDependence.ProjectiveSourceChartMorphism

/-! # The actual original projective chart sections are the original ratio ring

The homogeneous chart evaluation is injective on the original rational
source coordinates. Hence the actual projective affine section ring is
the same original source-ratio ring used by the local divisor models.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K]

local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "𝒢" => homogeneousSubmodule (Fin 4) K
local notation "R₀" a:max => projectiveCoordinateChartAlgebra (C := K) x₀ a

/-- Actual homogeneous chart evaluation on the original rational
coordinates is injective. -/
theorem originalProjectiveCoordinateChartToSource_injective (a : Fin 4) :
    Function.Injective (homogeneousCoordinateChartToSource (C := K) x₀ a
      (source_rationalCoordinate_ne_zero a)) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply bot_unique
  intro w hw
  change w = 0
  change homogeneousCoordinateChartToSource (C := K) x₀ a
    (source_rationalCoordinate_ne_zero a) w = 0 at hw
  obtain ⟨n, P, hP, rfl⟩ := Away.mk_surjective 𝒢 (isHomogeneous_X (R := K) a) w
  have hv : homogeneousCoordinateChartEval (C := K) x₀ a (source_rationalCoordinate_ne_zero a)
      (Away.mk 𝒢 (isHomogeneous_X (R := K) a) n P hP) = 0 := congrArg Subtype.val hw
  rw [homogeneousCoordinateChartEval_mk] at hv
  have hPeval : aeval x₀ P = 0 :=
    (div_eq_zero_iff.mp hv).resolve_right (pow_ne_zero n (source_rationalCoordinate_ne_zero a))
  have hPzero : P = 0 := (IsFractionRing.injective (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)))
    (by simpa only [rationalCoordinate_aeval, map_zero] using hPeval)
  apply HomogeneousLocalization.val_injective
  simp [Away.val_mk, hPzero, Localization.mk_zero]

/-- The actual homogeneous localization is the original source ratio
ring by its specified evaluation map. -/
noncomputable def originalProjectiveCoordinateChartEquiv (a : Fin 4) :
    Away 𝒢 (X a) ≃+* R₀ a :=
  RingEquiv.ofBijective (homogeneousCoordinateChartToSource (C := K) x₀ a
    (source_rationalCoordinate_ne_zero a))
    ⟨originalProjectiveCoordinateChartToSource_injective a,
      homogeneousCoordinateChartToSource_surjective (C := K) x₀ a (source_rationalCoordinate_ne_zero a)⟩

/-- The actual original projective affine section ring is the same
original source-ratio ring, with the original source evaluation map. -/
noncomputable def originalProjectiveAffineSectionEquiv (a : Fin 4) :
    Γ(AlgebraicGeometry.Proj 𝒢, Proj.basicOpen 𝒢 (X a)) ≃+* R₀ a :=
  (Proj.basicOpenIsoAway 𝒢 (X a) (isHomogeneous_X (R := K) a) (by omega)).symm.commRingCatIsoToRingEquiv.trans
    (originalProjectiveCoordinateChartEquiv a)

/-- The original projective section identification is the actual
source-ratio evaluation on every section. -/
theorem originalProjectiveAffineSectionEquiv_apply (a : Fin 4)
    (r : Γ(AlgebraicGeometry.Proj 𝒢, Proj.basicOpen 𝒢 (X a))) :
    originalProjectiveAffineSectionEquiv (K := K) a r =
      projectiveAmbientSectionToSource (C := K) x₀ a (source_rationalCoordinate_ne_zero a) r := rfl

end DimensionFourDependence
