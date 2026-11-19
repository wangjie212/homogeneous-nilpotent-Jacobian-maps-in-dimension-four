import DimensionFourDependence.HomogeneousChartEvaluation
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # The actual Proj chart prime and the source-ratio quotient

For a projective point whose homogeneous ideal consists of the original
source relations, its actual affine Proj-chart prime is the kernel of
evaluation on the original coordinate ratios. The corresponding prime
quotient is exactly the existing original-coefficient chart ring.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "Aₐ" a:max => HomogeneousLocalization.Away 𝒢 (X a)

/-- The prime on Mathlib's actual projective affine chart is precisely
the original homogeneous-fraction evaluation kernel. -/
theorem homogeneousCoordinateChartEval_ker_eq_projective_prime
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (z : ProjectiveSpectrum 𝒢)
    (hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom)
    (hza : X a ∉ z.asHomogeneousIdeal) :
    RingHom.ker (homogeneousCoordinateChartEval (C := C) x a ha) =
      ((Proj.basicOpenIsoSpec 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).hom
        ⟨z, hza⟩).asIdeal := by
  ext w
  obtain ⟨n, P, hP, rfl⟩ := Away.mk_surjective 𝒢 (isHomogeneous_X (R := C) a) w
  have hm : Away.mk 𝒢 (isHomogeneous_X (R := C) a) n P hP ∈
      ((Proj.basicOpenIsoSpec 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).hom
        ⟨z, hza⟩).asIdeal ↔ P ∈ z.asHomogeneousIdeal := by
    exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒢 ⟨z, hza⟩
      ⟨n • 1, ⟨P, hP⟩, ⟨X a ^ n, SetLike.pow_mem_graded n (isHomogeneous_X (R := C) a)⟩,
        ⟨n, rfl⟩⟩
  rw [hm]
  change homogeneousCoordinateChartEval x a ha _ = 0 ↔ P ∈ z.asHomogeneousIdeal.toIdeal
  rw [homogeneousCoordinateChartEval_mk, hrel]
  change aeval x P / x a ^ n = 0 ↔ aeval x P = 0
  simp only [div_eq_zero_iff, pow_ne_zero n ha, or_false]

/-- Restricting the evaluation codomain to its actual ratio algebra
does not change its kernel. -/
theorem homogeneousCoordinateChartToSource_ker
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) :
    RingHom.ker (homogeneousCoordinateChartToSource (C := C) x a ha) =
      RingHom.ker (homogeneousCoordinateChartEval (C := C) x a ha) := by
  ext w
  change homogeneousCoordinateChartToSource x a ha w = 0 ↔ homogeneousCoordinateChartEval x a ha w = 0
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The actual projective affine chart's prime quotient is the
original ratio-generated source coordinate ring. -/
noncomputable def homogeneousProjectiveChartPrimeQuotientEquiv
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (z : ProjectiveSpectrum 𝒢)
    (hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom)
    (hza : X a ∉ z.asHomogeneousIdeal) :
    Aₐ a ⧸ ((Proj.basicOpenIsoSpec 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).hom
      ⟨z, hza⟩).asIdeal ≃+* projectiveCoordinateChartAlgebra (C := C) x a :=
  (Ideal.quotEquivOfEq ((homogeneousCoordinateChartEval_ker_eq_projective_prime x a ha z hrel hza).symm.trans
    (homogeneousCoordinateChartToSource_ker x a ha).symm)).trans
      (RingHom.quotientKerEquivOfSurjective (homogeneousCoordinateChartToSource_surjective x a ha))

end DimensionFourDependence
