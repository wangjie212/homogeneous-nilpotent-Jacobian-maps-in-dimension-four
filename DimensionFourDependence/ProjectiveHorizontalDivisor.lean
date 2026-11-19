import DimensionFourDependence.ProjectiveSourceDivisor
import DimensionFourDependence.RationalCoverHorizontalLocalRing
import DimensionFourDependence.UnramifiedDvrBaseChange

/-! # Horizontal divisor coefficient extensions on the actual projective source

The source ring here is an actual standard projective coordinate chart,
and its fraction field is the original projective source field. The
closed Gauss parameter field embeds in a horizontal divisor DVR, with
the given parameter realization. Relative closedness then proves that
finite coefficient extensions give finite étale Dedekind domains.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
  (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "L₀" => projectiveCoordinateChartField (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

/-- The actual rational Gauss parameter realized in the original
projective source field on the chosen source chart. -/
noncomputable def closedGaussProjectiveParameterSourceHom : RatFunc K →ₐ[K] L₀ :=
  (IntermediateField.inclusion
    (actual_closed_gauss_parameter_field_le_projective_source_chart H hH I e (s.symm none))).comp e.toAlgHom

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

/-- The horizontal local Gauss-field action agrees with its actual
projective source-field inclusion, using the constructed prime-local map. -/
theorem closedGaussProjectiveHorizontalLocal_scalarTower
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X) :
    letI : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
    letI : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
    letI : Algebra C₀ (Localization.AtPrime Q) :=
      (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
    IsScalarTower C₀ (Localization.AtPrime Q) L₀ := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsScalarTower K R₀ L₀ := IsScalarTower.of_algebraMap_eq (by intro c; rfl)
  let : IsScalarTower K (Localization.AtPrime Q) L₀ := primeLocalizationFraction_base_scalarTower Q
  let : IsScalarTower K C₀ L₀ := IsScalarTower.of_algebraMap_eq (by intro c; rfl)
  exact rationalCoverHorizontalLocalHom_scalarTower e t ht hX

/-- Finite coefficient extensions of an actual horizontal divisor on
the projective source are Dedekind domains, with the actual projective
source field supplying the relative closedness hypothesis. -/
theorem actual_projective_horizontal_divisor_base_change_dedekind
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X)
    (E : Type*) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    letI : Algebra C₀ (Localization.AtPrime Q) :=
      (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
    letI : CommRing (Localization.AtPrime Q ⊗[C₀] E) :=
      Algebra.TensorProduct.instCommRing (R := C₀) (A := Localization.AtPrime Q) (B := E)
    IsDedekindDomain (Localization.AtPrime Q ⊗[C₀] E) := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_divisor_isDVR s Q f hf hQ
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  let : FaithfulSMul (Localization.AtPrime Q) L₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective (Localization.AtPrime Q) L₀)
  let : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  let : CommRing (Localization.AtPrime Q ⊗[C₀] E) :=
    Algebra.TensorProduct.instCommRing (R := C₀) (A := Localization.AtPrime Q) (B := E)
  let : IsScalarTower C₀ (Localization.AtPrime Q) L₀ :=
    closedGaussProjectiveHorizontalLocal_scalarTower H hH I e s Q t ht hX
  exact relatively_closed_dvr_base_change_dedekind
    (k := C₀) (A := Localization.AtPrime Q) (F := L₀) (E := E)
    (actual_closed_gauss_parameter_relatively_closed_in_projective_source H hH I e (s.symm none))

end DimensionFourDependence
