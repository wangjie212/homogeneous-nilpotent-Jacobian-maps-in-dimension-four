import DimensionFourDependence.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Normal codimension-one stalks supply their own discrete valuation

No source-divisor map or chosen uniformizer is required. Normality,
Noetherianity and intrinsic codimension one give the DVR needed to
interpret section orders as actual integer scheme orders.
-/

namespace DimensionFourDependence

open AlgebraicGeometry IsLocalRing

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- A normal Noetherian local domain of actual dimension one is a DVR. -/
theorem normal_local_dimension_one_isDVR
    (B : Type*) [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsNoetherianRing B] [IsIntegrallyClosed B] (hdim : ringKrullDim B = 1) :
    IsDiscreteValuationRing B := by
  let : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr hdim.le
  have hnf : ¬ IsField B := by
    intro hf
    let : Field B := hf.toField
    have hzero : ringKrullDim B ≤ 0 :=
      Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 B)
    rw [hdim] at hzero
    norm_num at hzero
  have hmax : maximalIdeal B ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hnf
  apply ((IsDiscreteValuationRing.TFAE B hnf).out 1 4).mpr
  refine ⟨inferInstance, maximalIdeal B, ⟨hmax, inferInstance⟩, ?_⟩
  intro P hP
  exact eq_maximalIdeal ((Ring.krullDimLE_one_iff_of_isPrime_bot.mp
    (inferInstance : Ring.KrullDimLE 1 B)) P hP.1 hP.2)

/-- At an intrinsic codimension-one point, a normal stalk on an integral
locally Noetherian scheme is itself a DVR. -/
theorem normal_codimension_one_scheme_stalk_isDVR
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (y : X) (hy : Order.coheight y = 1) [IsIntegrallyClosed (X.presheaf.stalk y)] :
    IsDiscreteValuationRing (X.presheaf.stalk y) := by
  apply normal_local_dimension_one_isDVR
  rw [ringKrullDim_stalk_eq_coheight, hy]
  rfl

end DimensionFourDependence
