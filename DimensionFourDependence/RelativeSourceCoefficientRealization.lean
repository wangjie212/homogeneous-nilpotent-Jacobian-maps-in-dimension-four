import DimensionFourDependence.AlgebraicSourceConstantLift
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Original source coefficients live in the actual relative constant field -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pointwise algebraic original coefficient values define their
actual embedding in the relative algebraic closure of the chosen constants.
No algebraically closed overfield or conjugate embedding is chosen. -/
noncomputable def sourceCoefficientRelativeClosureHom
    {L S C G : Type*} [Field L] [Field S] [Field C] [Field G]
    [Algebra L S] [Algebra C G] (f : S →+* G)
    (halg : ∀ l : L, IsAlgebraic C (f (algebraMap L S l))) :
    L →+* algebraicClosure C G :=
  (f.comp (algebraMap L S)).codRestrict (algebraicClosure C G).toSubring
    (fun l => mem_algebraicClosure_iff.mpr (halg l))

/-- Every original coefficient retains exactly its given source value. -/
theorem sourceCoefficientRelativeClosureHom_source_value
    {L S C G : Type*} [Field L] [Field S] [Field C] [Field G]
    [Algebra L S] [Algebra C G] (f : S →+* G)
    (halg : ∀ l : L, IsAlgebraic C (f (algebraMap L S l))) (l : L) :
    algebraMap (algebraicClosure C G) G (sourceCoefficientRelativeClosureHom f halg l) =
      f (algebraMap L S l) := rfl

/-- Algebraicity over the original full output makes all original
algebraic fiber coefficients belong to the actual relative constants of
any compatible algebraic coefficient realization. -/
theorem algebraic_source_coefficient_images_algebraic_over_extended_constants
    {D L S C G : Type*} [Field D] [Field L] [Field S] [Field C] [Field G]
    [Algebra D L] [Algebra L S] [Algebra D S] [IsScalarTower D L S]
    [Algebra D C] [Algebra C G] [Algebra D G] [IsScalarTower D C G]
    [Algebra.IsAlgebraic D L] (f : S →ₐ[D] G) (l : L) :
    IsAlgebraic C (f (algebraMap L S l)) := by
  have hl : IsAlgebraic D (algebraMap L S l) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := D) l).algebraMap
  exact (hl.algHom f).tower_top C

/-- The whole relative constant field is algebraic over the same
original coefficient embedding when it is algebraic over the common
full output field. Compatibility on that entire field is explicit. -/
theorem relative_constant_field_isAlgebraic_over_compatible_source_coefficients
    {D L C G : Type*} [Field D] [Field L] [Field C] [Field G]
    [Algebra D L] [Algebra D C] [Algebra C G] [Algebra.IsAlgebraic D C]
    (g : L →+* algebraicClosure C G)
    (hD : ∀ d : D, g (algebraMap D L d) = algebraMap C (algebraicClosure C G) (algebraMap D C d)) :
    letI : Algebra L (algebraicClosure C G) := g.toAlgebra
    Algebra.IsAlgebraic L (algebraicClosure C G) := by
  letI : Algebra L (algebraicClosure C G) := g.toAlgebra
  letI : Algebra D (algebraicClosure C G) :=
    ((algebraMap C (algebraicClosure C G)).comp (algebraMap D C)).toAlgebra
  letI : IsScalarTower D C (algebraicClosure C G) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower D L (algebraicClosure C G) :=
    IsScalarTower.of_algebraMap_eq (fun d => (hD d).symm)
  letI : Algebra.IsAlgebraic D (algebraicClosure C G) :=
    Algebra.IsAlgebraic.trans D C (algebraicClosure C G)
  exact Algebra.IsAlgebraic.tower_top (K := D) («L» := L)

end DimensionFourDependence
