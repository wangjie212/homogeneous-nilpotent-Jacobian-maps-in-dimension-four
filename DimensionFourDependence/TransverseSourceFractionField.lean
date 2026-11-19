import DimensionFourDependence.ActualVertexPolynomialChart
import Mathlib.RingTheory.Localization.Integral

/-! # Clearing coefficients in the actual transverse source field

The actual field K(x_1,x_2,x_3) is a fraction field of the polynomial
algebra in the original transverse coordinates. This identifies all
coefficient denominators with actual ternary source polynomials.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable (K : Type*) [Field K]

local notation "A₀" => MvPolynomial (Fin 3) K
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K

/-- A polynomial in the actual transverse coefficient coordinates has
exactly its original source value after inclusion into the source field. -/
theorem transverseSourceCoordinate_aeval_source_value (P : A₀) :
    algebraMap L₀ S₀ (aeval (transverseSourceCoordinate K) P) =
      algebraMap R₀ S₀ (rename Fin.castSucc P) := by
  have heq : (IsScalarTower.toAlgHom K L₀ S₀).comp (aeval (transverseSourceCoordinate K)) =
      (IsScalarTower.toAlgHom K R₀ S₀).comp (rename Fin.castSucc) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.rename_X]
    rfl
  exact DFunLike.congr_fun heq P

/-- The canonical coordinate evaluation realizes the actual transverse
coefficient field as the fraction field of the original ternary ring. -/
theorem transverseSourceCoordinate_isFractionRing :
    letI : Algebra A₀ L₀ := (aeval (transverseSourceCoordinate K)).toRingHom.toAlgebra
    IsFractionRing A₀ L₀ := by
  let : Algebra A₀ L₀ := (aeval (transverseSourceCoordinate K)).toRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap A₀ L₀) :=
    transverseSourceCoordinate_algebraicIndependent K
  let : FaithfulSMul A₀ L₀ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_range_iff K
    (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc) (z : S₀)).mp z.property
  refine ⟨p, q, ?_⟩
  apply Subtype.val_injective
  change (z : S₀) = algebraMap L₀ S₀ (aeval (transverseSourceCoordinate K) p) /
    algebraMap L₀ S₀ (aeval (transverseSourceCoordinate K) q)
  have hcoe (P : A₀) : algebraMap L₀ S₀ (aeval (transverseSourceCoordinate K) P) =
      aeval (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc) P :=
    MvPolynomial.comp_aeval_apply (f := transverseSourceCoordinate K)
      (IsScalarTower.toAlgHom K L₀ S₀) P
  rw [hcoe, hcoe]
  exact hpq

end DimensionFourDependence
