import DimensionFourDependence.GeneratedPointPrimeDimension
import DimensionFourDependence.TensorPencilResiduePointDimension
import DimensionFourDependence.ExtendedGaussSourceNormalization

/-! # The residue coordinate prime is the actual original source contraction -/

namespace DimensionFourDependence

universe u

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra tensorPencilResidueGenerationClosedAlgebra
  tensorPencilResidueGenerationClosedSMul tensorPencilResidueGenerationExtendedSMul
  tensorPencilResidueGenerationClosedTower tensorPencilResidueGenerationOriginalSMul
  tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra
attribute [local instance 2000] tensorPencilResiduePointAddCommMonoid
  tensorPencilResiduePointSemiring tensorPencilResiduePointOriginalModule
  tensorPencilResiduePointOriginalMulAction

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀

variable (Q : Ideal (normalizationRing
  (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[closedGaussParameterField H I] E)))
  [Q.IsPrime]

local notation "L₀" => FractionRing (N₀ ⧸ Q)
local notation "y₀" => originalTensorPencilResidueCoordinate H I E s Q
local notation "f₀" => extendedClosedGaussTensorNormalizationSourceHom H I E s
local notation "eₛ" => projectiveSourceFullChartCoordinateEquiv (K := K) s

noncomputable local instance tensorPencilResidueSourceNormalizationAlgebra : Algebra N₀ L₀ :=
  primeQuotientFractionOriginalAlgebra Q

/-- Every original source polynomial has precisely its original
coordinate value in the actual normalization-prime residue field. -/
theorem original_tensor_pencil_residue_source_polynomial_value
    (P : MvPolynomial (Fin 3) K) :
    algebraMap N₀ L₀ (f₀ (eₛ P)) = aeval y₀ P := by
  let f : MvPolynomial (Fin 3) K →+* L₀ :=
    (algebraMap N₀ L₀).comp ((f₀).comp (eₛ).toRingHom)
  have hf : f = (aeval y₀ : MvPolynomial (Fin 3) K →ₐ[K] L₀).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change algebraMap N₀ L₀ (f₀ (eₛ (C c))) = aeval y₀ (C c)
      have hc : eₛ (C c) = algebraMap K R₀ c := (eₛ).commutes c
      have hb : f₀ (algebraMap K R₀ c) = algebraMap T₀ N₀
          (algebraMap C₀ S₀ (algebraMap K C₀ c) ⊗ₜ[C₀] (1 : E)) := rfl
      have ht : (algebraMap C₀ S₀ (algebraMap K C₀ c) ⊗ₜ[C₀] (1 : E)) =
          algebraMap E T₀ (algebraMap C₀ E (algebraMap K C₀ c)) :=
        Algebra.TensorProduct.tmul_one_eq_one_tmul (R := C₀) (A := S₀) (B := E) _
      calc
        _ = algebraMap N₀ L₀ (f₀ (algebraMap K R₀ c)) :=
          congrArg (fun r : R₀ => algebraMap N₀ L₀ (f₀ r)) hc
        _ = algebraMap N₀ L₀ (algebraMap T₀ N₀
            (algebraMap C₀ S₀ (algebraMap K C₀ c) ⊗ₜ[C₀] (1 : E))) := congrArg (algebraMap N₀ L₀) hb
        _ = algebraMap T₀ L₀
            (algebraMap C₀ S₀ (algebraMap K C₀ c) ⊗ₜ[C₀] (1 : E)) :=
          normalization_prime_residue_source_value Q _
        _ = algebraMap T₀ L₀ (algebraMap E T₀ (algebraMap C₀ E (algebraMap K C₀ c))) :=
          congrArg (algebraMap T₀ L₀) ht
        _ = algebraMap E L₀ (algebraMap C₀ E (algebraMap K C₀ c)) :=
          (IsScalarTower.algebraMap_apply E T₀ L₀ _).symm
        _ = algebraMap C₀ L₀ (algebraMap K C₀ c) :=
          (IsScalarTower.algebraMap_apply C₀ E L₀ _).symm
        _ = algebraMap K L₀ c := rfl
        _ = aeval y₀ (C c) := (aeval_C (f := y₀) c).symm
    · intro j
      have hj : eₛ (X j) = projectiveChartTransition (C := K) x₀ (s.symm none) (s.symm (some j)) := by
        apply Subtype.ext
        rw [projectiveSourceFullChartCoordinateEquiv_source, aeval_X]
        rfl
      change algebraMap N₀ L₀ (f₀ (eₛ (X j))) = aeval y₀ (X j)
      have hv : algebraMap N₀ L₀
          (f₀ (projectiveChartTransition (C := K) x₀ (s.symm none) (s.symm (some j)))) = y₀ j :=
        normalization_prime_residue_source_value Q (originalTensorPencilCoordinate H I E s j)
      exact (congrArg (fun r : R₀ => algebraMap N₀ L₀ (f₀ r)) hj).trans
        (hv.trans (aeval_X (f := y₀) j).symm)
  exact RingHom.congr_fun hf P

/-- The polynomial prime of the actual residue coordinate point is
exactly the original source contraction, transported through the original
source chart's polynomial-coordinate isomorphism. -/
theorem original_tensor_pencil_residue_source_prime_polynomial_comap :
    (Q.comap f₀).comap (eₛ).toRingHom = fiberVanishingIdeal (L := K) y₀ := by
  ext P
  change f₀ (eₛ P) ∈ Q ↔ aeval y₀ P = 0
  have hmem : f₀ (eₛ P) ∈ Q ↔ f₀ (eₛ P) ∈ RingHom.ker (algebraMap N₀ L₀) :=
    Iff.of_eq (congrArg (fun J : Ideal N₀ => f₀ (eₛ P) ∈ J)
      (prime_quotient_fraction_algebraMap_ker Q).symm)
  apply hmem.trans
  change algebraMap N₀ L₀ (f₀ (eₛ P)) = 0 ↔ _
  have hv := original_tensor_pencil_residue_source_polynomial_value H I E s Q P
  exact ⟨fun h => hv.symm.trans h, fun h => hv.trans h⟩

/-- The height of the actual original source contraction is the
height of the original polynomial relation prime of its actual coordinate
residues. No source-image or function-field identification is assumed. -/
theorem original_tensor_pencil_residue_source_prime_height_eq :
    (Q.comap f₀).height = (fiberVanishingIdeal (L := K) y₀).height := by
  calc
    (Q.comap f₀).height = ((Q.comap f₀).comap (eₛ).toRingHom).height :=
      ((eₛ).toRingEquiv.height_comap _).symm
    _ = _ := congrArg Ideal.height (original_tensor_pencil_residue_source_prime_polynomial_comap H I E s Q)

end DimensionFourDependence
