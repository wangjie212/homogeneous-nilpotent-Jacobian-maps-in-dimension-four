import DimensionFourDependence.NativeDivisorCoordinateHilbert
import DimensionFourDependence.NativePencilStalkConstants

/-! # Actual coordinate residues retain the entire original projective image ideal -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e

local instance nativeProjectiveResidueIdealIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeProjectiveResidueIdealAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual polynomial germ map has exactly the actual stalk
constant-field action, including all extended coefficients. -/
theorem nativePolynomialCoefficientGermHom_constant
    (z : N) (a : Fin 4) (ha : z ∈ U a) (c : E) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    nativePolynomialCoefficientGermHom H I E hH e z a ha (C c) =
      algebraMap E ((N).presheaf.stalk z) c := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  letI := extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e z
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  rw [nativePolynomialCoefficientGermHom_apply,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ (isHomogeneous_C (Fin 4) c),
    aeval_C, pow_zero, div_one, ← IsScalarTower.algebraMap_apply E ((N).presheaf.stalk z) (N).functionField]

/-- Every original polynomial evaluated on the actual regular
coordinate residues is the residue of its actual original local germ. -/
theorem native_projective_coordinate_residue_evaluation
    (z : N) (a : Fin 4) (ha : z ∈ U a) (P : MvPolynomial (Fin 4) E) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    aeval (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
        (nativeProjectiveCoordinateGerm H I E hH e z a ha i)) P =
      IsLocalRing.residue ((N).presheaf.stalk z)
        (extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha) := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  have he :
      (aeval (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
        (nativeProjectiveCoordinateGerm H I E hH e z a ha i))).toRingHom =
      (IsLocalRing.residue ((N).presheaf.stalk z)).comp
        (nativePolynomialCoefficientGermHom H I E hH e z a ha) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change aeval _ (C c) = IsLocalRing.residue _
        (nativePolynomialCoefficientGermHom H I E hH e z a ha (C c))
      rw [aeval_C, nativePolynomialCoefficientGermHom_constant]
      exact IsScalarTower.algebraMap_apply E ((N).presheaf.stalk z)
        (IsLocalRing.ResidueField ((N).presheaf.stalk z)) c
    · intro i
      change aeval _ (X i) = IsLocalRing.residue _
        (nativePolynomialCoefficientGermHom H I E hH e z a ha (X i))
      rw [aeval_X]
      rfl
  exact RingHom.congr_fun he P

/-- The entire homogeneous ideal of the actual projective image
point equals the ideal represented by its actual coordinate residues. -/
theorem native_projective_coordinate_residue_ideal_eq_image
    (z : N) (a : Fin 4) (ha : z ∈ U a) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    projectiveFieldPointIdeal (E := E)
      (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
        (nativeProjectiveCoordinateGerm H I E hH e z a ha i)) =
      ((f) z).asHomogeneousIdeal := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  apply HomogeneousIdeal.ext'
  intro n P hP
  change P ∈ (projectiveFieldPointIdeal (E := E)
      (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
        (nativeProjectiveCoordinateGerm H I E hH e z a ha i))).toIdeal ↔ _
  rw [projectiveFieldPointIdeal_mem_homogeneous _ P hP,
    native_projective_coordinate_residue_evaluation,
    IsLocalRing.residue_eq_zero_iff]
  exact native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e P hP z a ha

/-- The actual specialized coordinate vector is nonzero, with
its specified source-chart frame equal to one. -/
theorem native_projective_coordinate_residue_ne_zero
    (z : N) (a : Fin 4) (ha : z ∈ U a) :
    (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
      (nativeProjectiveCoordinateGerm H I E hH e z a ha i)) ≠ 0 := by
  intro hz
  have he := congrFun hz a
  rw [nativeProjectiveCoordinateGerm_frame, map_one, Pi.zero_apply] at he
  exact one_ne_zero he

end DimensionFourDependence
