import DimensionFourDependence.CharacteristicPencilDegreeTwo
import DimensionFourDependence.CharacteristicPencilDivisorSpecialization

/-! # The actual characteristic pencil bounds every divisor specialization by two -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "C₀" r:max => pencilCoefficientCurveField (E := E)
  (nativeCharacteristicPencilValue H I E hH e hd hind hGauss r)

local instance characteristicPencilDivisorDegreeTwoIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilDivisorDegreeTwoAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Degree two for the actual generic pencil curve bounds every
positive divisor-specialization degree over its constructed coefficient
residue field. The actual divisor and original coordinate germs are retained. -/
theorem actual_characteristic_pencil_divisor_curve_degree_at_most_two
    (r : (N).functionField) {D : ℕ} (hD2 : D ≤ 2)
    (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C₀ r) (w)).toIdeal D)
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ U a) :
    letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
    letI := coefficientRestrictionResidueAlgebra
      (A := (N).presheaf.stalk z) (F := (N).functionField) (C₀ r)
    ∀ D' : ℕ, HasCurveHilbertDegree
      (projectiveFieldPointIdeal
        (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring
          (A := (N).presheaf.stalk z) (F := (N).functionField) (C₀ r)))
        (fun i => IsLocalRing.residue ((N).presheaf.stalk z)
          (nativeProjectiveCoordinateGerm H I E hH e z a ha i))).toIdeal D' → D' ≤ 2 := by
  letI := extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  letI := coefficientRestrictionResidueAlgebra
    (A := (N).presheaf.stalk z) (F := (N).functionField) (C₀ r)
  intro D' hD'
  exact (native_normalization_divisor_projective_curve_degree_bound
    H I E hH e z hz a ha (C₀ r) hD hD').trans hD2

end DimensionFourDependence
