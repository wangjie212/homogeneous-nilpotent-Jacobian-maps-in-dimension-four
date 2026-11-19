import DimensionFourDependence.NativeProjectiveResidueIdeal
import DimensionFourDependence.ProjectivePointCoefficientRestriction

/-! # All original source-curve equations survive on the same native branch -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
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

local instance nativeSpecializationPointRelationsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeSpecializationPointRelationsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

local notation "κ₀" z:max => IsLocalRing.ResidueField ((N).presheaf.stalk z)
local notation "x₀" z:max a:max ha:max => fun i => IsLocalRing.residue ((N).presheaf.stalk z)
  (nativeProjectiveCoordinateGerm H I E hH e z a ha i)
local notation "ι₀" => extendedClosedGaussSourceCoefficientHom H I E

/-- Every homogeneous equation of the source image of a native
point remains an equation at each specialization on that same branch. -/
theorem native_projective_coordinate_residue_ideal_le_of_specializes
    (x z : N) (hxz : x ⤳ z) (a b : Fin 4) (ha : x ∈ U a) (hb : z ∈ U b) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e x
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    (projectiveFieldPointIdeal (E := E) (x₀ x a ha)).toIdeal ≤
      (projectiveFieldPointIdeal (E := E) (x₀ z b hb)).toIdeal := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e x
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  have himage : ((f) x).asHomogeneousIdeal.toIdeal ≤ ((f) z).asHomogeneousIdeal.toIdeal := by
    intro P hP
    have hxP : (f) x ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E) {P} :=
      Set.singleton_subset_iff.mpr hP
    have hzP := (hxz.map (f).continuous).mem_closed
      (ProjectiveSpectrum.isClosed_zeroLocus (homogeneousSubmodule (Fin 4) E) {P}) hxP
    exact hzP (Set.mem_singleton P)
  have hix := congrArg HomogeneousIdeal.toIdeal
    (native_projective_coordinate_residue_ideal_eq_image H I E hH e x a ha)
  have hiz := congrArg HomogeneousIdeal.toIdeal
    (native_projective_coordinate_residue_ideal_eq_image H I E hH e z b hb)
  exact hix.le.trans (himage.trans hiz.ge)

/-- The same specialization retains all fixed source-curve equations
over the original ground field. The ground-field actions are constructed
from the actual original coefficient map and the actual stalk residues. -/
theorem native_original_projective_coordinate_residue_ideal_le_of_specializes
    (x z : N) (hxz : x ⤳ z) (a b : Fin 4) (ha : x ∈ U a) (hb : z ∈ U b) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e x
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    letI : Algebra K (κ₀ x) := ((algebraMap E (κ₀ x)).comp (ι₀)).toAlgebra
    letI : Algebra K (κ₀ z) := ((algebraMap E (κ₀ z)).comp (ι₀)).toAlgebra
    (projectiveFieldPointIdeal (E := K) (x₀ x a ha)).toIdeal ≤
      (projectiveFieldPointIdeal (E := K) (x₀ z b hb)).toIdeal := by
  letI : Algebra K E := (ι₀).toAlgebra
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e x
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  letI : Algebra K (κ₀ x) := ((algebraMap E (κ₀ x)).comp (ι₀)).toAlgebra
  letI : Algebra K (κ₀ z) := ((algebraMap E (κ₀ z)).comp (ι₀)).toAlgebra
  letI : IsScalarTower K E (κ₀ x) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K E (κ₀ z) := IsScalarTower.of_algebraMap_eq' rfl
  exact projectiveFieldPointIdeal_le_of_extended_coefficients (E := E)
    (x₀ x a ha) (x₀ z b hb)
    (native_projective_coordinate_residue_ideal_le_of_specializes H I E hH e x z hxz a b ha hb)

end DimensionFourDependence
