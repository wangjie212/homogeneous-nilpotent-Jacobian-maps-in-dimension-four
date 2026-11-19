import DimensionFourDependence.RationalScaleCoefficientResidue
import DimensionFourDependence.ProjectivePointCoefficientComparison

/-! # Specializing the independent scale bounds the curve over its relative constant closure -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] Algebra.toSMul

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable (B F : Type u) [Field B] [Field F] [Algebra B F]

local notation "A₀" => rationalScaleZeroLocalRing F
local notation "G₀" => RatFunc F
local notation "D₀" => pencilCoefficientCurveField (E := B) (RatFunc.X : G₀)
local notation "V₀" => coefficientRestrictionValuationSubring (A := A₀) (F := G₀) (D₀)
local notation "κ₀" => IsLocalRing.ResidueField (V₀)

local instance rationalScaleRelativeHilbertDvr : IsDiscreteValuationRing A₀ := rationalScaleZeroLocalRing_isDVR F
noncomputable local instance rationalScaleRelativeHilbertFractionAlgebra : Algebra A₀ G₀ := rationalScaleZeroFractionAlgebra F
local instance rationalScaleRelativeHilbertFractionRing : IsFractionRing A₀ G₀ := rationalScaleZeroFraction_isFractionRing F
local instance rationalScaleRelativeHilbertSourceTower : IsScalarTower F A₀ G₀ := rationalScaleZeroFraction_scalarTower F

/-- The projective coordinate Hilbert function over the original
relative constants is bounded by the same coordinates over the relative
closure of B(s) in the independently scaled source. The comparison is
constructed at the actual scale-zero valuation. -/
theorem rational_scale_relative_constant_closure_hilbert_bound
    {σ : Type*} [Finite σ] (x : σ → F) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := algebraicClosure B F) x).toIdeal n ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := D₀)
        (fun i => RatFunc.C (x i))).toIdeal n := by
  letI : IsScalarTower B A₀ G₀ := IsScalarTower.to₁₃₄ B F A₀ G₀
  letI : IsScalarTower B (D₀) G₀ := pencilCoefficientCurveField_scalarTower (E := B) RatFunc.X
  letI := coefficientRestrictionConstantAlgebra (A := A₀) (F := G₀) (D₀) B
  let ψ := rationalScaleRestrictedCoefficientResidueHom B F
  let χ := rationalScaleRestrictedResidueClosureHom B F
  letI : Algebra (κ₀) F := ψ.toRingHom.toAlgebra
  letI : Algebra (κ₀) (algebraicClosure B F) := χ.toRingHom.toAlgebra
  letI : IsScalarTower (κ₀) (algebraicClosure B F) F :=
    IsScalarTower.of_algebraMap_eq (fun c =>
      (rationalScaleRestrictedResidueClosureHom_source B F c).symm)
  have hcoeff : projectiveHilbertFunction
      (projectiveFieldPointIdeal (E := algebraicClosure B F) x).toIdeal n ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := κ₀) x).toIdeal n := by
    simpa only [Function.comp_def, AlgHom.id_apply] using
      projectiveHilbertFunction_point_le_of_source_embedding
        (K := κ₀) (L := algebraicClosure B F) (AlgHom.id (κ₀) F) x n
  let π := rationalScaleZeroEvaluation F
  letI : IsLocalHom π := rationalScaleZeroEvaluation_isLocalHom F
  have hres := source_valuation_realized_coefficient_residue_hilbert_bound
    (A := A₀) (G := G₀) (D₀) π (fun i => algebraMap F A₀ (x i)) n
  have hzero : (fun i => π (algebraMap F A₀ (x i))) = x :=
    funext (fun i => rationalScaleZeroEvaluation_constant F (x i))
  have hgeneric : (fun i => algebraMap A₀ G₀ (algebraMap F A₀ (x i))) =
      (fun i => RatFunc.C (x i)) := by
    funext i
    rw [← IsScalarTower.algebraMap_apply F A₀ G₀, RatFunc.algebraMap_eq_C]
  rw [hzero, hgeneric] at hres
  exact hcoeff.trans hres

/-- Any positive projective curve degrees obey the same constructed
independent-scale specialization comparison. -/
theorem rational_scale_relative_constant_closure_curve_degree_bound
    {σ : Type*} [Finite σ] (x : σ → F) {D D' : ℕ}
    (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := D₀)
      (fun i => RatFunc.C (x i))).toIdeal D)
    (hD' : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := algebraicClosure B F) x).toIdeal D') :
    D' ≤ D :=
  curveHilbertDegree_le_of_hilbertFunction_le _ _
    (fun n => rational_scale_relative_constant_closure_hilbert_bound B F x n) hD hD'

end DimensionFourDependence
