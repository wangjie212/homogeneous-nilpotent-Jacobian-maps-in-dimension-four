import DimensionFourDependence.ProjectiveConstantSections
import DimensionFourDependence.ProjectivePullbackHyperplaneSheaf
import DimensionFourDependence.HomogeneousEvaluationScaling

/-! # Actual regular chart coefficients of original homogeneous projective forms -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Field C] (Y : Scheme.{u}) [IsIntegral Y]
  (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C))

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "U" a:max => Proj.basicOpen 𝒢 (X a)

@[instance_reducible] noncomputable def projectivePullbackFunctionFieldAlgebra :
    Algebra C Y.functionField := (projectivePullbackScalarHom C Y f).toAlgebra

/-- Original coefficients give actual regular sections on each
inverse original projective coordinate chart. -/
noncomputable def projectivePullbackChartConstantHom (a : Fin 4) :
    C →+* Γ(Y, f ⁻¹ᵁ U a) :=
  (f.app (U a)).hom.comp (projectiveConstantSectionHom C (U a))

/-- Evaluation at the actual regular original coordinate ratios
gives actual regular polynomial coefficients on each inverse chart. -/
noncomputable def projectivePullbackChartPolynomialHom (a : Fin 4) :
    MvPolynomial (Fin 4) C →+* Γ(Y, f ⁻¹ᵁ U a) :=
  MvPolynomial.eval₂Hom (projectivePullbackChartConstantHom Y f a)
    (fun i => f.app (U a) (projectiveCoordinateRatioSection C a i))

/-- The entire regular chart-polynomial pullback retains its actual
original coordinate-ratio evaluation in the scheme function field. -/
theorem projectivePullbackChartPolynomialHom_generic_value
    (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a)) (a : Fin 4)
    (P : MvPolynomial (Fin 4) C) :
    let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
    let : Nonempty (f ⁻¹ᵁ U a) := hU a
    Y.germToFunctionField (f ⁻¹ᵁ U a) (projectivePullbackChartPolynomialHom Y f a P) =
      aeval (projectivePullbackRationalCoordinate Y f hU a) P := by
  let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
  let : Nonempty (f ⁻¹ᵁ U a) := hU a
  have hmap : (Y.germToFunctionField (f ⁻¹ᵁ U a)).hom.comp
      (projectivePullbackChartPolynomialHom Y f a) =
      (aeval (projectivePullbackRationalCoordinate Y f hU a)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [projectivePullbackChartPolynomialHom, RingHom.comp_apply, eval₂Hom_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact (projectivePullbackScalarHom_chart C Y f (U a) c).symm
    · intro i
      simp only [projectivePullbackChartPolynomialHom, RingHom.comp_apply, eval₂Hom_X',
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact RingHom.congr_fun hmap P

/-- Every actual local germ of the original regular chart-polynomial
coefficient has the same exact original ratio evaluation. -/
theorem projectivePullbackChartPolynomialHom_at_point
    (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a)) (a : Fin 4)
    (P : MvPolynomial (Fin 4) C) (p : f ⁻¹ᵁ U a) :
    let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
    schemeRationalSectionFunction Y (f ⁻¹ᵁ U a)
        (projectivePullbackChartPolynomialHom Y f a P) p =
      aeval (projectivePullbackRationalCoordinate Y f hU a) P := by
  let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
  let : Nonempty (f ⁻¹ᵁ U a) := hU a
  exact (schemeRationalSectionFunction_eq_generic Y (f ⁻¹ᵁ U a) _ p).trans
    (projectivePullbackChartPolynomialHom_generic_value Y f hU a P)

/-- The actual regular coefficient of a homogeneous degree-d source
form has common numerator P(X/X0) in the powered original frame Xa^d. -/
theorem projectivePullbackChartPolynomialHom_homogeneous_numerator
    (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a))
    (P : MvPolynomial (Fin 4) C) {d : ℕ} (hP : P.IsHomogeneous d)
    (a : Fin 4) (p : f ⁻¹ᵁ U a) :
    let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
    projectivePullbackHyperplaneWeight Y f hU a ^ d *
        schemeRationalSectionFunction Y (f ⁻¹ᵁ U a)
          (projectivePullbackChartPolynomialHom Y f a P) p =
      aeval (projectivePullbackHyperplaneWeight Y f hU) P := by
  let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
  let w := projectivePullbackHyperplaneWeight Y f hU
  have hcoords : projectivePullbackRationalCoordinate Y f hU a =
      (fun i => (w a)⁻¹ * w i) := by
    funext i
    exact (projectivePullbackRationalCoordinate_div Y f hU a 0 i).trans
      (by change w i / w a = (w a)⁻¹ * w i; rw [div_eq_mul_inv, mul_comm])
  rw [projectivePullbackChartPolynomialHom_at_point Y f hU, hcoords,
    homogeneous_aeval_scale P hP w (w a)⁻¹]
  change w a ^ d * ((w a)⁻¹ ^ d * aeval w P) = aeval w P
  rw [← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ (projectivePullbackHyperplaneWeight_ne_zero Y f hU a), one_pow, one_mul]

end DimensionFourDependence
