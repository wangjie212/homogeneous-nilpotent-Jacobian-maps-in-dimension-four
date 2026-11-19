import DimensionFourDependence.ExtendedSourceFormLocalIdeals
import DimensionFourDependence.ProjectivePolynomialGermVanishing
import DimensionFourDependence.AffineSourceConeForm

/-! # Actual native germs retain projective equations and specialization values -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" => FractionRing (MvPolynomial (Fin 4) K) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "U" a:max => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance nativePolynomialGermPointEquationsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance nativePolynomialGermPointEquationsTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance nativePolynomialGermPointEquationsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The native chart condition is the same actual projective open condition. -/
theorem native_polynomial_germ_point_mem_projective_chart
    (z : N) (a : Fin 4) (ha : z ∈ V a) : X a ∉ ((f) z).asHomogeneousIdeal := by
  change z ∈ (f) ⁻¹ᵁ U a
  rwa [extendedClosedGaussNormalizationProjectiveMap_preimage]

/-- Native coefficients of arbitrary extended-field polynomials
are the actual ambient projective stalk pullbacks at the same point. -/
theorem native_polynomial_germ_eq_projective_stalkMap
    (P : MvPolynomial (Fin 4) E) (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha =
      (f).stalkMap z ((AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) E)).presheaf.germ
        (U a) ((f) z) (native_polynomial_germ_point_mem_projective_chart H I E hH e z a ha)
        (projectiveChartPolynomialSectionHom E a P)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  unfold extendedClosedGaussPolynomialCoefficientGerm extendedClosedGaussChartPolynomialCoefficient
  rw [projectivePullbackChartPolynomialHom_eq_app]
  exact (N).presheaf.germ_res_apply _ z ha _

/-- Native homogeneous coefficient vanishing is tested by the
original homogeneous ideal of the same actual projective image point. -/
theorem native_polynomial_germ_mem_maximal_iff_projective_equation
    (P : MvPolynomial (Fin 4) E) {D : ℕ} (hP : P.IsHomogeneous D)
    (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ↔ P ∈ ((f) z).asHomogeneousIdeal := by
  rw [native_polynomial_germ_eq_projective_stalkMap]
  rw [← projectiveChartPolynomialSection_germ_mem_maximal_iff ((f) z) a
    (native_polynomial_germ_point_mem_projective_chart H I E hH e z a ha) P hP]
  change _ ∈ (IsLocalRing.maximalIdeal ((N).presheaf.stalk z)).comap ((f).stalkMap z).hom ↔ _
  rw [IsLocalRing.maximalIdeal_comap]

/-- The actual specialization map preserves every native polynomial
germ in a common original-coordinate chart. -/
theorem native_polynomial_germ_stalkSpecializes
    (P : MvPolynomial (Fin 4) E) (x z : N) (hxz : x ⤳ z)
    (a : Fin 4) (hz : z ∈ V a) :
    (N).presheaf.stalkSpecializes hxz
      (extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a hz) =
      extendedClosedGaussPolynomialCoefficientGerm H I E hH e P x a
        (hxz.mem_open (V a).isOpen hz) := by
  unfold extendedClosedGaussPolynomialCoefficientGerm
  exact ConcreteCategory.congr_hom ((N).presheaf.germ_stalkSpecializes hz hxz) _

/-- A nonzero actual affine source value prevents the same native
homogeneous coefficient germ from being identically zero at any point. -/
theorem native_polynomial_germ_ne_zero_of_affine_source_value
    (P : MvPolynomial (Fin 4) E) {D : ℕ} (hP : P.IsHomogeneous D)
    (hvalue : aeval (extendedClosedGaussAffineTensorCoordinate H I E) P ≠ 0)
    (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha ≠ 0 := by
  intro hz
  have hn := (extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff H I E hH e P hP z a ha).mp hz
  exact hvalue ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e P hP).mpr hn)

end DimensionFourDependence
