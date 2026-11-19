import DimensionFourDependence.ScaledPlaneBaseComponents
import DimensionFourDependence.HomogeneousPencilBaseExistence
import DimensionFourDependence.AffinePencilBaseRelations
import DimensionFourDependence.AffineSourceConeForm

/-! # Original native scaled-plane powers retain the exact affine root and vertex coefficient -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance scaledPlaneOriginalPowerDataDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance scaledPlaneOriginalPowerDataIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneOriginalPowerDataExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex e

/-- The specified original affine scaled power forces its own output
covector to be nonzero on the fixed vertex. A genuine original pencil
base component and its power congruence are constructed internally. -/
theorem original_affine_scaled_power_fourth_coefficient_ne_zero
    (s : Fin 4 → E) (u : E) (hu : u ≠ 0)
    (hpower : aeval (xₐ) ((O) s) =
      algebraMap E F₀ (u ^ d) * (aeval (xₐ) (L₀)) ^ d) :
    s (Fin.last 3) ≠ 0 := by
  obtain ⟨p, q, D, Q, _hD, _hp0, hq0, _hp, _hq, hrel, hparameter, hQ, _hhQ, _hoff⟩ :=
    actual_closed_gauss_parameter_constructs_nonempty_base_component H hH I e
  have hbase : (O) s - C (u ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)) := by
    apply affine_tensor_relation_mem_pencil_base_ideal H I E e p q hq0 hrel hparameter
    simpa only [map_sub, map_mul, map_pow, aeval_C, sub_eq_zero] using hpower
  exact (scaled_plane_base_component_eq_vertexLinePrime H I E hd hH hind hGauss hvertex e
    p q hq0 hrel hparameter s u hu hbase Q hQ).1

/-- The same original native scaled power constructs the nonzero
affine root, its exact output power and its own nonzero fourth output
coefficient. Neither the covector nor the plane scale is chosen again. -/
theorem original_native_scaled_power_constructs_specified_affine_root
    (s : Fin 4 → E) (u : E) (hu : u ≠ 0)
    (hL : aeval (R := E) (w) (L₀) ≠ 0)
    (hpower : aeval (R := E) (w) ((O) s) =
      algebraMap E (N).functionField (u ^ d) * (aeval (R := E) (w) (L₀)) ^ d) :
    s (Fin.last 3) ≠ 0 ∧
      algebraMap E F₀ u * aeval (xₐ) (L₀) ≠ 0 ∧
      (algebraMap E F₀ u * aeval (xₐ) (L₀)) ^ d = aeval (xₐ) ((O) s) := by
  have hhom : ((O) s - C (u ^ d) * (L₀) ^ d).IsHomogeneous d := by
    apply (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH s).sub
    simpa only [Nat.one_mul] using ((linearFormPolynomial_homogeneous
      (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)).pow d).C_mul (u ^ d)
  have hn : aeval (R := E) (w) ((O) s - C (u ^ d) * (L₀) ^ d) = 0 := by
    simpa only [map_sub, map_mul, map_pow, aeval_C, sub_eq_zero] using hpower
  have ha := (extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e
    ((O) s - C (u ^ d) * (L₀) ^ d) hhom).mpr hn
  have hpowerA : aeval (xₐ) ((O) s) =
      algebraMap E F₀ (u ^ d) * (aeval (xₐ) (L₀)) ^ d := by
    simpa only [map_sub, map_mul, map_pow, aeval_C, sub_eq_zero] using ha
  have hLA : aeval (xₐ) (L₀) ≠ 0 := fun hz => hL
    ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e
      (L₀) (linearFormPolynomial_homogeneous _)).mp hz)
  refine ⟨original_affine_scaled_power_fourth_coefficient_ne_zero H I E hd hH hind hGauss
    hvertex e s u hu hpowerA, mul_ne_zero ((map_ne_zero (algebraMap E F₀)).mpr hu) hLA, ?_⟩
  rw [mul_pow, ← map_pow, ← hpowerA]

end DimensionFourDependence
