import DimensionFourDependence.NativeScaleClosedGaussCoefficients
import DimensionFourDependence.AlgebraicConstantsCompatibleImages

/-! # The actual extended Gauss coefficients are algebraic over the original full output -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

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

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "D₀" => polynomialOutputField H

local instance nativeScaleAlgebraicCoefficientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeScaleAlgebraicCoefficientsExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance nativeScaleAlgebraicCoefficientsOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

/-- The original full output acts on the independently scaled native
field through the actual original source embedding and its actual inclusion. -/
@[instance_reducible]
noncomputable def nativeIndependentScaleFullOutputAlgebra
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0) :
    Algebra D₀ (RatFunc (N).functionField) :=
  ((nativeIndependentScaleSourceFieldHom H I E hH e L hL).toRingHom.comp (D₀).val.toRingHom).toAlgebra

/-- Every actual closed Gauss coefficient image is algebraic over
the original full output, with precisely its actual source-field action. -/
theorem native_independent_scale_closed_coefficient_algebraic_over_full_output
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0) (c : C₀) :
    letI : Algebra D₀ (RatFunc (N).functionField) := nativeIndependentScaleFullOutputAlgebra H I E hH e L hL
    IsAlgebraic D₀ (RatFunc.C (algebraMap E (N).functionField (algebraMap C₀ E c))) := by
  letI : Algebra D₀ (RatFunc (N).functionField) := nativeIndependentScaleFullOutputAlgebra H I E hH e L hL
  let Φ : S₀ →ₐ[D₀] RatFunc (N).functionField :=
    { (nativeIndependentScaleSourceFieldHom H I E hH e L hL).toRingHom with
      commutes' := fun _ => rfl }
  have hc := (original_closed_gauss_coefficient_algebraic_over_full_output H I c).algHom Φ
  change IsAlgebraic D₀ (nativeIndependentScaleSourceFieldHom H I E hH e L hL (c : S₀)) at hc
  rwa [nativeIndependentScaleSourceFieldHom_closed_coefficient] at hc

/-- Every element of the given algebraic Gauss coefficient extension
has an algebraic image over the original full output. The extension's
coefficient realization is proved compatible, rather than supplied. -/
theorem native_independent_scale_extended_coefficient_algebraic_over_full_output
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0) (b : E) :
    letI : Algebra D₀ (RatFunc (N).functionField) := nativeIndependentScaleFullOutputAlgebra H I E hH e L hL
    IsAlgebraic D₀ (RatFunc.C (algebraMap E (N).functionField b)) := by
  letI : Algebra D₀ (RatFunc (N).functionField) := nativeIndependentScaleFullOutputAlgebra H I E hH e L hL
  exact compatible_algebraic_constant_extension_images_algebraic
    ((RatFunc.C.comp (algebraMap E (N).functionField)).comp (algebraMap C₀ E))
    (RatFunc.C.comp (algebraMap E (N).functionField)) (fun _ => rfl)
    (fun c => native_independent_scale_closed_coefficient_algebraic_over_full_output H I E hH e L hL c) b

end DimensionFourDependence
