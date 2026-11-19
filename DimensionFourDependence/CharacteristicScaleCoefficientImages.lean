import DimensionFourDependence.CharacteristicPencilRegularZero
import DimensionFourDependence.NativeScaleHomogeneousQuotients
import DimensionFourDependence.RootFactorizationScaledTarget
import DimensionFourDependence.RealizedOutputCoefficientAlgebraicity
import DimensionFourDependence.FullOutputFiber

/-! # The actual characteristic scale realizes all original fiber coefficients over its parameter field -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower
attribute [local instance 2000] Algebra.toSMul

universe u

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "F₀" => (N).functionField
local notation "G₀" => RatFunc (F₀)
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "T₀" => ∑ j, algebraMap E (F₀) ((ν₀) j) * (w) j
local notation "L₀" => linearFormPolynomial (ν₀)
local notation "Y₀" => fun i => aeval (w) (MvPolynomial.map (ι) (H i))
local notation "B₀" r:max => IntermediateField.adjoin E
  {nativeCharacteristicPencilValue H I E hH e hd hind hGauss r}
local notation "J₀" r:max => IntermediateField.adjoin (B₀ r) {(RatFunc.X : G₀)}

local instance characteristicScaleCoefficientImagesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicScaleCoefficientImagesExtendedAlgebra : Algebra E (F₀) :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance characteristicScaleCoefficientImagesOriginalAlgebra : Algebra K (F₀) :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

/-- The original rational source embeds by the actual characteristic
tangent-plane normalization and one independent scale. -/
noncomputable def nativeCharacteristicScaleSourceHom (hT : (T₀) ≠ 0) : S₀ →ₐ[K] G₀ :=
  nativeIndependentScaleSourceFieldHom H I E hH e (L₀)
    (by simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hT)

/-- This source realization retains every original coordinate label. -/
theorem nativeCharacteristicScaleSourceHom_coordinate (hT : (T₀) ≠ 0) (i : Fin 4) :
    nativeCharacteristicScaleSourceHom H I E hH e hd hind hGauss hT
      (rationalCoordinate (K := K) i) = RatFunc.X * RatFunc.C ((w) i / (T₀)) := by
  unfold nativeCharacteristicScaleSourceHom
  have hL : aeval (w) (L₀) ≠ 0 := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hT
  simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using
    nativeIndependentScaleSourceFieldHom_coordinate H I E hH e (L₀) hL i

/-- Every original output retains its exact native normalization
and its full independent homogeneous scale. -/
theorem nativeCharacteristicScaleSourceHom_output (hT : (T₀) ≠ 0) (i : Fin 4) :
    nativeCharacteristicScaleSourceHom H I E hH e hd hind hGauss hT
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) =
      RatFunc.X ^ d * RatFunc.C ((Y₀) i / (T₀) ^ d) := by
  unfold nativeCharacteristicScaleSourceHom
  have hL : aeval (w) (L₀) ≠ 0 := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hT
  simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using
    nativeIndependentScaleSourceFieldHom_homogeneous_polynomial H I E hH e (L₀) hL (H i) (hH i)

/-- The actual characteristic factorization places all realized
original outputs in E(rho/L_t)(s), with no target specialization. -/
theorem actual_characteristic_scaled_output_mem_parameter_scale_field
    (cN : Fin 4 → E) (r : F₀)
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r)
    (hT : (T₀) ≠ 0) (i : Fin 4) :
    nativeCharacteristicScaleSourceHom H I E hH e hd hind hGauss hT
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ∈ J₀ r := by
  obtain ⟨V, W, _hVW, _hV, _hW, _hchar, _hspan, _hN, hY⟩ := hfactor
  rw [nativeCharacteristicScaleSourceHom_output, hY i]
  exact root_factorization_scaled_output_mem_parameter_scale_field r (T₀) hT (V i) (W i) hd

/-- The same actual source realization sends every original algebraic
fiber coefficient to an element algebraic over E(rho/L_t)(s). The
coefficient embedding is not independently chosen. -/
theorem actual_characteristic_scaled_original_fiber_coefficients_algebraic
    (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H (p i.castSucc))))
    (cN : Fin 4 → E) (r : F₀)
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r)
    (hT : (T₀) ≠ 0)
    (c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H (p i.castSucc)))) :
    IsAlgebraic (J₀ r) (nativeCharacteristicScaleSourceHom H I E hH e hd hind hGauss hT
      (algebraMap (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc)))) S₀ c)) := by
  let B := B₀ r
  let J := J₀ r
  let L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
    S₀ (H (p i.castSucc)))
  let Hs : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  let Φ := nativeCharacteristicScaleSourceHom H I E hH e hd hind hGauss hT
  letI : Algebra K E := (ι).toAlgebra
  letI : IsScalarTower K E (F₀) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K B (F₀) := IsScalarTower.to₁₃₄ K E B (F₀)
  letI : IsScalarTower K B G₀ := IsScalarTower.to₁₂₄ K B (F₀) G₀
  letI : IsScalarTower K J G₀ := IsScalarTower.to₁₃₄ K B J G₀
  have hrankS : (rationalJacobian Hs).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  letI := fullOutputCoefficientAlgebra Hs hrankS p hY
  letI : IsScalarTower (fullOutputField (K := K) Hs) L S₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsAlgebraic (fullOutputField (K := K) Hs) L :=
    fullOutputCoefficient_isAlgebraic Hs hrankS p hY
  let Y : Fin 4 → J := fun i => ⟨Φ (Hs i),
    actual_characteristic_scaled_output_mem_parameter_scale_field
      H I E hH e hd hind hGauss cN r hfactor hT i⟩
  exact realized_full_output_values_make_original_fiber_coefficients_algebraic
    Hs Φ Y (fun _ => rfl) c

end DimensionFourDependence
