import DimensionFourDependence.NativeIndependentRootGraphTransfer

/-! # The same specified native root formula retains its exact original graph invariant product -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "xₜ" => extendedClosedGaussSourceTensorCoordinate H I E
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "a₀" => actualClosedGaussNormalCovector H I e (p 3)
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap C₀ E (e ((A) i))
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (closedGaussCoefficientParameterHom H I p hY h hh e) (A) (y₀)
local notation "cN" => closedGaussCanonicalRootNumerator H I p hY h hh e E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance nativeSpecifiedRootGraphIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeSpecifiedRootGraphAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (κ : Type u) [Field κ] [Algebra (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ] [Algebra E κ]

/-- The specified native power and rational-root formula construct
exactly the original graph product and power identities in every compatible
coefficient field. Both covectors are retained without fixed-axis values
or any choice of replacement root forms. -/
theorem native_specified_root_formula_constructs_same_original_graph_root
    (hcompat :
      letI : Algebra C₀ κ := ((algebraMap (L) κ).comp (a).toRingHom).toAlgebra
      IsScalarTower C₀ E κ)
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (S M : Fin 4 → E) (r : (N₀).functionField)
    (hpower : r ^ d = aeval (w) ((O) S))
    (hmNative : aeval (w) ((O) M) ≠ 0)
    (hformula : r = aeval (w) ((O) (cN)) * aeval (w) (L₀) / aeval (w) ((O) M)) :
    ∃ rho : κ, rho ≠ 0 ∧
      algebraMap (L) κ (n₀) * algebraMap (L) κ c =
        ((fun i => algebraMap E κ (graphRestrictedCovector p (Aₑ) M i)) ⬝ᵥ
          (fun i => algebraMap (L) κ ((y₀) i))) * rho ∧
      rho ^ d = (fun i => algebraMap E κ (graphRestrictedCovector p (Aₑ) S i)) ⬝ᵥ
        (fun i => algebraMap (L) κ ((y₀) i)) := by
  classical
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
  let : IsScalarTower C₀ (L) S₀ := actualClosedGaussCoefficientAlgebra_source_tower H I p hY h hh
  let : Algebra C₀ κ := ((algebraMap (L) κ).comp (a).toRingHom).toAlgebra
  let : IsScalarTower C₀ (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower C₀ E κ := hcompat
  let : IsScalarTower C₀ E T₀ := IsScalarTower.of_algebraMap_eq
    (fun b => (Algebra.TensorProduct.includeRight.commutes b).symm)
  let f := IsScalarTower.toAlgHom C₀ (L) S₀
  let zL := originalGraphFullOutputCoordinate H p h
  let cScaled : L := (a) (a₀) * c
  have hf (b : L) : f b = (b : S₀) := rfl
  have hσ (b : C₀) : algebraMap (L) κ ((a) b) = algebraMap E κ (algebraMap C₀ E b) :=
    IsScalarTower.algebraMap_apply C₀ E κ b
  have hO (q : Fin 4 → E) : aeval (xₜ) ((O) q) =
      coefficientTensorLinearValue (C := C₀) q (fun i => f (zL i)) := by
    simpa only [hf] using original_graph_full_output_covector_source_tensor_value
      (H := H) (I := I) (p := p) (h := h) (hh := hh) (E := E) q
  have hscaled : (cScaled : S₀) = algebraMap C₀ S₀ (a₀) * (c : S₀) := by
    change ((a) (a₀) : S₀) * (c : S₀) = _
    have he : ((a) (a₀) : S₀) = algebraMap C₀ S₀ (a₀) := by
      simpa only [IntermediateField.algebraMap_apply] using
        original_closed_gauss_graph_inclusion_source_value H I p hY h hh (a₀)
    exact congrArg (fun z : S₀ => z * (c : S₀)) he
  have hpivotTensor : (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] T₀)
      (algebraMap C₀ S₀ (a₀)) = algebraMap E T₀ (algebraMap C₀ E (a₀)) :=
    (Algebra.TensorProduct.includeLeft.commutes (a₀)).trans (IsScalarTower.algebraMap_apply C₀ E T₀ (a₀))
  have hLsource : aeval (xₜ) (L₀) = f cScaled ⊗ₜ[C₀] (1 : E) := by
    rw [original_graph_chosen_normal_source_tensor_value H I p hY h hh E hH hd hind hGauss e c hc]
    change _ = (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] T₀) (cScaled : S₀)
    rw [hscaled, map_mul, hpivotTensor]
    rfl
  have hclearNative : (aeval (w) ((O) (cN)) * aeval (w) (L₀)) ^ d =
      aeval (w) ((O) S) * aeval (w) ((O) M) ^ d := by
    apply (rational_root_power_iff_cleared _ _ _ _ d hmNative).mp
    rw [← hformula]
    exact hpower
  let P := (((O) (cN)) * (L₀)) ^ d - ((O) S) * ((O) M) ^ d
  have hP : P.IsHomogeneous (d * (d + 1)) := rationalRootClearedPolynomial_homogeneous
    ((O) (cN)) ((O) M) ((O) S) (L₀)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH (cN))
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH M)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH S)
      (linearFormPolynomial_homogeneous _)
  have hzeroNative : aeval (w) P = 0 := by
    simpa only [P, map_sub, map_mul, map_pow, sub_eq_zero] using hclearNative
  have hzeroSource := (extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e P hP).mpr hzeroNative
  have hclearSource : (coefficientTensorLinearValue (C := C₀) (cN) (fun i => f (zL i)) *
        (f cScaled ⊗ₜ[C₀] (1 : E))) ^ d =
      coefficientTensorLinearValue (C := C₀) S (fun i => f (zL i)) *
        coefficientTensorLinearValue (C := C₀) M (fun i => f (zL i)) ^ d := by
    simpa only [P, map_sub, map_mul, map_pow, sub_eq_zero, hO, hLsource] using hzeroSource
  have hmSource : coefficientTensorLinearValue (C := C₀) M (fun i => f (zL i)) ≠ 0 := by
    intro hz
    apply hmNative
    apply (extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e ((O) M)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH M)).mp
    rw [hO]
    exact hz
  obtain ⟨_hmκ, hpowerκ, hprodκ⟩ := source_tensor_cleared_root_constructs_same_boundary_root
    (κ := κ) f (actual_closed_gauss_relatively_closed_in_coefficient_field H I p hY h hh)
      (cN) M S zL cScaled d hmSource hclearSource
  let v (q : Fin 4 → E) := ∑ i, algebraMap E κ (q i) * algebraMap (L) κ (zL i)
  let rho := v (cN) * algebraMap (L) κ cScaled / v M
  have hproduct : algebraMap (L) κ (n₀) * algebraMap (L) κ c = v M * rho :=
    (hprodκ.trans (original_canonical_boundary_numerator_normal_product_eq_graph_invariant_product
      H I p hY h hh E hd hH e hσ c)).symm
  have hrho : rho ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hproduct
    exact mul_ne_zero ((map_ne_zero (algebraMap (L) κ)).mpr
      (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd hH))
      ((map_ne_zero (algebraMap (L) κ)).mpr hc0) hproduct
  refine ⟨rho, hrho, ?_, ?_⟩
  · rw [← original_full_output_boundary_value_eq_graph_pairing H I p hY h hh E hd hH e hσ M]
    exact hproduct
  · rw [← original_full_output_boundary_value_eq_graph_pairing H I p hY h hh E hd hH e hσ S]
    exact hpowerκ

end DimensionFourDependence
