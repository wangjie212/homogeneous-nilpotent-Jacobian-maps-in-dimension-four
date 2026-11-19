import DimensionFourDependence.ActualBoundaryNativeRoot
import DimensionFourDependence.NativeRootNonvanishingTransfer

/-! # The actual boundary numerator gives a nonzero native rational root -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] coefficientFieldScalarTower Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
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
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh
local notation "Q" => MvPolynomial.map (algebraMap C₀ E) (linearFormPolynomial (ν))
local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "P" => selectedOutputLinearPolynomial H I E p

local instance actualNativeRootNonzeroIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualNativeRootNonzeroAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra E κ]

/-- The actual nonzero boundary numerator and original first
invariant prove the constructed native root nonzero. Nonvanishing of
the root itself is not supplied. -/
theorem actual_boundary_rational_root_native_formula_ne_zero
    (hcompat :
      letI : Algebra C₀ κ :=
        ((algebraMap (L) κ).comp (actualClosedGaussCoefficientHom H I p hY h hh).toRingHom).toAlgebra
      IsScalarTower C₀ E κ)
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (n m : Fin 3 → E)
    (hn : (∑ i, algebraMap E κ (n i) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) ≠ 0)
    (hm : aeval (w) ((P) m) ≠ 0) :
    aeval (w) ((P) n) * aeval (w) (Q) / aeval (w) ((P) m) ≠ 0 := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
  let : IsScalarTower C₀ (L) S₀ := actualClosedGaussCoefficientAlgebra_source_tower H I p hY h hh
  let : Algebra C₀ κ :=
    ((algebraMap (L) κ).comp (actualClosedGaussCoefficientHom H I p hY h hh).toRingHom).toAlgebra
  let : IsScalarTower C₀ (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower C₀ E κ := hcompat
  have hfsource (b : L) : IsScalarTower.toAlgHom C₀ (L) S₀ b = (b : S₀) := rfl
  have hnsource : aeval (extendedClosedGaussSourceTensorCoordinate H I E) ((P) n) ≠ 0 := by
    simpa only [selectedOutputLinearPolynomial_source_tensor_value, hfsource, coefficientCoordinate_coe] using
      boundary_linear_form_source_tensor_ne_zero (IsScalarTower.toAlgHom C₀ (L) S₀)
        n (coefficientCoordinate (K := K) (Y)) hn
  have hmsource : aeval (extendedClosedGaussSourceTensorCoordinate H I E) ((P) m) ≠ 0 := by
    intro hz
    exact hm ((extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e ((P) m)
      (selectedOutputLinearPolynomial_homogeneous H I E hH p m)).mp hz)
  have hqsource : aeval (extendedClosedGaussSourceTensorCoordinate H I E) (Q) ≠ 0 := by
    rw [extendedClosedGaussSourceTensorCoordinate_original_polynomial_value,
      actualClosedGaussFirstInvariantCovector_source_value, ← hc]
    let : IsDomain (S₀ ⊗[C₀] E) :=
      (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
    apply (map_ne_zero (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] S₀ ⊗[C₀] E)).mpr
    intro hz
    apply hc0
    apply Subtype.ext
    exact hz
  exact extendedClosedGauss_native_rational_formula_ne_zero H I E hH e ((P) n) ((P) m) (Q)
    (selectedOutputLinearPolynomial_homogeneous H I E hH p n)
    (selectedOutputLinearPolynomial_homogeneous H I E hH p m)
    ((extendedClosedGaussInputLinearPolynomial_homogeneous C₀ (ν)).map (algebraMap C₀ E))
    hnsource hmsource hqsource

end DimensionFourDependence
