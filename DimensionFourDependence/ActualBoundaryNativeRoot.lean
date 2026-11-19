import DimensionFourDependence.SourceTensorPolynomialValues
import DimensionFourDependence.NativeRationalRootTransfer
import DimensionFourDependence.ClosedGaussInvariantLinearForm

/-! # The actual boundary root formula constructs a root in the native pencil field

The actual graph coefficient field is relatively closed over the closed
Gauss field. Its boundary root equations therefore give the cleared
source identity. The original first invariant supplies its actual source
linear form. Exact homogeneous relation comparison then constructs the
same rational root in the native normalized pencil function field.
-/

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

local instance actualBoundaryNativeRootIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualBoundaryNativeRootAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra E κ]

/-- Actual boundary equations (4.4), with their actual finite
coefficient actions, construct the original rational root n(H)L_t/m(H)
in the native normalized pencil function field. No native root or
native identity is assumed. -/
theorem actual_boundary_equation_4_4_constructs_native_rational_root
    (hcompat :
      letI : Algebra C₀ κ :=
        ((algebraMap (L) κ).comp (actualClosedGaussCoefficientHom H I p hY h hh).toRingHom).toAlgebra
      IsScalarTower C₀ E κ)
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (n m s : Fin 3 → E) (ρ : κ)
    (hn : (∑ i, algebraMap E κ (n i) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) ≠ 0)
    (hprod : (∑ i, algebraMap E κ (n i) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) *
      algebraMap (L) κ c =
        (∑ i, algebraMap E κ (m i) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) * ρ)
    (hroot : ρ ^ d = ∑ i, algebraMap E κ (s i) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) :
    aeval (w) ((P) m) ≠ 0 ∧
      (aeval (w) ((P) n) * aeval (w) (Q) / aeval (w) ((P) m)) ^ d = aeval (w) ((P) s) := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
  let : IsScalarTower C₀ (L) S₀ := actualClosedGaussCoefficientAlgebra_source_tower H I p hY h hh
  let : Algebra C₀ κ :=
    ((algebraMap (L) κ).comp (actualClosedGaussCoefficientHom H I p hY h hh).toRingHom).toAlgebra
  let : IsScalarTower C₀ (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower C₀ E κ := hcompat
  obtain ⟨hm, hclear⟩ := boundary_rational_root_gives_source_tensor_equation
    (IsScalarTower.toAlgHom C₀ (L) S₀)
    (actual_closed_gauss_relatively_closed_in_coefficient_field H I p hY h hh)
    n m s (coefficientCoordinate (K := K) (Y)) c ρ d hn hc0 hprod hroot
  have hq : aeval (extendedClosedGaussSourceTensorCoordinate H I E) (Q) =
      (c : S₀) ⊗ₜ[C₀] (1 : E) := by
    rw [extendedClosedGaussSourceTensorCoordinate_original_polynomial_value,
      actualClosedGaussFirstInvariantCovector_source_value, ← hc]
    rfl
  have hfsource (b : L) : IsScalarTower.toAlgHom C₀ (L) S₀ b = (b : S₀) := rfl
  apply extendedClosedGauss_native_rational_root_of_source_tensor H I E hH e
    ((P) n) ((P) m) ((P) s) (Q)
    (selectedOutputLinearPolynomial_homogeneous H I E hH p n)
    (selectedOutputLinearPolynomial_homogeneous H I E hH p m)
    (selectedOutputLinearPolynomial_homogeneous H I E hH p s)
    ((extendedClosedGaussInputLinearPolynomial_homogeneous C₀ (ν)).map (algebraMap C₀ E))
  · simpa only [selectedOutputLinearPolynomial_source_tensor_value, hq,
      hfsource, coefficientCoordinate_coe] using hclear
  · simpa only [selectedOutputLinearPolynomial_source_tensor_value,
      hfsource, coefficientCoordinate_coe] using hm

end DimensionFourDependence
