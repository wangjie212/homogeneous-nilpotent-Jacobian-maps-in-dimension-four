import DimensionFourDependence.NativeSpecifiedPowerBoundary
import DimensionFourDependence.ActualBoundaryChosenRuling
import DimensionFourDependence.RulingProportionalCovectorBaseChange

/-! # The original proportional-power case forces the actual boundary onto the characteristic -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
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
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance characteristicNativePowerBoundaryIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicNativePowerBoundaryAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (R : Type u) [Field R]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]
    [Algebra K R]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]
    [Algebra E R]

/-- The retained canonical root numerator is unchanged by the same
compatible closed Gauss coefficient extension. -/
theorem canonical_root_numerator_map_of_compatible_closed_cover
    (hcompat :
      letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
      IsScalarTower C₀ E R) :
    letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
    (fun i => algebraMap E R ((cN) i)) = closedGaussCanonicalRootNumerator H I p hY h hh e R := by
  letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
  letI : IsScalarTower C₀ E R := hcompat
  funext i
  unfold closedGaussCanonicalRootNumerator
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply C₀ E R]
  congr 1
  refine Fin.lastCases ?_ (fun j => ?_) (p.symm i)
  · simp only [Fin.snoc_last, map_zero]
  · simp only [Fin.snoc_castSucc]
    exact (IsScalarTower.algebraMap_apply C₀ E R _).symm

include hrank

/-- In the actual proportional-power root case, the original full
fiber boundary annihilates its original canonical numerator. Both its
ruling equations and power-covector equation are derived internally. -/
theorem actual_proportional_power_boundary_annihilates_same_canonical_numerator
    (hN : IsNilpotent (jac H))
    (hcompat :
      letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
      IsScalarTower C₀ E R)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (S M : Fin 4 → E) (r : (N₀).functionField)
    (hpower : r ^ d = aeval (w) ((O) S))
    (hmNative : aeval (w) ((O) M) ≠ 0)
    (hformula : r = aeval (w) ((O) (cN)) * aeval (w) (L₀) / aeval (w) ((O) M))
    (hMN : LinearIndependent E ![rulingFormRestriction (LinearMap.ker (A₀).toLin') M,
      rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN)])
    (β : E) (hβ : β ≠ 0)
    (hSN : rulingFormRestriction (LinearMap.ker (A₀).toLin') S =
      β • rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN))
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈
      projectiveClosureSet («L» := L) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    (fun i => algebraMap E R ((cN) i)) ⬝ᵥ (fun i => z (some i)) = 0 := by
  have hpair := independent_ruling_forms_of_nonzero_proportional_second
    (LinearMap.ker (A₀).toLin') M (cN) S hMN β hβ hSN
  have hS := actual_algebraic_boundary_annihilates_specified_native_power_covector
    H hrank I p hY h hh E hd hH hind hGauss e R hN hcompat c q k hc hc0 hq hk
      S M r hpower hmNative hformula hpair z hz hpoint hz0 j hj
  have hruling := actual_full_boundary_mem_same_chosen_extended_ruling
    H hrank I p hY h hh E (Nat.lt_trans Nat.zero_lt_one hd) hH hind hGauss R
      hcompat c q hc hq z hz hpoint hz0
  exact proportional_ruling_covector_zero_after_field_extension (A₀) S (cN) β hβ hSN
    (fun i => z (some i)) hruling hS

/-- The same specified original boundary direction in the actual
proportional-power case belongs to the chosen characteristic line.
No numerator vanishing or characteristic membership is assumed. -/
theorem actual_proportional_power_boundary_mem_same_chosen_characteristic
    (hN : IsNilpotent (jac H))
    (hcompat :
      letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
      IsScalarTower C₀ E R)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (S M : Fin 4 → E) (r : (N₀).functionField)
    (hpower : r ^ d = aeval (w) ((O) S))
    (hmNative : aeval (w) ((O) M) ≠ 0)
    (hformula : r = aeval (w) ((O) (cN)) * aeval (w) (L₀) / aeval (w) ((O) M))
    (hMN : LinearIndependent E ![rulingFormRestriction (LinearMap.ker (A₀).toLin') M,
      rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN)])
    (β : E) (hβ : β ≠ 0)
    (hSN : rulingFormRestriction (LinearMap.ker (A₀).toLin') S =
      β • rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN))
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈
      projectiveClosureSet («L» := L) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
    (fun i => z (some i)) ∈ extendedClosedGaussChosenCharacteristicSubspace H I R hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss := by
  letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
  letI : IsScalarTower C₀ E R := hcompat
  have hzero := actual_proportional_power_boundary_annihilates_same_canonical_numerator
    H hrank I p hY h hh E hd hH hind hGauss e R hN hcompat c q k hc hc0 hq hk
      S M r hpower hmNative hformula hMN β hβ hSN z hz hpoint hz0 j hj
  have hruling := actual_full_boundary_mem_same_chosen_extended_ruling
    H hrank I p hY h hh E (Nat.lt_trans Nat.zero_lt_one hd) hH hind hGauss R
      hcompat c q hc hq z hz hpoint hz0
  have hmatrix : (A₀).map (algebraMap E R) = extendedClosedGaussChosenRulingMatrix H I R hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss := by
    ext u i
    exact (IsScalarTower.algebraMap_apply C₀ E R _).symm
  rw [hmatrix] at hruling
  have hnum := canonical_root_numerator_map_of_compatible_closed_cover H I p hY h hh E e R hcompat
  rw [hnum] at hzero
  exact (actual_canonical_gauss_root_numerator_zero_iff_characteristic H I p hY h hh e R hH
    (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss (fun i => z (some i)) hruling).mp hzero

end DimensionFourDependence
