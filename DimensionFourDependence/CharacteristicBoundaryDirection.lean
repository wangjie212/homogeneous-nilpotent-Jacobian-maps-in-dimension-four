import DimensionFourDependence.CharacteristicNativePowerBoundary
import DimensionFourDependence.GenericDirectionTangent

/-! # The original proportional-power boundary has the same characteristic projective direction -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower MvPolynomial.gradedAlgebra

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

local instance characteristicBoundaryDirectionIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicBoundaryDirectionAlgebra : Algebra E (N₀).functionField :=
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

include hrank

/-- The same original characteristic vector spans the entire actual
algebraic boundary direction in the proportional-power case. Its
nonzero proportionality scalar is constructed from the normalized
original source-coordinate frame. -/
theorem actual_proportional_power_boundary_direction_multiple_of_same_characteristic
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
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1)
    (W : Fin 4 → E) (hW0 : W ≠ 0)
    (hW : W ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    ∃ s : R, s ≠ 0 ∧ (fun i => z (some i)) = s • (fun i => algebraMap E R (W i)) := by
  letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
  letI : IsScalarTower C₀ E R := hcompat
  have hchar := actual_proportional_power_boundary_mem_same_chosen_characteristic
    H hrank I p hY h hh E hd hH hind hGauss e R hN hcompat c q k hc hc0 hq hk
      S M r hpower hmNative hformula hMN β hβ hSN z hz hpoint hz0 j hj
  have hmatrix : (extendedClosedGaussChosenCharacteristicMatrix H I E hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss).map (algebraMap E R) =
      extendedClosedGaussChosenCharacteristicMatrix H I R hH
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss := by
    ext u i
    exact (IsScalarTower.algebraMap_apply C₀ E R _).symm
  have hWmap : (fun i => algebraMap E R (W i)) ∈
      extendedClosedGaussChosenCharacteristicSubspace H I R hH
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss := by
    change extendedClosedGaussChosenCharacteristicMatrix H I R hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss *ᵥ (fun i => algebraMap E R (W i)) = 0
    rw [← hmatrix]
    change extendedClosedGaussChosenCharacteristicMatrix H I E hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss *ᵥ W = 0 at hW
    funext u
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, map_zero,
      Pi.zero_apply] using congrArg (algebraMap E R) (congrFun hW u)
  have hWmap0 : (fun i => algebraMap E R (W i)) ≠ 0 := by
    intro he
    apply hW0
    funext i
    apply (algebraMap E R).injective
    simpa only [Pi.zero_apply, map_zero] using congrFun he i
  have hspan := extendedClosedGaussChosenCharacteristic_span_of_nonzero H I R hH
    (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss _ hWmap0 hWmap
  rw [← hspan] at hchar
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hchar
  have hs0 : s ≠ 0 := by
    intro he
    have hval := congrFun hs j
    simpa only [he, zero_smul, Pi.zero_apply, hj, zero_ne_one] using hval
  exact ⟨s, hs0, hs.symm⟩

/-- The complete original projective ideal of the actual algebraic
boundary direction equals that of the same original characteristic
vector. This retains every equation needed for fixed-curve containment. -/
theorem actual_proportional_power_boundary_has_same_original_characteristic_ideal
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
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1)
    (W : Fin 4 → E) (hW0 : W ≠ 0)
    (hW : W ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    (projectiveFieldPointIdeal (E := E) (fun i => z (some i))).toIdeal =
      (projectiveFieldPointIdeal (E := E) W).toIdeal := by
  obtain ⟨s, hs, hrep⟩ := actual_proportional_power_boundary_direction_multiple_of_same_characteristic
    H hrank I p hY h hh E hd hH hind hGauss e R hN hcompat c q k hc hc0 hq hk
      S M r hpower hmNative hformula hMN β hβ hSN z hz hpoint hz0 j hj W hW0 hW
  have hscale := projectiveFieldPointIdeal_scale (K := E) (fun i => algebraMap E R (W i)) s hs
  have htransport := projectiveFieldPointIdeal_algHom W (Algebra.ofId E R)
  rw [hrep]
  have hscale' : (projectiveFieldPointIdeal (E := E) (s • (fun i => algebraMap E R (W i)))).toIdeal =
      (projectiveFieldPointIdeal (E := E) (fun i => algebraMap E R (W i))).toIdeal := by
    have he : (s • (fun i => algebraMap E R (W i))) =
        (fun i => s * algebraMap E R (W i)) := rfl
    exact (congrArg (fun v => (projectiveFieldPointIdeal (E := E) v).toIdeal) he).trans hscale
  exact hscale'.trans htransport

end DimensionFourDependence
