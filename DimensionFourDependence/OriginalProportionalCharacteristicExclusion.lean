import DimensionFourDependence.NativeCharacteristicIntersectionIdeal
import DimensionFourDependence.NativeCharacteristicRootContainment

/-! # The original proportional-power root is excluded by the characteristic image degree -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [kField : Field K] [kCharZero : CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [eField : Field E] [aCE : Algebra (closedGaussParameterField H I) E]
    [hAE : Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "D₀" => polynomialOutputField H
local notation "L" => coefficientField (K := K)
  (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField

local instance originalProportionalCharacteristicExclusionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance originalProportionalCharacteristicExclusionExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

noncomputable local instance originalProportionalCharacteristicExclusionExtendedSMul : SMul E (N).functionField :=
  (extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e).toSMul

variable (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "U" b:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' b)
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0
local notation "Lₜ" => ∑ j, algebraMap E (N).functionField ((ν₀) j) * (w) j
local notation "L₀" => linearFormPolynomial (ν₀)
local notation "vᵣ" => fun i => RatFunc.X * RatFunc.C ((w) i / (Lₜ))
local notation "Jᵣ" => algebraicClosure Cᵣ Gᵣ
local notation "Φ₀" hT:max => nativeCharacteristicScaleSourceHom H I E hH e
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss hT
local notation "Z₀" z:max b:max hb:max => fun j : Option (Fin 4) =>
  j.elim ((N).presheaf.germ (U b) z hb
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e (ν₀)) b))
        (nativeProjectiveCoordinateGerm H I E hH e z b hb)
local notation "ξ₀" z:max b:max hb:max => fun j => RatFunc.C (RatFunc.C
  (IsLocalRing.residue ((N).presheaf.stalk z) ((Z₀ z b hb) j)))

local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss
local notation "cN" => closedGaussCanonicalRootNumerator H I p hY h hh e E
local notation "x₀" z:max b:max hb:max => fun i => IsLocalRing.residue ((N).presheaf.stalk z)
  (nativeProjectiveCoordinateGerm H I E hH e z b hb i)

include hrank

/-- The original invariant equations and specified native proportional
power identities construct the exact boundary comparison required by
the root-divisor containment argument. No boundary point, characteristic
membership or equation inclusion is supplied. -/
theorem actual_original_proportional_power_constructs_characteristic_boundary_comparison
    (hN : IsNilpotent (jac H))
    (c q k : L)
    (hc : (c : S₀) = firstFiberInvariantInChart p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h) (hc0 : c ≠ 0)
    (hq : (q : S₀) = secondFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h c q)
    (S M : Fin 4 → E) (r : (N).functionField)
    (hpower : r ^ d = aeval (w) ((O) S))
    (hmNative : aeval (w) ((O) M) ≠ 0)
    (hformula : r = aeval (w) ((O) (cN)) * aeval (w) (L₀) / aeval (w) ((O) M))
    (hMN : LinearIndependent E ![rulingFormRestriction (LinearMap.ker (A₀).toLin') M,
      rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN)])
    (β : E) (hβ : β ≠ 0)
    (hSN : rulingFormRestriction (LinearMap.ker (A₀).toLin') S =
      β • rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN))
    : NativeCharacteristicBoundaryPointIdealComparison H I E hH e hd hind hGauss r := by
  intro z b hb hboundary W hW0 hW
  exact actual_characteristic_root_intersection_has_same_characteristic_point_ideal
    H hrank I p hY h hh E hH e hd hind hGauss hN c q k hc hc0 hq hk
      S M r hpower hmNative hformula hMN β hβ hSN z b hb hboundary W hW0 hW

end DimensionFourDependence
