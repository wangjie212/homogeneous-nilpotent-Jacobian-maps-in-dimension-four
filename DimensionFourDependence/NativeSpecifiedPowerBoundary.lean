import DimensionFourDependence.NativeSpecifiedRootGraphTransfer
import DimensionFourDependence.CanonicalScaledPlaneBoundaryContradiction

/-! # Every actual algebraic boundary annihilates the same original native power covector -/

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

local instance nativeSpecifiedPowerBoundaryIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeSpecifiedPowerBoundaryAlgebra : Algebra E (N₀).functionField :=
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

/-- The original generic-fiber boundary annihilates the very same
power covector as the specified native root formula. The original graph
root, its nonzero scalar, all dual values and coefficient algebraicity
are constructed; neither fixed-axis values nor a boundary equation
are supplied as assumptions. -/
theorem actual_algebraic_boundary_annihilates_specified_native_power_covector
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
    (hpair : LinearIndependent E ![rulingFormRestriction (LinearMap.ker (A₀).toLin') M,
      rulingFormRestriction (LinearMap.ker (A₀).toLin') S])
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈
      projectiveClosureSet («L» := L) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    (fun i => algebraMap E R (S i)) ⬝ᵥ (fun i => z (some i)) = 0 := by
  letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
  letI : IsScalarTower C₀ E R := hcompat
  let gK : (L) →ₐ[K] R := IsScalarTower.toAlgHom K (L) R
  let gC : C₀ →ₐ[K] R := gK.comp (a)
  let σ : E →+* R := algebraMap E R
  have hσC (t : C₀) : σ (algebraMap C₀ E t) = gC t :=
    (IsScalarTower.algebraMap_apply C₀ E R t).symm
  have hparam : gC.comp e.toAlgHom = gK.comp
      (closedGaussCoefficientParameterHom H I p hY h hh e) :=
    original_graph_parameter_map_composition_retained H I p hY h hh e gK
  have hgraph (q : Fin 4 → E) :
      graphRestrictedCovector p (fun i => (gK.comp
        (closedGaussCoefficientParameterHom H I p hY h hh e)) ((A) i)) (σ ∘ q) =
        σ ∘ graphRestrictedCovector p (Aₑ) q := by
    rw [← graphRestrictedCovector_field_map]
    congr 1
    funext i
    exact (DFunLike.congr_fun hparam ((A) i)).symm.trans (hσC (e ((A) i))).symm
  obtain ⟨rho, hrho, hprod, hroot⟩ := native_specified_root_formula_constructs_same_original_graph_root
    H I p hY h hh E (Nat.lt_trans Nat.zero_lt_one hd) hH hind hGauss e R hcompat
      c hc hc0 S M r hpower hmNative hformula
  obtain ⟨hm, hs, b, _v, _hb, _hv, hbgraph, _hvgraph, hmb, hsb, _hmv, _hsv, _hLI⟩ :=
    actual_chosen_graph_dual_pair_retained_by_specified_coefficients
      H I p hY h hh e E hH (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss gC σ hσC M S hpair
  rw [hparam] at hm hs hbgraph
  exact actual_full_boundary_annihilates_original_specified_root_covector
    H hrank I p hY h hh e R hd hH hN hind hGauss c q k hc hq hk
      (σ ∘ graphRestrictedCovector p (Aₑ) M) (σ ∘ S) (fun i => σ (b (p i.castSucc)))
      hm (by rw [hgraph]; exact hs) hbgraph hmb (by rw [hgraph]; exact hsb)
      rho hrho hprod (by rw [hgraph]; exact hroot) z hz hpoint hz0 j hj

end DimensionFourDependence
