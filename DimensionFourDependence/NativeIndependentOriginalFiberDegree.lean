import DimensionFourDependence.NativeGraphRootIdentityTransfer
import DimensionFourDependence.IndependentRulingGraphRootDegree
import DimensionFourDependence.OriginalFiberClosedCoefficientBoundary
import DimensionFourDependence.OriginalFiberRadialDegree
import DimensionFourDependence.DevelopableFirstInvariant

/-! # Independent native root identities bound the original full and radial fibers -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower MvPolynomial.gradedAlgebra

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

local instance nativeIndependentOriginalDegreeIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeIndependentOriginalDegreeAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Independent native root forms bound the original full generic
fiber by two without a fixed source vertex. A common algebraic closure
constructs both the compatible root coefficients and an actual original
boundary, so no boundary or coefficient realization is supplied. -/
theorem native_independent_root_identities_bound_original_full_fiber_degree
    (hrank : polyRank (jac H) = 3) (hN : IsNilpotent (jac H)) (hd1 : 1 < d)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (M S : Fin 4 → E) (r : (N₀).functionField)
    (hpower : r ^ d = aeval (w) ((O) S))
    (hmNative : aeval (w) ((O) M) ≠ 0)
    (hformula : r = aeval (w) ((O) (cN)) * aeval (w) (L₀) / aeval (w) ((O) M))
    (hpair : LinearIndependent E ![rulingFormRestriction (LinearMap.ker (A₀).toLin') M,
      rulingFormRestriction (LinearMap.ker (A₀).toLin') S]) :
    ∀ D : ℕ, HasCurveHilbertDegree (projectiveConeIdeal («L» := L)
      (rationalCoordinate (K := K) (n := 4))) D → D ≤ 2 := by
  have hc0 : c ≠ 0 := by
    intro hz
    apply I.developable_first_invariant_ne_zero H hd hH hind (by rw [hGauss]) p hY h hh
    rw [← hc, hz]
    rfl
  let κ := AlgebraicClosure (L)
  let aKκ : Algebra K κ := inferInstance
  let tKLκ : IsScalarTower K (L) κ := inferInstance
  let aCκ : Algebra C₀ κ := ((algebraMap (L) κ).comp (a).toRingHom).toAlgebra
  let σ : E →ₐ[C₀] κ := IsAlgClosed.lift
  let aEκ : Algebra E κ := σ.toRingHom.toAlgebra
  have hcompat :
      letI : Algebra C₀ κ := ((algebraMap (L) κ).comp (a).toRingHom).toAlgebra
      IsScalarTower C₀ E κ :=
    IsScalarTower.of_algebraMap_eq (fun b => (σ.commutes b).symm)
  obtain ⟨rho, hrho, hprod, hroot⟩ := native_root_identities_construct_same_boundary_graph_root
    H I p hY h hh E hd hH hind hGauss e κ hcompat c hc hc0 M S r hpower hmNative hformula
  obtain ⟨z, hz, hpoint, hz0, hv0, j, hj⟩ :=
    actual_full_fiber_normalized_boundary_in_closed_coefficients H hN hrank p hY h c hc κ
  exact original_independent_ruling_graph_root_bounds_actual_full_fiber_degree
    H I p hY h hh E hH hd hind hGauss e κ hrank hN hd1 hcompat M S hpair
    c q k hc hq hk rho hrho hprod hroot z hz hpoint hz0 hv0 j hj

/-- The same independent native root forms bound the original
radial projective-source curve, retaining the original coordinate labels. -/
theorem native_independent_root_identities_bound_original_radial_fiber_degree
    (hrank : polyRank (jac H) = 3) (hN : IsNilpotent (jac H)) (hd1 : 1 < d)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (M S : Fin 4 → E) (r : (N₀).functionField)
    (hpower : r ^ d = aeval (w) ((O) S))
    (hmNative : aeval (w) ((O) M) ≠ 0)
    (hformula : r = aeval (w) ((O) (cN)) * aeval (w) (L₀) / aeval (w) ((O) M))
    (hpair : LinearIndependent E ![rulingFormRestriction (LinearMap.ker (A₀).toLin') M,
      rulingFormRestriction (LinearMap.ker (A₀).toLin') S]) :
    ∀ D : ℕ, HasCurveHilbertDegree (projectiveFieldPointIdeal (E := L)
      (rationalCoordinate (K := K) (n := 4))).toIdeal D → D ≤ 2 := by
  have hc0 : c ≠ 0 := by
    intro hz
    apply I.developable_first_invariant_ne_zero H hd hH hind (by rw [hGauss]) p hY h hh
    rw [← hc, hz]
    rfl
  intro D hD
  apply native_independent_root_identities_bound_original_full_fiber_degree
    H I p hY h hh E hd hH hind hGauss e hrank hN hd1 c q k hc hq hk
    M S r hpower hmNative hformula hpair D
  exact (actual_first_invariant_radial_curve_degree p (Y) hY h c hc hc0 D).mpr hD

end DimensionFourDependence
