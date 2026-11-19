import DimensionFourDependence.FixedVertexGraphRootActualDegree
import DimensionFourDependence.FixedVertexFiniteGraphBasis
import DimensionFourDependence.FiniteGraphRootActualDegree
import DimensionFourDependence.FixedVertexFiniteGraphBasisData
import DimensionFourDependence.FixedVertexIndependentGraphBasis
import DimensionFourDependence.OriginalGraphTensorValues
import DimensionFourDependence.SpecifiedGraphDualTransport
import DimensionFourDependence.FiniteAlgebraicGraphDualPair
import DimensionFourDependence.FixedVertexGraphBasisWitness

/-! # The original fixed-axis graph basis constructs its finite parameter field -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [fieldK : Field K] [charK : CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [fieldE : Field E] [algCE : Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a₀" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap C₀ E (e ((A) i))
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "W₀" => LinearMap.ker ((extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin' : (Fin 4 → E) →ₗ[E] (Fin 2 → E))

variable (κ : Type u) [Field κ] [Algebra K κ] [Algebra (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ]
    [IsScalarTower K (coefficientField (K := K)
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ] [Algebra E κ]

local notation "g" => IsScalarTower.toAlgHom K (L) κ
local notation "f" => (g).comp (f₀)

variable [Algebra.IsAlgebraic (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ]

local notation "yκ" => fun i => (g) (coefficientCoordinate (K := K) (Y) i)
local notation "n₀" => parametricRulingDenominator (f₀) (A) (coefficientCoordinate (K := K) (Y))

/-- Exact original root forms over specified coefficient and target
fields, before introducing a finite intermediate-field presentation. -/
noncomputable def IndependentOriginalGraphRootForms (c : L) : Prop :=
  ∃ (M S : Fin 4 → E) (rho : κ), M (Fin.last 3) ≠ 0 ∧ S (Fin.last 3) = 0 ∧ rho ≠ 0 ∧
    (g) (n₀) * (g) c =
      ((fun i => algebraMap E κ (graphRestrictedCovector p (Aₑ) M i)) ⬝ᵥ (yκ)) * rho ∧
    rho ^ d = (fun i => algebraMap E κ (graphRestrictedCovector p (Aₑ) S i)) ⬝ᵥ (yκ) ∧
    IndependentOriginalChosenRulingForms H I E hH hd hind hGauss M S

/-- Eliminate the root forms while both their fields are abstract;
all actual local geometry is supplied by the checked root-degree theorem. -/
theorem independent_original_graph_root_forms_bound_actual_full_fiber_degree
    (hrank : polyRank (jac H) = 3) (hN : IsNilpotent (jac H)) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hcompat :
      letI : Algebra C₀ κ := ((algebraMap (L) κ).comp (a₀).toRingHom).toAlgebra
      IsScalarTower C₀ E κ)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (hforms : IndependentOriginalGraphRootForms H I p hY h hh E hH hd hind hGauss e κ c)
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L)
      (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (hv0 : (fun i : Fin 3 => z (some (p i.castSucc))) ≠ 0)
    (j : Fin 4) (hj : z (some j) = 1) :
    ∀ eCurve : ℕ, HasCurveHilbertDegree (projectiveConeIdeal («L» := L)
      (rationalCoordinate (K := K) (n := 4))) eCurve → eCurve ≤ 2 := by
  obtain ⟨M, S, rho, hM, hS, hrho, hprod, hroot, hpair⟩ := hforms
  let hbound := original_fixed_vertex_independent_graph_root_bounds_actual_full_fiber_degree
    H I p hY h hh E hH hd hind hGauss e κ hrank hN hd1 hvertex hcompat
      M S hM hS hpair c q k hc hq hk rho hrho hprod hroot z hz hpoint hz0 hv0 j hj
  exact hbound

end DimensionFourDependence
