import DimensionFourDependence.ActualClosedGaussSimpleBoundaryChart
import DimensionFourDependence.ActualSpecifiedSimpleRootBoundary
import DimensionFourDependence.ActualSimpleRootInfinitySupport
import DimensionFourDependence.OriginalFiberInfinityChartDegree

/-! # The actual original degree bound from the same finite independent graph root -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "x₃" => fun i : Fin 3 => (x) (p i.castSucc)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)
local notation "Λ₀" => parametricGraphCubicCovector (f₀) (A₀) (y₀)

variable (F : Type u) [Field F]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra K F]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]

local notation "g" => IsScalarTower.toAlgHom K (L) F
local notation "f" => (g).comp (f₀)
local notation "y" => fun i => (g) ((y₀) i)
local notation "delta" => extendedCoefficientPartial (Y) hY F

/-- The same finite independent graph root equations imply the actual
original full-fiber degree bound. Boundary vanishing and the single
infinity support point are derived from the original map. -/
theorem finite_independent_graph_root_data_bound_actual_full_fiber_degree
    (hrank : polyRank (jac H) = 3)
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (C : IntermediateField (f).fieldRange F) [Module.Finite (f).fieldRange C]
    (m s b a : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling (f) C (A₀)) m,
      rulingFormRestriction (finiteParameterGraphRuling (f) C (A₀)) s])
    (hb : b ∈ finiteParameterGraphRuling (f) C (A₀)) (ha : a ∈ finiteParameterGraphRuling (f) C (A₀))
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0) (hma : m ⬝ᵥ a = 0) (hsa : s ⬝ᵥ a = 1)
    (rho : F) (hrho : rho ≠ 0)
    (hprod : (g) (n₀) * (g) c = ((fun i => (m i : F)) ⬝ᵥ (y)) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ (y))
    (z : Option (Fin 4) → F) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) (hv0 : (fun i : Fin 3 => z (some (p i.castSucc))) ≠ 0)
    (j : Fin 4) (hj : z (some j) = 1) :
    ∀ eCurve : ℕ, HasCurveHilbertDegree (projectiveConeIdeal («L» := L) (x)) eCurve → eCurve ≤ 2 := by
  have hmbF : (fun i => (m i : F)) ⬝ᵥ (fun i => (b i : F)) = 1 := by
    simpa only [dotProduct, map_sum, map_mul, map_one, IntermediateField.algebraMap_apply] using
      congrArg (algebraMap C F) hmb
  have hsbF : (fun i => (s i : F)) ⬝ᵥ (fun i => (b i : F)) = 0 := by
    simpa only [dotProduct, map_sum, map_mul, map_zero, IntermediateField.algebraMap_apply] using
      congrArg (algebraMap C F) hsb
  have hsv := actual_normalized_boundary_annihilates_specified_simple_root_form
    H hrank I p hY h hh e F hd hH hN hind hGauss c q k hc hq hk
      (fun i => (m i : F)) (fun i => (s i : F)) (fun i => (b i : F))
      (fun i => finite_parameter_extension_coefficient_algebraic (f) C (m i))
      (fun i => finite_parameter_extension_coefficient_algebraic (f) C (s i))
      (finiteParameterGraphRuling_original_pairing (f) C (A₀) b hb) hmbF hsbF
      rho hrho hprod hroot z hz hpoint hz0 j hj
  obtain ⟨w', a', b', _hdetC, hdetF, _hb', _hpoint', hlocal⟩ :=
    actual_closed_gauss_independent_root_boundary_chart_local_bound H I p hY h hh e F
      hd hH hGauss c q k hq hk z hz hpoint hz0 hv0 C m s hpair rho hrho hprod hroot hsv
  obtain ⟨_hbF, hsupport⟩ := actual_extended_full_fiber_simple_root_infinity_support_single_point
    H hrank I p hY h hh e F hd hH hN hind hGauss c q k hc hq hk
      C m s b a hpair hb ha hmb hsb hma hsa rho hrho hprod hroot
  intro eCurve heCurve
  exact actual_full_fiber_degree_le_two_of_single_support_chart p (Y) hY h c hc F heCurve
    _ hsupport (fun i => (b' i : F)) (fun i => (w' i : F)) (fun i => (a' i : F)) hdetF hlocal

end DimensionFourDependence
