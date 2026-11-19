import DimensionFourDependence.ActualGaussIndependentConeRootData
import DimensionFourDependence.ActualFiniteNativeRootConstruction

/-! # Fixed coefficient maps construct independent native root data from boundary equations -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hN : IsNilpotent (jac H)) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh

variable (κ : Type u) [Field κ] [Algebra (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K)
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ]
    [Algebra.IsAlgebraic (coefficientField (K := K)
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ] [Algebra E κ]

include hrank hN hvertex

/-- The actual boundary equations construct independent ruling root
forms for fixed original coefficient maps. This isolates the proof
from later choices of valuation residue fields and finite subfields. -/
theorem specified_boundary_root_forms_construct_independent_fixed_vertex_data
    (hcompat :
      letI : Algebra C₀ κ :=
        ((algebraMap (L) κ).comp (actualClosedGaussCoefficientHom H I p hY h hh).toRingHom).toAlgebra
      IsScalarTower C₀ E κ)
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (n m s : Fin 3 → E) (rho : κ) (hn : n ≠ 0) (hm : m ≠ 0) (hs : s ≠ 0)
    (hnvalue : (∑ j, algebraMap E κ (n j) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) j)) ≠ 0)
    (hprod : (∑ j, algebraMap E κ (n j) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) j)) *
        algebraMap (L) κ c =
      (∑ j, algebraMap E κ (m j) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) j)) * rho)
    (hroot : rho ^ d = ∑ j, algebraMap E κ (s j) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) j))
    (hnumerator : ∀ j, n j = algebraMap C₀ E (closedGaussRootNumeratorCoefficient H I p hY h hh e j)) :
    ActualChosenIndependentGaussRootData H I E hH e (lt_trans Nat.zero_lt_one hd) hind hGauss := by
  have hd0 : 0 < d := lt_trans Nat.zero_lt_one hd
  obtain ⟨hmnative, hrootnative⟩ := actual_boundary_equation_4_4_constructs_native_rational_root
    H I p hY h hh E hH e κ hcompat c hc hc0 n m s rho hnvalue hprod hroot
  have hrnative := actual_boundary_rational_root_native_formula_ne_zero
    H I p hY h hh E hH e κ hcompat c hc hc0 n m hnvalue hmnative
  have hchosen : ActualChosenGaussRationalRootData H I E hH e hd0 hind hGauss :=
    selected_root_forms_construct_chosen_ruling_root_data H I E hH e hd0 hind hGauss p hY h hh
      n m s hn hm hs hmnative hrnative hrootnative hnumerator
  have halt := actual_chosen_root_data_construct_two_alternatives H I E hH e hd0 hind hGauss hchosen
  have hnormal := actual_chosen_root_alternatives_construct_native_normal_forms H I E hH e hd0 hind hGauss halt
  exact actual_chosen_root_normal_forms_construct_independent_fixed_vertex_root_data
    H hrank hN I E hd hH hind hGauss hvertex e hnormal

end DimensionFourDependence
