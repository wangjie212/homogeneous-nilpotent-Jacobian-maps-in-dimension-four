import DimensionFourDependence.BoundaryIndependentConeRootData

/-! # Boundary construction retains the exact original graph numerator -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
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
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh
local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "hd₀" => (lt_trans Nat.zero_lt_one hd)
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH (hd₀) hind hGauss 0)
local notation "cN" => closedGaussCanonicalRootNumerator H I p hY h hh e E

local instance boundaryCanonicalIndependentRootIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance boundaryCanonicalIndependentRootAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (κ : Type u) [Field κ] [Algebra (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ] [Algebra E κ]

include hrank hN hvertex

/-- The original boundary root and same finite cone construction
give independent root data indexed by the exact canonical numerator
of the specified original graph chart. -/
theorem specified_boundary_constructs_independent_root_data_for_original_canonical_numerator
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
    ActualChosenIndependentGaussRootDataForNumerator H I E hH e (hd₀) hind hGauss (cN) := by
  obtain ⟨hmnative, hrootnative⟩ := actual_boundary_equation_4_4_constructs_native_rational_root
    H I p hY h hh E hH e κ hcompat c hc hc0 n m s rho hnvalue hprod hroot
  have hrnative := actual_boundary_rational_root_native_formula_ne_zero
    H I p hY h hh E hH e κ hcompat c hc hc0 n m hnvalue hmnative
  have hchosen : ActualChosenGaussRationalRootData H I E hH e (hd₀) hind hGauss :=
    selected_root_forms_construct_chosen_ruling_root_data H I E hH e (hd₀) hind hGauss p hY h hh
      n m s hn hm hs hmnative hrnative hrootnative hnumerator
  have halt := actual_chosen_root_data_construct_two_alternatives H I E hH e (hd₀) hind hGauss hchosen
  have hnormal := actual_chosen_root_alternatives_construct_native_normal_forms H I E hH e (hd₀) hind hGauss halt
  obtain ⟨rA, hrA, hcone⟩ := actual_chosen_gauss_root_normal_forms_construct_full_affine_cone
    H hrank hN I E hd hH hind hGauss hvertex e hnormal
  have hcanon : (algebraMap C₀ E (actualClosedGaussNormalCovector H I e (p 3)))⁻¹ •
      selectedOutputCovector p n = (cN) := by
    rw [funext hnumerator]
    rfl
  have he := selected_root_formula_eq_chosen_plane_formula H I E hH e (hd₀) hind hGauss p hY h hh n m
  rw [hcanon] at he
  have hplane : (∑ i, algebraMap E (N₀).functionField
      (extendedClosedGaussChosenRulingMatrix H I E hH (hd₀) hind hGauss 0 i) * (w) i) = aeval (w) (L₀) := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  rw [hplane] at he
  have hnonzero : aeval (w) ((O) (cN)) * aeval (w) (L₀) /
      aeval (w) ((O) (selectedOutputCovector p m)) ≠ 0 := by rw [← he]; exact hrnative
  have hnN : aeval (w) ((O) (cN)) ≠ 0 := by
    intro hz
    exact hnonzero (by rw [hz, zero_mul, zero_div])
  have hLn : aeval (w) (L₀) ≠ 0 := by
    intro hz
    exact hnonzero (by rw [hz, mul_zero, zero_div])
  exact actual_affine_full_cone_constructs_independent_native_root_data_retaining_numerator
    H I E hH e (hd₀) hind hGauss hvertex (cN) ⟨p, hY, h, hh, rfl⟩ hnN hLn rA hrA hcone

end DimensionFourDependence
