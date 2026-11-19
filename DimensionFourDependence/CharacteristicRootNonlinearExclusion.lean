import DimensionFourDependence.OriginalProportionalCharacteristicExclusion
import DimensionFourDependence.ChosenNonlinearCharacteristic
import DimensionFourDependence.NativeCharacteristicRootDegreeObstruction

/-! # The actual characteristic-root alternative excludes nonlinear original fibers -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss).toLin'
local notation "R" => rulingFormRestriction (W₀)

local instance characteristicRootNonlinearExclusionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootNonlinearExclusionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original characteristic-root data construct their own exact
source-chart invariants, generic pencil degree bound, fixed root divisor
and same-branch characteristic containment. A nonlinear geometric fiber
supplies the nonplanar characteristic of that exact chosen ruling, and
the resulting degree contradiction excludes this entire root case. -/
theorem actual_characteristic_root_data_exclude_nonlinear_geometric_component
    [Module.Finite (closedGaussParameterField H I) E]
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hdata : ActualCharacteristicGaussRootData H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss)
    (F : Type u) [Field F] [Algebra (polynomialOutputField H) F] [Algebra K F]
    [IsScalarTower K (polynomialOutputField H) F] [IsAlgClosed F]
    [Algebra.IsAlgebraic (polynomialOutputField H) F]
    (P : Ideal (MvPolynomial (Fin 4) F)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal F (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := F) (primeQuotientCoordinate P)) : False := by
  obtain ⟨p', hY', h', hh', _hfull, hradial⟩ :=
    actual_characteristic_root_data_constructs_original_fiber_degree_bounds
      H I E hH e hd hind hGauss hN hrank hdata
  obtain ⟨D, _hD6, hD⟩ := original_developable_radial_curve_degree_exists_in_every_output_chart
    H I hH (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss hN hrank p' hY' h' hh'
  have hD2 := hradial D hD
  obtain ⟨S, M, cN, r, _hS, _hM, _hNcoeff, hr, hroot, hm, hformula, hMN, hSN, hfactor, hnumerator⟩ := hdata
  obtain ⟨β, hβ, hSN⟩ := hSN
  have ht := actual_characteristic_pencil_value_transcendental
    H I E hH e hd hind hGauss S cN r hr hroot hfactor
  have hT := actual_characteristic_pencil_tangent_value_ne_zero
    H I E hH e hd hind hGauss S cN r hr hroot hfactor
  obtain ⟨D', hle, hD'⟩ := actual_characteristic_pencil_curve_degree_exists_le_original
    H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss hrank p' hY' cN r hfactor hT ht hD
  obtain ⟨bR, hbR0, hbRC, _hpair, _hspan, hplane, _hlower⟩ :=
    chosen_nonlinear_geometric_component_constructs_characteristic
      H hd hH hN hrank hind I hGauss F P hP hline
  obtain ⟨p, hY, h, hh, hcN⟩ := hnumerator
  subst cN
  obtain ⟨c, q, k, hc, hq, hk⟩ := specified_original_chart_exists_exact_invariant_coefficients
    H hrank p hY hN h hh
  have hc0 : c ≠ 0 := by
    intro hcz
    have he : (c : S₀) = 0 := congrArg Subtype.val hcz
    exact (ImageRelationWitness.developable_first_invariant_ne_zero H
      (Nat.lt_trans Nat.zero_lt_one hd) hH hind I hGauss.le p hY h hh) (hc.symm.trans he)
  have hformula' : r = aeval (w) ((O) (closedGaussCanonicalRootNumerator H I p hY h hh e E)) *
      aeval (w) (linearFormPolynomial (extendedClosedGaussChosenRulingMatrix H I E hH
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0)) / aeval (w) ((O) M) := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hformula
  have hcompare := actual_original_proportional_power_constructs_characteristic_boundary_comparison
    H hrank I p hY h hh E hH e hd hind hGauss hN c q k hc hc0 hq hk
      S M r hroot hm hformula' hMN β hβ hSN
  exact actual_characteristic_degree_two_pencil_excluded_by_boundary_comparison
    H I E hH e hd hind hGauss S _ r hr hroot hfactor hcompare bR hbR0 hbRC hplane
      ⟨D', hle.trans hD2, hD'⟩

end DimensionFourDependence
