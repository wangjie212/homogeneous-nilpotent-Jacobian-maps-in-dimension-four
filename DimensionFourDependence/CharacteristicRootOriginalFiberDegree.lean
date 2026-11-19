import DimensionFourDependence.NativeIndependentOriginalFiberDegree
import DimensionFourDependence.IndependentNormalCharacteristicRoot
import DimensionFourDependence.SpecifiedGraphCoefficientExtension

/-! # The actual characteristic root constructs degree-two original generic fibers -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
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

local instance characteristicRootOriginalFiberDegreeIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootOriginalFiberDegreeAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The retained actual numerator selects an original independent
output chart. The characteristic root's independent denominator and
power forms then bound both the original affine generic fiber and its
radial projective-source curve by two, without a fixed vertex. -/
theorem actual_characteristic_root_data_constructs_original_fiber_degree_bounds
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hdata : ActualCharacteristicGaussRootData H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc))))
      (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc))))
      (_hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3))),
      (∀ D : ℕ, HasCurveHilbertDegree (projectiveConeIdeal
        (L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          S₀ (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))) D → D ≤ 2) ∧
      (∀ D : ℕ, HasCurveHilbertDegree (projectiveFieldPointIdeal
        (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          S₀ (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))).toIdeal D → D ≤ 2) := by
  obtain ⟨cS, cM, cN, r, _hS, _hM, _hN, _hr, hroot, hm, hformula, hMN, hSN, _hfactor, hnumerator⟩ := hdata
  obtain ⟨β, hβ, hSN⟩ := hSN
  have hMS : LinearIndependent E ![(R) cM, (R) cS] := by
    rw [hSN]
    have he := (LinearIndependent.pair_smul_smul_iff
      (isUnit_iff_ne_zero.mpr (one_ne_zero : (1 : E) ≠ 0))
      (isUnit_iff_ne_zero.mpr hβ)).mpr hMN
    simpa only [one_smul] using he
  obtain ⟨p, hY, h, hh, hcN⟩ := hnumerator
  subst cN
  obtain ⟨c, q, k, hc, hq, hk⟩ := specified_original_chart_exists_exact_invariant_coefficients
    H hrank p hY hN h hh
  have hformula' : r = aeval (w) ((O) (closedGaussCanonicalRootNumerator H I p hY h hh e E)) *
      aeval (w) (linearFormPolynomial (extendedClosedGaussChosenRulingMatrix H I E hH
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0)) / aeval (w) ((O) cM) := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hformula
  refine ⟨p, hY, h, hh, ?_, ?_⟩
  · exact native_independent_root_identities_bound_original_full_fiber_degree
      H I p hY h hh E (Nat.lt_trans Nat.zero_lt_one hd) hH hind hGauss e hrank hN hd
      c q k hc hq hk cM cS r hroot hm hformula' hMS
  · exact native_independent_root_identities_bound_original_radial_fiber_degree
      H I p hY h hh E (Nat.lt_trans Nat.zero_lt_one hd) hH hind hGauss e hrank hN hd
      c q k hc hq hk cM cS r hroot hm hformula' hMS

end DimensionFourDependence
