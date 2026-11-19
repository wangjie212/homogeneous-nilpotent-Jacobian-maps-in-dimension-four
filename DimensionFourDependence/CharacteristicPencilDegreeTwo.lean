import DimensionFourDependence.CharacteristicPencilOriginalHilbert
import DimensionFourDependence.PencilCurveHilbertLowerBound
import DimensionFourDependence.CurveHilbertComparisonExistence
import DimensionFourDependence.OriginalRadialCurveDegreeExistence
import DimensionFourDependence.CharacteristicRootOriginalFiberDegree
import DimensionFourDependence.CharacteristicPencilOutputField

/-! # The actual characteristic pencil constructs a positive curve degree at most two -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "F₀" => (N).functionField
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "T₀" => ∑ j, algebraMap E (F₀)
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0 j) * (w) j
local notation "t₀" r:max => nativeCharacteristicPencilValue H I E hH e hd hind hGauss r
local notation "C₀" r:max => pencilCoefficientCurveField (E := E) (t₀ r)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance characteristicPencilDegreeTwoIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilDegreeTwoAlgebra : Algebra E (F₀) :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual pencil's own positive Hilbert degree exists and is
bounded by the degree of an actual original radial fiber. No degree
existence or Hilbert-polynomial linearity of the pencil is assumed. -/
theorem actual_characteristic_pencil_curve_degree_exists_le_original
    (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H (p i.castSucc))))
    (cN : Fin 4 → E) (r : F₀)
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r)
    (hT : (T₀) ≠ 0) (ht : Transcendental E (t₀ r))
    {D : ℕ} (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))).toIdeal D) :
    ∃ D' : ℕ, D' ≤ D ∧ HasCurveHilbertDegree
      (projectiveFieldPointIdeal (E := C₀ r) (w)).toIdeal D' := by
  exact exists_curve_hilbert_degree_of_hilbert_comparison _
    (projectiveFieldPointIdeal (E := C₀ r) (w)).isHomogeneous _ hD
    (fun n => actual_normalized_surface_pencil_curve_hilbert_lower_bound H I E hH e hGauss (t₀ r) ht n)
    (fun n => actual_characteristic_pencil_hilbert_le_original_radial_fiber
      H I E hH e hd hind hGauss hrank p hY cN r hfactor hT n)

omit hd in
/-- The retained actual characteristic root data construct the
same root's generic pencil curve over its full relatively closed
coefficient field, with a positive Hilbert degree at most two.
The original nilpotent map supplies the degree and every coefficient. -/
theorem actual_characteristic_root_data_constructs_pencil_curve_degree_two
    [Module.Finite (closedGaussParameterField H I) E]
    (hd1 : 1 < d) (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hdata : ActualCharacteristicGaussRootData H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd1) hind hGauss) :
    ∃ (cS cN : Fin 4 → E) (r : F₀), cS ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧
      r ^ d = aeval (w) ((O) cS) ∧
      CharacteristicNativeRulingRootFactorization H I E hH e
        (Nat.lt_trans Nat.zero_lt_one hd1) hind hGauss cN r ∧
      HasActualGaussRootNumerator H I E e cN ∧
      ∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree
        (projectiveFieldPointIdeal (E := pencilCoefficientCurveField (E := E)
          (nativeCharacteristicPencilValue H I E hH e
            (Nat.lt_trans Nat.zero_lt_one hd1) hind hGauss r)) (w)).toIdeal D := by
  obtain ⟨p, hY, h, hh, _hfull, hradial⟩ :=
    actual_characteristic_root_data_constructs_original_fiber_degree_bounds
      H I E hH e hd1 hind hGauss hN hrank hdata
  obtain ⟨D, _hD6, hD⟩ := original_developable_radial_curve_degree_exists_in_every_output_chart
    H I hH (Nat.lt_trans Nat.zero_lt_one hd1) hind hGauss hN hrank p hY h hh
  have hD2 := hradial D hD
  obtain ⟨cS, _cM, cN, r, hS, _hM, hN', hr, hroot, _hm, _hformula, _hMN, _hSN, hfactor, hnumerator⟩ := hdata
  have ht := actual_characteristic_pencil_value_transcendental
    H I E hH e hd1 hind hGauss cS cN r hr hroot hfactor
  have hT := actual_characteristic_pencil_tangent_value_ne_zero
    H I E hH e hd1 hind hGauss cS cN r hr hroot hfactor
  obtain ⟨D', hle, hD'⟩ := actual_characteristic_pencil_curve_degree_exists_le_original
    H I E hH e (Nat.lt_trans Nat.zero_lt_one hd1) hind hGauss hrank p hY cN r hfactor hT ht hD
  exact ⟨cS, cN, r, hS, hN', hr, hroot, hfactor, hnumerator, D', hle.trans hD2, hD'⟩

end DimensionFourDependence
