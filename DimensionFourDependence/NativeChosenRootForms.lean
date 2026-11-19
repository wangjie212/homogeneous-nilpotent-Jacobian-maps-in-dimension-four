import DimensionFourDependence.NativeGraphNormalComparison
import DimensionFourDependence.SelectedOutputCovectors
import DimensionFourDependence.GaussRootNumeratorCoefficients

/-! # The constructed root forms have the actual chosen native tangent-plane formula

Lift the selected output covectors to their original four coordinates.
Dividing the numerator covector by the proved nonzero normal pivot
retains the root and its power while making its input form exactly the
chosen native tangent plane used by the divisor exclusions.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance nativeChosenRootFormsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeChosenRootFormsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Actual original-coordinate root forms with the input form equal
to the exact chosen native Gauss tangent plane. -/
noncomputable def ActualChosenGaussRationalRootData : Prop :=
  ∃ (cS cM cN : Fin 4 → E) (r : (N).functionField),
    cS ≠ 0 ∧ cM ≠ 0 ∧ cN ≠ 0 ∧ r ≠ 0 ∧
      r ^ d = aeval (w) ((O) cS) ∧ aeval (w) ((O) cM) ≠ 0 ∧
      r = aeval (w) ((O) cN) * (∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i) /
        aeval (w) ((O) cM) ∧ HasActualGaussRootNumerator H I E e cN

variable (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh
local notation "Q" => MvPolynomial.map (algebraMap C₀ E) (linearFormPolynomial (ν))
local notation "P" => selectedOutputLinearPolynomial H I E p
local notation "λ" => algebraMap C₀ E (actualClosedGaussNormalCovector H I e (p 3))

/-- The original selected-output rational root formula equals the
actual chosen-plane formula after rescaling only the numerator form. -/
theorem selected_root_formula_eq_chosen_plane_formula (n m : Fin 3 → E) :
    aeval (w) ((P) n) * aeval (w) (Q) / aeval (w) ((P) m) =
      aeval (w) ((O) ((λ)⁻¹ • selectedOutputCovector p n)) *
        (∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i) /
          aeval (w) ((O) (selectedOutputCovector p m)) := by
  rw [extendedClosedGaussOutputLinearPolynomial_smul_native_value,
    selectedOutputCovector_output_polynomial, selectedOutputCovector_output_polynomial,
    extendedClosedGauss_graph_value_eq_chosen_plane_div_pivot H I p hY h hh E e hH hd hind hGauss,
    map_inv₀]
  simp only [div_eq_mul_inv]
  ring

/-- The actual constructed selected root forms give the exact
chosen native ruling-root data. No plane comparison, numerator
rescaling, original covector lift or chosen-plane root formula is supplied. -/
theorem selected_root_forms_construct_chosen_ruling_root_data
    (n m s : Fin 3 → E) (hn : n ≠ 0) (hm : m ≠ 0) (hs : s ≠ 0)
    (hmvalue : aeval (w) ((P) m) ≠ 0)
    (hr : aeval (w) ((P) n) * aeval (w) (Q) / aeval (w) ((P) m) ≠ 0)
    (hroot : (aeval (w) ((P) n) * aeval (w) (Q) / aeval (w) ((P) m)) ^ d = aeval (w) ((P) s))
    (hnumerator : ∀ i, n i = algebraMap C₀ E (closedGaussRootNumeratorCoefficient H I p hY h hh e i)) :
    ActualChosenGaussRationalRootData H I E hH e hd hind hGauss := by
  have hPivot := extendedClosedGaussNormal_graph_pivot_ne_zero H I p hY h hh E e
  refine ⟨selectedOutputCovector p s, selectedOutputCovector p m,
    (λ)⁻¹ • selectedOutputCovector p n,
    aeval (w) ((P) n) * aeval (w) (Q) / aeval (w) ((P) m),
    selectedOutputCovector_ne_zero p s hs, selectedOutputCovector_ne_zero p m hm,
    smul_ne_zero (inv_ne_zero hPivot) (selectedOutputCovector_ne_zero p n hn), hr, ?_, ?_, ?_, ?_⟩
  · simpa only [selectedOutputCovector_output_polynomial] using hroot
  · simpa only [selectedOutputCovector_output_polynomial] using hmvalue
  · exact selected_root_formula_eq_chosen_plane_formula H I E hH e hd hind hGauss p hY h hh n m
  · refine ⟨p, hY, h, hh, ?_⟩
    rw [funext hnumerator]
    rfl

end DimensionFourDependence
