import DimensionFourDependence.ExtendedChosenGaussRuling

/-! # The actual chosen Gauss characteristic line after coefficient extension

The original nonzero three-column normal-jet minor remains nonzero
after the specified coefficient embedding. Thus the actual extended
characteristic matrix has rank three, and its kernel is a line inside
the actual chosen two-dimensional ruling.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "G₀" => projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "e₀" => actualGaussRulingParameterChoice H I hH hd hind hGauss
local notation "v" => gaussParameterNormal H I (e₀)
local notation "θ" => ((algebraMap C₀ E).comp (algebraMap G₀ C₀)).comp (e₀).toRingHom

/-- The actual chosen original normal, its first derivative and its
second derivative, in the original four coordinates over the actual extension. -/
noncomputable def extendedClosedGaussChosenCharacteristicMatrix : Matrix (Fin 3) (Fin 4) E :=
  (normalCharacteristicMatrix (rationalParameterDerivative K) (v)).map (θ)

/-- The actual characteristic subspace on the chosen Gauss ruling. -/
noncomputable def extendedClosedGaussChosenCharacteristicSubspace : Submodule E (Fin 4 → E) :=
  LinearMap.ker (extendedClosedGaussChosenCharacteristicMatrix H I E hH hd hind hGauss).toLin'

local notation "C₃" => extendedClosedGaussChosenCharacteristicMatrix H I E hH hd hind hGauss
local notation "Cline" => extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'

/-- The chosen actual characteristic kernel is contained in the
chosen actual ruling, with both original first-jet equations preserved. -/
theorem extendedClosedGaussChosenCharacteristicSubspace_le_ruling : (Cline) ≤ (W₀) := by
  intro b hb
  change (C₃) *ᵥ b = 0 at hb
  change extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss *ᵥ b = 0
  funext i
  fin_cases i
  · exact congrFun hb 0
  · exact congrFun hb 1

/-- The original nonzero normal-jet minor remains nonzero in the
actual coefficient extension, so all three actual characteristic rows
are independent. -/
theorem extendedClosedGaussChosenCharacteristicMatrix_rows_independent :
    LinearIndependent E (C₃).row := by
  obtain ⟨i, j, hminor, _⟩ := Classical.choose_spec
    (actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss)
  apply three_rows_independent_of_column_minor (C₃) ![imageNormalPivot H I, i, j]
  change (((rationalParameterJetMatrix (v)).submatrix id ![imageNormalPivot H I, i, j]).map (θ)).det ≠ 0
  change ((θ).mapMatrix ((rationalParameterJetMatrix (v)).submatrix id ![imageNormalPivot H I, i, j])).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (θ)).mpr hminor

/-- The actual characteristic subspace has dimension exactly one
after the actual coefficient extension. -/
theorem extendedClosedGaussChosenCharacteristicSubspace_finrank : finrank E (Cline) = 1 := by
  have hrows := extendedClosedGaussChosenCharacteristicMatrix_rows_independent H I E hH hd hind hGauss
  have hr : (C₃).rank = 3 := hrows.rank_matrix
  have hdim := LinearMap.finrank_range_add_finrank_ker (C₃).toLin'
  have hrange : finrank E (LinearMap.range (C₃).toLin') = 3 := hr
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  change finrank E (LinearMap.ker (C₃).toLin') = 1
  omega

/-- Every nonzero actual characteristic vector spans exactly the
actual characteristic line, so its projective direction is that point. -/
theorem extendedClosedGaussChosenCharacteristic_span_of_nonzero
    (b : Fin 4 → E) (hb : b ≠ 0) (hmem : b ∈ (Cline)) :
    Submodule.span E {b} = (Cline) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by intro x hx; rcases Set.mem_singleton_iff.mp hx with rfl; exact hmem)
  · rw [finrank_span_singleton hb, extendedClosedGaussChosenCharacteristicSubspace_finrank H I E hH hd hind hGauss]

end DimensionFourDependence
