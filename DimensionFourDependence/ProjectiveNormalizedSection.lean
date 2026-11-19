import DimensionFourDependence.ValuationProjectiveLinearFrame
import DimensionFourDependence.ProjectiveChartFunctionField

/-! # Global regular sections in the original normalized projective frames

The coefficients are regular functions on the actual normalizations of
the original projective coordinate charts. Their original hyperplane
transition identifies their common rational numerator. Valuation rings
then construct integrality in any nonzero original-field linear frame
whose coordinate ratios are integral over the specified projection base.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- A regular section of the pulled-back hyperplane bundle, in the
actual normalizations of all four original coordinate charts, with its
original transition relations in the common function field. -/
structure ProjectiveNormalizedSection (x : Fin 4 → L) where
  coefficient (j : Fin 4) : integralClosure (projectiveCoordinateChartAlgebra (C := k) x j) L
  transition (i j : Fin 4) : (coefficient i : L) * x i = (coefficient j : L) * x j

/-- An original normalized chart coefficient is regular in every
valuation ring containing the original constants and all original ratios
for that chart. No independent lift of the coefficient is assumed. -/
theorem projective_normalized_section_original_chart_mem_valuation
    (x : Fin 4 → L) (s : ProjectiveNormalizedSection (k := k) x)
    (V : ValuationSubring L) (hk : ∀ a : k, algebraMap k L a ∈ V)
    (j : Fin 4) (hratios : ∀ i, x i / x j ∈ V) : (s.coefficient j : L) ∈ V := by
  let Vk : Subalgebra k L := { V.toSubring with algebraMap_mem' := hk }
  have hchart : projectiveCoordinateChartAlgebra (C := k) x j ≤ Vk := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hratios i
  apply integral_value_mem_valuationSubring (s.coefficient j : L) (s.coefficient j).property V
  intro a
  exact hchart a.property

/-- In every valuation ring where the original coordinate ratios of a
nonzero linear frame are regular, the actual global section coefficient
in that frame is regular. An original unit coordinate supplies the chart
and its actual normalized coefficient. -/
theorem projective_normalized_section_linear_frame_mem_valuation
    (x : Fin 4 → L) (s : ProjectiveNormalizedSection (k := k) x)
    (c : Fin 4 → k) (h : L) (hh : h ≠ 0)
    (hlinear : h = ∑ i, algebraMap k L (c i) * x i)
    (V : ValuationSubring L) (hk : ∀ a : k, algebraMap k L a ∈ V)
    (hx : ∀ i, x i / h ∈ V) (a : Fin 4) :
    (s.coefficient a : L) * x a / h ∈ V := by
  obtain ⟨j, _, hratios⟩ := valuation_linear_frame_exists_original_chart x c h hh hlinear V hk hx
  have hs := projective_normalized_section_original_chart_mem_valuation x s V hk j hratios
  rw [s.transition a j, mul_div_assoc]
  exact V.mul_mem _ _ hs (hx j)

variable {R : Type*} [CommRing R] [Algebra R L]

/-- Integrality of the original coordinate ratios in a nonzero linear
frame constructs integrality of every actual global regular section in
that frame. The section is supplied only by its original normalized
chart coefficients and transition, not by a projection integrality
hypothesis or a coefficient on an auxiliary chart. -/
theorem projective_normalized_section_linear_frame_isIntegral
    (x : Fin 4 → L) (s : ProjectiveNormalizedSection (k := k) x)
    (c : Fin 4 → k) (h : L) (hh : h ≠ 0)
    (hlinear : h = ∑ i, algebraMap k L (c i) * x i)
    (hconstants : ∀ a : k, IsIntegral R (algebraMap k L a))
    (hcoordinates : ∀ i, IsIntegral R (x i / h)) (a : Fin 4) :
    IsIntegral R ((s.coefficient a : L) * x a / h) := by
  apply isIntegral_of_mem_all_valuationSubrings
  intro V hR
  have hk (z : k) : algebraMap k L z ∈ V := by
    exact integral_value_mem_valuationSubring _ (hconstants z) V hR
  exact projective_normalized_section_linear_frame_mem_valuation x s c h hh hlinear V hk
    (fun i => integral_value_mem_valuationSubring _ (hcoordinates i) V hR) a

end DimensionFourDependence
