import DimensionFourDependence.FixedVertexScaledOutputSpan
import DimensionFourDependence.RulingCoordinateBasis

/-! # The actual scaled-plane output covectors construct a dual ruling basis -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
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
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance fixedVertexScaledDualOutputBasisIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance fixedVertexScaledDualOutputBasisAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex

/-- The original fixed vertex and nonzero numerator construct the
actual two output basis vectors, their four dual pairings, and the
original component expressions with these very same vectors. -/
theorem fixed_vertex_scaled_covectors_construct_dual_output_basis
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0)
    (hnlast : n (Fin.last 3) = 0) (hn : aeval (w) ((O) n) ≠ 0) :
    ∃ bS bN : Fin 4 → E, LinearIndependent E ![bS, bN] ∧ bS ∈ W₀ ∧ bN ∈ W₀ ∧
      s ⬝ᵥ bS = 1 ∧ n ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ n ⬝ᵥ bN = 1 ∧
      ∀ i, aeval (w) (MvPolynomial.map (ι) (H i)) =
        algebraMap E (N).functionField (bS i) * aeval (w) ((O) s) +
          algebraMap E (N).functionField (bN i) * aeval (w) ((O) n) := by
  have hpair := (fixed_vertex_scaled_output_covectors_construct_original_output_span
    H I E hH e hd hind hGauss hvertex s n hs hnlast hn).1
  have hdim := extendedClosedGaussChosenRulingMatrix_kernel_finrank H I E hH hd hind hGauss
  obtain ⟨bS, bN, hLI, hbS, hbN, hsS, hnS, hsN, hnN, hcoord⟩ :=
    two_dimensional_ruling_coordinate_basis (W₀) hdim s n hpair
  refine ⟨bS, bN, hLI, hbS, hbN, hsS, hnS, hsN, hnN, fun i => ?_⟩
  have hi := matrix_kernel_coordinate_form_span_after_extension (E := (N).functionField)
    (A₀) s n bS bN hcoord
    (fun j => aeval (w) (MvPolynomial.map (ι) (H j)))
    (extendedClosedGauss_native_output_mem_chosen_ruling H I E hH e hd hind hGauss) i
  have hsvalue : ((fun j => algebraMap E (N).functionField (s j)) ⬝ᵥ
      (fun j => aeval (w) (MvPolynomial.map (ι) (H j)))) = aeval (w) ((O) s) :=
    (extendedClosedGaussOutputLinearPolynomial_value H I E hH e s).symm
  have hnvalue : ((fun j => algebraMap E (N).functionField (n j)) ⬝ᵥ
      (fun j => aeval (w) (MvPolynomial.map (ι) (H j)))) = aeval (w) ((O) n) :=
    (extendedClosedGaussOutputLinearPolynomial_value H I E hH e n).symm
  rwa [hsvalue, hnvalue] at hi

end DimensionFourDependence
