import DimensionFourDependence.GlobalNormalizationMultiplicity
import DimensionFourDependence.ExtendedGaussSourcePoint

/-! # The common-factor bound with actual projective source data

Both the source-divisor condition and the homogeneous-section pullback
orders are stated on the actual global geometric source projection.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "N₀" => normalizationRing (S₀ ⊗[C₀] E)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- Codimension one at the actual projective source-image point and
orders of the actual pulled-back original homogeneous sections force
the original homogeneous divisor power into the common factor. -/
theorem actual_global_projective_source_divisor_common_factor_degree
    [Module.Finite C₀ E]
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (a : ℕ) (q : PrimeSpectrum N₀)
    (hheight : ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1)
    (horder : ∀ i, extendedClosedGaussNormalizationProjectiveSourceGerm H I E hH e s q
        ((originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).symm
          (projectiveSourceSectionHom s (H i))) ∈
      (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a) :
    ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
      q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s) =
        Ideal.span {projectiveSourceSectionHom s Δ} ∧
      Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  have hheight' :=
    (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff H I E hH e s q).mp hheight
  have horder' : ∀ i, extendedClosedGaussNormalizationSourceGerm H I E hH e s q
      (projectiveSourceSectionHom s (H i)) ∈
        (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a := by
    intro i
    have hi := horder i
    rw [extendedClosedGaussNormalizationProjectiveSourceGerm_eq_source_germ] at hi
    have hsection : projectiveAmbientSectionToSource (C := K) x₀ (s.symm none)
        (source_rationalCoordinate_ne_zero _)
        ((originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).symm
          (projectiveSourceSectionHom s (H i))) = projectiveSourceSectionHom s (H i) := by
      change originalProjectiveAffineSectionEquiv (K := K) (s.symm none)
        ((originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).symm
          (projectiveSourceSectionHom s (H i))) = _
      exact RingEquiv.apply_symm_apply _ _
    simpa only [hsection] using hi
  exact actual_global_normalization_source_orders_common_factor_degree
    H I E hH e s P g hg hgh hP hprim hHP a q hheight' horder'

end DimensionFourDependence
