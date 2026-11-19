import DimensionFourDependence.ExtendedGaussStalkOrders
import DimensionFourDependence.ActualProjectiveImageMultiplicity

/-! # Source common-factor bounds from orders on the actual global normalization

Actual global geometric source germs have exactly their original
prime-localization values. The given-prime source-divisor theorem
therefore applies directly to order bounds in the actual global stalk.
-/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

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
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q

omit [CharZero K] [Algebra.IsAlgebraic C₀ E] in
/-- The specified original-source map is exactly the canonical action
used by the given-prime normalization local-model theorems. -/
theorem extendedClosedGaussTensorNormalizationSourceHom_canonical_algebraMap :
    letI : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra R₀ T₀ :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
    letI : Algebra R₀ N₀ := ((algebraMap T₀ N₀).comp (algebraMap R₀ T₀)).toAlgebra
    ∀ r : R₀, extendedClosedGaussTensorNormalizationSourceHom H I E s r = algebraMap R₀ N₀ r := by
  let : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ T₀ :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
  let : Algebra R₀ N₀ := ((algebraMap T₀ N₀).comp (algebraMap R₀ T₀)).toAlgebra
  intro r
  rfl

/-- Orders of the original homogeneous sections in the actual global
normalization stalk force the original homogeneous common-factor bound.
The source divisor is determined by the given prime's original-source
contraction; its defining equation and degree are constructed. -/
theorem actual_global_normalization_source_orders_common_factor_degree
    [hfinite : Module.Finite C₀ E]
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (a : ℕ) (q : PrimeSpectrum N₀)
    (hheight : (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)).height = 1)
    (horder : ∀ i, extendedClosedGaussNormalizationSourceGerm H I E hH e s q
        (projectiveSourceSectionHom s (H i)) ∈
      (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a) :
    ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
      q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s) =
        Ideal.span {projectiveSourceSectionHom s Δ} ∧
      Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ T₀ :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
  let : Algebra R₀ N₀ := ((algebraMap T₀ N₀).comp (algebraMap R₀ T₀)).toAlgebra
  let Q := q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)
  let : Q.IsPrime := inferInstanceAs
    (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)).IsPrime
  have hc := extendedClosedGaussTensorNormalizationSourceHom_canonical_algebraMap H I E s
  have hcontract : q.asIdeal.comap (algebraMap R₀ N₀) = Q := by rfl
  have himage : projectiveSourceChartImageClosure s (algebraMap R₀ N₀) q.asIdeal =
      PrimeSpectrum.zeroLocus (Q : Set R₀) :=
    (projective_source_chart_image_closure_eq_prime_iff s _ q.asIdeal Q).mpr hcontract
  have hlocal : ∀ i, algebraMap R₀ (Localization.AtPrime q.asIdeal)
        (projectiveSourceSectionHom s (H i)) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ a := by
    intro i
    have h := (extendedClosedGaussNormalizationSourceGerm_order_iff H I E hH e s q
      (projectiveSourceSectionHom s (H i)) a).mp (horder i)
    simpa only [hc, ← IsScalarTower.algebraMap_apply R₀ N₀ (Localization.AtPrime q.asIdeal)] using h
  have h := @actual_projective_divisor_image_common_factor_degree.{u, u}
    K inferInstance inferInstance H I s d hH e P g c D hg hgh hP hprim hHP a E
    inferInstance inferInstance hfinite q.asIdeal inferInstance Q inferInstance hheight himage hlocal
  convert! h using 1

end DimensionFourDependence
