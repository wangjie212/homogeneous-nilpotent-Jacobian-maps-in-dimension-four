import DimensionFourDependence.ExtendedInputLinearCoefficient
import DimensionFourDependence.TensorPencilResidueSourcePrime

/-! # Vanishing of the actual input linear section gives the original residue plane equation -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

/-- Linear coefficients in omitted-coordinate notation retain their
actual original coordinates under any coefficient-preserving map. -/
theorem map_linear_option_coefficient
    {E A F : Type*} [Field E] [CommRing A] [CommRing F] [Algebra E A] [Algebra E F]
    (φ : A →ₐ[E] F) (s : Fin 4 ≃ Option (Fin 3)) (c : Fin 3 → A) (ν : Fin 4 → E) :
    φ (∑ i, algebraMap E A (ν i) * (s i).elim 1 c) =
      ∑ i, (s i).elim 1 (fun j => φ (c j)) * algebraMap E F (ν i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, φ.commutes]
  cases hs : s i <;> simp [hs, mul_comm]

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra tensorPencilResidueGenerationClosedAlgebra
  tensorPencilResidueGenerationClosedSMul tensorPencilResidueGenerationExtendedSMul
  tensorPencilResidueGenerationClosedTower tensorPencilResidueGenerationOriginalSMul
  tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra
attribute [local instance 2000] tensorPencilResiduePointAddCommMonoid
  tensorPencilResiduePointSemiring tensorPencilResiduePointOriginalModule
  tensorPencilResiduePointOriginalMulAction

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" s:max => extendedClosedGaussNormalizationChartOpen H I E hH e s

local instance extendedInputLinearResidueIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- Vanishing of an actual normalized-chart regular function at its
actual geometric point is membership in the same original chart prime. -/
theorem extendedClosedGaussNormalizedChartSection_mem_prime_iff_germ
    (s : Fin 4 ≃ Option (Fin 3)) (q : PrimeSpectrum (normalizationRing (T₀ s)))
    (f : Γ(N, V s)) :
    extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s f ∈ q.asIdeal ↔
      (N).presheaf.germ (V s)
        (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q)
        (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e s q) f ∈
          IsLocalRing.maximalIdeal ((N).presheaf.stalk
            (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q)) := by
  let β := extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
  let g := (N).presheaf.germ (V s)
    (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q)
    (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e s q) f
  have hg := extendedClosedGaussNormalizationTensorChartStalkIso_regular_germ H I E hH e s q f
  have he := local_equiv_maximalIdeal_pow_mem_iff β g 1
  simp only [pow_one] at he
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q.asIdeal) q.asIdeal _).symm.trans
    ((congrArg (fun r : Localization.AtPrime q.asIdeal =>
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) hg.symm).to_iff.trans he)

variable (a : Fin 4)
  (q : PrimeSpectrum (normalizationRing
    (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
      (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[closedGaussParameterField H I] E)))

local notation "L₀" => FractionRing (normalizationRing (T₀ (finSuccEquiv' a)) ⧸ q.asIdeal)

noncomputable local instance extendedInputLinearResidueNormalizationAlgebra :
    Algebra (normalizationRing (T₀ (finSuccEquiv' a))) L₀ :=
  primeQuotientFractionOriginalAlgebra q.asIdeal

/-- Vanishing of the actual linear section at the actual tensor
normalization point gives exactly the original four-coordinate plane
equation in the actual prime residue fraction field. -/
theorem extendedClosedGaussInputLinearSection_vanishing_residue_plane
    (ν : Fin 4 → E)
    (hvan : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e ν) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q))) :
    ∑ i, (finSuccEquiv' a i).elim 1
      (originalTensorPencilResidueCoordinate H I E (finSuccEquiv' a) q.asIdeal) *
        algebraMap E L₀ (ν i) = 0 := by
  let f := extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
    (extendedClosedGaussInputLinearSection H I E hH e ν) a
  let c := extendedClosedGaussNormalizedChartSectionEquiv H I E hH e (finSuccEquiv' a) f
  have hc : c ∈ q.asIdeal :=
    (extendedClosedGaussNormalizedChartSection_mem_prime_iff_germ H I E hH e (finSuccEquiv' a) q f).mpr hvan
  have hz : algebraMap (normalizationRing (T₀ (finSuccEquiv' a))) L₀ c = 0 := by
    have hk := congrArg (fun J : Ideal (normalizationRing (T₀ (finSuccEquiv' a))) => c ∈ J)
      (prime_quotient_fraction_algebraMap_ker q.asIdeal)
    exact hk.to_iff.mpr hc
  let P := ∑ i, algebraMap E (T₀ (finSuccEquiv' a)) (ν i) *
    (finSuccEquiv' a i).elim 1 (originalTensorPencilCoordinate H I E (finSuccEquiv' a))
  have hP : algebraMap (T₀ (finSuccEquiv' a)) L₀ P = 0 :=
    (normalization_prime_residue_source_value q.asIdeal P).symm.trans
      ((congrArg (algebraMap (normalizationRing (T₀ (finSuccEquiv' a))) L₀)
        (extendedClosedGaussInputLinearSection_normalized_coefficient H I E hH e ν a).symm).trans hz)
  exact (map_linear_option_coefficient
    (IsScalarTower.toAlgHom E (T₀ (finSuccEquiv' a)) L₀) (finSuccEquiv' a)
    (originalTensorPencilCoordinate H I E (finSuccEquiv' a)) ν).symm.trans hP

end DimensionFourDependence
