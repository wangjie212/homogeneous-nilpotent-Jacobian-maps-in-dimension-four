import DimensionFourDependence.ExtendedNativeSectionGerms
import DimensionFourDependence.GlobalOriginalSectionMultiplicity
import DimensionFourDependence.ExtendedNormalizationDivisorDvr
import DimensionFourDependence.RegularSectionIntegerMultiplicity
import DimensionFourDependence.ExtendedGaussPointAtlas

/-! # Arbitrary actual native global hyperplane sections have pencil-degree-bounded multiplicity -/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "y" a:max Q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) Q

local instance extendedNativeSectionMultiplicityIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedNativeSectionMultiplicityNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance extendedNativeSectionMultiplicityDomain (a : Fin 4) : IsDomain (T a) :=
  original_tensor_pencil_chart_isDomain H I E (finSuccEquiv' a)

variable (hGauss : gaussImageDimension H I = 1)
  (p q : MvPolynomial (Fin 4) K) {D : ℕ}
  (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
  (ht : closedGaussParameterSourceHom H I e RatFunc.X =
    algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)

include hGauss hq0 hrel hpH hqH ht in
/-- The original pencil degree bounds every maximal-ideal power
order of the actual local coefficient of every nonzero actual native
global hyperplane section. No original coefficient family is supplied. -/
theorem actual_native_pencil_global_section_order_le_degree
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4)
    (Q : PrimeSpectrum (normalizationRing (T a))) (hcodim : Order.coheight (y a Q) = 1)
    (m : ℕ) (hm : extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e s a Q ∈
      (IsLocalRing.maximalIdeal ((N).presheaf.stalk (y a Q))) ^ m) : m ≤ D := by
  have hcanon := (extendedClosedGaussHyperplaneOriginalSectionStalkGerm_eq H I E hH e s a Q).symm ▸ hm
  exact @actual_global_pencil_original_chart_section_order_le_degree K
    (inferInstance : Field K) (inferInstance : CharZero K) H I E
    (inferInstance : Field E) (inferInstance : Algebra C₀ E)
    (inferInstance : Algebra.IsAlgebraic C₀ E) d hH e (finSuccEquiv' a) hGauss
    p q D hq0 hrel hpH hqH ht Q hcodim
    (extendedClosedGaussOriginalFrameCoordinates H I E hH e (finSuccEquiv' a))
    (extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e (finSuccEquiv' a) s)
    (extendedClosedGaussOriginalFrameCoordinates_ne_zero H I E hH e (finSuccEquiv' a) _)
    (extendedClosedGaussOriginalFrameCoordinates_ratios H I E hH e (finSuccEquiv' a))
    (extendedClosedGaussHyperplaneOriginalNormalizedSection_coefficient_ne_zero H I E hH e
      (finSuccEquiv' a) s hs _) m hcanon

include hGauss hq0 hrel hpH hqH ht in
/-- At every intrinsic normalization divisor point, the actual
integer multiplicity of every nonzero actual native global hyperplane
section lies between zero and the original pencil degree. -/
theorem actual_native_pencil_global_section_integer_multiplicity_bound
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4)
    (Q : PrimeSpectrum (normalizationRing (T a))) (hcodim : Order.coheight (y a Q) = 1) :
    let z := extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e s a Q
    0 ≤ (N).ord (algebraMap ((N).presheaf.stalk (y a Q)) (N).functionField z) (y a Q) ∧
      (N).ord (algebraMap ((N).presheaf.stalk (y a Q)) (N).functionField z) (y a Q) ≤ (D : ℤ) := by
  let : IsDiscreteValuationRing ((N).presheaf.stalk (y a Q)) :=
    extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e (y a Q) hcodim
  apply scheme_regular_integer_multiplicity_bounded (y a Q) hcodim
    (extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e s a Q)
    (extendedClosedGaussHyperplaneGlobalCoefficientGerm_ne_zero H I E hH e s hs a Q) D
  intro m hm
  exact actual_native_pencil_global_section_order_le_degree H I E hH e hGauss
    p q hq0 hrel hpH hqH ht s hs a Q hcodim m hm

include hGauss hq0 hrel hpH hqH ht in
/-- Every intrinsic divisor point of the actual normalized pencil
has an original regular frame in which each nonzero actual global
hyperplane section has integer multiplicity at most the pencil degree. -/
theorem actual_native_pencil_global_section_all_divisors_multiplicity_bound
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (z : N) (hcodim : Order.coheight z = 1) :
    ∃ (a : Fin 4) (hz : z ∈ U a),
      let r := (N).presheaf.germ (U a) z hz
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)
      0 ≤ (N).ord (algebraMap ((N).presheaf.stalk z) (N).functionField r) z ∧
        (N).ord (algebraMap ((N).presheaf.stalk z) (N).functionField r) z ≤ (D : ℤ) := by
  obtain ⟨a, Q, rfl⟩ := extendedClosedGaussNormalizationPoint_exists_tensor_prime H I E hH e z
  refine ⟨a, extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) Q, ?_⟩
  exact actual_native_pencil_global_section_integer_multiplicity_bound H I E hH e hGauss
    p q hq0 hrel hpH hqH ht s hs a Q hcodim

end DimensionFourDependence
