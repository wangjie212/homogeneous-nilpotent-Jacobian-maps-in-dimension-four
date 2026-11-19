import DimensionFourDependence.ProjectiveHeightOneMultiplicity
import DimensionFourDependence.ProjectiveSourceImageDivisor

/-! # The multiplicity bound from the actual source image closure

On the actual finite-coefficient normalized pencil chart, a prime whose
source image is dense in a codimension-one closed source subset gives
the original homogeneous common-factor bound. The defining homogeneous
equation, including its degree and its equation for that same image,
is constructed in the conclusion.
-/

namespace DimensionFourDependence

open scoped TensorProduct

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (s : Fin 4 ≃ Option (Fin 3)) {d₀ : ℕ} (hH : IsHomogMap H d₀)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "G₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

include hH e in
/-- The actual affine source image being dense in a divisor gives
an original homogeneous equation whose power divides the common factor.
No divisor equation or prime-contraction equality is assumed. -/
theorem actual_projective_divisor_image_common_factor_degree
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) (a : ℕ)
    (E : Type v) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra R₀ (G₀ ⊗[C₀] E) :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
    letI : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
      ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
        (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
    ∀ (q : Ideal (normalizationRing (G₀ ⊗[C₀] E))) [q.IsPrime]
      (Q : Ideal R₀) [Q.IsPrime], Q.height = 1 →
      projectiveSourceChartImageClosure s (algebraMap R₀ (normalizationRing (G₀ ⊗[C₀] E))) q =
        PrimeSpectrum.zeroLocus (Q : Set R₀) →
      (∀ i, algebraMap R₀ (Localization.AtPrime q) (projectiveSourceSectionHom s (H i)) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) →
      ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
        Q = Ideal.span {projectiveSourceSectionHom s Δ} ∧
        Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (G₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
  let : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
  intro q hq Q hQ hheight himage horder
  have hcontract : q.comap (algebraMap R₀ (normalizationRing (G₀ ⊗[C₀] E))) = Q :=
    (projective_source_chart_image_closure_eq_prime_iff s _ q Q).mp himage
  let : q.LiesOver Q := ⟨hcontract.symm⟩
  have h := actual_projective_height_one_normalization_common_factor_degree
    H I s hH e Q hheight P g hg hgh hP hprim hHP a E
  obtain ⟨δ, hδ, hQeq, hdiv, hdeg, hsmall⟩ := @h q hq inferInstance horder
  have hedegree := projectiveSourceHomogeneousDivisor_totalDegree s δ hδ.ne_zero
  refine ⟨projectiveSourceHomogeneousDivisor s δ,
    projectiveSourceHomogeneousDivisor_irreducible s δ hδ,
    ?_, ?_, hdiv, ?_, hsmall⟩
  · rw [hedegree]
    exact projectiveSourceHomogeneousDivisor_isHomogeneous s δ
  · have hsection : projectiveSourceSectionHom s (projectiveSourceHomogeneousDivisor s δ) =
        projectiveSourceFullChartCoordinateEquiv s δ := by
      change projectiveSourceFullChartCoordinateEquiv s
        (projectiveSourceDehomogenize s (projectiveSourceHomogeneousDivisor s δ)) = _
      rw [projectiveSourceHomogeneousDivisor_dehomogenize]
    rw [hsection]
    exact hQeq
  · simpa only [hedegree] using hdeg

end DimensionFourDependence
