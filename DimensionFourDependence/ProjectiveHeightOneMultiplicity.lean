import DimensionFourDependence.ActualProjectiveNormalizationMultiplicity
import DimensionFourDependence.ProjectiveSourceHeightOne

/-! # Actual normalization multiplicity from a codimension-one image

The defining source divisor equation is constructed from height one.
The same equation, its power dividing the original common factor, and
the degree bounds are conclusions rather than additional input data.
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
/-- A height-one source prime and actual normalized section orders
construct its irreducible equation and the original homogeneous
common-factor divisibility and degree bounds. -/
theorem actual_projective_height_one_normalization_common_factor_degree
    (Q : Ideal R₀) [Q.IsPrime] (hheight : Q.height = 1)
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
    PrimesOverSourceOrdersImply (T := normalizationRing (G₀ ⊗[C₀] E)) Q
      (fun i => projectiveSourceSectionHom s (H i)) a
      (∃ δ : MvPolynomial (Fin 3) K, Irreducible δ ∧
        Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ} ∧
        projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
        a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (G₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
  let : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
  obtain ⟨δ, hδ, hQ⟩ := projective_source_height_one_equation s Q hheight
  have h := actual_projective_given_normalization_prime_common_factor_degree
    H I s hH e Q P g hg hgh hP hprim hHP δ hδ hQ a E
  intro q hq hlie horder
  exact ⟨δ, hδ, hQ, @h q hq hlie horder⟩

include hH e in
/-- Begin with a prime of the actual normalization itself. Its
contraction determines the source divisor, so neither a separate source
prime nor a defining equation nor a lies-over proof is required. -/
theorem actual_projective_contracted_height_one_common_factor_degree
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
    ∀ (q : Ideal (normalizationRing (G₀ ⊗[C₀] E))) [q.IsPrime],
      (q.under R₀).height = 1 →
      (∀ i, algebraMap R₀ (Localization.AtPrime q) (projectiveSourceSectionHom s (H i)) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) →
      ∃ δ : MvPolynomial (Fin 3) K, Irreducible δ ∧
        q.under R₀ = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ} ∧
        projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
        a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (G₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
  let : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
  intro q hq hheight horder
  have h := actual_projective_height_one_normalization_common_factor_degree
    H I s hH e (q.under R₀) hheight P g hg hgh hP hprim hHP a E
  exact @h q hq inferInstance horder

end DimensionFourDependence
