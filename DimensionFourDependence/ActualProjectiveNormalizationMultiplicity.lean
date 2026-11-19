import DimensionFourDependence.CoefficientProjectiveMultiplicity
import DimensionFourDependence.ProjectiveGivenNormalizationPrime
import DimensionFourDependence.ProjectivePencilDenominators

/-! # Actual normalization section orders bound the original common factor

For a given prime of the actual finite-coefficient projective pencil
normalization over a source divisor, the horizontal parameter and local
order comparison are constructed. Orders on the original homogeneous
sections force the actual homogeneous divisor power into the original
common factor g and hence give a <= degree(g).
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
local notation "L₀" => projectiveCoordinateChartField (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

set_option maxHeartbeats 4000000 in
/-- The compatible actual horizontal parameter constructs the complete
finite-normalization common-factor consequence of the original section orders. -/
theorem actual_projective_parameter_normalization_common_factor_degree
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ)
    (hQ : Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ}) (a : ℕ)
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X)
    (E : Type v) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra R₀ (G₀ ⊗[C₀] E) :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
    letI : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
      ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
        (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
    PrimesOverSourceOrdersImply (T := normalizationRing (G₀ ⊗[C₀] E)) Q
      (fun i => projectiveSourceSectionHom s (H i)) a
      (projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
        a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (G₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
  let : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  have hf : Prime (projectiveSourceFullChartCoordinateEquiv (K := K) s δ) :=
    (MulEquiv.prime_iff (projectiveSourceFullChartCoordinateEquiv (K := K) s)).mpr
      (irreducible_iff_prime.mp hδ)
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    projective_source_divisor_isDVR s Q (projectiveSourceFullChartCoordinateEquiv s δ) hf hQ
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  let : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  let : IsScalarTower C₀ (Localization.AtPrime Q) L₀ :=
    closedGaussProjectiveHorizontalLocal_scalarTower H hH I e s Q t ht hX
  obtain ⟨φ, _, hRS, hfaith, hloc⟩ := actual_projective_pencil_source_denominator_model H I s hH e Q t ht hX
  let : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
  let : IsScalarTower C₀ G₀ (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (fun k => (φ.commutes k).symm)
  let : IsScalarTower R₀ G₀ (Localization.AtPrime Q) := hRS
  let : FaithfulSMul G₀ (Localization.AtPrime Q) := hfaith
  let : IsLocalization (Algebra.algebraMapSubmonoid G₀ Q.primeCompl) (Localization.AtPrime Q) := hloc
  refine coefficient_projective_normalization_common_factor_degree
    (K := K) (k := C₀) (S := G₀) (L := L₀) (E := E) s Q
    ?_
    H P g hg hgh hP hprim hHP δ hδ hQ a
  exact actual_closed_gauss_parameter_relatively_closed_in_projective_source H hH I e (s.symm none)

include hH e in
/-- A given prime of the actual canonical finite-coefficient projective
normalization over the source divisor has the original homogeneous
common-factor bound from its original section orders. Horizontal data,
source-local maps, and order comparisons are all derived from that prime. -/
theorem actual_projective_given_normalization_prime_common_factor_degree
    (P : Fin 4 → R₄) (g : R₄) {c D : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P D)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ)
    (hQ : Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ}) (a : ℕ)
    (E : Type v) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra R₀ (G₀ ⊗[C₀] E) :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
    letI : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
      ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
        (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
    PrimesOverSourceOrdersImply (T := normalizationRing (G₀ ⊗[C₀] E)) Q
      (fun i => projectiveSourceSectionHom s (H i)) a
      (projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
        a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (G₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
  let : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
  have hf : Prime (projectiveSourceFullChartCoordinateEquiv (K := K) s δ) :=
    (MulEquiv.prime_iff (projectiveSourceFullChartCoordinateEquiv (K := K) s)).mpr
      (irreducible_iff_prime.mp hδ)
  refine prime_local_order_consequence_of_models
    (R := R₀) (T := normalizationRing (G₀ ⊗[C₀] E)) Q
    (fun i => projectiveSourceSectionHom s (H i)) a
    (projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
      a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree)
    (M := ProjectiveAllFiniteNormalizationPrimeModels.{u, v}
      H I s hH e Q (projectiveSourceFullChartCoordinateEquiv s δ) hf hQ) ?_ ?_
  · exact actual_projective_given_normalization_prime_local_model.{u, v, v}
      H I s hH e Q (projectiveSourceFullChartCoordinateEquiv s δ) hf hQ E
  · intro hmodel
    obtain ⟨t, ht, hX, _⟩ := hmodel
    exact actual_projective_parameter_normalization_common_factor_degree H I s hH e Q
      P g hg hgh hP hprim hHP δ hδ hQ a t ht hX E

end DimensionFourDependence
