import DimensionFourDependence.ProjectiveCanonicalRegularOrders
import DimensionFourDependence.CoefficientCanonicalRationalOrders
import DimensionFourDependence.ClosedGaussCoordinateIntegrality

/-! # Canonical rational source orders at a given projective prime

The given finite-coefficient normalized prime over a height-one source
point supplies a DVR and a rational source pullback preserving every
normalized valuation, extending the actual canonical local map.
-/

namespace DimensionFourDependence

open scoped TensorProduct

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "L₀" => projectiveCoordinateChartField (C := K) x₀ (s.symm none)

/-- The actual given projective normalization prime constructs the
canonical rational source map and all its normalized valuation equalities. -/
theorem actual_projective_given_prime_canonical_rational_orders
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (Q : Ideal R₀) [Q.IsPrime] (hheight : Q.height = 1)
    (E : Type v) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
    letI : IsDomain (S₀ ⊗[C₀] E) := subalgebra_algebraic_base_change_isDomain
      (L := E) (closedGaussParameterField_relatively_closed H I) S₀
    letI : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra R₀ (S₀ ⊗[C₀] E) :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
    letI : Algebra R₀ (normalizationRing (S₀ ⊗[C₀] E)) :=
      ((algebraMap (S₀ ⊗[C₀] E) (normalizationRing (S₀ ⊗[C₀] E))).comp
        (algebraMap R₀ (S₀ ⊗[C₀] E))).toAlgebra
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_height_one_isDVR s Q hheight
    letI : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
    letI : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
    ∀ (q : Ideal (normalizationRing (S₀ ⊗[C₀] E))) [q.IsPrime] [q.LiesOver Q],
      CanonicalRationalSourceOrderComparison (F := L₀)
        (Localization.localRingHom Q q (algebraMap R₀ (normalizationRing (S₀ ⊗[C₀] E)))
          (Ideal.over_def q Q)) := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : IsDomain (S₀ ⊗[C₀] E) := subalgebra_algebraic_base_change_isDomain
    (L := E) (closedGaussParameterField_relatively_closed H I) S₀
  let : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (S₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
  let : Algebra R₀ (normalizationRing (S₀ ⊗[C₀] E)) :=
    ((algebraMap (S₀ ⊗[C₀] E) (normalizationRing (S₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (S₀ ⊗[C₀] E))).toAlgebra
  let : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_height_one_isDVR s Q hheight
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  intro q hq hlie
  have hdivisor : ∃ δ : MvPolynomial (Fin 3) K, Irreducible δ ∧
      Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ} :=
    @projective_source_height_one_equation K inferInstance s Q inferInstance hheight
  rcases hdivisor with ⟨δ, hδ, hQ⟩
  have hf : Prime (projectiveSourceFullChartCoordinateEquiv (K := K) s δ) :=
    (MulEquiv.prime_iff (projectiveSourceFullChartCoordinateEquiv (K := K) s)).mpr hδ.prime
  have hmodels := actual_projective_given_normalization_prime_local_model.{u, v, v}
    H I s hH e Q (projectiveSourceFullChartCoordinateEquiv s δ) hf hQ E
  have hmodel : ProjectiveAllFiniteNormalizationPrimeModels.{u, v}
      H I s hH e Q (projectiveSourceFullChartCoordinateEquiv s δ) hf hQ := @hmodels q hq hlie
  obtain ⟨t, ht, hX, _⟩ := hmodel
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  let : IsScalarTower C₀ (Localization.AtPrime Q) L₀ :=
    closedGaussProjectiveHorizontalLocal_scalarTower H hH I e s Q t ht hX
  have hdenom : ProjectivePencilSourceDenominatorModel H I s e Q t ht :=
    actual_projective_pencil_source_denominator_model H I s hH e Q t ht hX
  dsimp only [ProjectivePencilSourceDenominatorModel] at hdenom
  rcases hdenom with ⟨φ, _, hRS, hfaith, hloc⟩
  let : Algebra S₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
  let : IsScalarTower C₀ S₀ (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let : IsScalarTower R₀ S₀ (Localization.AtPrime Q) := hRS
  let : FaithfulSMul S₀ (Localization.AtPrime Q) := hfaith
  let : IsLocalization (Algebra.algebraMapSubmonoid S₀ Q.primeCompl) (Localization.AtPrime Q) := hloc
  have hcomparison := coefficient_canonical_rational_source_order_comparison
    (R := R₀) (k := C₀) (S := S₀) (F := L₀) (E := E) Q
    (actual_closed_gauss_parameter_relatively_closed_in_projective_source H hH I e (s.symm none))
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact @hcomparison q hq hlie

end DimensionFourDependence
