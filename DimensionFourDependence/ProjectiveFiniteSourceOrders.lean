import DimensionFourDependence.ProjectivePencilDenominators
import DimensionFourDependence.CoefficientCanonicalSourceOrders

/-! # Rational source orders on actual projective finite normalizations

All coordinate and source maps are the actual projective pencil maps.
The given prime of its canonical finite-coefficient normalization has
unchanged regular vanishing bounds and normalized rational source orders.
The original source parameter is derived from prime contraction.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (s : Fin 4 ≃ Option (Fin 3)) {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "G₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "L₀" => projectiveCoordinateChartField (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

/-- The full actual projective finite-coefficient source-order comparison.
The coordinate map and its original-source compatibility are constructed. -/
noncomputable def ProjectiveFiniteNormalizationSourceOrders
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X)
    (E : Type*) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] : Prop :=
  letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_divisor_isDVR s Q f hf hQ
  letI : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  letI : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  letI : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  letI : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  letI : IsScalarTower C₀ (Localization.AtPrime Q) L₀ :=
    closedGaussProjectiveHorizontalLocal_scalarTower H hH I e s Q t ht hX
  ∃ φ : G₀ →ₐ[C₀] Localization.AtPrime Q,
    (∀ r, (primeLocalizationFractionHom (F := L₀) Q (φ r) : F₀) = r.val) ∧
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
    letI : IsScalarTower C₀ G₀ (Localization.AtPrime Q) :=
      IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    ∃ hRS : IsScalarTower R₀ G₀ (Localization.AtPrime Q),
      letI := hRS
      ∃ hfaith : FaithfulSMul G₀ (Localization.AtPrime Q),
        letI := hfaith
        ∃ hloc : IsLocalization (Algebra.algebraMapSubmonoid G₀ Q.primeCompl) (Localization.AtPrime Q),
          letI := hloc
          CoefficientCanonicalNormalizationSourceOrders (R := R₀) (k := C₀) (S := G₀)
            (A := Localization.AtPrime Q) (F := L₀) (E := E)
            (actual_closed_gauss_parameter_relatively_closed_in_projective_source H hH I e (s.symm none)) Q

/-- The actual finite-coefficient projective normalization has the same
regular and rational source orders, with every coordinate map constructed. -/
theorem actual_projective_finite_normalization_source_orders
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X)
    (E : Type*) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    ProjectiveFiniteNormalizationSourceOrders H I s hH e Q f hf hQ t ht hX E := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_divisor_isDVR s Q f hf hQ
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  let : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  let : IsScalarTower C₀ (Localization.AtPrime Q) L₀ :=
    closedGaussProjectiveHorizontalLocal_scalarTower H hH I e s Q t ht hX
  obtain ⟨φ, hφ, hRS, hfaith, hloc⟩ := actual_projective_pencil_source_denominator_model H I s hH e Q t ht hX
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
  let : IsScalarTower C₀ G₀ (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let : IsScalarTower R₀ G₀ (Localization.AtPrime Q) := hRS
  let : FaithfulSMul G₀ (Localization.AtPrime Q) := hfaith
  let : IsLocalization (Algebra.algebraMapSubmonoid G₀ Q.primeCompl) (Localization.AtPrime Q) := hloc
  refine ⟨φ, hφ, hRS, hfaith, hloc, ?_⟩
  exact coefficient_canonical_normalization_source_orders (R := R₀) (k := C₀) (S := G₀)
    (A := Localization.AtPrime Q) (F := L₀) (E := E)
    (actual_closed_gauss_parameter_relatively_closed_in_projective_source H hH I e (s.symm none)) Q

/-- An actual contracted pencil prime supplies the horizontal parameter
and all canonical finite-normalization source-order comparisons for every
finite coefficient extension; neither is assumed as input. -/
theorem actual_projective_contracted_prime_finite_source_orders
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      ∃ (t : Localization.AtPrime Q)
        (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
        (hX : primeLocalizationFractionHom (F := L₀) Q t =
          closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X),
        ∀ (E : Type*) [Field E] [Algebra C₀ E] [Module.Finite C₀ E],
          ProjectiveFiniteNormalizationSourceOrders H I s hH e Q f hf hQ t ht hX E := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  obtain ⟨t, ht, hX⟩ := actual_projective_contracted_prime_horizontal_parameter H I s hH e Q f hf hQ P
  refine ⟨t, ht, hX, ?_⟩
  intro E hE halg hfinite
  exact actual_projective_finite_normalization_source_orders H I s hH e Q f hf hQ t ht hX E

end DimensionFourDependence


