import DimensionFourDependence.CoefficientCompatibleComponentSource
import DimensionFourDependence.NativeScaleClosedGaussCoefficients

/-! # The chosen geometric component retains the original closed Gauss coefficient realization -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "D₀" => polynomialOutputField H
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField

local instance nativeGeometricClosedCoefficientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeGeometricClosedCoefficientsExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance nativeGeometricClosedCoefficientsOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

variable (B Z : Type u) [Field B] [Field Z]
    [Algebra (RatFunc (RatFunc E)) B] [Algebra B Z]
    [Algebra (RatFunc (RatFunc E)) Z] [IsScalarTower (RatFunc (RatFunc E)) B Z]

/-- The chosen geometric component constructs an original rational
source embedding retaining the entire original closed Gauss field in
its specified coefficient realization. It uses the actual intermediate
source relation contraction, so no unrelated closed-field lift is chosen. -/
theorem native_geometric_component_constructs_original_closed_coefficient_realization
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0)
    (α : RatFunc E →ₐ[E] (N).functionField) :
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    ∀ (γ : Cᵣ →ₐ[RatFunc E] Gᵣ) (δ : D₀ →+* Cᵣ),
      (∀ c : K, δ (algebraMap K D₀ c) = RatFunc.C (RatFunc.C ((ι) c))) →
      ∀ x : Fin 4 → Z,
      letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
      letI : Algebra D₀ B := ((algebraMap Cᵣ B).comp δ).toAlgebra
      fiberVanishingIdeal (L := B) x ∈
        (extendCoefficientIdeal B (fiberVanishingIdeal (L := D₀)
          (rationalCoordinate (K := K) (n := 4)))).minimalPrimes →
      (fiberVanishingIdeal (L := B) x).comap (MvPolynomial.map (algebraMap Cᵣ B)) =
        fiberVanishingIdeal (L := Cᵣ)
          (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) L)) →
      ∃ f : S₀ →+* Z,
        (∀ c : K, f (algebraMap K S₀ c) = algebraMap Cᵣ Z (RatFunc.C (RatFunc.C ((ι) c)))) ∧
        (∀ i, f (rationalCoordinate (K := K) i) = x i) ∧
        ∀ c : C₀, f (c : S₀) =
          algebraMap Cᵣ Z (RatFunc.C (RatFunc.C (algebraMap C₀ E c))) := by
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  intro γ δ hδK x
  letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
  letI : Algebra D₀ B := ((algebraMap Cᵣ B).comp δ).toAlgebra
  intro hcomponent hcontract
  let κ : K →+* Cᵣ := (RatFunc.C.comp RatFunc.C).comp (ι)
  letI : Algebra K Cᵣ := κ.toAlgebra
  have hγC (b : RatFunc E) : γ (RatFunc.C b) = RatFunc.C (α b) :=
    (γ.commutes b).trans (IsScalarTower.algebraMap_apply (RatFunc E) (N).functionField Gᵣ b)
  have hαC (b : E) : α (RatFunc.C b) = algebraMap E (N).functionField b := α.commutes b
  letI : IsScalarTower K Cᵣ Gᵣ := IsScalarTower.of_algebraMap_eq' (by
    ext c
    change RatFunc.C (algebraMap E (N).functionField ((ι) c)) = γ (RatFunc.C (RatFunc.C ((ι) c)))
    rw [hγC, hαC])
  letI : Algebra K Z := ((algebraMap Cᵣ Z).comp κ).toAlgebra
  letI : IsScalarTower K Cᵣ Z := IsScalarTower.of_algebraMap_eq' rfl
  let δK : D₀ →ₐ[K] Cᵣ := { δ with commutes' := hδK }
  let Φ := nativeIndependentScaleSourceFieldHom H I E hH e L hL
  obtain ⟨f, hf, hconstants⟩ :=
    full_generic_component_constructs_coefficient_compatible_source (B := B) H δK Φ
      (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) L)) x
      (nativeIndependentScaleSourceFieldHom_coordinate H I E hH e L hL) hcomponent hcontract
  refine ⟨f.toRingHom, ?_, hf, ?_⟩
  · intro c
    exact f.commutes c
  · intro c
    apply hconstants (c : S₀) (RatFunc.C (RatFunc.C (algebraMap C₀ E c)))
    change nativeIndependentScaleSourceFieldHom H I E hH e L hL (c : S₀) =
      γ (RatFunc.C (RatFunc.C (algebraMap C₀ E c)))
    rw [nativeIndependentScaleSourceFieldHom_closed_coefficient, hγC, hαC]

end DimensionFourDependence
