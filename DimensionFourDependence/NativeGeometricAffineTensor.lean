import DimensionFourDependence.NativeGeometricClosedCoefficients
import DimensionFourDependence.OriginalAffineTensorRealization

/-! # The same chosen geometric component realizes the entire original affine tensor -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "D₀" => polynomialOutputField H
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField

local instance nativeGeometricAffineTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance nativeGeometricAffineTensorIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeGeometricAffineTensorExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (B Z : Type u) [Field B] [Field Z]
    [Algebra (RatFunc (RatFunc E)) B] [Algebra B Z]
    [Algebra (RatFunc (RatFunc E)) Z] [IsScalarTower (RatFunc (RatFunc E)) B Z]

/-- The actual component and its retained intermediate source
relations give a realization of the entire original affine tensor
fraction field, using precisely the specified coefficients and the
component's own four coordinates. All extended polynomial identities
therefore transfer through this one field embedding. -/
theorem native_geometric_component_constructs_original_affine_tensor_realization
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
      ∃ φ : F₀ →+* Z,
        (∀ b : E, φ (algebraMap E F₀ b) =
          algebraMap Cᵣ Z (RatFunc.C (RatFunc.C b))) ∧
        (∀ i, φ ((xₐ) i) = x i) ∧
        ∀ P : MvPolynomial (Fin 4) E,
          φ (aeval (xₐ) P) = MvPolynomial.eval₂
            ((algebraMap Cᵣ Z).comp (RatFunc.C.comp RatFunc.C)) x P := by
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  intro γ δ hδK x
  letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
  letI : Algebra D₀ B := ((algebraMap Cᵣ B).comp δ).toAlgebra
  intro hcomponent hcontract
  obtain ⟨f, _hfK, hfx, hfc⟩ :=
    native_geometric_component_constructs_original_closed_coefficient_realization
      H I E hH e B Z L hL α γ δ hδK x hcomponent hcontract
  let τ : E →+* Z := (algebraMap Cᵣ Z).comp (RatFunc.C.comp RatFunc.C)
  obtain ⟨φ, _hsource, hcoeff, hcoords, hpoly⟩ :=
    compatible_original_closed_coefficients_construct_affine_tensor_realization
      H I E f τ hfc
  refine ⟨φ, hcoeff, ?_, ?_⟩
  · intro i
    exact (hcoords i).trans (hfx i)
  · intro P
    rw [hpoly, show (fun i => f (rationalCoordinate (K := K) i)) = x from funext hfx]

end DimensionFourDependence
