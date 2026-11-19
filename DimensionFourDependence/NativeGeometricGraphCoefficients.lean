import DimensionFourDependence.NativeGeometricClosedCoefficients
import DimensionFourDependence.SameComponentGraphCoefficients
import DimensionFourDependence.OriginalAffineTensorRealization

/-! # One actual component retains the source, original graph coefficients and finite tensor coefficients -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
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
local notation "L" => coefficientField (K := K)
  (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField

local instance nativeGeometricGraphCoefficientsDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance nativeGeometricGraphCoefficientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeGeometricGraphCoefficientsExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (B Z : Type u) [Field B] [Field Z] [IsAlgClosed B]
    [Algebra (RatFunc (RatFunc E)) B] [Algebra B Z]
    [Algebra (RatFunc (RatFunc E)) Z] [IsScalarTower (RatFunc (RatFunc E)) B Z]

include hrank

/-- The same chosen actual geometric component simultaneously
realizes the original source, its entire graph coefficient field,
the specified finite Gauss coefficients and the full affine tensor.
The two coefficient embeddings agree on every closed Gauss element. -/
theorem native_geometric_component_constructs_same_source_graph_and_tensor_realizations
    (P : MvPolynomial (Fin 4) E) (hP : aeval (R := E) (w) P ≠ 0)
    (α : RatFunc E →ₐ[E] (N).functionField) :
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    ∀ (γ : Cᵣ →ₐ[RatFunc E] Gᵣ) (δ : D₀ →+* Cᵣ),
      (∀ c : K, δ (algebraMap K D₀ c) = RatFunc.C (RatFunc.C ((ι) c))) →
      ∀ x : Fin 4 → Z,
      letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
      letI : Algebra D₀ B := ((algebraMap Cᵣ B).comp δ).toAlgebra
      fiberVanishingIdeal («L» := B) x ∈
        (extendCoefficientIdeal B (fiberVanishingIdeal («L» := D₀)
          (rationalCoordinate (K := K) (n := 4)))).minimalPrimes →
      (fiberVanishingIdeal («L» := B) x).comap (MvPolynomial.map (algebraMap Cᵣ B)) =
        fiberVanishingIdeal («L» := Cᵣ)
          (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) P)) →
      ∃ (f : S₀ →+* Z) (g : (L) →+* B) (φ : F₀ →+* Z),
        (∀ i, f (rationalCoordinate (K := K) i) = x i) ∧
        (∀ l : L, algebraMap B Z (g l) = f (l : S₀)) ∧
        (∀ c : K, g (algebraMap K (L) c) = algebraMap Cᵣ B (RatFunc.C (RatFunc.C ((ι) c)))) ∧
        (∀ c : C₀, g ((a) c) = algebraMap Cᵣ B (RatFunc.C (RatFunc.C (algebraMap C₀ E c)))) ∧
        (∀ s : S₀, φ (algebraMap T₀ F₀ (s ⊗ₜ[C₀] (1 : E))) = f s) ∧
        (∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z
          (algebraMap Cᵣ B (RatFunc.C (RatFunc.C b)))) ∧
        (∀ i, φ ((xₐ) i) = x i) ∧
        ∀ (d : D₀) (l : L), (l : S₀) = (d : S₀) → g l = algebraMap Cᵣ B (δ d) := by
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  intro γ δ hδK x
  letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
  letI : Algebra D₀ B := ((algebraMap Cᵣ B).comp δ).toAlgebra
  intro hcomponent hcontract
  obtain ⟨f, hfK, hfx, hfC⟩ :=
    native_geometric_component_constructs_original_closed_coefficient_realization
      H I E hH e B Z P hP α γ δ hδK x hcomponent hcontract
  let σ : E →+* B := (algebraMap Cᵣ B).comp (RatFunc.C.comp RatFunc.C)
  let δB : D₀ →+* B := (algebraMap Cᵣ B).comp δ
  have hfK' (c : K) : f (algebraMap K S₀ c) = algebraMap B Z (δB (algebraMap K D₀ c)) := by
    rw [hfK]
    change algebraMap Cᵣ Z (RatFunc.C (RatFunc.C ((ι) c))) =
      algebraMap B Z (algebraMap Cᵣ B (δ (algebraMap K D₀ c)))
    rw [hδK]
    exact IsScalarTower.algebraMap_apply Cᵣ B Z _
  have hfC' (c : C₀) : f (c : S₀) = algebraMap B Z (σ (algebraMap C₀ E c)) := by
    rw [hfC]
    exact IsScalarTower.algebraMap_apply Cᵣ B Z _
  obtain ⟨g, hg, hgK, hgC, hgD⟩ :=
    same_full_generic_component_constructs_compatible_graph_coefficient_embedding
      H hrank I p hY h hh E δB σ f x hfK' hfx hfC' hcomponent
  obtain ⟨φ, hsource, hcoeff, hcoords, _hpoly⟩ :=
    compatible_original_closed_coefficients_construct_affine_tensor_realization
      H I E f ((algebraMap B Z).comp σ) hfC'
  refine ⟨f, g, φ, hfx, hg, ?_, hgC, hsource, hcoeff, ?_, hgD⟩
  · intro c
    exact (hgK c).trans (congrArg (algebraMap Cᵣ B) (hδK c))
  · intro i
    exact (hcoords i).trans (hfx i)

end DimensionFourDependence
