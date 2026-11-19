import DimensionFourDependence.ScaledPlaneGeometricFullOutputBoundary
import DimensionFourDependence.NativeGeometricAffineTensor

/-! # The fixed-vertex geometric component retains the original affine tensor -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
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
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField
local notation "B" => AlgebraicClosure Cᵣ

local instance scaledPlaneGeometricTensorComponentDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance scaledPlaneGeometricTensorComponentIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneGeometricTensorComponentExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex e

/-- The original root alternatives construct either the full cone
form or an actual geometric full generic-fiber component containing
the original fixed vertex at infinity. The same component realizes
the entire original affine tensor fraction field with its specified
finite coefficients and its own four source coordinates. -/
theorem actual_affine_root_alternatives_construct_geometric_tensor_vertex_component_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ δB : D₀ →+* B,
        (∀ c : K, δB (algebraMap K D₀ c) =
          algebraMap Cᵣ B (RatFunc.C (RatFunc.C ((ι) c)))) ∧
        letI : Algebra D₀ B := δB.toAlgebra
        Algebra.IsAlgebraic D₀ B ∧
        ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) B),
          ∃ hqa : X none ∉ q.asHomogeneousIdeal,
            fiberVanishingIdeal (L := B) (fun i => projectivePrimeRatioCoordinate q none (some i)) ∈
              (extendCoefficientIdeal B (fiberVanishingIdeal (L := D₀)
                (rationalCoordinate (K := K) (n := 4)))).minimalPrimes ∧
            fourthAxisAffineInfinityPoint B ∈ projectiveClosureSet (L := B)
              (fun i => projectivePrimeRatioCoordinate q none (some i)) ∧
            ∃ φ : F₀ →+* projectivePrimeRatioField q none,
              (∀ b : E, φ (algebraMap E F₀ b) =
                algebraMap B (projectivePrimeRatioField q none)
                  (algebraMap Cᵣ B (RatFunc.C (RatFunc.C b)))) ∧
              (∀ i, φ ((xₐ) i) = projectivePrimeRatioCoordinate q none (some i)) ∧
              ∀ P : MvPolynomial (Fin 4) E,
                φ (aeval (xₐ) P) = MvPolynomial.eval₂
                  (((algebraMap B (projectivePrimeRatioField q none)).comp (algebraMap Cᵣ B)).comp
                    (RatFunc.C.comp RatFunc.C))
                  (fun i => projectivePrimeRatioCoordinate q none (some i)) P := by
  rcases actual_affine_root_alternatives_construct_geometric_full_output_vertex_boundary_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, bS, bN, a, _hs, _hnlast, _ha, _hLI, _hsS, _hnS, _hsN, _hnN, α, hα,
        γ, _hγ, δ, hδK, _hδY, _halg, halgB, q, hqa, hQ, hcontract, hboundary⟩
  · exact Or.inl hcone
  · right
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
    letI : Algebra D₀ Cᵣ := δ.toAlgebra
    let aDB : Algebra D₀ B := inferInstance
    let δB : D₀ →+* B := (algebraMap Cᵣ B).comp δ
    have hδB : δB = algebraMap D₀ B := by
      apply RingHom.ext
      intro c
      exact (IsScalarTower.algebraMap_apply D₀ Cᵣ B c).symm
    have hDB : δB.toAlgebra = aDB := Algebra.algebra_ext _ _ (fun c =>
      (IsScalarTower.algebraMap_apply D₀ Cᵣ B c).symm)
    have hL : aeval (R := E) (w) (L₀) ≠ 0 := by
      intro hz
      have hX : α RatFunc.X ≠ 0 := (map_ne_zero α).mpr RatFunc.X_ne_zero
      apply hX
      rw [hα, hz, zero_pow (by omega), div_zero]
    let Z := projectivePrimeRatioField q none
    letI : Algebra Cᵣ Z := ((algebraMap B Z).comp (algebraMap Cᵣ B)).toAlgebra
    letI : IsScalarTower Cᵣ B Z := IsScalarTower.of_algebraMap_eq' rfl
    have hQ' : letI : Algebra D₀ B := δB.toAlgebra
        fiberVanishingIdeal (L := B) (fun i => projectivePrimeRatioCoordinate q none (some i)) ∈
          (extendCoefficientIdeal B (fiberVanishingIdeal (L := D₀)
            (rationalCoordinate (K := K) (n := 4)))).minimalPrimes := by
      change _ ∈ (Ideal.map (MvPolynomial.map δB)
        (fiberVanishingIdeal (L := D₀) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes
      rw [hδB]
      exact hQ
    obtain ⟨φ, hcoeff, hcoords, hpoly⟩ :=
      native_geometric_component_constructs_original_affine_tensor_realization
        H I E hH e B Z (L₀) hL α γ δ hδK
        (fun i => projectivePrimeRatioCoordinate q none (some i)) hQ' hcontract
    refine ⟨δB, ?_, ?_⟩
    · intro c
      change algebraMap Cᵣ B (δ (algebraMap K D₀ c)) = _
      rw [hδK]
    · refine ⟨?_, q, hqa, hQ', hboundary, φ, ?_, hcoords, hpoly⟩
      · exact (congrArg (fun a : Algebra D₀ B => @Algebra.IsAlgebraic D₀ B _ _ a) hDB).mpr halgB
      · intro b
        exact hcoeff b

end DimensionFourDependence
