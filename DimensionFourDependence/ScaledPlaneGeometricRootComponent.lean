import DimensionFourDependence.ScaledPlaneGeometricTensorComponent
import DimensionFourDependence.GeometricComponentSpecifiedRoots

/-! # Original finite root equations on the same fixed-vertex geometric component -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1500000
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
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "B" => AlgebraicClosure Cᵣ
local notation "σ" => (algebraMap Cᵣ B).comp (RatFunc.C.comp RatFunc.C)
local notation "H₀" => (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))

local instance scaledPlaneGeometricRootComponentDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

include hvertex e

/-- The original alternatives construct a single actual geometric
component through the fixed vertex together with the original finite
root covectors and their exact equations, or retain the full cone form.
The component, original tensor embedding, all coefficient labels and
nonzero numerator and denominator belong to the same realization. -/
theorem actual_affine_root_alternatives_construct_same_geometric_vertex_component_and_root_equations
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ δB : D₀ →+* B,
        (∀ c : K, δB (algebraMap K D₀ c) = (σ) ((ι) c)) ∧
        letI : Algebra D₀ B := δB.toAlgebra
        Algebra.IsAlgebraic D₀ B ∧
        ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) B),
          ∃ hqa : X none ∉ q.asHomogeneousIdeal,
            let Z := projectivePrimeRatioField q none
            let x : Fin 4 → Z := fun i => projectivePrimeRatioCoordinate q none (some i)
            let y : Fin 4 → B := fun i => δB (fullOutputCoordinate (K := K) (H₀) i)
            fiberVanishingIdeal (L := B) x ∈
              (extendCoefficientIdeal B (fiberVanishingIdeal (L := D₀)
                (rationalCoordinate (K := K) (n := 4)))).minimalPrimes ∧
            fourthAxisAffineInfinityPoint B ∈ projectiveClosureSet (L := B) x ∧
            ∃ φ : F₀ →+* Z,
              (∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z ((σ) b)) ∧
              (∀ i, φ ((xₐ) i) = x i) ∧
              OriginalFiniteRootEquationsOnRealization H I E hH hd hind hGauss φ (σ) x y := by
  rcases actual_affine_root_alternatives_construct_geometric_tensor_vertex_component_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨δB, hδK, halg, q, hqa, hQ, hboundary, φ, hcoeff, hcoords, _hpoly⟩
  · exact Or.inl hcone
  · right
    letI : Algebra D₀ B := δB.toAlgebra
    let Z := projectivePrimeRatioField q none
    let x : Fin 4 → Z := fun i => projectivePrimeRatioCoordinate q none (some i)
    have hσK (c : K) : (σ) ((ι) c) = δB (algebraMap K D₀ c) := (hδK c).symm
    have hroot :=
      full_generic_component_tensor_embedding_retains_original_finite_root_equations
        H I E hH hd hind hGauss δB (σ) hσK x φ hcoeff hcoords hdata hQ
    exact ⟨δB, hδK, halg, q, hqa, hQ, hboundary, φ, hcoeff, hcoords,
      hroot⟩

end DimensionFourDependence
