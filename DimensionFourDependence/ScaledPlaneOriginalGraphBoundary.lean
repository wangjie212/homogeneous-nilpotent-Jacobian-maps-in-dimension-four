import DimensionFourDependence.ScaledPlaneGeometricFullOutputBoundary
import DimensionFourDependence.NativeGeometricGraphCoefficients
import DimensionFourDependence.SpecifiedGraphCoefficientExtension
import DimensionFourDependence.CompatibleSourceBoundaryTransport

/-! # The fixed-vertex component is an actual boundary of the original graph fiber -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra
  coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
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
local notation "L" => coefficientField (K := K)
  (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField
local notation "B" => AlgebraicClosure Cᵣ
local notation "ζ" => (fun j : Option (Fin 4) => j.elim 0 (Fin.snoc (0 : Fin 3 → B) 1))

local instance scaledPlaneOriginalGraphBoundaryDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance scaledPlaneOriginalGraphBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneOriginalGraphBoundaryExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hrank hvertex e

/-- The actual root alternatives produce either their full cone form
or a fixed-vertex boundary of this specified original graph fiber.
The same source, full graph coefficient field and original tensor are
realized together, with algebraic geometric constants and the entire
original finite coefficient realization retained. -/
theorem actual_affine_root_alternatives_construct_original_graph_tensor_vertex_boundary_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) B),
        ∃ hqa : X none ∉ q.asHomogeneousIdeal,
          ∃ (f : S₀ →+* projectivePrimeRatioField q none) (g : (L) →+* B)
            (φ : F₀ →+* projectivePrimeRatioField q none),
            (∀ i, f (rationalCoordinate (K := K) i) = projectivePrimeRatioCoordinate q none (some i)) ∧
            (∀ l : L, algebraMap B (projectivePrimeRatioField q none) (g l) = f (l : S₀)) ∧
            (∀ c : C₀, g ((a) c) = algebraMap Cᵣ B (RatFunc.C (RatFunc.C (algebraMap C₀ E c)))) ∧
            (∀ s : S₀, φ (algebraMap T₀ F₀ (s ⊗ₜ[C₀] (1 : E))) = f s) ∧
            (∀ b : E, φ (algebraMap E F₀ b) = algebraMap B (projectivePrimeRatioField q none)
              (algebraMap Cᵣ B (RatFunc.C (RatFunc.C b)))) ∧
            (∀ i, φ ((xₐ) i) = projectivePrimeRatioCoordinate q none (some i)) ∧
            letI : Algebra (L) B := g.toAlgebra
            Algebra.IsAlgebraic (L) B ∧ ∃ hz : (ζ) ≠ 0,
              projectiveFieldPoint (E := L) (ζ) hz ∈ projectiveClosureSet («L» := L)
                (rationalCoordinate (K := K) (n := 4)) := by
  rcases actual_affine_root_alternatives_construct_geometric_full_output_vertex_boundary_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, bS, bN, u, _hs, _hnlast, _hu, _hLI, _hsS, _hnS, _hsN, _hnN, α, hα,
        γ, _hγ, δ, hδK, _hδY, _halg, halgB, q, hqa, hQ, hcontract, hboundary⟩
  · exact Or.inl hcone
  · right
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
    letI : Algebra D₀ Cᵣ := δ.toAlgebra
    let δB : D₀ →+* B := (algebraMap Cᵣ B).comp δ
    have hδB : δB = algebraMap D₀ B := by
      apply RingHom.ext
      intro c
      exact (IsScalarTower.algebraMap_apply D₀ Cᵣ B c).symm
    have hL : aeval (R := E) (w) (L₀) ≠ 0 := by
      intro hz
      have hX : α RatFunc.X ≠ 0 := (map_ne_zero α).mpr RatFunc.X_ne_zero
      apply hX
      rw [hα, hz, zero_pow (by omega), div_zero]
    let Z := projectivePrimeRatioField q none
    letI : Algebra Cᵣ Z := ((algebraMap B Z).comp (algebraMap Cᵣ B)).toAlgebra
    letI : IsScalarTower Cᵣ B Z := IsScalarTower.of_algebraMap_eq' rfl
    have hQ' : letI : Algebra D₀ B := δB.toAlgebra
        fiberVanishingIdeal («L» := B) (fun i => projectivePrimeRatioCoordinate q none (some i)) ∈
          (extendCoefficientIdeal B (fiberVanishingIdeal («L» := D₀)
            (rationalCoordinate (K := K) (n := 4)))).minimalPrimes := by
      change _ ∈ (Ideal.map (MvPolynomial.map δB)
        (fiberVanishingIdeal («L» := D₀) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes
      rw [hδB]
      exact hQ
    obtain ⟨f, g, φ, hfx, hg, _hgK, hgC, hsource, hcoeff, hcoords, hgD⟩ :=
      native_geometric_component_constructs_same_source_graph_and_tensor_realizations
        H hrank I p hY h hh E hH e B Z (L₀) hL α γ δ hδK
        (fun i => projectivePrimeRatioCoordinate q none (some i)) hQ' hcontract
    have hgD' (d : D₀) (l : L) (hl : (l : S₀) = (d : S₀)) : g l = algebraMap D₀ B d :=
      (hgD d l hl).trans (DFunLike.congr_fun hδB d)
    letI : Algebra.IsAlgebraic D₀ B := halgB
    have halgL := compatible_full_output_graph_embedding_is_algebraic H hrank p hY g hgD'
    letI : Algebra (L) B := g.toAlgebra
    have hz : (ζ) ≠ 0 := option_graph_coordinates_ne_zero _ fourthAxisVector_ne_zero _
    have hboundaryB : projectiveFieldPoint (E := B) (ζ) hz ∈
        projectiveClosureSet («L» := B) (fun i => projectivePrimeRatioCoordinate q none (some i)) := by
      rw [projectiveFieldPoint_self_eq_coordinatePoint]
      exact hboundary
    have hboundaryL := compatible_source_boundary_mem_original_coefficient_closure
      f g (rationalCoordinate (K := K) (n := 4))
      (fun i => projectivePrimeRatioCoordinate q none (some i)) (fun l => (hg l).symm) hfx
      (ζ) hz hboundaryB
    exact ⟨q, hqa, f, g, φ, hfx, hg, hgC, hsource, hcoeff, hcoords, halgL, hz, hboundaryL⟩

end DimensionFourDependence
