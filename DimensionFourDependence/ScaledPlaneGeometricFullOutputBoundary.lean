import DimensionFourDependence.ScaledPlaneAlgebraicFullOutputBoundary
import DimensionFourDependence.AlgebraicComponentTower
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The original scaled-plane vertex lies on a geometric full generic-fiber component -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

set_option maxHeartbeats 5000000
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equal original coordinate vectors define the same rational
projective point independently of their nonvanishing witnesses. -/
theorem projectiveCoordinatePoint_eq_of_coordinate_eq
    {F σ : Type*} [Field F] (b c : σ → F) (hb : b ≠ 0) (hc : c ≠ 0) (he : b = c) :
    projectiveCoordinatePoint b hb = projectiveCoordinatePoint c hc := by
  cases he
  rfl

universe u

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "F₀" => FractionRing (S₀ ⊗[C₀] E)
local notation "D₀" => polynomialOutputField H
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "vᵣ" => (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) (L₀)))
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField
local notation "B" => AlgebraicClosure Cᵣ
local notation "H₀" => (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))

local instance scaledPlaneGeometricFullOutputBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneGeometricFullOutputBoundaryExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

include hvertex

/-- The original root alternatives construct an actual geometric
full generic-fiber component whose own normalized source coordinates
have the original fixed vertex at infinity, or retain their full cone
form. The algebraically closed constants are an algebraic extension of
the same original full output embedding, and all intermediate original
source relations are retained. -/
theorem actual_affine_root_alternatives_construct_geometric_full_output_vertex_boundary_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n bS bN : Fin 4 → E) (a : E), s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧
        a ≠ 0 ∧ LinearIndependent E ![bS, bN] ∧
        s ⬝ᵥ bS = 1 ∧ n ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ n ⬝ᵥ bN = 1 ∧
        ∃ α : RatFunc E →ₐ[E] (N).functionField,
          α RatFunc.X = aeval (R := E) (w) ((O) n) / (aeval (R := E) (w) (L₀)) ^ d ∧
          letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
          ∃ γ : Cᵣ →ₐ[RatFunc E] Gᵣ, γ RatFunc.X = RatFunc.X ∧
            letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
            ∃ δ : D₀ →+* Cᵣ,
              (∀ c : K, δ (algebraMap K D₀ c) = RatFunc.C (RatFunc.C ((ι) c))) ∧
              (∀ i, δ (fullOutputCoordinate (K := K) (H₀) i) = RatFunc.X ^ d *
                RatFunc.C (RatFunc.C (a ^ d * bS i) + RatFunc.X * RatFunc.C (bN i))) ∧
              letI : Algebra D₀ Cᵣ := δ.toAlgebra
              Algebra.IsAlgebraic D₀ Cᵣ ∧ Algebra.IsAlgebraic D₀ B ∧
              ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) B),
                ∃ hqa : X none ∉ q.asHomogeneousIdeal,
                  fiberVanishingIdeal (L := B) (fun i => projectivePrimeRatioCoordinate q none (some i)) ∈
                    (extendCoefficientIdeal B (fiberVanishingIdeal (L := D₀)
                      (rationalCoordinate (K := K) (n := 4)))).minimalPrimes ∧
                  (fiberVanishingIdeal (L := B) (fun i => projectivePrimeRatioCoordinate q none (some i))).comap
                    (MvPolynomial.map (algebraMap Cᵣ B)) = fiberVanishingIdeal (L := Cᵣ) (vᵣ) ∧
                  fourthAxisAffineInfinityPoint B ∈ projectiveClosureSet (L := B)
                    (fun i => projectivePrimeRatioCoordinate q none (some i)) := by
  rcases actual_affine_root_alternatives_construct_algebraic_full_output_vertex_boundary_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, bS, bN, a, hs, hnlast, ha, hLI, hsS, hnS, hsN, hnN, α, hα, γ, hγ,
        δ, Φ, hδK, hδY, hΦK, hΦX, hcompat, halg, hcomponent, hboundary⟩
  · exact Or.inl hcone
  · right
    refine ⟨s, n, bS, bN, a, hs, hnlast, ha, hLI, hsS, hnS, hsN, hnN, α, hα, ?_⟩
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    refine ⟨γ, hγ, ?_⟩
    letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
    refine ⟨δ, hδK, hδY, ?_⟩
    letI : Algebra D₀ Cᵣ := δ.toAlgebra
    letI : Algebra.IsAlgebraic D₀ Cᵣ := halg
    letI : IsScalarTower D₀ Cᵣ B := inferInstance
    have halgB : Algebra.IsAlgebraic D₀ B := Algebra.IsAlgebraic.trans D₀ Cᵣ B
    let b : Option (Fin 4) → Cᵣ := fun j => j.elim 0 (Fin.snoc (0 : Fin 3 → Cᵣ) 1)
    have hb : b ≠ 0 := option_graph_coordinates_ne_zero _ fourthAxisVector_ne_zero _
    obtain ⟨hbB, q, hqa, hQ, hcontract, hboundaryB⟩ :=
      rational_boundary_constructs_component_over_algebraic_coefficient_tower (A := B)
        (rationalCoordinate (K := K) (n := 4)) (vᵣ) hcomponent b hb hboundary
    have hvec : (fun j => algebraMap Cᵣ B (b j)) =
        (fun j : Option (Fin 4) => j.elim 0 (Fin.snoc (0 : Fin 3 → B) 1)) := by
      funext j
      cases j with
      | none => simp only [b, Option.elim_none, map_zero]
      | some i =>
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [b, Option.elim_some, Fin.snoc_last, map_one]
        · simp only [b, Option.elim_some, Fin.snoc_castSucc, Pi.zero_apply, map_zero]
    have hpoint : projectiveCoordinatePoint (fun j => algebraMap Cᵣ B (b j)) hbB =
        fourthAxisAffineInfinityPoint B := by
      exact projectiveCoordinatePoint_eq_of_coordinate_eq _ _ hbB _ hvec
    refine ⟨halg, halgB, q, hqa, hQ, hcontract, ?_⟩
    rwa [← hpoint]

end DimensionFourDependence
