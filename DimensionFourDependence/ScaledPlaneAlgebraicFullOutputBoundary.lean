import DimensionFourDependence.ScaledPlaneIndependentScaleBoundary
import DimensionFourDependence.NativeScaledFullOutputEmbedding
import DimensionFourDependence.AlgebraicCompatibleSourceComponent

/-! # The constructed scaled-plane boundary is over an actual algebraic extension of K(H) -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
local notation "H₀" => (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))

local instance scaledPlaneAlgebraicFullOutputBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneAlgebraicFullOutputBoundaryExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance scaledPlaneAlgebraicFullOutputBoundaryOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

include hvertex

/-- The original root alternatives construct a coefficient-preserving
algebraic extension of the entire original output field together with
the same original source realization and vertex boundary, or retain
their full cone form. Both generic parameters stay free throughout. -/
theorem actual_affine_root_alternatives_construct_algebraic_full_output_vertex_boundary_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n bS bN : Fin 4 → E) (a : E), s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧
        a ≠ 0 ∧ LinearIndependent E ![bS, bN] ∧
        s ⬝ᵥ bS = 1 ∧ n ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ n ⬝ᵥ bN = 1 ∧
        ∃ α : RatFunc E →ₐ[E] (N).functionField,
          α RatFunc.X = aeval (R := E) (w) ((O) n) / (aeval (R := E) (w) (L₀)) ^ d ∧
          letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
          ∃ γ : Cᵣ →ₐ[RatFunc E] Gᵣ, γ RatFunc.X = RatFunc.X ∧
            ∃ (δ : D₀ →+* Cᵣ) (Φ : S₀ →+* Gᵣ),
              (∀ c : K, δ (algebraMap K D₀ c) = RatFunc.C (RatFunc.C ((ι) c))) ∧
              (∀ i, δ (fullOutputCoordinate (K := K) (H₀) i) = RatFunc.X ^ d *
                RatFunc.C (RatFunc.C (a ^ d * bS i) + RatFunc.X * RatFunc.C (bN i))) ∧
              (∀ c : K, Φ (algebraMap K S₀ c) = RatFunc.C (algebraMap E (N).functionField ((ι) c))) ∧
              (∀ i : Fin 4, Φ (rationalCoordinate (K := K) i) = (vᵣ) i) ∧
              (∀ q : D₀, γ (δ q) = Φ (q : S₀)) ∧
              (letI : Algebra D₀ Cᵣ := δ.toAlgebra; Algebra.IsAlgebraic D₀ Cᵣ) ∧
              (letI : Algebra D₀ Cᵣ := δ.toAlgebra;
                letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra;
                fiberVanishingIdeal (L := Cᵣ) (vᵣ) ∈
                  (extendCoefficientIdeal Cᵣ (fiberVanishingIdeal (L := D₀)
                    (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) ∧
              (letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra;
                fourthAxisAffineInfinityPoint Cᵣ ∈ projectiveClosureSet (L := Cᵣ) (vᵣ)) := by
  rcases actual_affine_root_alternatives_construct_independently_scaled_generic_target_boundary_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, bS, bN, a, hs, hnlast, ha, hLI, hsS, hnS, hsN, hnN, α, hα, γ, hγ, hLscale, htarget, hboundary⟩
  · exact Or.inl hcone
  · right
    have hf : aeval (R := E) (w) ((O) n) / (aeval (R := E) (w) (L₀)) ^ d ≠ 0 := by
      rw [← hα]
      exact (map_ne_zero α).mpr RatFunc.X_ne_zero
    have hL : aeval (R := E) (w) (L₀) ≠ 0 := by
      intro he
      simp only [he, zero_pow (ne_of_gt hd), div_zero, ne_eq, not_true_eq_false] at hf
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    obtain ⟨δ, hδK, hδY, hcompat, halg⟩ :=
      native_scaled_generic_target_constructs_algebraic_full_output_embedding H I E hd hH e
        (L₀) hL s n bS bN hsS hnS hsN hnN a ha α γ hγ htarget
    let Φ := (nativeIndependentScaleSourceFieldHom H I E hH e (L₀) hL).toRingHom
    refine ⟨s, n, bS, bN, a, hs, hnlast, ha, hLI, hsS, hnS, hsN, hnN, α, hα,
      γ, hγ, δ, Φ, hδK, hδY, ?_, ?_, hcompat, halg, ?_, hboundary⟩
    · exact nativeIndependentScaleSourceFieldHom_coefficient H I E hH e (L₀) hL
    · exact nativeIndependentScaleSourceFieldHom_coordinate H I E hH e (L₀) hL
    · exact original_full_output_compatible_source_constructs_actual_component H δ γ.toRingHom Φ
        hcompat (vᵣ) (nativeIndependentScaleSourceFieldHom_coordinate H I E hH e (L₀) hL) halg

end DimensionFourDependence
