import DimensionFourDependence.ScaledPlaneGenericTargetFiber
import DimensionFourDependence.GenericGraphScaledVertexInfinity
import DimensionFourDependence.IndependentScaleHomogeneousValues

/-! # The actual scaled-plane boundary retains both independent target parameters -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
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
local notation "F₀" => FractionRing (FractionRing (MvPolynomial (Fin 4) K) ⊗[C₀] E)
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "v" => (fun i => (w) i / aeval (w) (L₀))
local notation "vᵣ" => (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (w) (L₀)))

local instance scaledPlaneIndependentScaleBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneIndependentScaleBoundaryAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

include hvertex

/-- The original scaled-plane base component constructs the boundary
over E(lambda)(r), with lambda the actual quotient and r transcendental
over the entire original native source field. -/
theorem scaled_plane_base_component_constructs_independently_scaled_generic_vertex_boundary
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s n : Fin 4 → E) (hnlast : n (Fin.last 3) = 0)
    (hnvalue : aeval (xₐ) ((O) n) ≠ 0) (a : E) (ha : a ≠ 0)
    (hpower : aeval (w) ((O) s) =
      algebraMap E (N).functionField (a ^ d) * (aeval (w) (L₀)) ^ d)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ α : RatFunc E →ₐ[E] (N).functionField,
        α RatFunc.X = aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d ∧
        letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
        ∃ γ : RatFunc (RatFunc E) →ₐ[RatFunc E] RatFunc (N).functionField,
          γ RatFunc.X = RatFunc.X ∧
          letI : Algebra (RatFunc (RatFunc E)) (RatFunc (N).functionField) := γ.toRingHom.toAlgebra
          fourthAxisAffineInfinityPoint (RatFunc (RatFunc E)) ∈
            projectiveClosureSet (L := RatFunc (RatFunc E)) (vᵣ) := by
  obtain ⟨hs, hH4, x, z, hxz, himage, hz, hLvalue, hker⟩ :=
    scaled_plane_base_component_constructs_free_generic_graph_at_vertex H I E hd hH hind hGauss
      hvertex e p q hq hrel hparameter s n hnlast hnvalue a ha hpower hbase Q hQ
  let R := (N).presheaf.stalk z
  letI : Algebra E R := (((N).presheaf.germ ⊤ z (by trivial)).hom.comp
    (extendedClosedGaussGlobalConstantHom H I E hH e)).toAlgebra
  letI : IsScalarTower E R (N).functionField := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (extendedClosedGaussGlobalConstantHom_germ_value H I E hH e c z).symm)
  have hLvertex := actual_chosen_normal_mem_fixed_vertex_ideal H I E hd hH hind hGauss hvertex
  obtain ⟨hcoords, hres⟩ := native_vertex_affine_projective_germ_coordinates H I E hH e
    (L₀) (linearFormPolynomial_homogeneous _) hLvertex hLvalue z hz himage
  refine ⟨hs, hH4, ?_⟩
  exact rational_graph_constructs_independently_scaled_generic_vertex_boundary (k := E)
    (aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d) hker (v)
    (aeval (w) (L₀) / (w) (Fin.last 3))
    (fun j => j.elim (extendedClosedGaussPolynomialCoefficientGerm H I E hH e (L₀) z (Fin.last 3) hz)
      (fun i => extendedClosedGaussPolynomialCoefficientGerm H I E hH e (X i) z (Fin.last 3) hz))
    hcoords hres

/-- The original root alternatives construct an affine source solution
over the entire two-variable rational target field, and its original
vertex at infinity, or retain their full cone alternative. Both target
parameters remain free; the original source and coefficient labels are
preserved in all four component equations. -/
theorem actual_affine_root_alternatives_construct_independently_scaled_generic_target_boundary_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n bS bN : Fin 4 → E) (a : E), s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧
        a ≠ 0 ∧ LinearIndependent E ![bS, bN] ∧
        s ⬝ᵥ bS = 1 ∧ n ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ n ⬝ᵥ bN = 1 ∧
        ∃ α : RatFunc E →ₐ[E] (N).functionField,
          α RatFunc.X = aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d ∧
          letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
          ∃ γ : RatFunc (RatFunc E) →ₐ[RatFunc E] RatFunc (N).functionField,
            γ RatFunc.X = RatFunc.X ∧ aeval (vᵣ) (L₀) = RatFunc.X ∧
            (∀ i, aeval (vᵣ) (MvPolynomial.map (ι) (H i)) =
              γ (RatFunc.X ^ d * RatFunc.C
                (RatFunc.C (a ^ d * bS i) + RatFunc.X * RatFunc.C (bN i)))) ∧
            letI : Algebra (RatFunc (RatFunc E)) (RatFunc (N).functionField) := γ.toRingHom.toAlgebra
            fourthAxisAffineInfinityPoint (RatFunc (RatFunc E)) ∈
              projectiveClosureSet (L := RatFunc (RatFunc E)) (vᵣ) := by
  obtain ⟨p, q, D, Q, hD, hp0, hq0, hp, hq, hrel, hparameter, hQ, hhQ, hoff⟩ :=
    actual_closed_gauss_parameter_constructs_nonempty_base_component H hH I e
  obtain ⟨s, n, r, hs0, hn0, hnlast, hnvalue, hnbase, hr0, hroot, halt⟩ :=
    actual_affine_root_alternatives_construct_base_power_relation H I E hH hd hind hGauss e
      hvertex p q hq0 hrel hparameter hdata
  rcases halt with ⟨a, ha, hscaled, hbase⟩ | hcone
  · right
    have hpowerAffine : aeval (xₐ) ((O) s) =
        algebraMap E (F₀) (a ^ d) * (aeval (xₐ) (L₀)) ^ d := by
      rw [← hroot, hscaled, mul_pow, map_pow]
    have hpower := actual_affine_scaled_power_identity_constructs_native_power H I E hH e
      ((O) s) (L₀) (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH s)
        (linearFormPolynomial_homogeneous _) (a ^ d) hpowerAffine
    obtain ⟨hs, hH4, α, hα, γ, hγ, hboundary⟩ :=
      scaled_plane_base_component_constructs_independently_scaled_generic_vertex_boundary H I E hd hH hind hGauss
        hvertex e p q hq0 hrel hparameter s n hnlast hnvalue a ha hpower hbase Q hQ
    have hn : aeval (w) ((O) n) ≠ 0 := by
      intro he
      exact hnvalue ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e
        ((O) n) (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n)).mpr he)
    obtain ⟨hL, bS, bN, hLI, hsS, hnS, hsN, hnN, htargets⟩ :=
      actual_scaled_plane_normalized_source_constructs_generic_target_equations H I E hd hH hind hGauss
        hvertex e s n hs hnlast hn (a ^ d) hpower α hα
    refine ⟨s, n, bS, bN, a, hs, hnlast, ha, hLI, hsS, hnS, hsN, hnN, α, hα, ?_⟩
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    refine ⟨γ, hγ, ?_, ?_, hboundary⟩
    · rw [independent_scale_homogeneous_polynomial_value (L₀) (linearFormPolynomial_homogeneous _),
        hL, map_one, pow_one, mul_one]
    · intro i
      exact independent_scale_homogeneous_target_equation γ hγ (MvPolynomial.map (ι) (H i))
        ((hH i).map _) (v) _ (htargets i)
  · exact Or.inl ⟨r, hr0, hcone⟩

end DimensionFourDependence
