import DimensionFourDependence.ScaledPlaneVertexGenericGraph
import DimensionFourDependence.NativeVertexGermCoordinates
import DimensionFourDependence.GenericGraphVertexInfinity

/-! # The actual scaled-plane vertex lies over the unspecialized level field -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology
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

local instance scaledPlaneGenericLevelBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneGenericLevelBoundaryAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex

/-- The actual chosen normal form vanishes at the actual fixed source
vertex, with no supplied incidence hypothesis. -/
theorem actual_chosen_normal_mem_fixed_vertex_ideal :
    (L₀) ∈ (fourthAxisProjectivePoint E).asHomogeneousIdeal := by
  apply (projectiveCoordinatePoint_mem_homogeneous _ _ (linearFormPolynomial_homogeneous _)).mpr
  simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    Fin.snoc_last, mul_one, zero_add]
  exact extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex 0

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The original scaled-plane base component constructs an embedding
of the entire rational level field into the native source function field.
Over that same embedding its L-normalized four source coordinates have
the original fixed vertex at infinity. This keeps the level variable
free and preserves every coefficient of E. -/
theorem scaled_plane_base_component_constructs_actual_generic_level_vertex_infinity
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s n : Fin 4 → E) (hnlast : n (Fin.last 3) = 0)
    (hnvalue : aeval (extendedClosedGaussAffineTensorCoordinate H I E) ((O) n) ≠ 0)
    (a : E) (ha : a ≠ 0)
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
        fourthAxisAffineInfinityPoint (RatFunc E) ∈
          projectiveClosureSet (L := RatFunc E) (fun i => (w) i / aeval (w) (L₀)) := by
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
  exact rational_graph_retains_fixed_vertex_at_generic_level (k := E)
    (aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d) hker
    (fun i => (w) i / aeval (w) (L₀)) (aeval (w) (L₀) / (w) (Fin.last 3))
    (fun j => j.elim (extendedClosedGaussPolynomialCoefficientGerm H I E hH e (L₀) z (Fin.last 3) hz)
      (fun i => extendedClosedGaussPolynomialCoefficientGerm H I E hH e (X i) z (Fin.last 3) hz))
    hcoords hres

/-- The original affine root alternatives construct the unspecialized
level-field boundary, or retain their full cone form. The homogeneous
pencil, base component, native power relation, and local graph are all
constructed internally from those original alternatives. -/
theorem actual_affine_root_alternatives_construct_generic_level_vertex_boundary_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n : Fin 4 → E) (a : E), s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧
        a ≠ 0 ∧ aeval (xₐ) ((O) n) ≠ 0 ∧
        aeval (w) ((O) s) = algebraMap E (N).functionField (a ^ d) * (aeval (w) (L₀)) ^ d ∧
        ∃ α : RatFunc E →ₐ[E] (N).functionField,
          α RatFunc.X = aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d ∧
          letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
          fourthAxisAffineInfinityPoint (RatFunc E) ∈
            projectiveClosureSet (L := RatFunc E) (fun i => (w) i / aeval (w) (L₀)) := by
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
    obtain ⟨hs, hH4, α, hα, hboundary⟩ :=
      scaled_plane_base_component_constructs_actual_generic_level_vertex_infinity H I E hd hH hind hGauss
        hvertex e p q hq0 hrel hparameter s n hnlast hnvalue a ha hpower hbase Q hQ
    exact ⟨s, n, a, hs, hnlast, ha, hnvalue, hpower, α, hα, hboundary⟩
  · exact Or.inl ⟨r, hr0, hcone⟩

end DimensionFourDependence
