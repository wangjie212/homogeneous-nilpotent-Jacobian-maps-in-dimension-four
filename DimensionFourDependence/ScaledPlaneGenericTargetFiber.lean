import DimensionFourDependence.ScaledPlaneGenericLevelBoundary
import DimensionFourDependence.FixedVertexScaledDualOutputBasis

/-! # Exact original target equations over the free rational ruling field -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

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

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "v" => (fun i => (w) i / aeval (w) (L₀))
local notation "F₀" => FractionRing (FractionRing (MvPolynomial (Fin 4) K) ⊗[closedGaussParameterField H I] E)

local instance scaledPlaneGenericTargetFiberIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneGenericTargetFiberAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex

/-- A free graph parameter and the original power identity yield the
exact four original component equations over E(lambda), with L = 1.
The output basis and both of its dual pairings are constructed. -/
theorem actual_scaled_plane_normalized_source_constructs_generic_target_equations
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0) (hnlast : n (Fin.last 3) = 0)
    (hn : aeval (w) ((O) n) ≠ 0) (c : E)
    (hpower : aeval (w) ((O) s) = algebraMap E (N).functionField c * (aeval (w) (L₀)) ^ d)
    (α : RatFunc E →ₐ[E] (N).functionField)
    (hα : α RatFunc.X = aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d) :
    aeval (v) (L₀) = 1 ∧
      ∃ bS bN : Fin 4 → E, LinearIndependent E ![bS, bN] ∧
        s ⬝ᵥ bS = 1 ∧ n ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ n ⬝ᵥ bN = 1 ∧
        ∀ i, aeval (v) (MvPolynomial.map (ι) (H i)) =
          α (RatFunc.C (c * bS i) + RatFunc.X * RatFunc.C (bN i)) := by
  have hf : aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d ≠ 0 := by
    rw [← hα]
    exact (map_ne_zero α).mpr RatFunc.X_ne_zero
  have hL : aeval (w) (L₀) ≠ 0 := by
    intro he
    simp only [he, zero_pow (ne_of_gt hd), div_zero, ne_eq, not_true_eq_false] at hf
  have hscale (P : MvPolynomial (Fin 4) E) {D : ℕ} (hP : P.IsHomogeneous D) :
      aeval (v) P = aeval (w) P / (aeval (w) (L₀)) ^ D := by
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
      homogeneous_aeval_scale_indexed P hP (w) (aeval (w) (L₀))⁻¹
  refine ⟨?_, ?_⟩
  · rw [hscale (L₀) (linearFormPolynomial_homogeneous _), pow_one, div_self hL]
  · obtain ⟨bS, bN, hLI, hbS, hbN, hsS, hnS, hsN, hnN, hspan⟩ :=
      fixed_vertex_scaled_covectors_construct_dual_output_basis H I E hH e hd hind hGauss
        hvertex s n hs hnlast hn
    refine ⟨bS, bN, hLI, hsS, hnS, hsN, hnN, fun i => ?_⟩
    have hαC (b : E) : α (RatFunc.C b) = algebraMap E (N).functionField b := α.commutes b
    rw [hscale _ ((hH i).map _), hspan i, hpower]
    simp only [map_add, map_mul, hαC, hα]
    field_simp [hL]

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The original root alternatives yield an actual affine solution of
the generic ruling target and the original vertex at infinity in that
solution's projective closure, or retain their full cone form. The
ruling parameter is transcendental and no scalar level is chosen.
The independent homogeneous target scale is not yet adjoined. -/
theorem actual_affine_root_alternatives_construct_generic_target_solution_vertex_boundary_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n bS bN : Fin 4 → E) (a : E), s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧
        a ≠ 0 ∧ LinearIndependent E ![bS, bN] ∧
        s ⬝ᵥ bS = 1 ∧ n ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ n ⬝ᵥ bN = 1 ∧
        ∃ α : RatFunc E →ₐ[E] (N).functionField,
          α RatFunc.X = aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d ∧
          aeval (v) (L₀) = 1 ∧
          (∀ i, aeval (v) (MvPolynomial.map (ι) (H i)) =
            α (RatFunc.C (a ^ d * bS i) + RatFunc.X * RatFunc.C (bN i))) ∧
          letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
          fourthAxisAffineInfinityPoint (RatFunc E) ∈ projectiveClosureSet (L := RatFunc E) (v) := by
  rcases actual_affine_root_alternatives_construct_generic_level_vertex_boundary_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, a, hs, hnlast, ha, hnvalue, hpower, α, hα, hboundary⟩
  · exact Or.inl hcone
  · right
    have hn : aeval (w) ((O) n) ≠ 0 := by
      intro hzero
      exact hnvalue ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff
        H I E hH e ((O) n) (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n)).mpr hzero)
    obtain ⟨hL, bS, bN, hLI, hsS, hnS, hsN, hnN, htargets⟩ :=
      actual_scaled_plane_normalized_source_constructs_generic_target_equations H I E hd hH hind hGauss
        hvertex e s n hs hnlast hn (a ^ d) hpower α hα
    exact ⟨s, n, bS, bN, a, hs, hnlast, ha, hLI, hsS, hnS, hsN, hnN, α, hα, hL, htargets, hboundary⟩

end DimensionFourDependence
