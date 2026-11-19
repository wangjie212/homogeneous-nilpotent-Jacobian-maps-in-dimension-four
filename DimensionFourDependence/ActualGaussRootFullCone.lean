import DimensionFourDependence.ScaledPlaneOriginalGraphBoundary
import DimensionFourDependence.ScaledPlaneOriginalPowerData
import DimensionFourDependence.CanonicalScaledPlaneBoundaryContradiction

/-! # Actual chosen Gauss root normal forms construct the full affine cone form -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hN : IsNilpotent (jac H)) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "hd₀" => (lt_trans Nat.zero_lt_one hd)
local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH (hd₀) hind hGauss 0)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "B" => AlgebraicClosure Cᵣ

local instance actualGaussRootFullConeDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance actualGaussRootFullConeIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualGaussRootFullConeExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hrank hN hvertex

/-- The actual chosen Gauss root normal forms construct the complete
affine fixed-vertex cone form. In the scaled-plane case the original
canonical numerator, original power equation and same compatible
geometric boundary give a contradiction unless the full cone form
has already been obtained. No independent boundary or coefficient
compatibility assumption is supplied. -/
theorem actual_chosen_gauss_root_normal_forms_construct_full_affine_cone
    (hdata : ActualChosenGaussRootNormalForms H I E hH e (hd₀) hind hGauss) :
    ∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH (hd₀) hind hGauss r := by
  have hweak := actual_chosen_root_normal_forms_construct_affine_fixed_vertex_alternatives
    H I E hH e (hd₀) hind hGauss hvertex hdata
  obtain ⟨cS, cM, cN, r, _hS, _hM, _hNc, hr, _hpower, hm, hformula, halt, hnumerator⟩ := hdata
  have hL : aeval (R := E) (w) (L₀) = ∑ i : Fin 4,
      algebraMap E (N).functionField
        (extendedClosedGaussChosenRulingMatrix H I E hH (hd₀) hind hGauss 0 i) * (w) i := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  have hroot : r = aeval (R := E) (w) ((O) cN) * aeval (R := E) (w) (L₀) /
      aeval (R := E) (w) ((O) cM) := by rw [hL]; exact hformula
  rcases halt with ⟨gamma, hgamma, _hMN, hplane, hplanePower⟩ |
      ⟨_hMN, _beta, _hbeta, _hSN, hfactor⟩
  · have hLn : aeval (R := E) (w) (L₀) ≠ 0 := by
      intro hzero
      apply hr
      rw [hplane, ← hL, hzero, mul_zero]
    have hpowerN : aeval (R := E) (w) ((O) cS) =
        algebraMap E (N).functionField ((gamma⁻¹) ^ d) * (aeval (R := E) (w) (L₀)) ^ d := by
      simpa only [hL, map_pow] using hplanePower
    obtain ⟨hs, hrA, hpowerA⟩ := original_native_scaled_power_constructs_specified_affine_root
      H I E (hd₀) hH hind hGauss hvertex e cS gamma⁻¹ (inv_ne_zero hgamma) hLn hpowerN
    have hn : aeval (R := E) (w) ((O) cN) ≠ 0 := by
      intro hzero
      apply hr
      rw [hroot, hzero, zero_mul, zero_div]
    obtain ⟨p, hY, h, hh, hcN⟩ := hnumerator
    rw [hcN] at hn
    rcases actual_affine_root_alternatives_construct_original_graph_tensor_vertex_boundary_or_full_cone
      H hrank I p hY h hh E (hd₀) hH hind hGauss hvertex e hweak with hcone |
        ⟨q, _hqa, f, g, φ, hfx, hg, hσ, hsource, hcoeff, hcoords, halg, hz, hpoint⟩
    · exact hcone
    · let σ : E →+* B := (algebraMap Cᵣ B).comp (RatFunc.C.comp RatFunc.C)
      apply False.elim
      exact canonical_scaled_plane_root_has_no_actual_fixed_vertex_boundary
        H hrank I p hY h hh E hd hH hN hind hGauss hvertex e cS hs hn
        gamma⁻¹ (inv_ne_zero hgamma)
        (algebraMap E F₀ gamma⁻¹ * aeval (xₐ) (L₀)) hrA rfl hpowerA
        f g σ φ hg hσ hsource hcoeff (fun i => (hcoords i).trans (hfx i).symm)
        halg (fun j : Option (Fin 4) => j.elim 0 (Fin.snoc (0 : Fin 3 → B) 1)) hz hpoint
        rfl (by intro i; simp only [Option.elim_some, Fin.snoc_castSucc, Pi.zero_apply])
        (by simp only [Option.elim_some, Fin.snoc_last])
  · obtain ⟨_hmA, hrA, hconeA⟩ :=
      native_characteristic_root_constructs_affine_source_fixed_vertex_cone_form
        H I E hH e (hd₀) hind hGauss hvertex cM cN r hr hm hroot hfactor
    exact ⟨_, hrA, hconeA⟩

end DimensionFourDependence
