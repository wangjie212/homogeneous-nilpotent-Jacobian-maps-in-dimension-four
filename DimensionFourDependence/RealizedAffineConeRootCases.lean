import DimensionFourDependence.ClosedGaussAlgebraicRealization
import DimensionFourDependence.AffineFixedVertexRootAlternatives
import DimensionFourDependence.ParabolaFieldEmbedding

/-! # The complete affine root alternatives on one actual source realization

The common source and algebraic coefficient realization transfers the
entire affine root construction. Its output-linear power makes the root
algebraic over the geometric constants, hence an actual nonzero constant.
The first ruling row becomes the actual closed Gauss normal. Both root
alternatives therefore retain the same original source point and normal.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    {E G : Type u} [Field E] [Field G] [Algebra K E] [Algebra E G] [Algebra K G]
    [IsScalarTower K E G] [IsAlgClosed E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Both actual root alternatives with every scalar in the same
geometric constants, all coefficient algebraicity over the same closed
Gauss image, and the exact actual closed-normal linear form. -/
noncomputable def RealizedAffineFixedVertexRootAlternatives
    (e : RatFunc K ≃ₐ[K] C₀) (g : C₀ →ₐ[K] E) (z : Fin 4 → G) (y : Fin 4 → E) (d : ℕ) : Prop :=
  let ν : Fin 3 → E := fun i => g (e (closedGaussParameterNormal H I e i.castSucc))
  let Λ := ∑ i : Fin 3, algebraMap E G (ν i) * z i.castSucc
  ∃ (cS : Fin 4 → E) (R : E), (∀ i, IsAlgebraic g.fieldRange (cS i)) ∧ cS ≠ 0 ∧ R ≠ 0 ∧
    R ^ d = ∑ i : Fin 4, cS i * y i ∧
    (∃ cN : Fin 4 → E, (∀ i, IsAlgebraic g.fieldRange (cN i)) ∧ cN ≠ 0 ∧
      cN (Fin.last 3) = 0 ∧ (∑ i : Fin 4, cN i * y i) ≠ 0) ∧
    ((∃ γ : E, γ ≠ 0 ∧ IsAlgebraic g.fieldRange γ ∧ algebraMap E G R = algebraMap E G γ * Λ) ∨
      ∃ (V : Fin 3 → E) (a b : E), V ≠ 0 ∧ b ≠ 0 ∧
        (∀ i, IsAlgebraic g.fieldRange (V i)) ∧ IsAlgebraic g.fieldRange a ∧ IsAlgebraic g.fieldRange b ∧
        (∀ i : Fin 3, aeval z (H i.castSucc) = algebraMap E G (V i) * (algebraMap E G R) ^ d) ∧
        aeval z (H (Fin.last 3)) = algebraMap E G a * (algebraMap E G R) ^ d +
          algebraMap E G b * (algebraMap E G R) ^ (d - 1) * Λ)

variable (L : Type u) [Field L] [Algebra (closedGaussParameterField H I) L]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) L]

local notation "T₀" => S₀ ⊗[C₀] L
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I L

local instance realizedAffineConeRootCasesDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I L).isDomain

/-- The actual affine root alternatives transfer through every
compatible original source and closed Gauss realization. The root is
constructed in the geometric constants from its output-linear power. -/
theorem affine_fixed_vertex_root_alternatives_transfer_to_actual_source_realization
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] C₀) (f : S₀ →ₐ[K] G) (g : C₀ →ₐ[K] E)
    (hg : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀))
    (z : Fin 4 → G) (hf : ∀ i, f (rationalCoordinate (K := K) i) = z i)
    (y : Fin 4 → E) (hout : ∀ i, aeval z (H i) = algebraMap E G (y i))
    (hdata : ActualAffineFixedVertexRootAlternatives H I L hH hd hind hGauss) :
    RealizedAffineFixedVertexRootAlternatives H I e g z y d := by
  classical
  obtain ⟨σ, hσ, halg, φ, hsource, hcoeff, hcoords, hpoly⟩ :=
    compatible_closed_gauss_realization_extends_to_affine_source H I L f g hg
  let A := extendedClosedGaussChosenRulingMatrix H I L hH hd hind hGauss
  let ν : Fin 3 → E := fun i => g (e (closedGaussParameterNormal H I e i.castSucc))
  let Λ : G := ∑ i : Fin 3, algebraMap E G (ν i) * z i.castSucc
  let O := extendedClosedGaussOutputLinearPolynomial H I L
  have hφpoly (Q : MvPolynomial (Fin 4) K) :
      φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) Q)) = aeval z Q := by
    rw [hpoly]
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f Q
    rw [rationalCoordinate_aeval] at he
    simpa only [hf] using he
  have houtput (c : Fin 4 → L) : φ (aeval (xₐ) (O c)) =
      algebraMap E G (∑ i : Fin 4, σ (c i) * y i) := by
    have he : aeval (xₐ) (O c) = ∑ i : Fin 4,
        algebraMap L F₀ (c i) * aeval (xₐ)
          (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) (H i)) := by
      simp only [O, extendedClosedGaussOutputLinearPolynomial, map_sum, Algebra.smul_def,
        map_mul, AlgHom.commutes]
    rw [he]
    simp only [map_sum, map_mul, hcoeff, hφpoly, hout]
  have hnormal (i : Fin 3) : σ (A 0 i.castSucc) = ν i :=
    compatible_algebraic_coefficient_chosen_normal_value H I L g σ hσ hH hd hind hGauss e i.castSucc
  have hL : aeval (xₐ) (linearFormPolynomial (A 0)) =
      ∑ i : Fin 3, algebraMap L F₀ (A 0 i.castSucc) * (xₐ) i.castSucc := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
    have hcol : A 0 (Fin.last 3) = 0 :=
      extended_chosen_ruling_fixed_vertex_last_column H I L hH hd hind hGauss hvertex 0
    rw [Fin.sum_univ_castSucc, hcol, map_zero, zero_mul, add_zero]
  have hLmap : φ (aeval (xₐ) (linearFormPolynomial (A 0))) = Λ := by
    rw [hL]
    simp only [map_sum, map_mul, hcoeff, hcoords, hf, hnormal, Λ]
  have hLmap3 : φ (∑ i : Fin 3, algebraMap L F₀ (A 0 i.castSucc) * (xₐ) i.castSucc) = Λ := by
    rw [← hL]
    exact hLmap
  obtain ⟨cS, cM, cN, hS, _hM, _hN, hnlast, _hm, hr, hpower, halt⟩ := hdata
  let r : F₀ := aeval (xₐ) (O cN) * aeval (xₐ) (linearFormPolynomial (A 0)) / aeval (xₐ) (O cM)
  have hpow : (φ r) ^ d = algebraMap E G (∑ i : Fin 4, σ (cS i) * y i) := by
    rw [← map_pow]
    exact (congrArg φ hpower).trans (houtput cS)
  have hralg : IsAlgebraic E (φ r) := IsAlgebraic.of_pow hd (by rw [hpow]; exact isAlgebraic_algebraMap _)
  obtain ⟨R, hR⟩ := algebraic_value_preimage_of_isAlgClosed (φ r) hralg
  have hR0 : R ≠ 0 := by
    intro hz
    apply hr
    apply φ.injective
    change φ r = φ 0
    rw [← hR, hz, map_zero, map_zero]
  have hRp : R ^ d = ∑ i : Fin 4, σ (cS i) * y i := by
    apply (algebraMap E G).injective
    rw [map_pow, hR, hpow]
  have hS0 : (fun i => σ (cS i)) ≠ 0 := by
    intro hz
    apply hS
    funext i
    apply σ.injective
    simpa only [map_zero, Pi.zero_apply] using congrFun hz i
  have hNvalue : aeval (xₐ) (O cN) ≠ 0 := by
    intro hz
    apply hr
    rw [hz, zero_mul, zero_div]
  have hNout : (∑ i : Fin 4, σ (cN i) * y i) ≠ 0 := by
    intro hz
    apply hNvalue
    apply φ.injective
    rw [houtput, hz, map_zero, map_zero]
  have hN0 : (fun i => σ (cN i)) ≠ 0 := by
    intro hz
    apply hNout
    simp only [congrFun hz, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  refine ⟨fun i => σ (cS i), R, fun i => halg _, hS0, hR0, hRp,
    ⟨fun i => σ (cN i), fun i => halg _, hN0, ?_, hNout⟩, ?_⟩
  · change σ (cN (Fin.last 3)) = 0
    rw [hnlast, map_zero]
  rcases halt with ⟨γ, hγ, hplane⟩ | ⟨V, a, b, hV, hb, _hinc, hfirst, hlast⟩
  · left
    refine ⟨σ γ⁻¹, ?_, halg _, ?_⟩
    · exact (map_ne_zero σ).mpr (inv_ne_zero hγ)
    · have he := congrArg φ hplane
      change φ r = φ (algebraMap L F₀ γ⁻¹ * aeval (xₐ) (linearFormPolynomial (A 0))) at he
      simpa only [map_mul, hcoeff, hLmap, ← hR] using he
  · right
    have hV0 : (fun i => σ (V i)) ≠ 0 := by
      intro hz
      apply hV
      funext i
      apply σ.injective
      simpa only [map_zero, Pi.zero_apply] using congrFun hz i
    refine ⟨fun i => σ (V i), σ a, σ b, hV0, (map_ne_zero σ).mpr hb,
      fun _ => halg _, halg _, halg _, ?_, ?_⟩
    · intro i
      have he := congrArg φ (hfirst i)
      change φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) (H i.castSucc))) =
        φ (algebraMap L F₀ (V i) * r ^ d) at he
      simpa only [map_mul, map_pow, hcoeff, hφpoly, ← hR] using he
    · have he := congrArg φ hlast
      change φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) (H (Fin.last 3)))) =
        φ (algebraMap L F₀ a * r ^ d + algebraMap L F₀ b * r ^ (d - 1) *
          (∑ i : Fin 3, algebraMap L F₀ (A 0 i.castSucc) * (xₐ) i.castSucc)) at he
      simpa only [φ.map_add, φ.map_mul, φ.map_pow, hcoeff, hφpoly, hLmap3, ← hR] using he

end DimensionFourDependence
