import DimensionFourDependence.ClosedGaussAlgebraicRealization
import DimensionFourDependence.SpecifiedTensorFirstInvariant
import DimensionFourDependence.ParabolaFieldEmbedding

/-! # The complete affine cone form on the same geometric source realization -/

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

/-- The whole original cone presentation, with its nonzero root in
the actual geometric constants, its coefficients algebraic over the
same closed Gauss image, and its exact original normal linear form. -/
noncomputable def RealizedAffineFixedVertexFullCone
    (e : RatFunc K ≃ₐ[K] C₀) (g : C₀ →ₐ[K] E) (z : Fin 4 → G) (d : ℕ) : Prop :=
  let ν : Fin 3 → E := fun i => g (e (closedGaussParameterNormal H I e i.castSucc))
  let Λ := ∑ i : Fin 3, algebraMap E G (ν i) * z i.castSucc
  ∃ (R : E) (V : Fin 3 → E) (a b : E), R ≠ 0 ∧ V ≠ 0 ∧ b ≠ 0 ∧
    (∀ i, IsAlgebraic g.fieldRange (V i)) ∧ IsAlgebraic g.fieldRange a ∧
    IsAlgebraic g.fieldRange b ∧
    (∀ i : Fin 3, aeval z (H i.castSucc) = algebraMap E G (V i) * (algebraMap E G R) ^ d) ∧
    aeval z (H (Fin.last 3)) = algebraMap E G a * (algebraMap E G R) ^ d +
      algebraMap E G b * (algebraMap E G R) ^ (d - 1) * Λ ∧
    ν ⬝ᵥ V = 0

variable (L : Type u) [Field L] [Algebra (closedGaussParameterField H I) L]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) L]

local notation "T₀" => S₀ ⊗[C₀] L
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I L

local instance realizedAffineFullConeDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I L).isDomain

/-- The full affine cone formula transfers through any compatible
original source and closed Gauss realization. One nonzero directrix
coordinate constructs the nonzero scalar root in the geometric
constants; no output-linear power or scalar root is supplied. -/
theorem affine_full_cone_transfers_to_actual_source_realization
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] C₀) (f : S₀ →ₐ[K] G) (g : C₀ →ₐ[K] E)
    (hg : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀))
    (z : Fin 4 → G) (hf : ∀ i, f (rationalCoordinate (K := K) i) = z i)
    (y : Fin 4 → E) (hout : ∀ i, aeval z (H i) = algebraMap E G (y i))
    (r : F₀) (hr : r ≠ 0)
    (hcone : AffineSourceFixedVertexConeRootForm H I L hH hd hind hGauss r) :
    RealizedAffineFixedVertexFullCone H I e g z d := by
  classical
  obtain ⟨σ, hσ, halg, φ, _hsource, hcoeff, hcoords, hpoly⟩ :=
    compatible_closed_gauss_realization_extends_to_affine_source H I L f g hg
  let A := extendedClosedGaussChosenRulingMatrix H I L hH hd hind hGauss
  let ν : Fin 3 → E := fun i => g (e (closedGaussParameterNormal H I e i.castSucc))
  let Λ : G := ∑ i : Fin 3, algebraMap E G (ν i) * z i.castSucc
  have hφpoly (Q : MvPolynomial (Fin 4) K) :
      φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L) Q)) = aeval z Q := by
    rw [hpoly]
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f Q
    rw [rationalCoordinate_aeval] at he
    simpa only [hf] using he
  have hnormal (i : Fin 3) : σ (A 0 i.castSucc) = ν i :=
    compatible_algebraic_coefficient_chosen_normal_value H I L g σ hσ hH hd hind hGauss e i.castSucc
  have hLmap : φ (∑ i : Fin 3, algebraMap L F₀ (A 0 i.castSucc) * (xₐ) i.castSucc) = Λ := by
    simp only [map_sum, map_mul, hcoeff, hcoords, hf, hnormal, Λ]
  obtain ⟨V, a, b, hV, hb, hinc, hfirst, hlast⟩ := hcone
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, V j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hV (funext hn)
  have hjσ : σ (V j) ≠ 0 := (map_ne_zero σ).mpr hj
  have hjG : algebraMap E G (σ (V j)) ≠ 0 := (map_ne_zero (algebraMap E G)).mpr hjσ
  have hfirstMap (i : Fin 3) : algebraMap E G (y i.castSucc) =
      algebraMap E G (σ (V i)) * (φ r) ^ d := by
    have he := congrArg φ (hfirst i)
    change φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L)
      (H i.castSucc))) = φ (algebraMap L F₀ (V i) * r ^ d) at he
    simpa only [map_mul, map_pow, hcoeff, hφpoly, hout] using he
  have hpow : (φ r) ^ d = algebraMap E G (y j.castSucc / σ (V j)) := by
    rw [map_div₀]
    apply (eq_div_iff hjG).mpr
    exact (mul_comm _ _).trans (hfirstMap j).symm
  have hralg : IsAlgebraic E (φ r) := IsAlgebraic.of_pow hd
    (by rw [hpow]; exact isAlgebraic_algebraMap _)
  obtain ⟨R, hR⟩ := algebraic_value_preimage_of_isAlgClosed (φ r) hralg
  have hR0 : R ≠ 0 := by
    intro hz
    have he : φ r = φ 0 := hR.symm.trans
      ((congrArg (algebraMap E G) hz).trans
        ((algebraMap E G).map_zero'.trans φ.map_zero'.symm))
    exact hr (specified_original_affine_tensor_realization_injective H I L φ he)
  have hV0 : (fun i => σ (V i)) ≠ 0 := by
    intro hz
    exact hjσ (congrFun hz j)
  refine ⟨R, fun i => σ (V i), σ a, σ b, hR0, hV0, (map_ne_zero σ).mpr hb,
    fun _ => halg _, halg _, halg _, ?_, ?_, ?_⟩
  · intro i
    exact (hout i.castSucc).trans (by simpa only [← hR] using hfirstMap i)
  · have he := congrArg φ hlast
    change φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I L)
      (H (Fin.last 3)))) = φ (algebraMap L F₀ a * r ^ d + algebraMap L F₀ b * r ^ (d - 1) *
        (∑ i : Fin 3, algebraMap L F₀ (A 0 i.castSucc) * (xₐ) i.castSucc)) at he
    simpa only [φ.map_add, φ.map_mul, φ.map_pow, hcoeff, hφpoly, hLmap, ← hR, Λ] using he
  · have he := congrArg σ (hinc 0)
    change σ (∑ i : Fin 3, A 0 i.castSucc * V i) = σ 0 at he
    simpa only [map_sum, map_mul, hnormal, map_zero, ν, dotProduct] using he

end DimensionFourDependence
